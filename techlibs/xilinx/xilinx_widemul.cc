/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// The DSP48E2 multiplier is 27 x 18 bits (signed). Its PCIN >> 17 cascade
// input lines up partial products whose weights differ by 2^17, so operands
// are split into 17-bit chunks (unsigned, i.e. zero-extended to 18 bits)
// with a signed (or zero-extended) top chunk.
static const int CHUNK = 17;

// Number of chunks of a 'width'-bit operand whose top chunk may be up to
// 'top' bits wide (one bit less if unsigned, to leave a zero sign bit)
static int widemul_nchunks(int width, bool is_signed, int top)
{
	int lim = is_signed ? top : top - 1;
	return width <= lim ? 1 : 1 + (width - lim + CHUNK - 1) / CHUNK;
}

// Chunk i of n of 'sig', as a signed multiplier operand
static SigSpec widemul_chunk(const SigSpec &sig, bool is_signed, int n, int i)
{
	SigSpec c = i < n - 1 ? sig.extract(CHUNK * i, CHUNK) : sig.extract_end(CHUNK * i);
	if (i < n - 1 || !is_signed)
		c.append(State::S0);
	return c;
}

// Width of 'sig' without redundant sign (or leading zero) bits
static int widemul_width(const SigSpec &sig, bool is_signed)
{
	int w = GetSize(sig);
	while (w > 1 && (is_signed ? sig[w-1] == sig[w-2] : sig[w-1] == State::S0))
		w--;
	return w;
}

// Value range of a signed multiplier operand (an unsigned chunk carries a
// zero sign bit)
static std::pair<int64_t, int64_t> widemul_range(const SigSpec &sig)
{
	int w = GetSize(sig);
	if (sig[w-1] == State::S0)
		return {0, (int64_t(1) << (w-1)) - 1};
	return {-(int64_t(1) << (w-1)), (int64_t(1) << (w-1)) - 1};
}

// Bits needed for values in [lo, hi]: two's complement if is_signed, else
// unsigned (lo >= 0)
static int widemul_bits(int64_t lo, int64_t hi, bool is_signed)
{
	int w = 1;
	if (is_signed)
		while (lo < -(int64_t(1) << (w-1)) || hi > (int64_t(1) << (w-1)) - 1)
			w++;
	else
		while (hi > (int64_t(1) << w) - 1)
			w++;
	return w;
}

struct WidemulProd {
	int i, j, k;   // A chunk, B chunk, column (weight 2^(17*k))
};

struct WidemulPart {
	int chain;     // the chain it comes from
	int offset;    // bit position of its LSB in the product
	SigSpec sig;
	bool tail;     // the chain result (sign-extended upwards), else a 17-bit slice
};

static void widemul(Module *module, Cell *mul, int maxchain, bool retime)
{
	bool is_signed = mul->getParam(ID::A_SIGNED).as_bool();
	if (mul->getParam(ID::B_SIGNED).as_bool() != is_signed)
		return;

	SigMap sigmap(module);
	SigSpec Y = mul->getPort(ID::Y);
	int wy = GetSize(Y);
	SigSpec A = sigmap(mul->getPort(ID::A)), B = sigmap(mul->getPort(ID::B));
	// operand bits at or above Y_WIDTH do not affect Y
	if (GetSize(A) > wy)
		A = A.extract(0, wy);
	if (GetSize(B) > wy)
		B = B.extract(0, wy);
	A = A.extract(0, widemul_width(A, is_signed));
	B = B.extract(0, widemul_width(B, is_signed));

	// A chunks go to the 27-bit A port, B chunks to the 18-bit B port; pick
	// the orientation with fewer DSPs, and on a tie the one with a single row.
	// (mul2dsp always puts the wider operand on A, so e.g. 30 x 20 bits takes
	// four DSPs there instead of two.)
	int na = widemul_nchunks(GetSize(A), is_signed, 27), nb = widemul_nchunks(GetSize(B), is_signed, 18);
	int na2 = widemul_nchunks(GetSize(B), is_signed, 27), nb2 = widemul_nchunks(GetSize(A), is_signed, 18);
	if (na2 * nb2 < na * nb || (na2 * nb2 == na * nb && std::min(na2, nb2) < std::min(na, nb))) {
		std::swap(A, B);
		na = na2, nb = nb2;
	}
	// a single DSP is left to mul2dsp
	if (na * nb < 2)
		return;

	std::vector<SigSpec> ca, cb;
	for (int i = 0; i < na; i++)
		ca.push_back(widemul_chunk(A, is_signed, na, i));
	for (int j = 0; j < nb; j++)
		cb.push_back(widemul_chunk(B, is_signed, nb, j));

	// List the products column by column (lowest weight first, then by A
	// chunk) and cut the list into chains of 'len' products, as Vivado does
	// (by default as many as the larger number of chunks). A chain is also
	// cut where a column is missing, since links only shift by 17 bits.
	// Products with a constant zero chunk, and columns at or above Y_WIDTH,
	// are skipped.
	int len = maxchain > 0 ? maxchain : std::max(na, nb);
	std::vector<std::vector<WidemulProd>> chains;
	for (int k = 0; k < na + nb - 1 && CHUNK * k < wy; k++)
		for (int i = 0; i < na; i++) {
			int j = k - i;
			if (j < 0 || j >= nb || ca[i].is_fully_zero() || cb[j].is_fully_zero())
				continue;
			if (chains.empty() || GetSize(chains.back()) == len || chains.back().back().k < k - 1)
				chains.emplace_back();
			chains.back().push_back({i, j, k});
		}
	if (chains.empty())
		return;

	// Value range of each chain's running sum, to check that it never
	// overflows the 48-bit DSP accumulator, and to keep only the bits of each
	// chain's tail that can be non-redundant
	std::vector<int> tail_bits;
	for (auto &chain : chains) {
		int64_t lo = 0, hi = 0;
		int acc_k = chain.front().k;
		for (auto &p : chain) {
			auto ra = widemul_range(ca[p.i]), rb = widemul_range(cb[p.j]);
			int64_t c[4] = {ra.first * rb.first, ra.first * rb.second, ra.second * rb.first, ra.second * rb.second};
			int64_t plo = *std::min_element(c, c + 4), phi = *std::max_element(c, c + 4);
			if (p.k != acc_k) {
				// arithmetic shift right by 17 (floor)
				lo >>= CHUNK, hi >>= CHUNK;
				acc_k = p.k;
			}
			lo += plo, hi += phi;
			if (lo < -(int64_t(1) << 47) || hi > (int64_t(1) << 47) - 1) {
				log("Not decomposing %s: a cascade chain could overflow the DSP48E2 accumulator.\n", mul);
				return;
			}
		}
		tail_bits.push_back(widemul_bits(lo, hi, is_signed));
	}

	// The product register to move onto the chain outputs, if any: the only
	// user of Y, taking nothing but Y bits on D, clocked, with no async
	// controls, and with zero (or no) reset and init values
	Cell *ffcell = nullptr;
	FfInitVals initvals(&sigmap, module);
	FfData ff;
	std::vector<int> ffmap;
	if (retime) {
		dict<SigBit, int> yidx;
		SigSpec sigY = sigmap(Y);
		for (int i = 0; i < wy; i++)
			if (sigY[i].wire && !yidx.count(sigY[i]))
				yidx[sigY[i]] = i;
		bool ok = true;
		for (auto cell : module->cells()) {
			if (cell == mul)
				continue;
			for (auto &conn : cell->connections())
				for (auto bit : sigmap(conn.second))
					if (yidx.count(bit)) {
						if (ffcell && ffcell != cell)
							ok = false;
						ffcell = cell;
					}
		}
		for (auto wire : module->wires())
			if (wire->port_id > 0)
				for (auto bit : sigmap(wire))
					if (yidx.count(bit))
						ok = false;
		if (ok && ffcell && ffcell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce))) {
			ff = FfData(&initvals, ffcell);
			ok = ff.has_clk && !ff.has_gclk && !ff.has_aload && !ff.has_arst && !ff.has_sr && !ff.is_fine && !ff.is_anyinit &&
					(!ff.has_srst || ff.val_srst.is_fully_zero());
			for (int i = 0; ok && i < GetSize(ff.val_init); i++)
				ok = ff.val_init[i] == State::S0 || ff.val_init[i] == State::Sx;
			// Y must reach the register on D only
			for (auto &sig : {ff.sig_clk, ff.sig_ce, ff.sig_srst})
				for (auto bit : sigmap(sig))
					if (yidx.count(bit))
						ok = false;
			SigSpec D = sigmap(ff.sig_d);
			for (int i = 0; ok && i < GetSize(D); i++) {
				auto it = yidx.find(D[i]);
				if (it == yidx.end())
					ok = false;
				else
					ffmap.push_back(it->second);
			}
		} else
			ok = false;
		if (!ok)
			ffcell = nullptr;
	}

	std::string src = mul->get_src_attribute();
	auto add_cell = [&](Cell *cell) {
		if (!module->design->selected_whole_module(module))
			module->design->select(module, cell);
		return cell;
	};

	// Build the chains. Each chain sums its products in order, shifting the
	// running sum right by 17 bits when it moves on to the next column; the
	// 17 bits shifted out are final bits of the chain's value (a slice).
	// The last sum of a chain (its tail) only needs its significant bits (by
	// value range) up to Y_WIDTH; the higher bits are sign (or zero)
	// extension. Its adder is that wide, so that the register on all of its
	// bits can become the P register of the chain's last DSP.
	std::vector<WidemulPart> parts;
	int nprod = 0;
	for (int c = 0; c < GetSize(chains); c++) {
		auto &chain = chains[c];
		SigSpec acc;
		int acc_k = -1;
		for (int n = 0; n < GetSize(chain); n++) {
			auto &p = chain[n];
			bool last = n == GetSize(chain) - 1;
			int need = std::min(wy - CHUNK * p.k, tail_bits[c]);
			int wprod = GetSize(ca[p.i]) + GetSize(cb[p.j]);
			// a product only used as the tail of a chain may be truncated
			SigSpec prod = module->addWire(NEW_ID, last && n == 0 ? std::min(wprod, need) : wprod);
			add_cell(module->addMul(NEW_ID, ca[p.i], cb[p.j], prod, true, src));
			nprod++;
			if (n == 0) {
				acc = prod;
				acc_k = p.k;
				continue;
			}
			SigSpec in = acc;
			if (p.k != acc_k) {
				log_assert(p.k == acc_k + 1);
				parts.push_back({c, CHUNK * acc_k, acc.extract(0, CHUNK), false});
				in = acc.extract_end(CHUNK);
				acc_k = p.k;
			}
			SigSpec sum = module->addWire(NEW_ID, last ? std::min(48, need) : 48);
			add_cell(module->addAdd(NEW_ID, prod, in, sum, true, src));
			acc = sum;
		}
		parts.push_back({c, CHUNK * acc_k, acc, true});
	}

	// Register the slices and tails instead of the product
	if (ffcell) {
		bool init_zero = !ff.val_init.is_fully_undef();
		for (auto &part : parts) {
			int w = std::min(GetSize(part.sig), wy - part.offset);
			FfData nf = ff;
			nf.cell = nullptr;
			nf.name = module->twines().add(NEW_ID);
			nf.width = w;
			nf.sig_d = part.sig.extract(0, w);
			nf.sig_q = module->addWire(NEW_ID, w);
			nf.val_init = Const(init_zero ? State::S0 : State::Sx, w);
			if (nf.has_srst)
				nf.val_srst = Const(State::S0, w);
			add_cell(nf.emit());
			part.sig = nf.sig_q;
		}
	}

	// Each chain's value: its slices, then its tail. The tails of an unsigned
	// product are never negative (zero-extended). A signed tail with its sign
	// bit s at position p below the top of Y is not sign-extended (which
	// would add a full row of s bits to the fabric adder): since
	// sext(x) == x with s inverted, minus 2^p (modulo 2^Y_WIDTH), use ~s at p
	// and fold the sum of all those -2^p into the free upper bits of the row
	// with the lowest p. Adding a constant T and a single bit b = ~s0 there
	// gives bits that are constants, b or ~b.
	std::vector<std::vector<SigBit>> value(GetSize(chains), std::vector<SigBit>(wy, State::S0));
	std::vector<int> signpos(GetSize(chains), -1);
	std::vector<SigBit> signbit(GetSize(chains));
	for (auto &part : parts) {
		auto &v = value[part.chain];
		int w = GetSize(part.sig);
		for (int b = 0; b < w && part.offset + b < wy; b++)
			v[part.offset + b] = part.sig[b];
		if (part.tail && is_signed && part.offset + w < wy) {
			int p = part.offset + w - 1;
			signpos[part.chain] = p;
			signbit[part.chain] = part.sig[w-1];
			v[p] = add_cell(module->addNot(NEW_ID, part.sig[w-1], module->addWire(NEW_ID)))->getPort(ID::Y);
		}
	}
	int r0 = -1;
	for (int c = 0; c < GetSize(chains); c++)
		if (signpos[c] >= 0 && (r0 < 0 || signpos[c] < signpos[r0]))
			r0 = c;
	if (r0 >= 0) {
		int p0 = signpos[r0], n = wy - p0;
		// T = -sum(2^(p - p0)) and T + 1, modulo 2^n
		std::vector<bool> t(n, false), t1;
		for (int c = 0; c < GetSize(chains); c++)
			if (signpos[c] >= 0)
				for (int q = signpos[c] - p0; q < n; q++) {
					t[q] = !t[q];
					if (t[q])   // borrow
						continue;
					break;
				}
		t1 = t;
		for (int q = 0; q < n; q++) {
			t1[q] = !t1[q];
			if (t1[q])   // no carry
				break;
		}
		SigBit b = value[r0][p0], s0 = signbit[r0];
		for (int q = 0; q < n; q++)
			value[r0][p0 + q] = t[q] == t1[q] ? SigBit(t[q] ? State::S1 : State::S0) : t1[q] ? b : s0;
	}

	// Add the chain values in fabric. Below the lowest bit with two
	// contributions, the product bits are taken directly.
	int lo = wy;
	for (int b = 0; b < wy && lo == wy; b++) {
		int n = 0;
		for (auto &v : value)
			if (v[b] != State::S0)
				n++;
		if (n >= 2)
			lo = b;
	}
	std::vector<SigBit> result(wy, State::S0);
	for (int b = 0; b < lo; b++)
		for (auto &v : value)
			if (v[b] != State::S0)
				result[b] = v[b];
	SigSpec sum;
	for (auto &v : value) {
		SigSpec hi = SigSpec(v).extract(lo, wy - lo);
		if (hi.is_fully_zero())
			continue;
		if (GetSize(sum) == 0) {
			sum = hi;
			continue;
		}
		SigSpec s = module->addWire(NEW_ID, wy - lo);
		add_cell(module->addAdd(NEW_ID, sum, hi, s, false, src));
		sum = s;
	}
	for (int b = lo; b < wy; b++)
		result[b] = GetSize(sum) ? sum[b - lo] : State::S0;

	log("Decomposed %s (%d x %d bits) into %d DSP products in %d cascade chains", mul, GetSize(A), GetSize(B), nprod, GetSize(chains));
	module->remove(mul);
	if (ffcell) {
		log(", moving register %s onto the chain outputs.\n", ffcell);
		SigSpec Q = ff.sig_q;
		ff.remove();
		for (int t = 0; t < GetSize(Q); t++)
			module->connect(Q[t], result[ffmap[t]]);
	} else {
		log(".\n");
		module->connect(Y, SigSpec(result));
	}
}

struct XilinxWidemulPass : public Pass {
	XilinxWidemulPass() : Pass("xilinx_widemul", "Xilinx: split wide multipliers into DSP48E2 cascade columns") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_widemul [options] [selection]\n");
		log("\n");
		log("Split $mul cells that need more than one DSP48E2 into products of 17-bit\n");
		log("operand chunks (the operand that fits the 27-bit multiplier port best goes\n");
		log("there). Products of equal weight (a column) are summed in a chain, and\n");
		log("consecutive columns are linked by a 17-bit right shift, which xilinx_dsp maps\n");
		log("to PCOUT->PCIN cascades. As in Vivado, the products are listed column by\n");
		log("column and the list is cut into chains as long as the larger number of\n");
		log("chunks (e.g. three chains of three DSPs for 48 x 48 bits); only the chain\n");
		log("results are added in fabric.\n");
		log("\n");
		log("When the product only feeds a flip-flop (clocked, no asynchronous controls,\n");
		log("zero or no reset and init values), the flip-flop is moved onto the chain\n");
		log("outputs, so that xilinx_dsp can absorb it into the P registers of the last\n");
		log("DSP of each chain. The fabric adder then follows the registers.\n");
		log("\n");
		log("This pass is meant to run before multipliers are mapped to DSPs (mul2dsp).\n");
		log("\n");
		log("    -chain <n>\n");
		log("        number of DSPs per cascade chain (default: the larger number of\n");
		log("        operand chunks)\n");
		log("\n");
		log("    -noretime\n");
		log("        do not move a flip-flop on the product onto the chain outputs\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing XILINX_WIDEMUL pass (split wide multipliers for DSP48E2).\n");

		int maxchain = 0;
		bool retime = true;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-chain" && argidx+1 < args.size()) {
				maxchain = std::max(1, atoi(args[++argidx].c_str()));
				continue;
			}
			if (args[argidx] == "-noretime") {
				retime = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			std::vector<Cell*> muls;
			for (auto cell : module->selected_cells())
				if (cell->type == ID($mul))
					muls.push_back(cell);
			for (auto cell : muls)
				widemul(module, cell, maxchain, retime);
		}
	}
} XilinxWidemulPass;

PRIVATE_NAMESPACE_END
