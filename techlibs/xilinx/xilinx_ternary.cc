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
#include "kernel/macc.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// A bit of an addend: a signal or a constant, and whether it is inverted.
// The inversion of a subtracted addend is folded into the logic reading it.
struct TernaryBit {
	SigBit bit;
	bool inv;
	TernaryBit(SigBit b = State::S0, bool i = false) : bit(b), inv(i) {
		if (bit.wire == nullptr) {
			bool one = (bit.data == State::S1) != inv;
			bit = one ? State::S1 : State::S0;
			inv = false;
		}
	}
	bool is_const() const { return bit.wire == nullptr; }
	bool is_zero() const { return bit == State::S0; }
};
typedef std::vector<TernaryBit> TernaryOp;

// Lowest bit of an addend that is not constant zero
static int ternary_lo(const TernaryOp &op)
{
	int i = 0;
	while (i < GetSize(op) && op[i].is_zero())
		i++;
	return i;
}

// Lowest bit where two of 'ops' are not constant zero (w if none)
static int ternary_lo2(const std::vector<TernaryOp> &ops, int w)
{
	for (int i = 0; i < w; i++) {
		int n = 0;
		for (auto &op : ops)
			n += !op[i].is_zero();
		if (n >= 2)
			return i;
	}
	return w;
}

// Four addends can take a ternary adder and then a binary one, or a row of
// full adders (3:2) and then a ternary adder, which needs a single carry
// chain. Estimate the LUTs of each to choose: a carry-chain adder needs one
// for each bit with two non-zero inputs (or with one, right above such a bit
// in a ternary adder, for its carry-save bit); a full adder one for each bit
// with two signals among its inputs.
static bool ternary_prefer_fa(const std::vector<TernaryOp> &ops, int w, bool cin)
{
	std::vector<int> n3(w), m(w);
	int lo3 = cin ? 0 : ternary_lo2({ops[0], ops[1], ops[2]}, w);
	int add_add = 0, fa_add = 0;
	for (int i = 0; i < w; i++) {
		int nsig = 0;
		for (int j = 0; j < 3; j++) {
			n3[i] += !ops[j][i].is_zero();
			nsig += !ops[j][i].is_const();
		}
		bool d = !ops[3][i].is_zero();
		// inputs of the second stage: the ternary sum and d; or the full
		// adder sum, its carry from the bit below, and d
		bool r = n3[i] > 0 || i >= lo3;
		m[i] = (n3[i] > 0) + (i > 0 && n3[i-1] >= 2) + d;
		add_add += (n3[i] >= 2 || (n3[i] == 1 && i > 0 && n3[i-1] >= 2)) + (r && d);
		fa_add += (nsig >= 2) + (m[i] >= 2 || (m[i] == 1 && i > 0 && m[i-1] >= 2));
	}
	return fa_add <= add_add;
}

// A boolean function of up to four signals, as a truth table indexed by
// their values (bit j of the index is vars[j])
struct TernaryFunc {
	std::vector<SigBit> vars;
	int table = 0;

	bool depends(int j) const {
		for (int m = 0; m < (1 << GetSize(vars)); m++)
			if (((table >> m) & 1) != ((table >> (m ^ (1 << j))) & 1))
				return true;
		return false;
	}
	// The function as a constant or a single (inverted) signal, if it is one
	bool trivial(TernaryBit &t) const {
		int nsup = 0, sup = 0;
		for (int j = 0; j < GetSize(vars); j++)
			if (depends(j))
				nsup++, sup = j;
		if (nsup == 0)
			t = TernaryBit(table & 1 ? State::S1 : State::S0);
		else if (nsup == 1)
			t = TernaryBit(vars[sup], table & 1);
		return nsup <= 1;
	}
};

struct TernaryWorker {
	Module *module;
	SigMap sigmap;
	// inverter outputs and inputs, to read addend bits through inverters
	// (folded into the LUTs) and to reuse inverters
	dict<SigBit, SigBit> not_in, not_out;
	std::string src;

	TernaryWorker(Module *module) : module(module), sigmap(module) {
		for (auto cell : module->cells()) {
			if (!cell->type.in(ID($_NOT_), ID($not)))
				continue;
			SigSpec a = sigmap(cell->getPort(ID::A)), y = sigmap(cell->getPort(ID::Y));
			if (GetSize(a) != GetSize(y))
				continue;
			for (int i = 0; i < GetSize(y); i++)
				if (y[i].wire != nullptr) {
					not_in[y[i]] = a[i];
					not_out[a[i]] = y[i];
				}
		}
	}

	TernaryBit fold(SigBit bit, bool inv) {
		bit = sigmap(bit);
		for (int n = 0; n < 8 && not_in.count(bit); n++) {
			bit = not_in.at(bit);
			inv = !inv;
		}
		return TernaryBit(bit, inv);
	}

	SigBit materialize(const TernaryBit &t) {
		if (!t.inv)
			return t.bit;
		auto it = not_out.find(t.bit);
		if (it != not_out.end())
			return it->second;
		SigBit y = module->NotGate(NEW_ID, t.bit, src);
		not_out[t.bit] = y;
		return y;
	}

	// Truth tables of the parity of all of 'in' and of the majority of its
	// first three bits, over the signals among them
	static void funcs(const std::vector<TernaryBit> &in, TernaryFunc &fs, TernaryFunc &fk)
	{
		fs = fk = TernaryFunc();
		for (auto &t : in)
			if (!t.is_const() && std::find(fs.vars.begin(), fs.vars.end(), t.bit) == fs.vars.end())
				fs.vars.push_back(t.bit);
		fk.vars = fs.vars;
		int nv = GetSize(fs.vars);
		for (int m = 0; m < (1 << nv); m++) {
			bool p = false;
			int n = 0;
			for (int j = 0; j < GetSize(in); j++) {
				int idx = std::find(fs.vars.begin(), fs.vars.end(), in[j].bit) - fs.vars.begin();
				bool v = in[j].is_const() ? in[j].bit == State::S1 : (((m >> idx) & 1) != 0) != in[j].inv;
				p ^= v;
				if (j < 3)
					n += v;
			}
			if (p)
				fs.table |= 1 << m;
			if (n >= 2)
				fk.table |= 1 << m;
		}
	}

	// One LUT6_2 with I5 high: O6 (INIT[63:32]) computes f6 and O5
	// (INIT[31:0]) f5, both functions of the same signals on I0..I4. The
	// signals take the fastest of those pins, from I4 down, 'late' first (the
	// carry-save bit from the LUT below, which arrives last).
	std::pair<SigBit, SigBit> lut62(const TernaryFunc &f6, const TernaryFunc &f5, SigBit late = State::S0)
	{
		int nv = GetSize(f6.vars);
		log_assert(nv <= 5 && f5.vars == f6.vars);
		std::vector<int> order;
		for (int j = 0; j < nv; j++)
			if (f6.vars[j] == late)
				order.push_back(j);
		for (int j = 0; j < nv; j++)
			if (f6.vars[j] != late)
				order.push_back(j);
		std::vector<int> pin_of(nv);
		for (int p = 0; p < nv; p++)
			pin_of[order[p]] = 4 - p;
		Cell *lut = module->addCell(NEW_ID, ID(LUT6_2));
		Const init(State::S0, 64);
		for (int m = 0; m < 32; m++) {
			int idx = 0;
			for (int j = 0; j < nv; j++)
				if ((m >> pin_of[j]) & 1)
					idx |= 1 << j;
			init.set(m, (f5.table >> idx) & 1 ? State::S1 : State::S0);
			init.set(32 + m, (f6.table >> idx) & 1 ? State::S1 : State::S0);
		}
		lut->setParam(ID::INIT, init);
		static const IdString pins[6] = {ID(I0), ID(I1), ID(I2), ID(I3), ID(I4), ID(I5)};
		for (int p = 0; p < 5; p++)
			lut->setPort(pins[p], State::S0);
		lut->setPort(pins[5], State::S1);
		for (int j = 0; j < nv; j++)
			lut->setPort(pins[pin_of[j]], f6.vars[j]);
		SigBit o6 = module->addWire(NEW_ID), o5 = module->addWire(NEW_ID);
		lut->setPort(ID(O6), o6);
		lut->setPort(ID(O5), o5);
		lut->set_src_attribute(src);
		return {o6, o5};
	}

	// A parity function of signals, as plain logic for abc9 to map
	SigBit parity(const TernaryFunc &f)
	{
		TernaryBit t;
		if (f.trivial(t))
			return materialize(t);
		SigBit y;
		bool first = true;
		for (int j = 0; j < GetSize(f.vars); j++)
			if (f.depends(j)) {
				y = first ? f.vars[j] : module->XorGate(NEW_ID, y, f.vars[j], src);
				first = false;
			}
		if (f.table & 1)
			y = module->NotGate(NEW_ID, y, src);
		return y;
	}

	// A row of full adders: the bitwise parity of three addends, and their
	// majority shifted up by one bit (one LUT6_2 per bit for both)
	std::vector<TernaryOp> fa_row(const std::vector<TernaryOp> &ops, int w)
	{
		TernaryOp s(w), c(w);
		for (int i = 0; i < w; i++) {
			TernaryFunc fs, fk;
			funcs({ops[0][i], ops[1][i], ops[2][i]}, fs, fk);
			TernaryBit k;
			if (i + 1 < w && !fk.trivial(k)) {
				auto o = lut62(fs, fk);
				s[i] = TernaryBit(o.first);
				c[i + 1] = TernaryBit(o.second);
			} else {
				if (!fs.trivial(s[i]))
					s[i] = TernaryBit(parity(fs));
				if (i + 1 < w)
					c[i + 1] = k;
			}
		}
		return {s, c};
	}

	// Sum of three w-bit addends and up to two carry-in bits (of weight 1),
	// modulo 2^w. As in Vivado's ternary adder, one LUT6_2 per bit computes
	// the carry-save bit k_i = maj(x_i, y_i, z_i) on O5 and the sum bit
	// x_i ^ y_i ^ z_i ^ k_(i-1) on O6, which drives the carry chain (with
	// DI_i = k_(i-1)); the chain adds the two rows. Below the lowest bit with
	// two non-zero addend bits, there is nothing to add.
	SigSpec add3(const std::vector<TernaryOp> &ops, const std::vector<TernaryBit> &cins, int w)
	{
		log_assert(GetSize(ops) == 3 && GetSize(cins) <= 2);
		SigSpec out;
		int lo = cins.empty() ? ternary_lo2(ops, w) : 0;
		for (int i = 0; i < lo; i++) {
			TernaryBit b;
			for (auto &op : ops)
				if (!op[i].is_zero())
					b = op[i];
			out.append(materialize(b));
		}
		if (lo == w)
			return out;

		// A carry-in signal goes to the chain input, a constant one rather
		// into the LUT of the lowest bit (as k_(lo-1)): with a constant one on
		// the chain input, abc9 computes the lowest sum bits as inverters of
		// the LUT outputs instead of taking them from the chain. Two constant
		// ones are a one at bit 1, where the chain then starts.
		TernaryBit ci, kprev;
		int ci_pos = 0;
		if (GetSize(cins) == 2 && cins[0].is_const() && cins[1].is_const())
			ci = TernaryBit(State::S1), ci_pos = 1;
		else if (GetSize(cins) == 2) {
			bool swap = cins[0].is_const();
			ci = cins[swap ? 1 : 0];
			kprev = cins[swap ? 0 : 1];
		} else if (GetSize(cins) == 1)
			(cins[0].is_const() ? kprev : ci) = cins[0];
		SigSpec s, di;
		for (int i = lo; i < w; i++) {
			TernaryFunc fs, fk;
			funcs({ops[0][i], ops[1][i], ops[2][i], kprev}, fs, fk);

			// k_i is not needed by the top bit, and needs no logic if it is a
			// constant or one of the inputs
			TernaryBit knext;
			bool dual = i + 1 < w && !fk.trivial(knext);
			SigBit sbit;
			if (dual) {
				auto o = lut62(fs, fk, kprev.bit);
				sbit = o.first;
				knext = TernaryBit(o.second);
			} else
				sbit = parity(fs);
			s.append(sbit);
			di.append(materialize(kprev));
			kprev = knext;
		}

		// No carry can enter the bits below the first one with k_(i-1) or a
		// carry-in: their sums are the LUT outputs
		int n = w - lo, c0 = 0;
		while (c0 < n && di[c0] == State::S0 && (ci.is_zero() || c0 < ci_pos))
			out.append(s[c0++]);
		log_assert(ci.is_zero() || c0 == ci_pos);
		s = s.extract_end(c0);
		di = di.extract_end(c0);
		n -= c0;
		SigBit carry;
		for (int c = 0; 4 * c < n; c++) {
			SigSpec cs, cd;
			for (int j = 4 * c; j < 4 * c + 4; j++) {
				cs.append(j < n ? s[j] : State::S0);
				cd.append(j < n ? di[j] : State::S0);
			}
			SigSpec o = module->addWire(NEW_ID, 4), co = module->addWire(NEW_ID, 4);
			Cell *cy = module->addCell(NEW_ID, ID(CARRY4));
			cy->setPort(ID(CYINIT), c == 0 ? materialize(ci) : State::S0);
			cy->setPort(ID(CI), c == 0 ? State::S0 : carry);
			cy->setPort(ID(DI), cd);
			cy->setPort(ID::S, cs);
			cy->setPort(ID::O, o);
			cy->setPort(ID(CO), co);
			cy->set_src_attribute(src);
			out.append(o.extract(0, std::min(4, n - 4 * c)));
			carry = co[3];
		}
		return out;
	}

	// Sum of two w-bit addends, as an $add of the bits from the lowest one
	// where both are non-zero
	SigSpec add2(const TernaryOp &a, const TernaryOp &b, int w)
	{
		SigSpec out, sa, sb;
		int lo = std::max(ternary_lo(a), ternary_lo(b));
		for (int i = 0; i < w; i++) {
			if (i < lo)
				out.append(materialize(a[i].is_zero() ? b[i] : a[i]));
			else {
				sa.append(materialize(a[i]));
				sb.append(materialize(b[i]));
			}
		}
		if (lo < w) {
			SigSpec y = module->addWire(NEW_ID, w - lo);
			module->addAdd(NEW_ID, sa, sb, y, false, src);
			out.append(y);
		}
		return out;
	}

	bool run(Cell *cell)
	{
		src = cell->get_src_attribute();
		Macc macc;
		macc.from_cell(cell);
		SigSpec y = cell->getPort(ID::Y);
		int w = GetSize(y);
		if (w < 3)
			return false;

		// Addends extended to w bits, constants summed, bits of weight 1
		// (single-bit addends, and the +1 of each subtracted addend) kept
		// for the carry inputs
		std::vector<TernaryOp> ops;
		std::vector<TernaryBit> cins;
		Const k(State::S0, w);
		int nplus = 0;
		for (auto &term : macc.terms) {
			if (GetSize(term.in_b) != 0)
				return false;
			SigSpec a = term.in_a;
			if (GetSize(a) == 0)
				continue;
			if (GetSize(a) > w)
				a = a.extract(0, w);
			else
				a.extend_u0(w, term.is_signed);
			if (a.is_fully_const()) {
				k = term.do_subtract ? const_sub(k, a.as_const(), false, false, w) : const_add(k, a.as_const(), false, false, w);
				continue;
			}
			if (!term.do_subtract && a.extract(1, w - 1).is_fully_zero()) {
				cins.push_back(fold(a[0], false));
				continue;
			}
			TernaryOp op;
			for (auto bit : a)
				op.push_back(fold(bit, term.do_subtract));
			ops.push_back(op);
			if (term.do_subtract)
				nplus++;
		}
		// the first adder takes up to two carry-in bits; the +1s go into the
		// constant addend instead when there is one, or when there are too many
		if (!k.is_fully_zero() || nplus + GetSize(cins) > 2) {
			k = const_add(k, Const(nplus, w), false, false, w);
			nplus = 0;
		}
		while (GetSize(cins) > 2) {
			TernaryOp op(w);
			op[0] = cins.back();
			cins.pop_back();
			ops.push_back(op);
		}
		for (int i = 0; i < nplus; i++)
			cins.push_back(TernaryBit(State::S1));
		if (!k.is_fully_zero()) {
			TernaryOp op;
			for (int i = 0; i < w; i++)
				op.push_back(TernaryBit(k[i]));
			ops.push_back(op);
		}
		if (GetSize(ops) < 3)
			return false;

		log("  %s: %d addends of %d bits\n", cell, GetSize(ops), w);

		// Add three addends at a time, those starting at the lowest bits
		// first; two left at the end take a binary adder, unless four were
		// left and a row of full adders went first
		while (GetSize(ops) > 1) {
			std::stable_sort(ops.begin(), ops.end(), [](const TernaryOp &a, const TernaryOp &b) {
				return ternary_lo(a) < ternary_lo(b);
			});
			if (GetSize(ops) == 4 && ternary_prefer_fa(ops, w, !cins.empty())) {
				std::vector<TernaryOp> sc = fa_row({ops[0], ops[1], ops[2]}, w);
				ops = {sc[0], sc[1], ops[3]};
				continue;
			}
			SigSpec sum;
			if (GetSize(ops) >= 3) {
				std::vector<TernaryOp> three(ops.begin(), ops.begin() + 3);
				sum = add3(three, cins, w);
				cins.clear();
				ops.erase(ops.begin(), ops.begin() + 3);
			} else {
				sum = add2(ops[0], ops[1], w);
				ops.clear();
			}
			TernaryOp op;
			for (auto bit : sum)
				op.push_back(TernaryBit(bit));
			ops.push_back(op);
		}
		SigSpec sum;
		for (auto &t : ops[0])
			sum.append(materialize(t));
		module->connect(y, sum);
		module->remove(cell);
		return true;
	}
};

struct XilinxTernaryPass : public Pass {
	XilinxTernaryPass() : Pass("xilinx_ternary", "Xilinx: map sums of three or more addends to ternary adders") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_ternary [selection]\n");
		log("\n");
		log("Map $macc cells that only sum (or subtract) three or more addends to ternary\n");
		log("adders: per bit, one LUT6_2 computes the carry-save carry on O5 and the sum\n");
		log("bit on O6, which feeds a CARRY4 chain. This takes one LUT per bit, where a\n");
		log("carry-save row followed by a binary adder takes two. Constant addends are\n");
		log("folded into the LUTs, and up to two bits of weight one (e.g. the +1 of a\n");
		log("subtracted addend) use the carry inputs. More addends are summed three at a\n");
		log("time, with a binary adder ($add) for two left at the end.\n");
		log("\n");
		log("This pass is meant to run before $macc and $alu cells are mapped (techmap),\n");
		log("for devices with LUT6_2 and CARRY4/CARRY8 primitives.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing XILINX_TERNARY pass (map multi-operand sums to ternary adders).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			std::vector<Cell*> maccs;
			for (auto cell : module->selected_cells())
				if (cell->type == ID($macc) || cell->type == ID($macc_v2))
					maccs.push_back(cell);
			if (maccs.empty())
				continue;
			TernaryWorker worker(module);
			for (auto cell : maccs)
				worker.run(cell);
		}
	}
} XilinxTernaryPass;

PRIVATE_NAMESPACE_END
