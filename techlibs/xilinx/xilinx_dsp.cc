/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2019  Eddie Hung    <eddie@fpgeh.com>
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
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Helpers used by the pattern matchers below to reason about the range of
// values a DSP48E1/DSP48E2 computes. The DSP always produces a full 48-bit
// result, whereas the netlist it replaces may only use (and re-extend) some
// of its low bits; absorbing an adder or forming a cascade is only valid if
// those views agree.

// Smallest n such that 'sig' is the sign-extension of sig[n-1:0], i.e. the
// number of significant bits of 'sig' as a two's complement number
static int xilinx_dsp_signed_width(const SigSpec &sig)
{
	int n = GetSize(sig);
	while (n > 1 && sig[n-1] == sig[n-2])
		n--;
	return n;
}

static std::string xilinx_dsp_param_str(Cell *dsp, IdString name, const char *def)
{
	return dsp->hasParam(name) ? dsp->getParam(name).decode_string() : std::string(def);
}

// Upper bound on the number of significant (two's complement) bits of the
// multiplier output of a DSP48E1/DSP48E2, derived from its operands; 48 if
// unknown. *nonneg is set if the product is known to be non-negative.
static int xilinx_dsp_product_width(const SigMap &sigmap, Cell *dsp, bool *nonneg = nullptr)
{
	if (nonneg)
		*nonneg = false;
	if (!dsp->type.in(ID(DSP48E1), ID(DSP48E2)))
		return 48;
	if (xilinx_dsp_param_str(dsp, ID(USE_MULT), "MULTIPLY") != "MULTIPLY")
		return 48;
	if (xilinx_dsp_param_str(dsp, ID(A_INPUT), "DIRECT") != "DIRECT" ||
			xilinx_dsp_param_str(dsp, ID(B_INPUT), "DIRECT") != "DIRECT")
		return 48;
	bool e2 = dsp->type == ID(DSP48E2);
	if (e2 && xilinx_dsp_param_str(dsp, ID(BMULTSEL), "B") != "B")
		return 48;
	if (!dsp->hasPort(ID::A) || !dsp->hasPort(ID::B))
		return 48;
	int aw = e2 ? 27 : 25;
	SigSpec A = sigmap(dsp->getPort(ID::A));
	A.extend_u0(30, true);
	A = A.extract(0, aw);
	int wa = xilinx_dsp_signed_width(A);
	bool nna = A[aw-1] == State::S0;
	bool preadd = e2 ? xilinx_dsp_param_str(dsp, ID(AMULTSEL), "A") == "AD"
			: xilinx_dsp_param_str(dsp, ID(USE_DPORT), "FALSE") == "TRUE";
	if (preadd) {
		SigSpec D = dsp->hasPort(ID::D) ? sigmap(dsp->getPort(ID::D)) : SigSpec(State::S0, aw);
		D.extend_u0(aw, true);
		wa = std::min(aw, std::max(wa, xilinx_dsp_signed_width(D)) + 1);
		nna = false;
	}
	SigSpec B = sigmap(dsp->getPort(ID::B));
	B.extend_u0(18, true);
	int wb = xilinx_dsp_signed_width(B);
	bool nnb = B[17] == State::S0;
	if (nonneg)
		*nonneg = nna && nnb;
	// a product with at least one non-negative operand needs one bit less
	return std::min(48, wa + wb - ((nna || nnb) ? 1 : 0));
}

// Range of the full 48-bit result of a DSP48E1/DSP48E2 computing M (Z = 0)
// or M +/- Z with Z = C: an upper bound on its significant (two's
// complement) bits, and whether it is known to be non-negative. If 'pcin' is
// given, Z may instead carry that range right-shifted by 'shift' (the cell is
// about to take PCIN from the previous element of a cascade chain); both
// possibilities are covered. {48, false} if unknown.
struct XilinxDspRange {
	int width;
	bool nonneg;
};

static XilinxDspRange xilinx_dsp_range(const SigMap &sigmap, Cell *dsp, const XilinxDspRange *pcin = nullptr, int shift = 0)
{
	const XilinxDspRange unknown = {48, false};
	if (!dsp->type.in(ID(DSP48E1), ID(DSP48E2)))
		return unknown;
	SigSpec opmode = dsp->hasPort(ID(OPMODE)) ? sigmap(dsp->getPort(ID(OPMODE))) : SigSpec();
	SigSpec alumode = dsp->hasPort(ID(ALUMODE)) ? sigmap(dsp->getPort(ID(ALUMODE))) : SigSpec(State::S0, 4);
	SigSpec carryinsel = dsp->hasPort(ID(CARRYINSEL)) ? sigmap(dsp->getPort(ID(CARRYINSEL))) : SigSpec(State::S0, 3);
	SigSpec carryin = dsp->hasPort(ID(CARRYIN)) ? sigmap(dsp->getPort(ID(CARRYIN))) : SigSpec(State::S0);
	if (GetSize(opmode) < 7 || !opmode.is_fully_const() || !alumode.is_fully_const() ||
			!carryinsel.is_fully_zero() || !carryin.is_fully_const())
		return unknown;
	// Z + M or Z - M (ALUMODE 0000/0011, no carry-in), or M - Z (ALUMODE 0001
	// with carry-in, i.e. ~Z + M + 1): all fit in max(width(M), width(Z)) + 1
	Const am = alumode.as_const(), ci = carryin.as_const();
	bool add = am == Const::from_string("0000") && ci.is_fully_zero();
	bool sub = (am == Const::from_string("0011") && ci.is_fully_zero()) ||
			(am == Const::from_string("0001") && ci.is_fully_ones());
	if (!add && !sub)
		return unknown;
	Const op = opmode.as_const();
	// X and Y must select M; W (DSP48E2 only) must select 0
	if (op.extract(0, 4) != Const::from_string("0101"))
		return unknown;
	if (dsp->type == ID(DSP48E2) && (GetSize(op) < 9 || op.extract(7, 2) != Const::from_string("00")))
		return unknown;
	bool nonneg_m;
	int wm = xilinx_dsp_product_width(sigmap, dsp, &nonneg_m);
	Const z = op.extract(4, 3);
	if (z == Const::from_string("000"))
		return add ? XilinxDspRange{wm, nonneg_m} : unknown;
	if (z != Const::from_string("011") || !dsp->hasPort(ID::C))
		return unknown;
	SigSpec C = sigmap(dsp->getPort(ID::C));
	int wz = xilinx_dsp_signed_width(C);
	bool nonneg_z = C[GetSize(C)-1] == State::S0;
	if (pcin) {
		wz = std::max(wz, std::max(1, pcin->width - shift));
		nonneg_z = nonneg_z && pcin->nonneg;
	}
	return XilinxDspRange{std::min(48, std::max(wm, wz) + 1), add && nonneg_m && nonneg_z};
}

// The post-adder input 'in' is 'sigP' (the used low bits of the DSP's
// product), extended to 'y_width' by the adder. Since the DSP adds its full
// (sign-extended) product instead, the extension bits must agree with it.
static bool xilinx_dsp_postadd_ok(const SigMap &sigmap, Cell *dsp, const SigSpec &in, bool in_signed, int y_width, const SigSpec &sigP)
{
	int k = GetSize(sigP);
	if (k == 0)
		return false;
	if (y_width <= k)
		return true;
	SigSpec ext = in;
	ext.extend_u0(std::max(y_width, GetSize(ext)), in_signed);
	SigSpec upper = ext.extract(k, y_width - k);
	bool nonneg;
	int wm = xilinx_dsp_product_width(sigmap, dsp, &nonneg);
	if (upper == SigSpec(sigP[k-1], y_width - k))
		return wm <= k;
	if (upper.is_fully_zero())
		return nonneg && wm <= k + 1;
	return false;
}

// Can the multiplier product of 'dsp' be scaled by 2**shift by left-shifting
// one of its operands, without overflowing the operand? B is preferred; A is
// only used when the pre-adder is not (going to be) used.
static int xilinx_dsp_shift_operand(const SigMap &sigmap, Cell *dsp, int shift, bool preadd)
{
	SigSpec B = sigmap(dsp->getPort(ID::B));
	B.extend_u0(18, true);
	if (xilinx_dsp_signed_width(B) + shift <= 18)
		return 'B';
	if (preadd)
		return 0;
	int aw = dsp->type == ID(DSP48E2) ? 27 : 25;
	SigSpec A = sigmap(dsp->getPort(ID::A));
	A.extend_u0(30, true);
	if (xilinx_dsp_signed_width(A) + shift <= aw)
		return 'A';
	return 0;
}

static bool xilinx_dsp_can_shift(const SigMap &sigmap, Cell *dsp, int shift, bool preadd)
{
	return xilinx_dsp_shift_operand(sigmap, dsp, shift, preadd) != 0;
}

// 'next' has its C input driven by the P output of 'prev' = chain.back()
// (right-shifted by 'shift' bits, possibly truncated and extended). Check that
// taking the full PCOUT of 'prev' via PCIN instead does not change anything
// observable: either the whole of C equals PCIN (using the range of 'prev''s
// result, propagated along the cascade chain), or the bits of 'next''s result
// that could differ (at and above the first mismatching C bit -- carries only
// propagate upwards) are not used at all.
template<typename Chain, typename NUsers>
static bool xilinx_dsp_cascade_ok(const SigMap &sigmap, const Chain &chain, Cell *next, int shift, NUsers nusers)
{
	Cell *prev = std::get<0>(chain.back());
	if (!prev->hasPort(ID::P) || !next->hasPort(ID::C) || !next->hasPort(ID::P))
		return false;
	SigSpec P = sigmap(prev->getPort(ID::P));
	SigSpec C = sigmap(next->getPort(ID::C));
	if (GetSize(P) != 48 || GetSize(C) != 48)
		return false;
	int k = 0;
	while (k + shift < 48 && C[k] == P[k + shift])
		k++;
	if (k == 0)
		return false;
	// Only the low k bits of 'next''s result can be relied upon
	if (nusers(next->getPort(ID::P).extract_end(k)) <= 1)
		return true;
	bool sext = true, zext = true;
	for (int j = k; j < 48; j++) {
		sext = sext && C[j] == C[k-1];
		zext = zext && C[j] == State::S0;
	}
	if (sext && k + shift >= 48)
		return true;
	// Range of 'prev''s result, propagated from the head of the chain
	XilinxDspRange r = xilinx_dsp_range(sigmap, std::get<0>(chain.front()));
	for (int i = 1; i < GetSize(chain); i++)
		r = xilinx_dsp_range(sigmap, std::get<0>(chain[i]), &r, std::max(0, std::get<1>(chain[i])));
	if (sext && r.width <= k + shift)
		return true;
	if (zext && r.nonneg && r.width - 1 <= k + shift)
		return true;
	return false;
}

// Signal to drive the RST pin of a DSP register replacing fabric register
// 'ff'. DSP registers reset regardless of their CE, so the reset of an
// enable-gated $sdffce must be qualified with its enable (RST = SRST & EN).
static SigSpec xilinx_dsp_rst_sig(Module *module, Cell *ff)
{
	if (!ff->type.in(ID($sdff), ID($sdffe), ID($sdffce)))
		return State::S0;
	SigSpec srst = ff->getPort(ID::SRST);
	if (!ff->getParam(ID::SRST_POLARITY).as_bool())
		srst = module->Not(NEW_ID, srst);
	if (ff->type == ID($sdffce)) {
		SigSpec en = ff->getPort(ID::EN);
		if (!ff->getParam(ID::EN_POLARITY).as_bool())
			en = module->Not(NEW_ID, en);
		srst = module->And(NEW_ID, srst, en);
	}
	return srst;
}

#include "techlibs/xilinx/xilinx_dsp_pm.h"
#include "techlibs/xilinx/xilinx_dsp48a_pm.h"
#include "techlibs/xilinx/xilinx_dsp_CREG_pm.h"
#include "techlibs/xilinx/xilinx_dsp_cascade_pm.h"

static Cell* addDsp(Module *module) {
	Cell *cell = module->addCell(NEW_ID, ID(DSP48E1));
	cell->setParam(ID(ACASCREG), 0);
	cell->setParam(ID(ADREG), 0);
	cell->setParam(ID(A_INPUT), Const("DIRECT"));
	cell->setParam(ID(ALUMODEREG), 0);
	cell->setParam(ID(AREG), 0);
	cell->setParam(ID(BCASCREG), 0);
	cell->setParam(ID(B_INPUT), Const("DIRECT"));
	cell->setParam(ID(BREG), 0);
	cell->setParam(ID(CARRYINREG), 0);
	cell->setParam(ID(CARRYINSELREG), 0);
	cell->setParam(ID(CREG), 0);
	cell->setParam(ID(DREG), 0);
	cell->setParam(ID(INMODEREG), 0);
	cell->setParam(ID(MREG), 0);
	cell->setParam(ID(OPMODEREG), 0);
	cell->setParam(ID(PREG), 0);
	cell->setParam(ID(USE_MULT), Const("NONE"));
	cell->setParam(ID(USE_SIMD), Const("ONE48"));
	cell->setParam(ID(USE_DPORT), Const("FALSE"));

	cell->setPort(ID::D, Const(0, 25));
	cell->setPort(ID(INMODE), Const(0, 5));
	cell->setPort(ID(ALUMODE), Const(0, 4));
	cell->setPort(ID(OPMODE), Const(0, 7));
	cell->setPort(ID(CARRYINSEL), Const(0, 3));
	cell->setPort(ID(ACIN), Const(0, 30));
	cell->setPort(ID(BCIN), Const(0, 18));
	cell->setPort(ID(PCIN), Const(0, 48));
	cell->setPort(ID(CARRYIN), Const(0, 1));
	return cell;
}

void xilinx_simd_pack(Module *module, const std::vector<Cell*> &selected_cells)
{
	std::deque<Cell*> simd12_add, simd12_sub;
	std::deque<Cell*> simd24_add, simd24_sub;

	for (auto cell : selected_cells) {
		if (!cell->type.in(ID($add), ID($sub)))
			continue;
		SigSpec Y = cell->getPort(ID::Y);
		if (!Y.is_chunk())
			continue;
		if (!Y.as_chunk().wire->get_strpool_attribute(ID(use_dsp)).count("simd"))
			continue;
		if (GetSize(Y) > 25)
			continue;
		SigSpec A = cell->getPort(ID::A);
		SigSpec B = cell->getPort(ID::B);
		if (GetSize(Y) <= 13) {
			if (GetSize(A) > 12)
				continue;
			if (GetSize(B) > 12)
				continue;
			if (cell->type == ID($add))
				simd12_add.push_back(cell);
			else if (cell->type == ID($sub))
				simd12_sub.push_back(cell);
		}
		else if (GetSize(Y) <= 25) {
			if (GetSize(A) > 24)
				continue;
			if (GetSize(B) > 24)
				continue;
			if (cell->type == ID($add))
				simd24_add.push_back(cell);
			else if (cell->type == ID($sub))
				simd24_sub.push_back(cell);
		}
		else
			log_abort();
	}

	auto f12 = [module](SigSpec &AB, SigSpec &C, SigSpec &P, SigSpec &CARRYOUT, Cell *lane) {
		SigSpec A = lane->getPort(ID::A);
		SigSpec B = lane->getPort(ID::B);
		SigSpec Y = lane->getPort(ID::Y);
		A.extend_u0(12, lane->getParam(ID::A_SIGNED).as_bool());
		B.extend_u0(12, lane->getParam(ID::B_SIGNED).as_bool());
		AB.append(A);
		C.append(B);
		if (GetSize(Y) < 13)
			Y.append(module->addWire(NEW_ID, 13-GetSize(Y)));
		else
			log_assert(GetSize(Y) == 13);
		P.append(Y.extract(0, 12));
		CARRYOUT.append(Y[12]);
	};
	auto g12 = [&f12,module](std::deque<Cell*> &simd12) {
		while (simd12.size() > 1) {
			SigSpec AB, C, P, CARRYOUT;

			Cell *lane1 = simd12.front();
			simd12.pop_front();
			Cell *lane2 = simd12.front();
			simd12.pop_front();
			Cell *lane3 = nullptr;
			Cell *lane4 = nullptr;

			if (!simd12.empty()) {
				lane3 = simd12.front();
				simd12.pop_front();
				if (!simd12.empty()) {
					lane4 = simd12.front();
					simd12.pop_front();
				}
			}

			log("Analysing %s.%s for Xilinx DSP SIMD12 packing.\n", module, lane1);

			Cell *cell = addDsp(module);
			cell->setParam(ID(USE_SIMD), Const("FOUR12"));
			// X = A:B
			// Y = 0
			// Z = C
			cell->setPort(ID(OPMODE), Const::from_string("0110011"));

			log_assert(lane1);
			log_assert(lane2);
			f12(AB, C, P, CARRYOUT, lane1);
			f12(AB, C, P, CARRYOUT, lane2);
			if (lane3) {
				f12(AB, C, P, CARRYOUT, lane3);
				if (lane4)
					f12(AB, C, P, CARRYOUT, lane4);
				else {
					AB.append(Const(0, 12));
					C.append(Const(0, 12));
					P.append(module->addWire(NEW_ID, 12));
					CARRYOUT.append(module->addWire(NEW_ID, 1));
				}
			}
			else {
				AB.append(Const(0, 24));
				C.append(Const(0, 24));
				P.append(module->addWire(NEW_ID, 24));
				CARRYOUT.append(module->addWire(NEW_ID, 2));
			}
			log_assert(GetSize(AB) == 48);
			log_assert(GetSize(C) == 48);
			log_assert(GetSize(P) == 48);
			log_assert(GetSize(CARRYOUT) == 4);
			cell->setPort(ID::A, AB.extract(18, 30));
			cell->setPort(ID::B, AB.extract(0, 18));
			cell->setPort(ID::C, C);
			cell->setPort(ID::P, P);
			cell->setPort(ID(CARRYOUT), CARRYOUT);
			if (lane1->type == ID($sub))
				cell->setPort(ID(ALUMODE), Const::from_string("0011"));

			module->remove(lane1);
			module->remove(lane2);
			if (lane3) module->remove(lane3);
			if (lane4) module->remove(lane4);

			module->design->select(module, cell);
		}
	};
	g12(simd12_add);
	g12(simd12_sub);

	auto f24 = [module](SigSpec &AB, SigSpec &C, SigSpec &P, SigSpec &CARRYOUT, Cell *lane) {
		SigSpec A = lane->getPort(ID::A);
		SigSpec B = lane->getPort(ID::B);
		SigSpec Y = lane->getPort(ID::Y);
		A.extend_u0(24, lane->getParam(ID::A_SIGNED).as_bool());
		B.extend_u0(24, lane->getParam(ID::B_SIGNED).as_bool());
		C.append(A);
		AB.append(B);
		if (GetSize(Y) < 25)
			Y.append(module->addWire(NEW_ID, 25-GetSize(Y)));
		else
			log_assert(GetSize(Y) == 25);
		P.append(Y.extract(0, 24));
		CARRYOUT.append(module->addWire(NEW_ID)); // TWO24 uses every other bit
		CARRYOUT.append(Y[24]);
	};
	auto g24 = [&f24,module](std::deque<Cell*> &simd24) {
		while (simd24.size() > 1) {
			SigSpec AB;
			SigSpec C;
			SigSpec P;
			SigSpec CARRYOUT;

			Cell *lane1 = simd24.front();
			simd24.pop_front();
			Cell *lane2 = simd24.front();
			simd24.pop_front();

			log("Analysing %s.%s for Xilinx DSP SIMD24 packing.\n", module, lane1);

			Cell *cell = addDsp(module);
			cell->setParam(ID(USE_SIMD), Const("TWO24"));
			// X = A:B
			// Y = 0
			// Z = C
			cell->setPort(ID(OPMODE), Const::from_string("0110011"));

			log_assert(lane1);
			log_assert(lane2);
			f24(AB, C, P, CARRYOUT, lane1);
			f24(AB, C, P, CARRYOUT, lane2);
			log_assert(GetSize(AB) == 48);
			log_assert(GetSize(C) == 48);
			log_assert(GetSize(P) == 48);
			log_assert(GetSize(CARRYOUT) == 4);
			cell->setPort(ID::A, AB.extract(18, 30));
			cell->setPort(ID::B, AB.extract(0, 18));
			cell->setPort(ID::C, C);
			cell->setPort(ID::P, P);
			cell->setPort(ID(CARRYOUT), CARRYOUT);
			if (lane1->type == ID($sub))
				cell->setPort(ID(ALUMODE), Const::from_string("0011"));

			module->remove(lane1);
			module->remove(lane2);

			module->design->select(module, cell);
		}
	};
	g24(simd24_add);
	g24(simd24_sub);
}

void xilinx_dsp_pack(xilinx_dsp_pm &pm)
{
	auto &st = pm.st_xilinx_dsp_pack;

	log("Analysing %s.%s for Xilinx DSP packing.\n", pm.module, st.dsp);

	log_debug("preAdd:     %s\n", st.preAdd ? st.preAdd->name.unescape() : "--");
	log_debug("preSub:     %s\n", st.preSub ? st.preSub->name.unescape() : "--");
	log_debug("ffAD:       %s\n", st.ffAD ? st.ffAD->name.unescape() : "--");
	log_debug("ffA2:       %s\n", st.ffA2 ? st.ffA2->name.unescape() : "--");
	log_debug("ffA1:       %s\n", st.ffA1 ? st.ffA1->name.unescape() : "--");
	log_debug("ffB2:       %s\n", st.ffB2 ? st.ffB2->name.unescape() : "--");
	log_debug("ffB1:       %s\n", st.ffB1 ? st.ffB1->name.unescape() : "--");
	log_debug("ffD:        %s\n", st.ffD ? st.ffD->name.unescape() : "--");
	log_debug("dsp:        %s\n", st.dsp ? st.dsp->name.unescape() : "--");
	log_debug("ffM:        %s\n", st.ffM ? st.ffM->name.unescape() : "--");
	log_debug("postAdd:    %s\n", st.postAdd ? st.postAdd->name.unescape() : "--");
	log_debug("postAddMux: %s\n", st.postAddMux ? st.postAddMux->name.unescape() : "--");
	log_debug("ffP:        %s\n", st.ffP ? st.ffP->name.unescape() : "--");
	log_debug("overflow:   %s\n", st.overflow ? st.overflow->name.unescape() : "--");

	Cell *cell = st.dsp;

	if (st.preAdd || st.preSub) {
		Cell* preAdder = st.preAdd ? st.preAdd : st.preSub;

		log("  preadder %s (%s)\n", preAdder, preAdder->type.unescape());
		bool A_SIGNED = preAdder->getParam(ID::A_SIGNED).as_bool();
		bool D_SIGNED = preAdder->getParam(ID::B_SIGNED).as_bool();
		if (st.sigA == preAdder->getPort(ID::B))
			std::swap(A_SIGNED, D_SIGNED);
		st.sigA.extend_u0(30, A_SIGNED);
		// D port (and pre-adder) is 25 bits on DSP48E1, 27 bits on DSP48E2
		st.sigD.extend_u0(cell->type == ID(DSP48E2) ? 27 : 25, D_SIGNED);
		cell->setPort(ID::A, st.sigA);
		cell->setPort(ID::D, st.sigD);
		if (preAdder->type == ID($add))
			cell->setPort(ID(INMODE), Const::from_string("00100"));
		else
			cell->setPort(ID(INMODE), Const::from_string("01100"));

		if (st.ffAD) {
			if (st.ffAD->type.in(ID($dffe), ID($sdffe), ID($sdffce))) {
				bool pol = st.ffAD->getParam(ID::EN_POLARITY).as_bool();
				SigSpec S = st.ffAD->getPort(ID::EN);
				cell->setPort(ID(CEAD), pol ? S : pm.module->Not(NEW_ID, S));
			}
			else
				cell->setPort(ID(CEAD), State::S1);
			// The AD register is reset by RSTD (shared with DREG; the pattern
			// matcher only packs a DREG whose reset is identical)
			cell->setPort(ID(RSTD), xilinx_dsp_rst_sig(pm.module, st.ffAD));
			cell->setParam(ID(ADREG), 1);
		}

		if (cell->type == ID(DSP48E2))
			// Multiplier A-input is the pre-adder output; the pre-adder
			// takes A (PREADDINSEL = "A", the default) and D
			cell->setParam(ID(AMULTSEL), Const("AD"));
		else
			cell->setParam(ID(USE_DPORT), Const("TRUE"));

		pm.autoremove(preAdder);
	}
	if (st.postAdd) {
		log("  postadder %s (%s)\n", st.postAdd, st.postAdd->type.unescape());

		if (st.postAddShift > 0) {
			// The product reaches the adder left-shifted (with zero LSBs), so
			// move that shift into a multiplier operand
			int n = st.postAddShift;
			int which = xilinx_dsp_shift_operand(pm.sigmap, cell, n, st.preAdd || st.preSub);
			log_assert(which != 0);
			IdString port = which == 'B' ? ID::B : ID::A;
			int width = which == 'B' ? 18 : 30;
			SigSpec sig = cell->getPort(port);
			sig.extend_u0(width, true);
			SigSpec shifted(State::S0, n);
			shifted.append(sig.extract(0, width - n));
			cell->setPort(port, shifted);
			log("  shifted %s operand left by %d to absorb zero LSBs of the post-adder input\n", which == 'B' ? "B" : "A", n);
		}

		SigSpec &opmode = cell->connections_.at(ID(OPMODE));
		if (st.postAddMux) {
			log_assert(st.ffP);
			// Z = P (OPMODE[6:4] = 010) while the mux passes the accumulator,
			// C (011) while it passes its other input
			SigSpec S = st.postAddMux->getPort(ID::S);
			if (st.postAddMuxAB == ID::A)
				opmode[4] = S;
			else if (cell->type == ID(DSP48E2)) {
				// invert the pin rather than S (the DSP48E1 model does not
				// support IS_OPMODE_INVERTED)
				opmode[4] = S;
				Const inv = cell->hasParam(ID(IS_OPMODE_INVERTED)) ? cell->getParam(ID(IS_OPMODE_INVERTED)) : Const(State::S0, 9);
				inv.resize(9, State::S0);
				inv.set(4, State::S1);
				cell->setParam(ID(IS_OPMODE_INVERTED), inv);
			} else
				opmode[4] = pm.module->Not(NEW_ID, S);
			pm.autoremove(st.postAddMux);
		}
		else if (st.ffP && st.sigC == st.sigP)
			opmode[4] = State::S0;
		else
			opmode[4] = State::S1;
		opmode[6] = State::S0;
		opmode[5] = State::S1;

		if (opmode[4] != State::S0) {
			// extend C according to the signedness of the adder input it replaces
			if (st.postAddAB == ID::A)
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::B_SIGNED).as_bool());
			else
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::A_SIGNED).as_bool());
			cell->setPort(ID::C, st.sigC);
		}

		if (st.postAdd->type == ID($sub)) {
			if (st.postAddAB == ID::A) {
				// product - Z  ==  ~Z + product + 1
				cell->setPort(ID(ALUMODE), Const::from_string("0001"));
				cell->setPort(ID(CARRYIN), State::S1);
			} else {
				// Z - product
				cell->setPort(ID(ALUMODE), Const::from_string("0011"));
				cell->setPort(ID(CARRYIN), State::S0);
			}
			cell->setPort(ID(CARRYINSEL), Const(0, 3));
		}

		pm.autoremove(st.postAdd);
	}
	if (st.overflow) {
		log("  overflow %s (%s)\n", st.overflow, st.overflow->type.unescape());
		cell->setParam(ID(USE_PATTERN_DETECT), Const("PATDET"));
		cell->setParam(ID(SEL_PATTERN), Const("PATTERN"));
		cell->setParam(ID(SEL_MASK), Const("MASK"));

		if (st.overflow->type == ID($ge)) {
			Const B = st.overflow->getPort(ID::B).as_const();
			log_assert(std::count(B.begin(), B.end(), State::S1) == 1);
			// Since B is an exact power of 2, subtract 1
			//   by inverting all bits up until hitting
			//   that one hi bit
			for (auto b : B)
				if (b == State::S0) b = State::S1;
				else if (b == State::S1) {
					b = State::S0;
					break;
				}
			B.extu(48);

			cell->setParam(ID(MASK), B);
			cell->setParam(ID(PATTERN), Const(0, 48));
			cell->setPort(ID(OVERFLOW), st.overflow->getPort(ID::Y));
		}
		else log_abort();

		pm.autoremove(st.overflow);
	}

	if (st.clock != SigBit())
	{
		cell->setPort(ID::CLK, st.clock);

		auto f = [&pm,cell](SigSpec &A, Cell* ff, IdString ceport, IdString rstport) {
			SigSpec D = ff->getPort(ID::D);
			SigSpec Q = pm.sigmap(ff->getPort(ID::Q));
			if (!A.empty())
				A.replace(Q, D);
			if (rstport != IdString::Null)
				cell->setPort(rstport, xilinx_dsp_rst_sig(pm.module, ff));
			if (ff->type.in(ID($dffe), ID($sdffe), ID($sdffce))) {
				SigSpec ce = ff->getPort(ID::EN);
				bool cepol = ff->getParam(ID::EN_POLARITY).as_bool();
				cell->setPort(ceport, cepol ? ce : pm.module->Not(NEW_ID, ce));
			}
			else
				cell->setPort(ceport, State::S1);

			for (auto c : Q.chunks()) {
				auto it = c.wire->attributes.find(ID::init);
				if (it == c.wire->attributes.end())
					continue;
				for (int i = c.offset; i < c.offset+c.width; i++) {
					log_assert(it->second[i] == State::S0 || it->second[i] == State::Sx);
					it->second.set(i, State::Sx);
				}
			}
		};

		if (st.ffA2) {
			SigSpec A = cell->getPort(ID::A);
			f(A, st.ffA2, ID(CEA2), ID(RSTA));
			if (st.ffA1) {
				f(A, st.ffA1, ID(CEA1), IdString::Null);
				cell->setParam(ID(AREG), 2);
				cell->setParam(ID(ACASCREG), 2);
			}
			else {
				cell->setParam(ID(AREG), 1);
				cell->setParam(ID(ACASCREG), 1);
			}
			pm.add_siguser(A, cell);
			cell->setPort(ID::A, A);
		}
		if (st.ffB2) {
			SigSpec B = cell->getPort(ID::B);
			f(B, st.ffB2, ID(CEB2), ID(RSTB));
			if (st.ffB1) {
				f(B, st.ffB1, ID(CEB1), IdString::Null);
				cell->setParam(ID(BREG), 2);
				cell->setParam(ID(BCASCREG), 2);
			}
			else {
				cell->setParam(ID(BREG), 1);
				cell->setParam(ID(BCASCREG), 1);
			}
			pm.add_siguser(B, cell);
			cell->setPort(ID::B, B);
		}
		if (st.ffD) {
			SigSpec D = cell->getPort(ID::D);
			f(D, st.ffD, ID(CED), ID(RSTD));
			pm.add_siguser(D, cell);
			cell->setPort(ID::D, D);
			cell->setParam(ID(DREG), 1);
		}
		if (st.ffM) {
			SigSpec M; // unused
			f(M, st.ffM, ID(CEM), ID(RSTM));
			st.ffM->connections_.at(ID::Q).replace(st.sigM, pm.module->addWire(NEW_ID, GetSize(st.sigM)));
			cell->setParam(ID(MREG), State::S1);
		}
		if (st.ffP) {
			SigSpec P; // unused
			f(P, st.ffP, ID(CEP), ID(RSTP));
			// Bits of the P register that are not absorbed into the DSP but
			// whose 'D' duplicates an absorbed bit (e.g. sign-extension bits)
			// would lose their driver: drive them from the equivalent
			// (absorbed) bit instead, which is now driven by the DSP's 'P'
			{
				pool<SigBit> absorbed(st.sigP.begin(), st.sigP.end());
				SigSpec D = pm.sigmap(st.ffP->getPort(ID::D));
				SigSpec Q = st.ffP->getPort(ID::Q);
				dict<SigBit, SigBit> d2q;
				for (int i = 0; i < GetSize(Q); i++)
					if (absorbed.count(Q[i]))
						d2q[D[i]] = Q[i];
				SigSpec newQ = Q;
				for (int i = 0; i < GetSize(Q); i++)
					if (!absorbed.count(Q[i]) && d2q.count(D[i])) {
						pm.module->connect(Q[i], d2q.at(D[i]));
						newQ[i] = pm.module->addWire(NEW_ID);
					}
				st.ffP->setPort(ID::Q, newQ);
			}
			st.ffP->connections_.at(ID::Q).replace(st.sigP, pm.module->addWire(NEW_ID, GetSize(st.sigP)));
			cell->setParam(ID(PREG), State::S1);
		}

		log("  clock: %s (%s)\n", log_signal(st.clock), "posedge");

		if (st.ffA2) {
			log(" ffA2:%s\n", st.ffA2);
			if (st.ffA1)
				log(" ffA1:%s\n", st.ffA1);
		}

		if (st.ffAD)
			log(" ffAD:%s\n", st.ffAD);

		if (st.ffB2) {
			log(" ffB2:%s\n", st.ffB2);
			if (st.ffB1)
				log(" ffB1:%s\n", st.ffB1);
		}

		if (st.ffD)
			log(" ffD:%s\n", st.ffD);

		if (st.ffM)
			log(" ffM:%s\n", st.ffM);

		if (st.ffP)
			log(" ffP:%s\n", st.ffP);
	}
	log("\n");

	SigSpec P = st.sigP;
	if (GetSize(P) < 48)
		P.append(pm.module->addWire(NEW_ID, 48-GetSize(P)));
	cell->setPort(ID::P, P);

	pm.blacklist(cell);
}

void xilinx_dsp48a_pack(xilinx_dsp48a_pm &pm)
{
	auto &st = pm.st_xilinx_dsp48a_pack;

	log("Analysing %s.%s for Xilinx DSP48A/DSP48A1 packing.\n", pm.module, st.dsp);

	log_debug("preAdd:     %s\n", st.preAdd ? st.preAdd->name.unescape() : "--");
	log_debug("ffA1:       %s\n", st.ffA1 ? st.ffA1->name.unescape() : "--");
	log_debug("ffA0:       %s\n", st.ffA0 ? st.ffA0->name.unescape() : "--");
	log_debug("ffB1:       %s\n", st.ffB1 ? st.ffB1->name.unescape() : "--");
	log_debug("ffB0:       %s\n", st.ffB0 ? st.ffB0->name.unescape() : "--");
	log_debug("ffD:        %s\n", st.ffD ? st.ffD->name.unescape() : "--");
	log_debug("dsp:        %s\n", st.dsp ? st.dsp->name.unescape() : "--");
	log_debug("ffM:        %s\n", st.ffM ? st.ffM->name.unescape() : "--");
	log_debug("postAdd:    %s\n", st.postAdd ? st.postAdd->name.unescape() : "--");
	log_debug("postAddMux: %s\n", st.postAddMux ? st.postAddMux->name.unescape() : "--");
	log_debug("ffP:        %s\n", st.ffP ? st.ffP->name.unescape() : "--");

	Cell *cell = st.dsp;
	SigSpec &opmode = cell->connections_.at(ID(OPMODE));

	if (st.preAdd) {
		log("  preadder %s (%s)\n", st.preAdd, st.preAdd->type.unescape());
		bool D_SIGNED = st.preAdd->getParam(ID::A_SIGNED).as_bool();
		bool B_SIGNED = st.preAdd->getParam(ID::B_SIGNED).as_bool();
		st.sigB.extend_u0(18, B_SIGNED);
		st.sigD.extend_u0(18, D_SIGNED);
		cell->setPort(ID::B, st.sigB);
		cell->setPort(ID::D, st.sigD);
		opmode[4] = State::S1;
		if (st.preAdd->type == ID($add))
			opmode[6] = State::S0;
		else if (st.preAdd->type == ID($sub))
			opmode[6] = State::S1;
		else
			log_assert(!"strange pre-adder type");

		pm.autoremove(st.preAdd);
	}
	if (st.postAdd) {
		log("  postadder %s (%s)\n", st.postAdd, st.postAdd->type.unescape());

		if (st.postAddMux) {
			log_assert(st.ffP);
			opmode[2] = st.postAddMux->getPort(ID::S);
			pm.autoremove(st.postAddMux);
		}
		else if (st.ffP && st.sigC == st.sigP)
			opmode[2] = State::S0;
		else
			opmode[2] = State::S1;
		opmode[3] = State::S1;

		if (opmode[2] != State::S0) {
			if (st.postAddMuxAB == ID::A)
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::B_SIGNED).as_bool());
			else
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::A_SIGNED).as_bool());
			cell->setPort(ID::C, st.sigC);
		}

		pm.autoremove(st.postAdd);
	}

	if (st.clock != SigBit())
	{
		cell->setPort(ID::CLK, st.clock);

		auto f = [&pm,cell](SigSpec &A, Cell* ff, IdString ceport, IdString rstport) {
			SigSpec D = ff->getPort(ID::D);
			SigSpec Q = pm.sigmap(ff->getPort(ID::Q));
			if (!A.empty())
				A.replace(Q, D);
			if (rstport != IdString::Null) {
				if (ff->type.in(ID($sdff), ID($sdffe))) {
					SigSpec srst = ff->getPort(ID::SRST);
					bool rstpol = ff->getParam(ID::SRST_POLARITY).as_bool();
					cell->setPort(rstport, rstpol ? srst : pm.module->Not(NEW_ID, srst));
				} else {
					cell->setPort(rstport, State::S0);
				}
			}
			if (ff->type.in(ID($dffe), ID($sdffe))) {
				SigSpec ce = ff->getPort(ID::EN);
				bool cepol = ff->getParam(ID::EN_POLARITY).as_bool();
				cell->setPort(ceport, cepol ? ce : pm.module->Not(NEW_ID, ce));
			}
			else
				cell->setPort(ceport, State::S1);

			for (auto c : Q.chunks()) {
				auto it = c.wire->attributes.find(ID::init);
				if (it == c.wire->attributes.end())
					continue;
				for (int i = c.offset; i < c.offset+c.width; i++) {
					log_assert(it->second[i] == State::S0 || it->second[i] == State::Sx);
					it->second.set(i, State::Sx);
				}
			}
		};

		if (st.ffA0 || st.ffA1) {
			SigSpec A = cell->getPort(ID::A);
			if (st.ffA1) {
				f(A, st.ffA1, ID(CEA), ID(RSTA));
				cell->setParam(ID(A1REG), 1);
			}
			if (st.ffA0) {
				f(A, st.ffA0, ID(CEA), ID(RSTA));
				cell->setParam(ID(A0REG), 1);
			}
			pm.add_siguser(A, cell);
			cell->setPort(ID::A, A);
		}
		if (st.ffB0 || st.ffB1) {
			SigSpec B = cell->getPort(ID::B);
			if (st.ffB1) {
				f(B, st.ffB1, ID(CEB), ID(RSTB));
				cell->setParam(ID(B1REG), 1);
			}
			if (st.ffB0) {
				f(B, st.ffB0, ID(CEB), ID(RSTB));
				cell->setParam(ID(B0REG), 1);
			}
			pm.add_siguser(B, cell);
			cell->setPort(ID::B, B);
		}
		if (st.ffD) {
			SigSpec D = cell->getPort(ID::D);
			f(D, st.ffD, ID(CED), ID(RSTD));
			pm.add_siguser(D, cell);
			cell->setPort(ID::D, D);
			cell->setParam(ID(DREG), 1);
		}
		if (st.ffM) {
			SigSpec M; // unused
			f(M, st.ffM, ID(CEM), ID(RSTM));
			st.ffM->connections_.at(ID::Q).replace(st.sigM, pm.module->addWire(NEW_ID, GetSize(st.sigM)));
			cell->setParam(ID(MREG), State::S1);
		}
		if (st.ffP) {
			SigSpec P; // unused
			f(P, st.ffP, ID(CEP), ID(RSTP));
			st.ffP->connections_.at(ID::Q).replace(st.sigP, pm.module->addWire(NEW_ID, GetSize(st.sigP)));
			cell->setParam(ID(PREG), State::S1);
		}

		std::string message = stringf("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffA0)
			message += stringf(" ffA0:%s", st.ffA0);
		if (st.ffA1)
			message += stringf(" ffA1:%s", st.ffA1);

		if (st.ffB0)
			message += stringf(" ffB0:%s", st.ffB0);
		if (st.ffB1)
			message += stringf(" ffB1:%s", st.ffB1);

		if (st.ffD)
			message += stringf(" ffD:%s", st.ffD);

		if (st.ffM)
			message += stringf(" ffM:%s", st.ffM);

		if (st.ffP)
			message += stringf(" ffP:%s", st.ffP);

		log("%s\n", message);
	}

	SigSpec P = st.sigP;
	if (GetSize(P) < 48)
		P.append(pm.module->addWire(NEW_ID, 48-GetSize(P)));
	cell->setPort(ID::P, P);

	pm.blacklist(cell);
}

void xilinx_dsp_packC(xilinx_dsp_CREG_pm &pm)
{
	auto &st = pm.st_xilinx_dsp_packC;

	log_debug("Analysing %s.%s for Xilinx DSP packing (CREG).\n", pm.module, st.dsp);
	log_debug("ffC:        %s\n", st.ffC ? st.ffC->name.unescape() : "--");

	Cell *cell = st.dsp;

	if (st.clock != SigBit())
	{
		cell->setPort(ID::CLK, st.clock);

		auto f = [&pm,cell](SigSpec &A, Cell* ff, IdString ceport, IdString rstport) {
			SigSpec D = ff->getPort(ID::D);
			SigSpec Q = pm.sigmap(ff->getPort(ID::Q));
			if (!A.empty())
				A.replace(Q, D);
			if (rstport != IdString::Null)
				cell->setPort(rstport, xilinx_dsp_rst_sig(pm.module, ff));
			if (ff->type.in(ID($dffe), ID($sdffe), ID($sdffce))) {
				SigSpec ce = ff->getPort(ID::EN);
				bool cepol = ff->getParam(ID::EN_POLARITY).as_bool();
				cell->setPort(ceport, cepol ? ce : pm.module->Not(NEW_ID, ce));
			}
			else
				cell->setPort(ceport, State::S1);

			for (auto c : Q.chunks()) {
				auto it = c.wire->attributes.find(ID::init);
				if (it == c.wire->attributes.end())
					continue;
				for (int i = c.offset; i < c.offset+c.width; i++) {
					log_assert(it->second[i] == State::S0 || it->second[i] == State::Sx);
					it->second.set(i, State::Sx);
				}
			}
		};

		if (st.ffC) {
			SigSpec C = cell->getPort(ID::C);
			f(C, st.ffC, ID(CEC), ID(RSTC));
			pm.add_siguser(C, cell);
			cell->setPort(ID::C, C);
			cell->setParam(ID(CREG), 1);
		}

		std::string message = stringf("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffC)
			message += stringf(" ffC:%s", st.ffC);
		log("%s\n", message);
	}

	pm.blacklist(cell);
}

// Vivado's opt_design moves a C input of a DSP that is driven by the full P
// output of another DSP onto the dedicated PCOUT -> PCIN cascade. If such
// DSP -> DSP connections form a cycle (e.g. an accumulator spread over several
// DSPs, acc <= acc + m0 - m1), the cascade chain cannot be placed and routing
// fails. Break such cycles by moving the P register of one DSP in the cycle
// back into the fabric (keeping the same clock enable and reset), so that the
// cycle passes through a fabric register.
static void xilinx_dsp_break_cycles(Module *module, const std::vector<Cell*> &selected_cells)
{
	SigMap sigmap(module);
	std::vector<Cell*> dsps;
	dict<SigBit, Cell*> pdrv;
	for (auto cell : selected_cells)
		if (cell->type == ID(DSP48E2)) {
			dsps.push_back(cell);
			if (cell->hasPort(ID::P))
				for (auto bit : sigmap(cell->getPort(ID::P)))
					if (bit.wire)
						pdrv[bit] = cell;
		}
	if (GetSize(dsps) < 2)
		return;

	pool<SigBit> consumed;
	for (auto cell : module->cells())
		for (auto &conn : cell->connections())
			if (cell->input(conn.first))
				for (auto bit : sigmap(conn.second))
					consumed.insert(bit);
	for (auto wire : module->wires())
		if (wire->port_output)
			for (auto bit : sigmap(SigSpec(wire)))
				consumed.insert(bit);

	auto port_used = [&](Cell *c, IdString p) {
		if (!c->hasPort(p))
			return false;
		for (auto bit : sigmap(c->getPort(p)))
			if (bit.wire && consumed.count(bit))
				return true;
		return false;
	};
	// Can the P register of 'c' move into the fabric without changing anything?
	auto can_unpack = [&](Cell *c) {
		if (!c->hasParam(ID(PREG)) || c->getParam(ID(PREG)).as_int() != 1)
			return false;
		for (auto p : {ID(PCOUT), ID(CARRYOUT), ID(CARRYCASCOUT), ID(MULTSIGNOUT), ID(PATTERNDETECT),
				ID(PATTERNBDETECT), ID(OVERFLOW), ID(UNDERFLOW), ID(XOROUT)})
			if (port_used(c, p))
				return false;
		for (auto p : {ID(IS_CLK_INVERTED), ID(IS_RSTP_INVERTED)})
			if (c->hasParam(p) && c->getParam(p).as_bool())
				return false;
		// P feedback (Z = P, P >> 17 or MACC extend; W = P) requires PREG
		SigSpec opmode = c->hasPort(ID(OPMODE)) ? sigmap(c->getPort(ID(OPMODE))) : SigSpec();
		if (GetSize(opmode) != 9 || !opmode.is_fully_const())
			return false;
		Const op = opmode.as_const();
		Const z = op.extract(4, 3), w = op.extract(7, 2);
		if (z == Const::from_string("010") || z == Const::from_string("100") || z == Const::from_string("110") ||
				w == Const::from_string("01"))
			return false;
		return true;
	};
	auto unpack_preg = [&](Cell *c) {
		SigSpec P = c->getPort(ID::P);
		SigSpec newP = module->addWire(NEW_ID, GetSize(P));
		SigSpec clk = c->getPort(ID::CLK);
		SigSpec cep = c->hasPort(ID(CEP)) ? c->getPort(ID(CEP)) : SigSpec(State::S1);
		SigSpec rstp = c->hasPort(ID(RSTP)) ? c->getPort(ID(RSTP)) : SigSpec(State::S0);
		bool has_ce = !sigmap(cep).is_fully_ones(), has_rst = !sigmap(rstp).is_fully_zero();
		// DSP registers reset regardless of their CE, i.e. like $sdffe
		if (has_rst && has_ce)
			module->addSdffe(NEW_ID, clk, cep, rstp, newP, P, Const(0, GetSize(P)));
		else if (has_rst)
			module->addSdff(NEW_ID, clk, rstp, newP, P, Const(0, GetSize(P)));
		else if (has_ce)
			module->addDffe(NEW_ID, clk, cep, newP, P);
		else
			module->addDff(NEW_ID, clk, newP, P);
		c->setPort(ID::P, newP);
		c->setParam(ID(PREG), 0);
		for (auto bit : sigmap(P))
			pdrv.erase(bit);
		log("Moved the P register of %s into the fabric to break a DSP -> DSP C-input cycle.\n", c);
	};

	for (int iter = 0; iter < GetSize(dsps); iter++) {
		dict<Cell*, std::vector<Cell*>> succ;
		for (auto y : dsps) {
			if (!y->hasPort(ID::C))
				continue;
			pool<Cell*> seen;
			for (auto bit : sigmap(y->getPort(ID::C))) {
				auto it = pdrv.find(bit);
				if (it != pdrv.end() && seen.insert(it->second).second)
					succ[it->second].push_back(y);
			}
		}
		// find a cycle (iterative DFS with colours)
		dict<Cell*, int> colour;
		dict<Cell*, Cell*> parent;
		std::vector<Cell*> cycle;
		for (auto root : dsps) {
			if (colour[root] != 0 || !cycle.empty())
				continue;
			std::vector<std::pair<Cell*, int>> stack = {{root, 0}};
			colour[root] = 1;
			while (!stack.empty() && cycle.empty()) {
				Cell *c = stack.back().first;
				int &idx = stack.back().second;
				auto &next = succ[c];
				if (idx < GetSize(next)) {
					Cell *n = next[idx++];
					if (colour[n] == 0) {
						colour[n] = 1;
						parent[n] = c;
						stack.push_back({n, 0});
					} else if (colour[n] == 1) {
						for (Cell *x = c; ; x = parent.at(x)) {
							cycle.push_back(x);
							if (x == n)
								break;
						}
					}
				} else {
					colour[c] = 2;
					stack.pop_back();
				}
			}
		}
		if (cycle.empty())
			break;
		Cell *victim = nullptr;
		for (auto c : cycle)
			if (can_unpack(c)) {
				victim = c;
				break;
			}
		if (victim == nullptr) {
			log_warning("DSP -> DSP C-input cycle through %s cannot be broken; Vivado may fail to place its cascades.\n", cycle.front());
			break;
		}
		unpack_preg(victim);
	}
}

// mul2dsp puts the wider multiplier operand on A. If the operand on B is the
// output of an adder/subtractor (directly or through one register) that could
// use the DSP48E2 pre-adder (which is on the A side), and the A operand also
// fits into B, swap the two operands (e.g. symmetric FIR filters, where the
// pre-added data is narrower than the coefficient). Both operands are sign
// extended, so swapping them does not change the product.
// An accumulator with a load written as two sums, y = S ? (X1 + M) : (X2 + M),
// gives the product M two users, so it never reaches the DSP post-adder. When M
// is a DSP product (directly, or through one register: the future MREG), rewrite
// it as y = (S ? X1 : X2) + M. The pattern matcher then packs the adder as the
// post-adder and the $mux as the dynamic Z-mux select between P and C (or as a
// mux in front of C). A branch that is M alone counts as 0 + M. $sub is handled
// when both branches subtract M (X - M) or both subtract from M (M - X); then
// only M - X allows a branch of M alone (M - 0).
// The rewrite is exact: a branch reaches the mux either at no more than its
// adder's width (both forms then agree modulo 2^width), or sign/zero-extended
// from an adder wide enough to hold every possible result.
static void xilinx_dsp_share_postadd(Module *module, const std::vector<Cell*> &selected_cells)
{
	SigMap sigmap(module);
	pool<Cell*> selected(selected_cells.begin(), selected_cells.end());
	pool<SigBit> product;              // bits driven by a DSP P output
	dict<SigBit, SigBit> ff_d;         // register Q bit -> its D bit
	dict<SigBit, Cell*> adder;         // selected $add/$sub Y bit -> cell
	dict<SigBit, pool<Cell*>> users;   // including the driver; nullptr for ports
	std::vector<Cell*> muxes;
	for (auto cell : module->cells()) {
		for (auto &conn : cell->connections())
			for (auto bit : sigmap(conn.second))
				if (bit.wire)
					users[bit].insert(cell);
		if (cell->type.in(ID(DSP48E1), ID(DSP48E2))) {
			if (cell->hasPort(ID::P))
				for (auto bit : sigmap(cell->getPort(ID::P)))
					if (bit.wire)
						product.insert(bit);
		} else if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce))) {
			SigSpec Q = sigmap(cell->getPort(ID::Q)), D = sigmap(cell->getPort(ID::D));
			for (int i = 0; i < GetSize(Q); i++)
				if (Q[i].wire)
					ff_d[Q[i]] = D[i];
		} else if (selected.count(cell)) {
			if (cell->type.in(ID($add), ID($sub))) {
				for (auto bit : sigmap(cell->getPort(ID::Y)))
					if (bit.wire)
						adder[bit] = cell;
			} else if (cell->type == ID($mux))
				muxes.push_back(cell);
		}
	}
	for (auto wire : module->wires())
		if (wire->port_id > 0)
			for (auto bit : sigmap(wire))
				users[bit].insert(nullptr);

	// All non-constant bits of 'sig' (at least one) are (registered) DSP products
	auto is_product = [&](const SigSpec &sig) {
		bool any = false;
		for (auto bit : sig) {
			if (!bit.wire)
				continue;
			auto it = ff_d.find(bit);
			if (!product.count(bit) && (it == ff_d.end() || !product.count(it->second)))
				return false;
			any = true;
		}
		return any;
	};
	// How the mux input 'in' extends 'base': -1 if it does not; 0 if it uses
	// at most GetSize(base) bits of it; otherwise a mask of the extensions it
	// matches (1: sign, 2: zero)
	auto extension = [](const SigSpec &in, const SigSpec &base) {
		int n = std::min(GetSize(in), GetSize(base));
		if (n == 0 || in.extract(0, n) != base.extract(0, n))
			return -1;
		if (GetSize(in) <= GetSize(base))
			return 0;
		SigSpec rest = in.extract_end(n);
		int mask = 0;
		if (rest == SigSpec(base[n-1], GetSize(rest)))
			mask |= 1;
		if (rest.is_fully_zero())
			mask |= 2;
		return mask ? mask : -1;
	};

	struct Branch {
		Cell *cell = nullptr;   // the adder; nullptr for a branch of M alone
		SigSpec ops[2];         // its operands
		int width = 0;          // width of the value the mux input extends
		int ext = 0;            // as returned by extension()
	};

	for (auto mux : muxes) {
		SigSpec S = sigmap(mux->getPort(ID::S));
		SigSpec in[2] = {sigmap(mux->getPort(ID::A)), sigmap(mux->getPort(ID::B))};
		int Wm = GetSize(in[0]);
		if (Wm == 0 || Wm > 48)
			continue;

		Branch b[2];
		bool ok = true;
		for (int k = 0; k < 2 && ok; k++) {
			auto it = adder.find(in[k][0]);
			if (it == adder.end())
				continue;
			Cell *cell = it->second;
			SigSpec Y = sigmap(cell->getPort(ID::Y));
			b[k].ext = extension(in[k], Y);
			b[k].width = GetSize(Y);
			ok = b[k].ext >= 0 && cell->getParam(ID::A_SIGNED).as_bool() == cell->getParam(ID::B_SIGNED).as_bool();
			// the adder must feed this mux input only
			for (auto bit : Y) {
				if (!ok || !bit.wire)
					continue;
				if (bit == S[0])
					ok = false;
				for (auto user : users.at(bit))
					if (user != cell && user != mux)
						ok = false;
			}
			b[k].cell = cell;
			b[k].ops[0] = sigmap(cell->getPort(ID::A));
			b[k].ops[1] = sigmap(cell->getPort(ID::B));
		}
		if (!ok || (!b[0].cell && !b[1].cell) || b[0].cell == b[1].cell)
			continue;

		// Find the shared operand M (position mpos in the adders) and the
		// other operands X[k] (empty for a branch of M alone)
		Cell *ref = b[0].cell ? b[0].cell : b[1].cell;
		IdString type = ref->type;
		bool sgn = ref->getParam(ID::A_SIGNED).as_bool();
		SigSpec M, X[2];
		int mpos = -1;
		if (b[0].cell && b[1].cell) {
			if (b[1].cell->type != type || b[1].cell->getParam(ID::A_SIGNED).as_bool() != sgn)
				continue;
			for (int i = 0; i < 2 && mpos < 0; i++)
				for (int j = 0; j < 2 && mpos < 0; j++) {
					if ((type == ID($sub) && i != j) || b[0].ops[i] != b[1].ops[j] || !is_product(b[0].ops[i]))
						continue;
					M = b[0].ops[i];
					X[0] = b[0].ops[1-i];
					X[1] = b[1].ops[1-j];
					mpos = i;
				}
		} else {
			int k = b[0].cell ? 0 : 1;
			for (int i = 0; i < 2 && mpos < 0; i++) {
				if ((type == ID($sub) && i != 0) || !is_product(b[k].ops[i]))
					continue;
				int ext = extension(in[1-k], b[k].ops[i]);
				if (ext < 0)
					continue;
				M = b[k].ops[i];
				X[k] = b[k].ops[1-i];
				b[1-k].width = GetSize(M);
				b[1-k].ext = ext;
				mpos = i;
			}
		}
		if (mpos < 0 || GetSize(M) > 60 || GetSize(X[0]) > 60 || GetSize(X[1]) > 60)
			continue;

		// Exactness: a branch extended beyond the width of its value must
		// hold every result of X op M in that width
		auto range = [sgn](const SigSpec &sig, int64_t &lo, int64_t &hi) {
			int w = GetSize(sig);
			if (w == 0)
				lo = hi = 0;
			else if (sgn)
				lo = -(int64_t(1) << (w-1)), hi = (int64_t(1) << (w-1)) - 1;
			else
				lo = 0, hi = (int64_t(1) << w) - 1;
		};
		for (int k = 0; k < 2 && ok; k++) {
			if (b[k].ext == 0)
				continue;
			int64_t xlo, xhi, mlo, mhi, lo, hi;
			range(X[k], xlo, xhi);
			range(M, mlo, mhi);
			if (type == ID($add))
				lo = xlo + mlo, hi = xhi + mhi;
			else if (mpos == 1)
				lo = xlo - mhi, hi = xhi - mlo;
			else
				lo = mlo - xhi, hi = mhi - xlo;
			int64_t W = b[k].width;
			ok = ((b[k].ext & 1) && lo >= -(int64_t(1) << (W-1)) && hi < (int64_t(1) << (W-1))) ||
					((b[k].ext & 2) && lo >= 0 && hi < (int64_t(1) << W));
		}
		if (!ok)
			continue;

		SigSpec N = module->addWire(NEW_ID, Wm);
		SigSpec Y = mux->getPort(ID::Y);
		for (int k = 0; k < 2; k++) {
			SigSpec x = X[k];
			if (GetSize(x) == 0)
				x = SigSpec(State::S0, Wm);
			x.extend_u0(Wm, sgn);
			mux->setPort(k ? ID::B : ID::A, x);
		}
		mux->setPort(ID::Y, N);
		std::string src = ref->get_src_attribute();
		Cell *cell;
		if (type == ID($add))
			cell = module->addAdd(NEW_ID, N, M, Y, sgn, src);
		else if (mpos == 1)
			cell = module->addSub(NEW_ID, N, M, Y, sgn, src);
		else
			cell = module->addSub(NEW_ID, M, N, Y, sgn, src);
		if (!module->design->selected_whole_module(module))
			module->design->select(module, cell);
		log("Moved %s in front of a single %s %s: both of its inputs used the product %s.\n",
				mux, cell->type.unescape(), cell, log_signal(M));
		for (int k = 0; k < 2; k++)
			if (b[k].cell) {
				for (auto bit : sigmap(b[k].cell->getPort(ID::Y)))
					adder.erase(bit);
				module->remove(b[k].cell);
			}
	}
}

static void xilinx_dsp_swap_operands(Module *module, const std::vector<Cell*> &selected_cells)
{
	SigMap sigmap(module);
	dict<SigBit, Cell*> driver;
	for (auto cell : module->cells()) {
		IdString out;
		if (cell->type.in(ID($add), ID($sub)))
			out = ID::Y;
		else if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce)))
			out = ID::Q;
		else
			continue;
		for (auto bit : sigmap(cell->getPort(out)))
			if (bit.wire)
				driver[bit] = cell;
	}
	// The single cell driving all non-constant bits of 'sig', if any
	auto single_driver = [&](const SigSpec &sig) -> Cell* {
		Cell *d = nullptr;
		for (auto bit : sig) {
			if (!bit.wire)
				continue;
			auto it = driver.find(bit);
			if (it == driver.end() || (d && it->second != d))
				return nullptr;
			d = it->second;
		}
		return d;
	};
	auto from_adder = [&](const SigSpec &sig) {
		Cell *d = single_driver(sig);
		if (d && d->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce))) {
			SigSpec dsig;
			SigSpec Q = sigmap(d->getPort(ID::Q)), D = sigmap(d->getPort(ID::D));
			for (auto bit : sig) {
				int i = 0;
				while (i < GetSize(Q) && Q[i] != bit)
					i++;
				dsig.append(i < GetSize(Q) ? D[i] : bit);
			}
			d = single_driver(dsig);
		}
		return d && d->type.in(ID($add), ID($sub));
	};

	for (auto dsp : selected_cells) {
		if (dsp->type != ID(DSP48E2))
			continue;
		if (xilinx_dsp_param_str(dsp, ID(AMULTSEL), "A") != "A" || xilinx_dsp_param_str(dsp, ID(BMULTSEL), "B") != "B" ||
				xilinx_dsp_param_str(dsp, ID(USE_MULT), "MULTIPLY") != "MULTIPLY" ||
				xilinx_dsp_param_str(dsp, ID(A_INPUT), "DIRECT") != "DIRECT" ||
				xilinx_dsp_param_str(dsp, ID(B_INPUT), "DIRECT") != "DIRECT")
			continue;
		if ((dsp->hasParam(ID(AREG)) && dsp->getParam(ID(AREG)).as_int() != 0) ||
				(dsp->hasParam(ID(BREG)) && dsp->getParam(ID(BREG)).as_int() != 0))
			continue;
		if (dsp->hasPort(ID::D) && !sigmap(dsp->getPort(ID::D)).is_fully_zero())
			continue;
		if (dsp->hasPort(ID(INMODE)) && !sigmap(dsp->getPort(ID(INMODE))).is_fully_zero())
			continue;
		SigSpec A = sigmap(dsp->getPort(ID::A)), B = sigmap(dsp->getPort(ID::B));
		if (GetSize(A) != 30 || GetSize(B) != 18)
			continue;
		int wa = xilinx_dsp_signed_width(A), wb = xilinx_dsp_signed_width(B);
		if (wa > 18 || from_adder(A.extract(0, wa)) || !from_adder(B.extract(0, wb)))
			continue;
		SigSpec oldA = dsp->getPort(ID::A), oldB = dsp->getPort(ID::B);
		SigSpec newA = oldB;
		newA.extend_u0(30, true);
		dsp->setPort(ID::A, newA);
		dsp->setPort(ID::B, oldA.extract(0, 18));
		log("Swapped A and B operands of %s so that the pre-adder can be used.\n", dsp);
	}
}

// opt_expr strips the zero LSBs of constant multiplicands, so a DSP computing
// e.g. x * 1234 actually computes x * 617 with the "<< 1" done in wiring. For a
// DSP48E2 whose P is just its product (Z = 0, no carry-in), and whose P drives
// the C input of other DSPs only through such a left shift by 's' (with zero
// LSBs), move the shift back into the multiplier: shift an operand left by 's'
// and drive its existing P wires from P[j+s] instead of P[j] -- every user sees
// the same values -- and let those DSPs take the (zero) LSBs of P instead of
// constant zeros in C. This allows PCOUT -> PCIN cascades to be formed later.
static void xilinx_dsp_shift_heads(Module *module, const std::vector<Cell*> &selected_cells)
{
	SigMap sigmap(module);
	dict<SigBit, std::pair<Cell*, int>> pbit;
	for (auto cell : selected_cells)
		if (cell->type == ID(DSP48E2) && cell->hasPort(ID::P)) {
			SigSpec P = sigmap(cell->getPort(ID::P));
			for (int i = 0; i < GetSize(P); i++)
				if (P[i].wire)
					pbit[P[i]] = {cell, i};
		}

	// Bits consumed by any cell input or module output
	pool<SigBit> consumed;
	for (auto cell : module->cells())
		for (auto &conn : cell->connections())
			if (cell->input(conn.first))
				for (auto bit : sigmap(conn.second))
					consumed.insert(bit);
	for (auto wire : module->wires())
		if (wire->port_output)
			for (auto bit : sigmap(SigSpec(wire)))
				consumed.insert(bit);

	// Candidate shift per head DSP, from the C inputs of other DSP48E2s
	dict<Cell*, int> shift;
	dict<Cell*, std::vector<Cell*>> users;
	pool<Cell*> bad;
	for (auto next : selected_cells) {
		if (next->type != ID(DSP48E2) || !next->hasPort(ID::C))
			continue;
		SigSpec C = sigmap(next->getPort(ID::C));
		int z = 0;
		while (z < GetSize(C) && C[z] == State::S0)
			z++;
		if (z == 0 || z == GetSize(C))
			continue;
		auto it = pbit.find(C[z]);
		if (it == pbit.end() || it->second.second != 0)
			continue;
		Cell *head = it->second.first;
		if (shift.count(head) && shift.at(head) != z)
			bad.insert(head);
		shift[head] = z;
		users[head].push_back(next);
	}

	for (auto &it : shift) {
		Cell *head = it.first;
		int s = it.second;
		if (bad.count(head))
			continue;
		// P must be exactly the product: X/Y = M, Z = 0, W = 0, ALUMODE add, no carry-in
		SigSpec opmode = head->hasPort(ID(OPMODE)) ? sigmap(head->getPort(ID(OPMODE))) : SigSpec();
		if (GetSize(opmode) != 9 || !opmode.is_fully_const() || opmode.as_const() != Const::from_string("000000101"))
			continue;
		if (!head->hasPort(ID(ALUMODE)) || !sigmap(head->getPort(ID(ALUMODE))).is_fully_zero() ||
				(head->hasPort(ID(CARRYIN)) && !sigmap(head->getPort(ID(CARRYIN))).is_fully_zero()) ||
				(head->hasPort(ID(CARRYINSEL)) && !sigmap(head->getPort(ID(CARRYINSEL))).is_fully_zero()))
			continue;
		if (xilinx_dsp_param_str(head, ID(USE_MULT), "MULTIPLY") != "MULTIPLY")
			continue;
		bool preadd = xilinx_dsp_param_str(head, ID(AMULTSEL), "A") == "AD";
		int which = xilinx_dsp_shift_operand(sigmap, head, s, preadd);
		if (!which)
			continue;
		// the top 's' bits of P would be lost: they must be unused
		SigSpec P = head->getPort(ID::P);
		bool top_used = false;
		for (int i = GetSize(P) - s; i < GetSize(P); i++)
			if (consumed.count(sigmap(P[i])))
				top_used = true;
		if (top_used)
			continue;

		// shift the operand
		IdString port = which == 'B' ? ID::B : ID::A;
		int width = which == 'B' ? 18 : 30;
		SigSpec op = head->getPort(port);
		op.extend_u0(width, true);
		SigSpec shifted_op(State::S0, s);
		shifted_op.append(op.extract(0, width - s));
		head->setPort(port, shifted_op);
		// re-drive the existing P wires from P[j+s]; P[s-1:0] are new (always 0)
		SigSpec lsb = module->addWire(NEW_ID, s);
		SigSpec newP = lsb;
		newP.append(P.extract(0, GetSize(P) - s));
		head->setPort(ID::P, newP);
		// the users take P's (zero) LSBs instead of constant zeros
		for (auto next : users.at(head)) {
			SigSpec C = next->getPort(ID::C);
			for (int i = 0; i < s; i++)
				C[i] = lsb[i];
			next->setPort(ID::C, C);
		}
		log("Moved the << %d of %s's product into its %s operand.\n", s, head, which == 'B' ? "B" : "A");
	}
}

// Use ACOUT -> ACIN and BCOUT -> BCIN cascades for A/B inputs that are
// delayed copies of the A/B input of another DSP48E2, e.g. the data delay line
// of a systolic FIR filter (x -> xr[0] -> xr[1] -> ...). If the A (B) input of
// 'next' is the A (B) input of 'prev' delayed by one or two fabric registers
// that are equivalent to the A1/A2 (B1/B2) registers of 'prev' (same clock,
// enable and reset, zero init), then 'next' can take 'prev's ACOUT (BCOUT)
// instead, with ACASCREG (BCASCREG) set accordingly, making those fabric
// registers redundant. Every DSP keeps at most one cascade neighbour in each
// direction (shared by its [ABP]CIN/[ABP]COUT), as required for placement.
static void xilinx_dsp_abcascade(Module *module, const std::vector<Cell*> &selected_cells)
{
	const int MAX_CASCADE = 20;
	SigMap sigmap(module);

	dict<SigBit, std::pair<Cell*, int>> ffq;
	dict<SigBit, Cell*> cout_driver;
	for (auto cell : module->cells()) {
		if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe))) {
			SigSpec Q = sigmap(cell->getPort(ID::Q));
			for (int i = 0; i < GetSize(Q); i++)
				if (Q[i].wire)
					ffq[Q[i]] = {cell, i};
		}
		if (cell->type == ID(DSP48E2))
			for (auto p : {ID(ACOUT), ID(BCOUT), ID(PCOUT)})
				if (cell->hasPort(p))
					for (auto bit : sigmap(cell->getPort(p)))
						if (bit.wire)
							cout_driver[bit] = cell;
	}

	auto pstr = [](Cell *c, IdString p, const char *def) { return xilinx_dsp_param_str(c, p, def); };
	auto pint = [](Cell *c, IdString p, int def) { return c->hasParam(p) ? c->getParam(p).as_int() : def; };
	auto port_or = [&](Cell *c, IdString p, SigSpec def) { return c->hasPort(p) ? sigmap(c->getPort(p)) : def; };
	auto used = [&](Cell *c, IdString p) {
		if (!c->hasPort(p))
			return false;
		for (auto bit : sigmap(c->getPort(p)))
			if (bit.wire)
				return true;
		return false;
	};

	// Existing cascade neighbours (from the PCOUT -> PCIN matcher etc.)
	dict<Cell*, Cell*> pred, succ;
	for (auto cell : selected_cells) {
		if (cell->type != ID(DSP48E2))
			continue;
		for (auto p : {ID(ACIN), ID(BCIN), ID(PCIN)})
			if (cell->hasPort(p))
				for (auto bit : sigmap(cell->getPort(p))) {
					auto it = cout_driver.find(bit);
					if (it != cout_driver.end()) {
						pred[cell] = it->second;
						succ[it->second] = cell;
					}
				}
	}

	// The fabric register driving all non-constant bits of 'sig' (if any one
	// register does), returning 'sig' as seen at that register's D input
	auto through_ff = [&](const SigSpec &sig, Cell *&ff) {
		ff = nullptr;
		SigSpec d;
		for (auto bit : sig) {
			if (!bit.wire) {
				d.append(bit);
				continue;
			}
			auto it = ffq.find(bit);
			if (it == ffq.end() || (ff && it->second.first != ff))
				return SigSpec();
			ff = it->second.first;
			d.append(sigmap(ff->getPort(ID::D))[it->second.second]);
		}
		return ff ? d : SigSpec();
	};

	// Is fabric register 'ff' equivalent to a 'prev' input register with
	// enable 'ce' and reset 'rst' (inverted if parameter 'rst_inv' is set)?
	auto ff_matches = [&](Cell *ff, Cell *prev, IdString ce, IdString rst, IdString rst_inv) {
		if (!ff->getParam(ID::CLK_POLARITY).as_bool())
			return false;
		if (sigmap(ff->getPort(ID::CLK)) != port_or(prev, ID::CLK, SigSpec()))
			return false;
		SigSpec r = port_or(prev, rst, SigSpec(State::S0));
		if (ff->type.in(ID($sdff), ID($sdffe))) {
			if (!ff->getParam(ID::SRST_VALUE).is_fully_zero() || !ff->getParam(ID::SRST_POLARITY).as_bool() ||
					sigmap(ff->getPort(ID::SRST)) != r || pint(prev, rst_inv, 0))
				return false;
		} else if (!r.is_fully_zero())
			return false;
		SigSpec en = port_or(prev, ce, SigSpec(State::S1));
		if (ff->type.in(ID($dffe), ID($sdffe))) {
			if (!ff->getParam(ID::EN_POLARITY).as_bool() || sigmap(ff->getPort(ID::EN)) != en)
				return false;
		} else if (!en.is_fully_ones())
			return false;
		// DSP registers power up as zero
		for (auto bit : ff->getPort(ID::Q))
			if (bit.wire) {
				Const init = bit.wire->attributes.at(ID::init, Const());
				if (!init.empty() && init[bit.offset] == State::S1)
					return false;
			}
		return true;
	};

	struct Kind {
		IdString port, cin, cout, input, cascreg, reg, ce1, ce2, rst, rst_inv;
		int width;
	};
	const Kind kinds[2] = {
		{ID::A, ID(ACIN), ID(ACOUT), ID(A_INPUT), ID(ACASCREG), ID(AREG), ID(CEA1), ID(CEA2), ID(RSTA), ID(IS_RSTA_INVERTED), 30},
		{ID::B, ID(BCIN), ID(BCOUT), ID(B_INPUT), ID(BCASCREG), ID(BREG), ID(CEB1), ID(CEB2), ID(RSTB), ID(IS_RSTB_INVERTED), 18},
	};

	// Forward map: register D bit -> (register, bit index), to find the
	// fabric copy of a signal delayed by one cycle
	dict<SigBit, std::pair<Cell*, int>> ffd;
	for (auto &it : ffq) {
		Cell *ff = it.second.first;
		int idx = it.second.second;
		SigBit d = sigmap(ff->getPort(ID::D))[idx];
		if (d.wire)
			ffd[d] = it.second;
	}
	auto forward_ff = [&](const SigSpec &sig) {
		Cell *ff = nullptr;
		SigSpec q;
		for (auto bit : sig) {
			if (!bit.wire) {
				q.append(bit);
				continue;
			}
			auto it = ffd.find(bit);
			if (it == ffd.end() || (ff && it->second.first != ff))
				return SigSpec();
			ff = it->second.first;
			q.append(sigmap(ff->getPort(ID::Q))[it->second.second]);
		}
		return ff ? q : SigSpec();
	};

	for (auto &k : kinds) {
		// Index DSPs by their (logical) A/B input. For DSPs already fed by a
		// cascade, that is the input of the predecessor delayed by its
		// [AB]CASCREG, if that delayed copy exists in the fabric.
		dict<Cell*, SigSpec> logical;
		std::function<SigSpec(Cell*, int)> logical_input = [&](Cell *c, int depth) -> SigSpec {
			if (logical.count(c))
				return logical.at(c);
			SigSpec r;
			if (pstr(c, k.input, "DIRECT") == "DIRECT")
				r = sigmap(c->getPort(k.port));
			else if (depth < MAX_CASCADE && pred.count(c) && used(c, k.cin)) {
				Cell *p = pred.at(c);
				r = logical_input(p, depth + 1);
				for (int i = 0; i < pint(p, k.cascreg, 1) && !r.empty(); i++)
					r = forward_ff(r);
			}
			logical[c] = r;
			return r;
		};
		dict<SigSpec, Cell*> by_input;
		for (auto cell : selected_cells)
			if (cell->type == ID(DSP48E2) && !pint(cell, ID(IS_CLK_INVERTED), 0)) {
				SigSpec in = logical_input(cell, 0);
				if (!in.empty() && !in.is_fully_const())
					by_input[in] = cell;
			}

		std::vector<std::tuple<Cell*, Cell*, int>> todo;
		for (auto next : selected_cells) {
			if (next->type != ID(DSP48E2) || pstr(next, k.input, "DIRECT") != "DIRECT" || used(next, k.cin))
				continue;
			SigSpec s0 = sigmap(next->getPort(k.port));
			Cell *ff1 = nullptr, *ff2 = nullptr;
			SigSpec s1 = through_ff(s0, ff1);
			SigSpec s2 = s1.empty() ? SigSpec() : through_ff(s1, ff2);
			for (int levels = 2; levels >= 1; levels--) {
				SigSpec src = levels == 2 ? s2 : s1;
				if (src.empty())
					continue;
				auto it = by_input.find(src);
				if (it == by_input.end())
					continue;
				Cell *prev = it->second;
				if (prev == next || used(prev, k.cout))
					continue;
				// keep a single cascade neighbour per direction
				if ((pred.count(next) && pred.at(next) != prev) || (succ.count(prev) && succ.at(prev) != next))
					continue;
				int reg = pint(prev, k.reg, 1);
				bool ok;
				if (levels == 2)
					ok = reg == 2 && ff_matches(ff1, prev, k.ce2, k.rst, k.rst_inv) &&
							ff_matches(ff2, prev, k.ce1, k.rst, k.rst_inv);
				else
					ok = reg >= 1 && ff_matches(ff1, prev, reg == 2 ? k.ce1 : k.ce2, k.rst, k.rst_inv);
				if (!ok)
					continue;
				// keep chains acyclic and no longer than MAX_CASCADE in total
				int len = 2;
				for (Cell *c = prev; ok && pred.count(c); c = pred.at(c))
					if (++len > MAX_CASCADE || pred.at(c) == next)
						ok = false;
				for (Cell *c = next; ok && succ.count(c); c = succ.at(c))
					if (++len > MAX_CASCADE || succ.at(c) == prev)
						ok = false;
				if (!ok)
					continue;
				pred[next] = prev;
				succ[prev] = next;
				todo.emplace_back(prev, next, levels);
				break;
			}
		}

		for (auto &t : todo) {
			Cell *prev = std::get<0>(t), *next = std::get<1>(t);
			int levels = std::get<2>(t);
			Wire *cascade = module->addWire(NEW_ID, k.width);
			prev->setPort(k.cout, cascade);
			prev->setParam(k.cascreg, levels);
			next->setPort(k.port, Const(0, k.width));
			next->setPort(k.cin, cascade);
			next->setParam(k.input, Const("CASCADE"));
			log("%sCOUT -> %sCIN cascade for %s -> %s (%sCASCREG=%d)\n", k.port == ID::A ? "A" : "B",
					k.port == ID::A ? "A" : "B", prev, next, k.port == ID::A ? "A" : "B", levels);
		}
	}
}

struct XilinxDspPass : public Pass {
	XilinxDspPass() : Pass("xilinx_dsp", "Xilinx: pack resources into DSPs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_dsp [options] [selection]\n");
		log("\n");
		log("Pack input registers (A2, A1, B2, B1, C, D, AD; with optional enable/reset),\n");
		log("pipeline registers (M; with optional enable/reset), output registers (P; with\n");
		log("optional enable/reset), pre-adder and/or post-adder into Xilinx DSP resources.\n");
		log("\n");
		log("Multiply-accumulate operations using the post-adder with feedback on the 'C'\n");
		log("input will be folded into the DSP. In this scenario only, the 'C' input can be\n");
		log("used to override the current accumulation result with a new value, which will\n");
		log("be added to the multiplier result to form the next accumulation result.\n");
		log("\n");
		log("Use of the dedicated 'PCOUT' -> 'PCIN' cascade path is detected for 'P' -> 'C'\n");
		log("connections (optionally, where 'P' is right-shifted by 17-bits and used as an\n");
		log("input to the post-adder -- a pattern common for summing partial products to\n");
		log("implement wide multipliers). Limited support also exists for similar cascading\n");
		log("for A and B using '[AB]COUT' -> '[AB]CIN'. Currently, cascade chains are limited\n");
		log("to a maximum length of 20 cells, corresponding to the smallest Xilinx 7 Series\n");
		log("device.\n");
		log("\n");
		log("This pass is a no-op if the scratchpad variable 'xilinx_dsp.multonly' is set\n");
		log("to 1.\n");
		log("\n");
		log("\n");
		log("Experimental feature: addition/subtractions less than 12 or 24 bits with the\n");
		log("'(* use_dsp=\"simd\" *)' attribute attached to the output wire or attached to\n");
		log("the add/subtract operator will cause those operations to be implemented using\n");
		log("the 'SIMD' feature of DSPs.\n");
		log("\n");
		log("Experimental feature: the presence of a `$ge' cell attached to the registered\n");
		log("P output implementing the operation \"(P >= <power-of-2>)\" will be transformed\n");
		log("into using the DSP48E1's/DSP48E2's pattern detector feature for overflow detection.\n");
		log("\n");
		log("    -family {xcup|xcu|xc7|xc6v|xc5v|xc4v|xc6s|xc3sda}\n");
		log("        select the family to target\n");
		log("        default: xc7\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing XILINX_DSP pass (pack resources into DSPs).\n");

		std::string family = "xc7";
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if ((args[argidx] == "-family" || args[argidx] == "-arch") && argidx+1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Don't bother distinguishing between those.
		if (family == "xc6v")
			family = "xc7";
		if (family == "xcup")
			family = "xcu";

		for (auto module : design->selected_modules()) {

			if (design->scratchpad_get_bool("xilinx_dsp.multonly"))
				continue;

			// Experimental feature: pack $add/$sub cells with
			//   (* use_dsp48="simd" *) into DSP48E1's using its
			//   SIMD feature
			if (family == "xc7")
				xilinx_simd_pack(module, module->selected_cells());

			// Let the pre-adder see adder outputs that mul2dsp put on B
			if (family == "xcu")
				xilinx_dsp_swap_operands(module, module->selected_cells());

			// S ? (X1 + M) : (X2 + M)  ->  (S ? X1 : X2) + M  for DSP products M
			if (family == "xcu")
				xilinx_dsp_share_postadd(module, module->selected_cells());

			// Match for all features ([ABDMP][12]?REG, pre-adder,
			// post-adder, pattern detector, etc.) except for CREG
			if (family == "xc7" || family == "xcu") {
				xilinx_dsp_pm pm(module, module->selected_cells());
				pm.run_xilinx_dsp_pack(xilinx_dsp_pack);
			} else if (family == "xc6s" || family == "xc3sda") {
				xilinx_dsp48a_pm pm(module, module->selected_cells());
				pm.run_xilinx_dsp48a_pack(xilinx_dsp48a_pack);
			}
			// Separating out CREG packing is necessary since there
			//   is no guarantee that the cell ordering corresponds
			//   to the "expected" case (i.e. the order in which
			//   they appear in the source) thus the possiblity
			//   existed that a register got packed as a CREG into a
			//   downstream DSP that should have otherwise been a
			//   PREG of an upstream DSP that had not been visited
			//   yet
			{
				xilinx_dsp_CREG_pm pm(module, module->selected_cells());
				pm.run_xilinx_dsp_packC(xilinx_dsp_packC);
			}
			// Lastly, identify and utilise PCOUT -> PCIN,
			//   ACOUT -> ACIN, and BCOUT-> BCIN dedicated cascade
			//   chains
			{
				if (family == "xcu") {
					xilinx_dsp_break_cycles(module, module->selected_cells());
					xilinx_dsp_shift_heads(module, module->selected_cells());
				}
				xilinx_dsp_cascade_pm pm(module, module->selected_cells());
				pm.run_xilinx_dsp_cascade();
			}
			// ACOUT -> ACIN cascades for delayed A inputs (e.g. FIR delay
			// lines) that the PCOUT -> PCIN driven matcher above cannot see
			if (family == "xcu")
				xilinx_dsp_abcascade(module, module->selected_cells());
		}
	}
} XilinxDspPass;

PRIVATE_NAMESPACE_END
