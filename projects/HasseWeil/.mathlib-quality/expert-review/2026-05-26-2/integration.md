# Reply integration — round 2 (2026-05-26): QF route resolved

Reply: ./reply.md   Brief: ./brief.md   State: ./state.md

## Decision (committed)

The QF `qf_nonneg` route is **B (narrow) primary + C (supporting)**:
- **B — complete the Pic⁰ route honestly but NARROWLY**: construct, for the family β = rπ−s,
  a *genuine* degree-bearing dual β_dual = rV−s (real pullback / comorphism) with
  `β_dual ∘ β = [N]` at the function-field level. NOT the full Picard-functor comorphism
  stack. This is the named pivot `genuineIsogSmulSub_pivot_witness`. The genuine pullback is
  the irreducible object — neither a placeholder (shipped Pic⁰ dual) nor an equality proof
  (C) supplies it.
- **C — supporting accelerator**: prove `genuine_isogeny_ext_of_geometric_pointMap_eq`
  (genuine morphisms equal on E(K̄) ⟹ equal pullback). Shortens the pullback-equality proof
  once genuine maps exist; it is NOT a replacement for the genuine pullback construction and
  in practice depends on B's output.
- **Ruled out**: D (deg_s·deg_i — a detour, two-parameter kernel + inseparable-degree
  bookkeeping, likely harder); Weil-pairing/torsion-determinant (valid but a major new
  branch); explicit-coordinate Route 3 (V-side pole obstruction real).
- **Irreducible keystone**: `(rπ−s)^ = rV−s` at the degree-bearing isogeny level. The
  composition square alone gives only `deg(rV−s)·deg(rπ−s)=N²` (absolute-value); the *signed*
  `deg(rπ−s)=N` needs the genuine dual identification.

## Concrete next target (reviewer)

`frobeniusPlane_genuine_dual (r s : ℤ) : ∃ β βdual, β.toPointMap = r•π − s•id ∧
βdual.toPointMap = r•V − s•id ∧ β.IsGenuine ∧ βdual.IsGenuine ∧ βdual.comp β = mulByInt(N)`,
then extract `degree β = N`. β = rπ−s already genuine (genuineIsogSmulSub); the work is
construct/repair the genuine βdual.

## Changes

- QF ticket board (`tickets/QF-PIC0-ROUTE.md`): round-2 decision recorded; T-QF-DUALADD /
  T-QF-PIVOT-FULL framed as B-narrow; T-QF-EXT reclassified as C supporting accelerator;
  next target frobeniusPlane_genuine_dual.
- Memory `hasse-qf-route-pic0` updated to the B-narrow+C refinement.

## Settled

- B vs C: B primary, C supporting (Q1). No lighter degree-only route (Q2). C ≠ B but depends
  on B in practice (Q3). Genuine dual pullback irreducible for the Silverman/Pic⁰ route (Q4).

## Open

The two keystones (now precisely pinned), each a substantial development:
- QF: `genuineIsogSmulSub_pivot_witness` (genuine comorphism of rV−s, B-narrow).
- V.1.3: `Sinf_kernelPrime_pow_mem_of_le_ord` (carrier P_T-adic valuation = curve ord_T;
  shared with bridge_Bii_bijective / B(iv)).
