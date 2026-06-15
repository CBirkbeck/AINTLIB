# Reply integration — 2026-06-04 (Lemma 7.54)

Reply received from an adic-spaces/Huber expert on 2026-06-04.
Brief: ./brief.md
Reply: ./reply.md

## Interpretation summary

All four questions answered directly, high confidence, no pushback, no unanswered Qs.
- Q1 (elementary route): YES — a clean 2-stage route = Huber [Hu3] 2.6 Tate-specialised
  (normalised rational refinement via Cor 7.32/7.31 + the product trick P, S + Cor 7.53).
- Q2 (avoid 7.54): NO — prove it; avoid only the FULL [Hu3] generality (Tate Cor 7.32/7.31
  replaces Huber's local normalisation).
- Q3 ([Hu3] 2.6 skeleton): the 7 steps; Lean split into 5 sub-lemmas + assembly.
- Q4 (absolute vs relative): ABSOLUTE over Spa A suffices at the top; relative wrapper over
  presheafValue D later.
- Secondary: 8.34(ii) dominating unit IS Cor 7.32 (in-repo `exists_dominating_unit`);
  8.33/A.3(3) keep current plan.

## Project inventory (user-requested "check what we already have", verified 2026-06-04)

Most route ingredients ALREADY PROVEN in-repo:
- 7.45 Nullstellensatz containment: `Lemma745` (exists_spa_point_supp_ge_maxIdeal_of_complete,
  isUnit_iff_forall_not_vle_zero_of_complete). [user was right]
- Cor 7.53: `spanTop_iff_noCommonZero_spa` (StandardCover:838), proven, needs complete
  PairOfDefinition + A⁺⊆A₀.
- Step-1 normalisation unit: `exists_zero_nbhd_lt_on_qc` (Wedhorn 7.31, Cor732:431), proven,
  [IsTateRing] only — LIGHTER than the full dominating unit.
- Cor 7.32 dominating unit (for 8.34(ii)): `exists_dominating_unit` (Cor732:207), proven,
  parametrized by principal-pair + hArch.
- product identity: `rationalOpen_inter` (RationalSubsets:72), proven.
- form-(a) packaging: `rationalCovering_from_idealGenSet`, sorry-free.
NEW work only: product combinatorics (sub-lemmas 2–5 + assembly), unit-from-0-nbhd helper,
hArch-free Spa quasi-compactness (Tate CompactSpace instance currently carries
principal-pair+hArch; general Spv QC root = ValuationSpectrum.instCompactSpace).
DEFECT to fix: `exists_form_a_refinement` carries forbidden `[IsDomain A]` — strip it.

## Changes applied

- T-CECH-754 RESTRUCTURED: 🔴 BLOCKED-deferred-to-Huber → open, de-risked; replaced the
  invented-Nullstellensatz sketch with the reviewer's Huber-faithful 7-step product-trick
  route, wired to the in-repo ingredients above; flagged the NEW work (product combinatorics,
  unit-from-0-nbhd, hArch-free Spa QC); strip [IsDomain A].
- T-CECH-754-REL ADDED (low priority): relative wrapper over presheafValue D (Q4), deferred.
- Milestone chain (SEVER-D → IMPORT → 834-W828 → WIRE) no longer gated on a Huber black-box;
  754 is now an ordinary (de-risked) leaf.

## Changes rejected by user

(none)

## Open questions remaining

(none — all four answered.)

## Decisions recorded but not actioned

- 8.34(ii) dominating unit = `exists_dominating_unit` (in-repo, parametrized by PAIR + 7.40(6));
  the PAIR/740-6 work remains for that, route confirmed.
- 8.33 / A.3(3) gluing cocycle: keep current plan (reviewer: formalisation work, not uncertainty).
