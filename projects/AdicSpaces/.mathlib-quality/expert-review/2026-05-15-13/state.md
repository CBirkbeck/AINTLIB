# Expert-review session state — round 18

- Generated: 2026-05-15
- Audience: ChatGPT Pro (continuing series; round 18, follow-up to round 17 reframing)
- Goal of brief: Specific blocker — round-17 transport approach also obstructed; needs resolution between four options
- Scope: P3 obstruction (the same `1/h ∈ locSubring` algebraic barrier round 17 was supposed to bypass)
- Reply received: true (2026-05-15)
- Reply integrated: true (2026-05-15)

## Questions in the brief

| # | Question |
|---|----------|
| Q1 | Of options I/II/III/IV in §8: which is the correct route forward? (I: approximate-inverse lemma via Wedhorn 7.45+7.50; II: different `D''.P` pair; III: relax `plus_open_eq` to image equality; IV: different relative-split target) |
| Q2 | In Wedhorn's own write-up of Lemma 8.34 Step (iii), how is the absolute `T`, `s`, pair of definition `P` chosen for each ratio split, and how is `hopen` established? |
| Q3 | Does the recurring `1/h ∈ locSubring` obstruction indicate `RatioNodeData` needs to be relaxed (Option III), or that an "approximate inverse" mathlib-grade infrastructure piece is missing (Option I)? Round-17 said architecture is sound; round-18 asks if it's correct *as a target* but missing infrastructure, vs. needing structural change. |
| Q4 | The bridge lemma also depends on Spa equivalence Wedhorn 7.49 which has the same `1/h` flavour. Is the targeted rational-open transport (per round-17 alternative) realisable, or does it have the same issue under the hood? |
| Q5 | Is the architecture genuinely correct *as a target* but stuck on missing mathlib-grade approximate-inverse infrastructure, OR does the recurring obstacle indicate that `RatioNodeData` should carry `plus.P` as a field (allowing the pair of definition to be chosen per-piece)? |

## Ticket-board snapshot at brief time

Same as round 17, plus:
- `comap_canonicalMap_not_vle_zero_of_isUnit_aux` (bridge): proved modulo Spa equivalence (round-17 reframed; partial proof in file).
- `rationalOpen_equiv_Spa_presheafValue_aux`: open, B3-flagged round 17.
- `relative_RationalLocData_to_absolute_transport`: blocked (round-18 finding §8.1).

## Stuck points (from §8 of brief)

1. §8.1 — round-17 transport approach also hits `1/h ∈ locSubring` issue. Specifically: relative datum at `r = u_g · u_h⁻¹` after denominator-clearing → absolute `D'' = (L.P, {g}, h)` whose `hopen` requires `h_inv ∈ L.P.A_0` (unavailable) or approximate inverse.
2. §8.2 — Spa equivalence Wedhorn 7.49 also blocked on missing mathlib infrastructure (continuous valuation extension to commutative-ring completion).
3. Four resolution options surfaced: I (approximate inverse), II (different `D''.P`), III (relax structure), IV (different relative target).

## Reference list (from §2.2 of brief)

- [Wedhorn 2019] Adic Spaces — Lemmas 7.44–7.45, 7.50, 8.34, Prop 8.2, Thm 8.28(b).
- [Huber 1993] Étale Cohomology of Rigid Analytic Varieties.

## Architecture status

Round 16 final architecture approval (RatioLaurentTree + RatioNodeData + RatioTreeRealization).
Round 17 reframing approved: keep `plus_open_eq` literal equality, change construction method from direct denominator-cleared to Group-III-transport-based.
Round 18 reports: round-17's transport method has its own obstruction at the same `1/h` algebraic barrier, asking how the reviewer wants to resolve.
