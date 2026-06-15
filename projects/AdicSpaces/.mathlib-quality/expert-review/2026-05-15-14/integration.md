# Reply integration — round 19, 2026-05-15

Reply received from ChatGPT Pro on 2026-05-15.
Brief: `brief.md`
Reply: `reply.md`

## Interpretation summary

Reviewer's core message: **None of the existing Wedhorn 2.13 shapes (A iterated-minus, B iterated-overlap, C Laurent-normalized) fits P3.** Don't reformulate P3 through iterated-minus/overlap. Don't build the fully general reverse Wedhorn 2.13 (too big). **Build a P3-specific reverse instance** for the relative Laurent at `r = u_g · u_h⁻¹`. The absolute output should NOT prescribe `plus.P = L.P` — let the reverse-rational-subdomain construction output whatever pair fits.

Five questions answered:

- **Q1**: No existing shape fits. Shape A/B = overlap/equality (not half-space); Shape C requires absolute input.
- **Q2**: Build a P3-SPECIFIC reverse instance, not the fully general theorem.
- **Q3**: Wedhorn doesn't use the old pair `L.P`. He uses stability of rational localizations. Output some `RationalLocData A`, not a predetermined denominator-cleared one over `L.P`.
- **Q4**: Wedhorn 7.49 reverse direction is real, NOT field-specific. Need project-level Spa/presheaf-value equivalence.
- **Q5**: Focused project-internal gap, not mathlib-level rewrite, but substantive. Do this before W3-transport.

## Changes applied

### File: `Adic spaces/TateAcyclicityResiduals.lean`

1. **Renamed** `rationalOpen_equiv_Spa_presheafValue_aux` → `exists_spa_presheafValue_point_over_rationalOpen_point` (reviewer-recommended name). Body unchanged.

2. **Removed (replaced)** `exists_absolute_rationalLocData_of_relative` (round-18 general theorem). Replaced with two P3-specific sub-lemmas per reviewer guidance.

3. **Added** `relativeUnitGenerator_vle_transport_aux` — comap-formula lemma for the relative unit generator's `vle`. Stubbed.

4. **Added** `exists_absolute_ratio_rationalLocData_aux` — the P3-specific reverse Wedhorn 2.13 instance. Stubbed. Produces `plus, minus : RationalLocData A` with explicit rationalOpen equalities `R(L) ∩ {v.vle g h}` and `R(L) ∩ {v.vle h g}`. Does NOT prescribe `plus.P = L.P`.

5. **Updated** P3 (`relative_ratio_split_transports_to_RatioNodeData`) docstring with the round-19 four-piece proof plan: Spa lift + unit-vle transport + absolute representation + package. Body unchanged (still sorry; uses three new sub-lemmas).

6. **Updated** file header (lines 115-160) with round-17 → round-19 history. Documents: round-17 Group III restriction discovered, round-18 attempted general theorem, round-19 specific reverse instance per audit findings.

## Changes rejected by user

None. User approved "apply all".

## Open questions remaining

None — reviewer answered all 5 questions in round-19 brief.

## Decisions recorded but not actioned

- Architecture remains locked at round 16 + round-17/18/19 construction-method refinements.
- The fully general reverse Wedhorn 2.13 theorem (`exists_absolute_rationalLocData_of_relative`) is NOT pursued; replaced with P3-specific instance.
- W3 can proceed in parallel; W3-transport waits for new P3 API (round 19 reaffirms round 18 on this point).

## Net effect

File compiles cleanly. Sorry count: 10 → 11 (closed 1 round-18 general stub, added 2 round-19 specific stubs).

The trade-off is intentional: trade one big general sorry for two smaller specific sorries, each of which is closer to what P3 actually needs. The P3-specific reverse Wedhorn 2.13 is smaller and better-targeted than a fully general theorem.

## Round-19 status

- Architecture: SOUND across rounds 16/17/18/19.
- Bridge lemma: proved modulo `exists_spa_presheafValue_point_over_rationalOpen_point`.
- P3: structurally planned via three sub-lemmas (Spa lift + unit-vle transport + absolute representation). Body to be written by chaining the three sub-lemmas + packaging into `RatioNodeData`.
- Path forward: discharge the three sub-lemmas. The Spa lift is shared by both the bridge lemma and the absolute representation. The unit-vle transport is a short comap calculation. The absolute representation is the substantive P3-specific reverse Wedhorn 2.13.
