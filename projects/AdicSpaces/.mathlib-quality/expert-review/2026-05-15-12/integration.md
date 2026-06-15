# Reply integration — round 17, 2026-05-15

Reply received from ChatGPT Pro on 2026-05-15.
Brief: `brief.md`
Reply: `reply.md`

## Interpretation summary

Reviewer's core message: the obstruction in P3 is real but does **not** invalidate the round-16 architecture. P3's construction method is wrong — it should not produce `RatioNodeData` by direct denominator-cleared `RationalLocData A` (which leads to impossible `hopen` proofs over the old pair `L.P`). Instead, P3 should produce `RatioNodeData` by **transporting** a relative rational datum over `𝒪(L)` (where the inverse of `h` actually lives) to an absolute rational datum over `A` via the project's already-closed Group III equivalence (`presheafValue_relative_equiv` III.1 + `presheafValue_relative_equiv_isHomeomorph` III.2).

Five questions answered:

- **Q1**: Option A wrong (too weak for transport story); Option C wrong (too restrictive). Option B reframed: NOT a new `PairOfDefinition A`, but a relative-to-absolute transport via Group III.
- **Q2**: Round-16 architecture remains sound; only local P3 construction-method adjustment.
- **Q3**: Bridge lemma via Spa equivalence (Wedhorn 7.49), not density+non-arch.
- **Q4**: Don't enrich `A`'s pair of definition with completion-side inverse; use relative rational datum + transitivity.
- **Q5**: Pause P3 only to change statement/plan; continue round-16 order. W3 in parallel allowed.

## Changes applied

### File: `Adic spaces/TateAcyclicityResiduals.lean`

1. **Bridge sub-lemma** `comap_canonicalMap_not_vle_zero_of_isUnit_aux` — proof body replaced. Round-16 density+non-arch+strict-triangle sketch retired. New proof: Spa equivalence → `not_vle_zero_of_isUnit` on completion-side `w` → `comap_vle` pullback. Three-step conceptual proof, with the substance moved to a new sub-lemma.

2. **NEW sub-lemma** `rationalOpen_equiv_Spa_presheafValue_aux` — added (Spa equivalence Wedhorn 7.49). Sorry'd. This is the only substantive sorry the bridge depends on.

3. **NEW API stub** `relative_RationalLocData_to_absolute_transport` — added. Statement: given a relative `D' : RationalLocData (presheafValue L)`, produce the transported absolute `D'' : RationalLocData A` with the Spv-comap image equality. Sorry'd. This is the load-bearing transport API for P3.

4. **P3 docstring rewrite** `relative_ratio_split_transports_to_RatioNodeData` — replaced round-16 denominator-cleared sketch with the round-17 relative-transport construction. Seven-step explicit construction plan. Sorry preserved on body.

5. **File header update** — added round-17 reviewer-mandated reframing section. Documents the closed bridge lemmas, the reformulation, and the two new sub-tickets.

## Changes rejected by user

None. User approved all changes.

## Open questions remaining (the reviewer answered all)

(None — Q1-Q5 all addressed.)

## Decisions recorded but not actioned

- Architecture remains locked at round-16; no further refinements needed.
- Bridge lemma's `localizationLift`-route attempt retired; only the Spa-equivalence route is to be pursued.
- `RatioNodeData.plus_open_eq` and `minus_open_eq` kept as literal set equalities (Option A explicitly rejected).

## Net effect

File compiles cleanly. Sorry count: 9 → 11 (added `rationalOpen_equiv_Spa_presheafValue_aux` and `relative_RationalLocData_to_absolute_transport` as separate sub-tickets). P3 still sorry'd in body, but the proof plan is now sound — uses the two new sub-tickets, both of which have clear mathematical content (Wedhorn 7.49 + Group III transport).

The trade-off is intentional per reviewer guidance: decompose P3 into named sub-lemmas with clear content rather than have one large sorry with an impossible internal `hopen` proof.
