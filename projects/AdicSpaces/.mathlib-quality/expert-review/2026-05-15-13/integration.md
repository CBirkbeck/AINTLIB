# Reply integration — round 18, 2026-05-15

Reply received from ChatGPT Pro on 2026-05-15.
Brief: `brief.md`
Reply: `reply.md`

## Interpretation summary

Reviewer's core message: the round-17 transport approach's obstruction is real, but the fix is **not** Option A (relax `plus_open_eq` to inclusion), **not** Option C (require `g_inv ∈ A_0`), **not** Option I as stated (approximate inverse). The correct route is a refined Option II/IV: use the general **relative-rational-to-absolute-rational representation theorem** (Wedhorn rational-subdomain stability / transitivity, Lemma 2.13 generalized direction). This is more general than Group III's `relativeRationalLocData_laurentNormalized` — it works for ANY relative rational datum, not just the canonical form, and it produces an absolute datum with `hopen` and presheaf-value equivalence both inherited.

Five questions answered:

- **Q1**: Options A/C wrong; Option I wrong; correct route is the general relative-to-absolute representation theorem (refined Option II/IV).
- **Q2**: Wedhorn does NOT use an old-pair datum for the ratio split. He works in `O(V_j)` and uses transitivity/stability of rational localizations. The absolute datum is supplied by the general theorem.
- **Q3**: `RatioNodeData` is the right structure. Do NOT relax to inclusions. The missing API is the general representation theorem.
- **Q4**: Bridge lemma's density route wrong; Spa equivalence Wedhorn 7.49 is the cleaner route (Spa(O(D)) ≃ rationalOpen(D), not field-only `Valued.extensionValuation`).
- **Q5**: Pause P3 only to swap the proof plan. W3 can run in parallel (lives over `presheafValue L`); W3-transport waits for the new P3 API.

## Changes applied

### File: `Adic spaces/TateAcyclicityResiduals.lean`

1. **Sub-lemma rename + statement refinement**: `relative_RationalLocData_to_absolute_transport` → `exists_absolute_rationalLocData_of_relative`. Docstring rewritten to reference Wedhorn rational-subdomain stability / transitivity (Lemma 2.13). Statement: given any `Drel : RationalLocData (presheafValue L)`, produce `Dabs : RationalLocData A` with `rationalOpen Dabs = Set.image (comap L.canonicalMap) (rationalOpen Drel)`. Reviewer also suggested adding a presheaf-value topological-ring equivalence clause; this is currently noted in the docstring as optional and will be added when the consumer needs it.

2. **P3 docstring rewrite**: `relative_ratio_split_transports_to_RatioNodeData` docstring updated with the round-18 8-step construction plan (work in `B = presheafValue L`, form `r = u_g · u_h⁻¹`, build relative Laurent two-cover, apply new representation API, discharge structure fields). Explicitly notes the round-17 plan retired: Group III's `presheafValue_relative_equiv` is too restrictive (requires canonical form, our `r` is not in it).

3. **File header update**: replaced the round-17 reframing section with a combined round-17/round-18 history. Documents:
   - Why round-17 fix wasn't enough (Group III requires canonical form, our `r` isn't).
   - Why round-18's general representation theorem is the right level.
   - New sub-ticket name (`exists_absolute_rationalLocData_of_relative`).
   - W3 parallel-work note (W3 can proceed; W3-transport waits).

4. **Bridge lemma unchanged**: `comap_canonicalMap_not_vle_zero_of_isUnit_aux` is already in round-17 form (uses Spa equivalence sub-lemma). Reviewer Q4 confirms this is the right approach.

## Changes rejected by user

None. User approved all changes ("apply all").

## Open questions remaining

(All five questions addressed by the reviewer.)

## Decisions recorded but not actioned

- Architecture remains locked at round 16 + round-17 + round-18 refinements (no further architectural change; only the construction-API plan continues to refine).
- Optional presheaf-value equivalence clause in `exists_absolute_rationalLocData_of_relative`: noted in docstring, not yet added to the signature. Add when first consumer needs it.

## Net effect

File compiles cleanly. Sorry count unchanged from round-17 (still 10). The round-18 reframing renames `relative_RationalLocData_to_absolute_transport` to `exists_absolute_rationalLocData_of_relative` and broadens its mathematical content. P3's proof plan is now mathematically sound and matches Wedhorn's actual construction.

The trade-off is intentional: discharge a more general sub-lemma rather than fight the canonical-form restriction of Group III.

## Round-18 status

- Architecture: SOUND. The three reviewer rounds (16, 17, 18) have settled the structure (`RatioNodeData` with literal equalities) and the construction method (general relative-rational representation API).
- Bridge lemma: structurally proved modulo `rationalOpen_equiv_Spa_presheafValue_aux` (Spa equivalence Wedhorn 7.49).
- P3: structurally planned via `exists_absolute_rationalLocData_of_relative` (Wedhorn rational-subdomain stability / transitivity).
- Path forward: discharge the two new sub-lemmas (or build the missing mathlib-grade infrastructure for them); then P3 follows mechanically.
