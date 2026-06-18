# Reply integration — round 7 (2026-05-29)

Reply received from the standing arithmetic-geometry reviewer, 2026-05-29.
Brief: ./brief.md   Reply: ./reply.md

## Verdict (one line)
Do NOT pivot to Stepanov yet. Finish Leaf 2 via the separable-isogeny fibre count; for Leaf 1 prove only the RESTRICTED Frobenius-plane dual `(rπ−s)^=rV−s`, not general III.6.1. Prototype Stepanov only as a bounded decision-check.

## Interpretation summary
- Q1: Stepanov plausible but not obviously cheaper; prototype its 2 core lemmas first. (no pivot)
- Q2: some duality unavoidable; prove RESTRICTED `(rπ−s)^=rV−s`. `{1,π,V}`+relations alone insufficient; parallelogram law not a shortcut.
- Q3: Leaf 2 via separable⇒unramified fibre count (Option B); drop the Sinf detour; must actually prove III.4.10(a).
- Q4: staged `IsGenuine` hygiene now; no naive affine compat field (must be local/projective/function-field-aware); core-type split later.
- Q5: Silverman route preserves almost all assets; Stepanov strands the isogeny work.
- Correction: "positive-definite" → "positive semidefinite (nonnegative)".

## Changes applied (all approved by user)
- **A** MODIFIED `W4-repair-dual-composition`: narrowed to the RESTRICTED `frobeniusPlane_dual` on the ℤπ+ℤ plane; dropped the "full III.6.2 additivity / general III.6.1" dependency; promoted to PRIMARY Leaf-1 target; added Round-7 guidance (and the "{1,π,V}+relations / parallelogram law are NOT shortcuts" point); semidefinite note.
- **B** MODIFIED `GAP-QF-DEGQF`: noted the restricted-dual route likely OBVIATES Wall A (V-side addIsog pole bound / VII.2) and Wall-B-as-stated; re-scoped to pursue `W4-repair-dual-composition` first; semidefinite terminology.
- **C** SUPERSEDED `SK-L6CA` (the Sinf pole-locus / inertia-sum detour) by the new `separable-isogeny-fibre-count`.
- **C-new** ADDED `separable-isogeny-fibre-count` (Silverman III.4.10a via Option B: separable⇒unramified-everywhere + Σ e_P f_P = deg + fibre over O + ker(1−π)=E(F_q)); PRIMARY Leaf-2 target.
- **D** ADDED `stepanov-prototype` (GATED; two core lemmas: explicit `L(nO)` basis + `zeros_le_poles`; do NOT pivot until assessed).
- **E** ADDED `isogeny-genuine-hygiene` (policy: require `IsGenuine`/compatible-isogeny on point-map↔pullback/degree transfer lemmas; no naive affine compat; type split deferred).
- **F** Doc terminology fix: "positive-definite" → "positive semidefinite (nonnegative)" in HasseBound.lean and OpenLemmas.lean (3 docstring/comment sites).

## Changes rejected by user
- (none)

## Open questions remaining (the reviewer addressed all five)
- (none unanswered) — Q1–Q5 all answered.

## Decisions recorded
- Leaf 2 is the chosen near-term target (user directive: start the separable-isogeny fibre count next).
- Stepanov is held as a fallback pending a bounded prototype; no pivot now.
- Isogeny core-type refactor deferred; carry explicit genuine hypotheses in the interim.
