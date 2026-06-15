# Reply integration — round 9 (2026-05-29)

Reply: ./reply.md   Brief: ./brief.md

## Verdict (one line)
Leaf 2 via R2 implemented as an EMBEDDINGS-CLASSIFICATION theorem (NOT IsGalois-first):
Hom_M(L,Ω) ≅ ker(1−π) = E(F_q); finite-separable count #Hom = [L:M] = deg(1−π) ⟹ deg(1−π) = #E(F_q).

## Interpretation
One decisive recommendation. Do not prove normality up front (circular via cardinality). Construct translations τ_T, prove they fix M, show every M-embedding into an alg closure Ω is a translation (the core), count embeddings by finite separability. Normality follows after.

## Changes applied
- MODIFIED `separable-isogeny-fibre-count` ticket: added the "★ ROUND-9 CHOSEN ROUTE" — R2 embeddings-classification, 5 steps, with the existing assets identified:
  - Step 1 τ_T: `translateAlgEquivOfPoint` (EC/TranslationOrd.lean:3307) likely already built (+ valuation API in EC/TranslateValuation.lean) — verify sorry-free.
  - Step 5 count: mathlib `AlgHom.card` (IsAlgClosed) + `finSepDegree_eq_finrank_of_isSeparable`.
  - Steps 2–4 are the net new work; step 4 (classify every embedding as a translation) is the core.
- Base-change (R1) deprioritized.

## Changes rejected
- (none)

## Open questions remaining
- (none) — reviewer gave a complete 5-step plan + traps.

## Decision recorded
- R2 embeddings-classification is the chosen Leaf-2 path. Next: verify Step 1 (translateAlgEquivOfPoint) is the right τ_T + sorry-free; then implement steps 2–4 (core), close with the mathlib count (step 5).
- Key traps: P_gen over L vs σ-image over Ω (common extension via σ-inclusion); projective group law not affine slopes; reuse a^q=a⟺a∈F_q for ker=E(F_q) over Ω; count Hom (embeddings) not Aut until normality proven.
