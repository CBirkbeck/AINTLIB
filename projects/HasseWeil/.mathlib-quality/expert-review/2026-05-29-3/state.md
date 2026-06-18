# Expert-review session state — round 9 (follow-up)

- Generated: 2026-05-29 (follow-up to round 8)
- Audience: standing arithmetic-geometry reviewer
- Goal: report that the base-change route (round 8) hit the SAME generic-fibre/CoordHom wall as the K-level route; ask which route to #ker(1−π)=deg(1−π) — R1 (CoordHom-free generic fibre over K̄) vs R2 (over-K Galois Aut≃ker via translation autos) — and whether a slicker 4th route exists.
- Scope: Leaf 2 (deg(1−π)=#E(F_q)) only.
- Reply received: true (2026-05-29)
- Reply integrated: true (2026-05-29)

## Questions
Q1: Is R2 (over-K Galois: ker K-rational ⟹ K(E)/(1−π)*K(E) Galois with group ker acting by translation ⟹ deg=#ker) the right III.4.10a formalisation for 1−π? Traps (normality)?
Q2: A route needing NEITHER generic-fibre/CoordHom NOR the translation-auto construction (embeddings-vs-translations count from separability + the function-field-level (1−π)*)?
Q3: If R1: lightest CoordHom-free "geometric fibre = deg" over K̄ (reduction to finite-separable-field embedding count)?
Meta: two routes have hit the same wall; is R2 (Galois/translation) where to invest, or a 4th route?

## Status at brief time
- Shipped axiom-clean: #E(F_q) ≤ deg(1−π); and over K̄, #ker(1−geomFrob)=#E(F_q) (FrobeniusFixedPoint.lean, step 4 of base-change route).
- Open: reverse deg(1−π) ≤ #E(F_q) = the #ker=deg core (III.4.10a for 1−π).
- Obstruction: III.4.10a needs the generic-fibre theorem (II.2.6b); project's is CoordHom-bound; 1−π has no CoordHom (even over K̄); circularity trap (only fibre over 0 computable).
- R2 scaffold: PointFix.lean card_kernel_eq_degree_of_galois_witness; undischarged = τ_k construction (~200 LOC) + IsGalois normality.

## Cross-reference
Rounds 7 (2026-05-29/), 8 (2026-05-29-2/). This is round 9 (2026-05-29-3/).
