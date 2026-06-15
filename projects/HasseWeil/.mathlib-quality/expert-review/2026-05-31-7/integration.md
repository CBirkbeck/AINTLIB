# Reply integration — round 19 (2026-05-31)

Reply received from the senior arithmetic-geometry reviewer on 2026-05-31.
Brief: ./brief.md   Reply: ./reply.md

## Interpretation summary

- **Verdict (Q4):** Route 2A confirmed soundest. Do NOT revert to Route 1 (reopens dual additivity /
  theorem-of-square / genuine dual of rπ−s in char p). Do NOT upgrade to full Tate modules (finite level
  for all ℓ≠p suffices). The three §8 sub-dependencies are bounded and expected. Attack order **§8.1 → §8.2 → §8.3**.
- **Q1 (#E[ℓ]=ℓ²):** option (a) — a GENERAL separable-isogeny fibre-count theorem
  `card_kernel_eq_degree_of_separable_isogeny` over K̄ (III.4.10c at function-field level); reuse the
  Leaf-2 embeddings-as-translations style. The affine R→R CoordHom is confirmed impossible; the x-line
  route is rejected (messier).
- **Q2 (pairing def):** the divisor-theoretic pairing is soundest, but DEFINE it by the CONSTANT QUOTIENT
  `(τ_S^*g_T)/g_T`, not pointwise evaluation. Build only `div_translate` + the `g_T` special case; defer a
  broad evaluation API. No materially shorter path avoiding the pairing.
- **Q3 (adjoint):** YES — use `picDual` (not `isogDual`) for the SEPARABLE adjoint; needs only the 4
  Picard-level facts + multiplicity-free pullback.
- **Cautions:** (1) call the form "nonnegative/semidefinite" not "positive definite"; (2) keep `e_ℓ^ℓ=1`
  a core PROPS output; (3) nondegeneracy gets its own ticket; (4) integer separation via the D-not-divisible
  argument = the shipped `int_eq_of_congr_all_primes_ne`.

## Changes applied (to `.mathlib-quality/tickets-route2-weil-pairing.md`)

- Added a "REVIEWER-ENDORSED PLAN (round 19)" block with the attack order and the three approach changes.
- `T-R2-TORSION` (now PRIORITY 1): re-pointed to `card_kernel_eq_degree_of_separable_isogeny`; dependency
  changed from the impossible `T-R2-TORSION-COORDHOM` to the new `T-R2-SEP-FIBRE`.
- `T-R2-TORSION-COORDHOM` → replaced by **`T-R2-SEP-FIBRE`** (the general separable-isogeny fibre count via
  the Leaf-2 embeddings-as-translations style); both dead routes (affine CoordHom; x-line) recorded as
  reviewer-confirmed.
- `T-R2-EVAL` (PRIORITY 2): narrowed to `div_translate` + the `g_T` special case (constant-ratio); broad
  pointwise-evaluation API explicitly deferred.
- `T-R2-PAIRING-DEF`: definition changed to the constant quotient of `(τ_S^*g_T)/g_T`; `e_ℓ^ℓ=1` kept as a
  core output.
- `T-R2-PAIRING-PROPS`: narrowed to bilinear/alternating; nondegeneracy split out.
- **`T-R2-NONDEG`**: NEW ticket (nondegeneracy on its own, per caution 3).
- `T-R2-ADJOINT` (PRIORITY 3): re-pointed to `weilPairing_adjoint_separable_picDual` (picDual, separable
  scope, the 4 required facts); `isogDual` explicitly not needed.
- `T-R2-DET-DEG`: uses `picDual∘φ=[deg φ]` (not isogDual) + the separable adjoint; π handled by Galois.

## Changes rejected by user

- (none) — user approved all.

## Open questions remaining

- (none) — the reviewer answered Q1–Q4 directly.

## Decisions recorded but not actioned (code-level, for the build phase)

- Naming: "nonnegative/semidefinite" in comments (caution 1).
- `int_eq_of_congr_all_primes_ne` already implements caution 4 (no new work).

## Next action

Resume the build (`/beastmode`) on **T-R2-SEP-FIBRE → T-R2-TORSION** (PRIORITY 1): the general
separable-isogeny fibre-count `#ker φ = deg φ` over K̄, Leaf-2 embeddings-as-translations style.
