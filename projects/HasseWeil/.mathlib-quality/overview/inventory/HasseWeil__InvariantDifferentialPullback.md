# Inventory: ./HasseWeil/InvariantDifferentialPullback.lean

File length: 119 lines.
Imports: `HasseWeil.Auxiliary.PullbackKaehler`, `HasseWeil.OmegaPullbackCoeff`.

---

## Declarations

### `noncomputable def Isogeny.pullbackKaehler`

- **Type**: `(α : Isogeny W.toAffine W.toAffine) : KaehlerDifferential F KE →+ KaehlerDifferential F KE`
- **What**: Defines the additive map on Kähler differentials `Ω[K(E)/F]` induced by an isogeny `α`, via pullback along the algebra homomorphism `α.pullback : K(E) →ₐ[F] K(E)`.
- **How**: One-liner delegation to `AlgHom.pullbackKaehler` from `HasseWeil.Auxiliary.PullbackKaehler`.
- **Hypotheses**: `F` a field with decidable equality, `W` a Weierstrass curve over `F`, `W.toAffine.IsElliptic`.
- **Uses from project**: `Isogeny.pullback` (implicit via `α.pullback`), `AlgHom.pullbackKaehler`
- **Used by**: `pullbackKaehler_D`, `pullbackKaehler_smul_F`, `pullbackKaehler_smul_KE`, `pullbackKaehler_comp`, `pullbackKaehler_invariantDifferential`
- **Visibility**: public
- **Lines**: 34–36, proof length: 1 line (definition)
- **Notes**: `noncomputable` due to `KaehlerDifferential`.

---

### `theorem Isogeny.pullbackKaehler_D`

- **Type**: `(α : Isogeny W.toAffine W.toAffine) (x : KE) : α.pullbackKaehler (KaehlerDifferential.D F KE x) = KaehlerDifferential.D F KE (α.pullback x)`
- **What**: Computes the pullbackKaehler on the universal derivation `D`: it equals `D` applied to the pullback of `x`.
- **How**: One-liner delegation to `AlgHom.pullbackKaehler_D`.
- **Hypotheses**: Same as `pullbackKaehler`.
- **Uses from project**: `Isogeny.pullbackKaehler`, `AlgHom.pullbackKaehler_D`
- **Used by**: `pullbackKaehler_invariantDifferential`
- **Visibility**: public (`@[simp]`)
- **Lines**: 40–43, proof length: 1 line
- **Notes**: Tagged `@[simp]`.

---

### `theorem Isogeny.pullbackKaehler_smul_F`

- **Type**: `(α : Isogeny W.toAffine W.toAffine) (c : F) (ω : KaehlerDifferential F KE) : α.pullbackKaehler (c • ω) = c • α.pullbackKaehler ω`
- **What**: States that `pullbackKaehler` is `F`-linear: base-field scalars pass through unchanged.
- **How**: One-liner delegation to `AlgHom.pullbackKaehler_smul_R`.
- **Hypotheses**: Same as `pullbackKaehler`.
- **Uses from project**: `Isogeny.pullbackKaehler`, `AlgHom.pullbackKaehler_smul_R`
- **Used by**: `omegaPullbackCoeff_comp_of_base`
- **Visibility**: public
- **Lines**: 46–49, proof length: 1 line
- **Notes**: None.

---

### `theorem Isogeny.pullbackKaehler_smul_KE`

- **Type**: `(α : Isogeny W.toAffine W.toAffine) (s : KE) (ω : KaehlerDifferential F KE) : α.pullbackKaehler (s • ω) = α.pullback s • α.pullbackKaehler ω`
- **What**: States the semilinearity of `pullbackKaehler` over `K(E)` scalars: a `K(E)`-scalar `s` transforms to `α.pullback s` on the right.
- **How**: One-liner delegation to `AlgHom.pullbackKaehler_smul_S`.
- **Hypotheses**: Same as `pullbackKaehler`.
- **Uses from project**: `Isogeny.pullbackKaehler`, `AlgHom.pullbackKaehler_smul_S`
- **Used by**: `pullbackKaehler_invariantDifferential`, `omegaPullbackCoeff_comp_of_base`
- **Visibility**: public
- **Lines**: 53–56, proof length: 1 line
- **Notes**: None.

---

### `theorem Isogeny.pullbackKaehler_comp`

- **Type**: `(α β : Isogeny W.toAffine W.toAffine) : (α.comp β).pullbackKaehler = β.pullbackKaehler.comp α.pullbackKaehler`
- **What**: Composition of isogenies acts contravariantly on `pullbackKaehler`: `(α∘β)^* = β^* ∘ α^*`.
- **How**: Unfolds the definition via two `change` tactics matching `(α.comp β).pullback = β.pullback.comp α.pullback`, then applies `AlgHom.pullbackKaehler_comp` and `rfl`.
- **Hypotheses**: Same as `pullbackKaehler`.
- **Uses from project**: `Isogeny.pullbackKaehler`, `AlgHom.pullbackKaehler_comp`, `Isogeny.comp` (via `(α.comp β).pullback`)
- **Used by**: `omegaPullbackCoeff_comp_of_base`
- **Visibility**: public (`@[simp]`)
- **Lines**: 63–69, proof length: 7 lines
- **Notes**: Tagged `@[simp]`. Uses `change` twice to expose the pullback composition definitional equality.

---

### `theorem Isogeny.pullbackKaehler_invariantDifferential`

- **Type**: `(α : Isogeny W.toAffine W.toAffine) : α.pullbackKaehler (invariantDifferential W.toAffine) = omegaPullbackCoeff W α • invariantDifferential W.toAffine`
- **What**: The key bridge: applying `pullbackKaehler α` to the invariant differential `ω` of `E` yields `a_α • ω`, where `a_α = omegaPullbackCoeff W α` is the pullback coefficient.
- **How**: Unfolds `invariantDifferential` as `(u_gen)⁻¹ • D(x)`, applies `pullbackKaehler_smul_KE` and `pullbackKaehler_D`, then rewrites `α.pullback (u_gen)⁻¹ = (alpha_star_u W α)⁻¹` via `map_inv₀` and `alpha_star_u_eq`, and concludes with the symmetric form of `omegaPullbackCoeff_spec`.
- **Hypotheses**: Same as `pullbackKaehler`.
- **Uses from project**: `pullbackKaehler_smul_KE`, `pullbackKaehler_D`, `u_gen`, `alpha_star_u`, `alpha_star_u_eq`, `omegaPullbackCoeff_spec`, `omegaPullbackCoeff` (implicit)
- **Used by**: `omegaPullbackCoeff_comp_of_base`
- **Visibility**: public
- **Lines**: 74–85, proof length: 12 lines
- **Notes**: Core bridge lemma of the file.

---

### `theorem omegaPullbackCoeff_comp_of_base`

- **Type**: `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] (α β : Isogeny W.toAffine W.toAffine) (c_α : F) (hα : omegaPullbackCoeff W α = algebraMap F W.toAffine.FunctionField c_α) : omegaPullbackCoeff W (α.comp β) = algebraMap F W.toAffine.FunctionField c_α * omegaPullbackCoeff W β`
- **What**: The chain rule for `omegaPullbackCoeff` (Silverman III.5.6a): if the pullback coefficient of `α` is a base-field constant `c_α ∈ F`, then `a_{α∘β} = c_α · a_β`.
- **How**: Applies `omegaPullbackCoeff_unique` to reduce to an identity on `invariantDifferential`; then rewrites via `pullbackKaehler_invariantDifferential (α.comp β)`, `pullbackKaehler_comp`, `pullbackKaehler_invariantDifferential α`, hypothesis `hα`, `pullbackKaehler_smul_KE`, `β.pullback.commutes c_α` (that the pullback fixes base field elements), `pullbackKaehler_invariantDifferential β`, and `smul_smul`.
- **Hypotheses**: `F` field with decidable equality; `W` elliptic curve; `α`, `β` isogenies `E→E`; `a_α = algebraMap c_α` for some `c_α : F`.
- **Uses from project**: `omegaPullbackCoeff_unique`, `pullbackKaehler_invariantDifferential`, `pullbackKaehler_comp`, `pullbackKaehler_smul_KE`; `Isogeny.pullback.commutes`
- **Used by**: unused in this file (exported; used in `GapSpines.lean`, `GapQfKernel.lean`, `AdditionPullback/Differential.lean`)
- **Visibility**: public
- **Lines**: 104–118, proof length: 15 lines
- **Notes**: The main exported theorem of the file. The hypothesis that `a_α` is a base-field element is essential for the `F`-linearity step.

---

## Summary statistics

| Metric | Value |
|---|---|
| Total declarations | 7 |
| noncomputable defs | 1 |
| theorems/lemmas | 6 |
| instances | 0 |
| sorry | none |
| set_option maxHeartbeats | none |
| proofs > 30 lines | none |

## Key API (used by 3+ others in this file)

- `Isogeny.pullbackKaehler`: used by `pullbackKaehler_D`, `pullbackKaehler_smul_F`, `pullbackKaehler_smul_KE`, `pullbackKaehler_comp`, `pullbackKaehler_invariantDifferential` (5 callers)
- `pullbackKaehler_invariantDifferential`: used by `omegaPullbackCoeff_comp_of_base` (1 caller, but key export to many other files)

## Unused in this file (dead-code candidates within file)

- `pullbackKaehler_smul_F`: only used by `omegaPullbackCoeff_comp_of_base` (1 caller in this file — note it IS used externally via other files)
- `omegaPullbackCoeff_comp_of_base`: not called by anything else in this file

## Notes

This is a small, focused bridge file (119 lines, 7 declarations, no sorries, no sorry, no `set_option maxHeartbeats`). It specializes the abstract `AlgHom.pullbackKaehler` API to elliptic curve isogenies and proves the chain rule `a_{α∘β} = c_α · a_β` (Silverman III.5.6a) used downstream in `GapSpines.lean` and `GapQfKernel.lean`. All proofs are short (≤15 lines), clean, and axiom-free assuming the imports are clean.
