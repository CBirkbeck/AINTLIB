import ModularCurves.Moduli.WeierstrassAtlas
import Mathlib.RingTheory.Localization.Basic

/-!
# T-W7 P0 — the universal atlas ring is an integral domain

Part of the constructive group-scheme structure on the universal Weierstrass curve
(Stream W, ticket **T-W7.0a**). The coefficient-with-discriminant-inverted ring
`WeierstrassAtlasRing = ℤ[a₁,…,a₆][Δ⁻¹]` is an integral domain: it is the localization of the
polynomial domain `MvPolynomial (Fin 5) ℤ` away from the (nonzero) universal discriminant `Δ`.

This domain property is the foundation of the generic-point method used throughout T-W7: the
group-law axioms over the atlas are proved by evaluating at the single generic point `η` of the
integral scheme `U = Spec ℤ[a₁,…,a₆][Δ⁻¹]`.

## Main results

* `universalWeierstrass_Δ_ne_zero`: the universal discriminant is a nonzero polynomial,
  witnessed by the specialisation to `y² = x³ − x` (whose discriminant is `64`).
* the `IsDomain WeierstrassAtlasRing` instance.
-/

open AlgebraicGeometry WeierstrassCurve

namespace ModularCurves

/-- The universal discriminant `Δ ∈ ℤ[a₁,…,a₆]` is nonzero: specialising the coefficients to
the elliptic curve `y² = x³ − x` (`a₄ = −1`, other `aᵢ = 0`) sends `Δ` to `64 ≠ 0`. -/
theorem universalWeierstrass_Δ_ne_zero : universalWeierstrass.Δ ≠ 0 := by
  intro hΔ
  have key : (universalWeierstrass.map
      (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ))).Δ = 64 := by
    have e2 : (![0, 0, 0, -1, 0] : Fin 5 → ℤ) 2 = 0 := by decide
    have e3 : (![0, 0, 0, -1, 0] : Fin 5 → ℤ) 3 = -1 := by decide
    have e4 : (![0, 0, 0, -1, 0] : Fin 5 → ℤ) 4 = 0 := by decide
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.map, universalWeierstrass,
      MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, e2, e3, e4]
    norm_num
  rw [WeierstrassCurve.map_Δ, hΔ, map_zero] at key
  norm_num at key

/-- **(T-W7.0a)** The Weierstrass atlas ring `ℤ[a₁,…,a₆][Δ⁻¹]` is an integral domain — a
localization of the polynomial domain `MvPolynomial (Fin 5) ℤ` at the powers of the nonzero
discriminant. -/
instance instIsDomainWeierstrassAtlasRing : IsDomain WeierstrassAtlasRing :=
  have hle : Submonoid.powers universalWeierstrass.Δ ≤
      nonZeroDivisors (MvPolynomial (Fin 5) ℤ) :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero universalWeierstrass_Δ_ne_zero)
  IsLocalization.isDomain_localization hle

end ModularCurves
