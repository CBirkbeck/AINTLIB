/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TorsionGeometric

/-!
# The division-polynomial Wronskian over a general field (axiom-clean, downstream route)

The **division-polynomial Wronskian identity** (Silverman Exercise III.3.7)

  `Φ_n' · ΨSq_n − Φ_n · ΨSq_n' = n · preΨ_{2n}`   in `F[X]`

is proved in `HasseWeil/OmegaPullbackCoeff.lean` (`wronskian_Φ_ΨSq`) by strong induction on `n`,
but the `n ≥ 5` inductive step needs the **EDS addition formula** (Ward's relation), which mathlib
does not currently provide. That proof therefore carries a `sorryAx` taint.

This file gives an **axiom-clean** proof of the same polynomial identity (for `n ≠ 0`) by routing
**downstream** through the function field, avoiding the EDS addition formula entirely. The chain is:

1. The **general-field differential** `a_{[n]} = n`
   (`HasseWeil.omegaCoeff_mulByInt`, finite-field free, proved by the
   Route-B chord recurrence — no EDS Wronskian).
2. The bridge `divPoly_wronskian_identity_of_omega` turns `a_{[n]} = n` into the **K(E)-level**
   Wronskian `(Φ' ΨSq − Φ ΨSq') · u = n · ΨSq² · α*u`.
3. The bridge `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u` rewrites `ΨSq² · α*u = preΨ_{2n} · u`,
   collapsing the right-hand side to `n · preΨ_{2n} · u`.
4. Cancelling the nonzero `u = u_gen` (`u_gen_ne_zero`) leaves an equality of
   `algebraMap (Polynomial F) KE`-images of two polynomials; by **injectivity** of that algebra map
   (`x_gen` transcendental: `IsFractionRing.injective` composed with
   `Affine.CoordinateRing.algebraMap_poly_injective`) the identity descends to `F[X]`.

The two bridge lemmas (2,3) and `omegaCoeff_mulByInt` (1) are all axiom-clean, so the resulting
polynomial Wronskian is axiom-clean. It is the EDS-free replacement for `wronskian_Φ_ΨSq` consumed
by the affine unramifiedness lemma `ord_P_mulByInt_x_sub_const_eq_one`
(`HasseWeil/EC/MulByIntUnramified.lean`).

Reference: Silverman, *The Arithmetic of Elliptic Curves*, Exercise III.3.7, III.5.3.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil.EC

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `algebraMap (Polynomial F) KE` is injective (`x_gen` is transcendental): it factors as the
two-step scalar tower `Polynomial F → R → KE`, the first injective because `R = CoordinateRing` is
a domain in which `X` is transcendental (`Affine.CoordinateRing.algebraMap_poly_injective`), the
second because `KE = FunctionField` is the fraction field of `R` (`IsFractionRing.injective`). -/
theorem algebraMap_polynomial_KE_injective :
    Function.Injective (algebraMap (Polynomial F) KE) := by
  have hfactor : (algebraMap (Polynomial F) KE : Polynomial F →+* KE) =
      (algebraMap R KE).comp (algebraMap (Polynomial F) R) :=
    IsScalarTower.algebraMap_eq (Polynomial F) R KE
  rw [show (algebraMap (Polynomial F) KE : Polynomial F → KE) =
      ((algebraMap R KE).comp (algebraMap (Polynomial F) R) : Polynomial F → KE) from
      congrArg DFunLike.coe hfactor]
  exact (IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective

set_option linter.unusedDecidableInType false in
/-- **The division-polynomial Wronskian identity over a general field, axiom-clean.**

`Φ_n' · ΨSq_n − Φ_n · ΨSq_n' = n · preΨ_{2n}` as polynomials in `F[X]` (Silverman Exercise III.3.7),
for `n ≠ 0`.

Unlike `HasseWeil.wronskian_Φ_ΨSq` (which proves this by strong induction whose `n ≥ 5` step needs
the unavailable EDS addition formula, hence `sorryAx`), this proof routes through the function
field: the general-field differential `a_{[n]} = n` (`omegaCoeff_mulByInt`, Route-B, EDS-free), K(E)
Wronskian bridge (`divPoly_wronskian_identity_of_omega`) and the `preΨ`/`u` bridge
(`preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`), then cancellation of `u_gen` and injectivity of
`algebraMap (Polynomial F) KE`. It is therefore axiom-clean. -/
theorem wronskian_Φ_ΨSq_general (n : ℤ) (hn : n ≠ 0) :
    Polynomial.derivative (W.Φ n) * W.ΨSq n - W.Φ n * Polynomial.derivative (W.ΨSq n) =
    Polynomial.C ((n : ℤ) : F) * W.preΨ (2 * n) := by
  -- (1) The general-field differential `a_{[n]} = n` (Route-B, finite-field-free, EDS-free).
  have homega := omegaCoeff_mulByInt W n hn
  -- (2) The K(E)-level Wronskian from the differential, via the axiom-clean bridge.
  have hKE := divPoly_wronskian_identity_of_omega W n hn homega
  -- (3) The `preΨ`/`u` bridge: `ΨSq² · α*u = preΨ_{2n} · u` in K(E).
  have hbridge := preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u W n hn
  -- Substitute the bridge into the RHS of `hKE`.
  -- `hKE`'s RHS is `algebraMap F KE n * ΨSq_ff W n ^ 2 * alpha_star_u …`.
  -- `hbridge : algebraMap (Polynomial F) KE (preΨ (2n)) * u_gen = ΨSq_ff W n ^ 2 * alpha_star_u …`.
  rw [mul_assoc, ← hbridge] at hKE
  -- Now `hKE : (Φ'·ΨSq − Φ·ΨSq') · u_gen
  --            = algebraMap F KE n * (algebraMap (Polynomial F) KE (preΨ (2n)) * u_gen)`.
  -- Rewrite `Φ_ff`/`ΨSq_ff` as `algebraMap (Polynomial F) KE` images (tower `F[X] → R → KE`).
  have hΦ_ff : Φ_ff W n = algebraMap (Polynomial F) KE (W.Φ n) :=
    (IsScalarTower.algebraMap_apply (Polynomial F) R KE (W.Φ n)).symm
  have hΨSq_ff : ΨSq_ff W n = algebraMap (Polynomial F) KE (W.ΨSq n) :=
    (IsScalarTower.algebraMap_apply (Polynomial F) R KE (W.ΨSq n)).symm
  rw [hΦ_ff, hΨSq_ff] at hKE
  -- Fold `algebraMap F KE n` into the polynomial image (scalar tower `F → F[X] → KE` via `C`).
  have hn_cast : algebraMap F KE (n : F) =
      algebraMap (Polynomial F) KE (Polynomial.C ((n : ℤ) : F)) := by
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply F (Polynomial F) KE]
  rw [hn_cast] at hKE
  -- Both sides of `hKE` are now `algebraMap (Polynomial F) KE (poly) * u_gen W`.
  -- Collect each side into a single `algebraMap`-image times `u_gen`.
  have hLHS : (algebraMap (Polynomial F) KE (Polynomial.derivative (W.Φ n)) *
        algebraMap (Polynomial F) KE (W.ΨSq n) -
      algebraMap (Polynomial F) KE (W.Φ n) *
        algebraMap (Polynomial F) KE (Polynomial.derivative (W.ΨSq n))) =
      algebraMap (Polynomial F) KE
        (Polynomial.derivative (W.Φ n) * W.ΨSq n -
          W.Φ n * Polynomial.derivative (W.ΨSq n)) := by
    rw [map_sub, map_mul, map_mul]
  have hRHS : algebraMap (Polynomial F) KE (Polynomial.C ((n : ℤ) : F)) *
        algebraMap (Polynomial F) KE (W.preΨ (2 * n)) =
      algebraMap (Polynomial F) KE (Polynomial.C ((n : ℤ) : F) * W.preΨ (2 * n)) := by
    rw [map_mul]
  rw [hLHS, ← mul_assoc, hRHS] at hKE
  -- `hKE : algebraMap (LHS_poly) * u_gen = algebraMap (RHS_poly) * u_gen`. Cancel `u_gen`.
  have hu := mul_right_cancel₀ (u_gen_ne_zero W) hKE
  -- Descend across the injective algebra map.
  exact algebraMap_polynomial_KE_injective W hu

end HasseWeil.EC
