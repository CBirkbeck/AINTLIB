/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafMonomialSequence

/-!
# Pole monomials away from the marked section

In the canonical trivialization away from the marked section, multiplication
of pole sections is ordinary multiplication of coefficients. Consequently,
the normalized pole-section sequence has coefficients `X, Y, X², XY, ...`.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

/-- The positive-pole monomial sequence `x, y, x², xy, x³, ...` in a
multiplicative type. Its `n`th term has weighted pole order `n + 2` when
`x` and `y` have weights two and three. -/
def positivePoleMonomial {R : Type*} [Mul R] (x y : R) : ℕ → R
  | 0 => x
  | 1 => y
  | n + 2 => positivePoleMonomial x y n * x

/-- In the canonical frames on an open disjoint from the marked section, the
coefficient of a product of pole sections is the product of its coefficients. -/
theorem
    overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_of_preimage_eq_bot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (m n : ℕ)
    (p : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz m))
    (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz n)) :
    overTrivializationCoefficient
        (sectionPoleSheafPower π z hz (m + n)) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz (m + n)) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV (m + n)))
        (sectionPoleSheafPower_baseSectionsMul z hz m n (p ⊗ₜ q)) =
      overTrivializationCoefficient
          (sectionPoleSheafPower π z hz m) V
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz m) V
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz V hV m)) p *
        overTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) V
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz n) V
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz V hV n)) q := by
  let ePole :=
    sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV
  simpa only [ePole,
    sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot] using
    overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
      z hz V ePole m n p q

/-- The canonical away coefficient of the normalized pole-section monomial is
the corresponding ordinary monomial in the away coefficients of `x` and `y`. -/
theorem overTrivializationCoefficient_sectionPoleSheafPower_normalizedMonomial
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (n : ℕ) :
    let X :=
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 2) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 2) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV 2)) x
    let Y :=
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 3) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV 3)) y
    overTrivializationCoefficient
        (sectionPoleSheafPower π z hz (n + 2)) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz (n + 2)) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV (n + 2)))
        (sectionPoleSheafPower_normalizedMonomial z hz x y n) =
      positivePoleMonomial X Y n := by
  dsimp only
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n hn _ =>
      rw [sectionPoleSheafPower_normalizedMonomial_add_two,
        positivePoleMonomial]
      rw [
        overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_of_preimage_eq_bot
          z hz V hV (n + 2) 2
          (sectionPoleSheafPower_normalizedMonomial z hz x y n) x,
        hn]

end ModularCurves
