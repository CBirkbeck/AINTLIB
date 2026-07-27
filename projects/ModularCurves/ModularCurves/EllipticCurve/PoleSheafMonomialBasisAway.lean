/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafFiniteStageLinearEquiv
import ModularCurves.EllipticCurve.PoleSheafAwayCoordinate

/-!
# Away coefficients of the compatible pole bases

In the canonical frame away from the marked section, the compatible basis of
each abstract pole module has coefficients `1, X, Y, X², XY, X³, ...`.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

/-- The full pole-monomial sequence `1, x, y, x², xy, x³, ...`. -/
def poleMonomialSequence {M : Type*} [One M] [Mul M]
    (x y : M) : ℕ → M
  | 0 => 1
  | n + 1 => positivePoleMonomial x y n

/-- Ring homomorphisms preserve the positive-pole monomial sequence. -/
theorem map_positivePoleMonomial
    {R A : Type*} [Semiring R] [Semiring A]
    (f : R →+* A) (x y : R) (n : ℕ) :
    f (positivePoleMonomial x y n) =
      positivePoleMonomial (f x) (f y) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n hn _ =>
      rw [positivePoleMonomial, positivePoleMonomial, map_mul, hn]

/-- Ring homomorphisms preserve the full pole-monomial sequence. -/
theorem map_poleMonomialSequence
    {R A : Type*} [Semiring R] [Semiring A]
    (f : R →+* A) (x y : R) (n : ℕ) :
    f (poleMonomialSequence x y n) =
      poleMonomialSequence (f x) (f y) n := by
  rcases n with _ | n
  · exact map_one f
  · exact map_positivePoleMonomial f x y n

/-- The model pole-order sequence is the full pole-monomial sequence
specialized to the model coordinates. -/
theorem poleOrderMonomialSequence_eq_poleMonomialSequence
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) (n : ℕ) :
    poleOrderMonomialSequence W n =
      poleMonomialSequence (coordX W) (coordY W) n := by
  rcases n with _ | n <;> rfl

/-- Every vector in the compatible abstract pole basis has the corresponding
ordinary monomial as its coefficient away from the marked section. -/
theorem overTrivializationCoefficient_sectionPoleSheafPower_monomialBasis
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1)))
    (hbOne : bOne 0 = sectionPoleSheafPowerOneSection π z hz)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥) :
    let coeff : (n : ℕ) →
        Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz n) → Γ(C, V) :=
      fun n q =>
        overTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) V
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz n) V
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz V hV n)) q
    let X := coeff 2 x
    let Y := coeff 3 y
    ∀ (n : ℕ) (i : Fin (n + 1)),
      coeff (n + 1)
          (sectionPoleSheafPower_monomialBasis
            hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n i) =
        poleMonomialSequence X Y i := by
  dsimp only
  intro n
  induction n with
  | zero =>
      intro i
      rw [Fin.eq_zero i,
        sectionPoleSheafPower_monomialBasis_zero,
        hbOne,
        overTrivializationCoefficient_sectionPoleSheafPowerOneSection_of_preimage_eq_bot]
      rfl
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [sectionPoleSheafPower_monomialBasis_succ_last,
          overTrivializationCoefficient_sectionPoleSheafPower_normalizedMonomial]
        rfl
      · change
          overTrivializationCoefficient _ V _
              (sectionPoleSheafPower_monomialBasis
                hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy
                (n + 1) (Fin.castAdd 1 j)) =
            poleMonomialSequence _ _ j
        rw [sectionPoleSheafPower_monomialBasis_succ_castAdd,
          overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc_of_preimage_eq_bot,
          ih]

end ModularCurves
