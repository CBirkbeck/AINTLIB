/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleFiltrationMonomialBasis
import ModularCurves.EllipticCurve.PoleSheafUniformMonomialBasis

/-!
# Finite-stage comparison with the model pole filtration

The compatible basis of each abstract pole module is identified with the
ordered monomial basis of the corresponding Weierstrass-model filtration.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

/-- The finite-stage linear equivalence from abstract pole sections to the
model pole-order filtration, defined by the two ordered monomial bases. -/
noncomputable def sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
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
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (n : ℕ) :
    Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)) ≃ₗ[Γ(S, (⊤ : S.Opens))]
      poleOrderFiltration W (n + 1) :=
  (sectionPoleSheafPower_monomialBasis
    hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n).equiv
      (poleOrderFiltrationMonomialBasis W (by omega))
      (Equiv.refl (Fin (n + 1)))

/-- The finite-stage equivalence sends each abstract compatible-basis vector
to the model monomial with the same pole-order index. -/
@[simp]
theorem sectionPoleSheafPower_poleOrderFiltrationLinearEquiv_apply_basis
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
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (n : ℕ) (i : Fin (n + 1)) :
    sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
        hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy W n
        (sectionPoleSheafPower_monomialBasis
          hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n i) =
      ⟨poleOrderMonomialSequence W i,
        poleOrderMonomialSequence_mem W (by omega) i⟩ := by
  rw [sectionPoleSheafPower_poleOrderFiltrationLinearEquiv,
    Module.Basis.equiv_apply, Equiv.refl_apply,
    poleOrderFiltrationMonomialBasis_apply]

/-- The finite-stage equivalence sends every normalized positive-pole section
to the corresponding literal model monomial. -/
theorem sectionPoleSheafPower_poleOrderFiltrationLinearEquiv_normalizedMonomial
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
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (n : ℕ) :
    ((sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
        hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy W (n + 1)
        (sectionPoleSheafPower_normalizedMonomial z hz x y n) :
      poleOrderFiltration W (n + 2)) :
        W.toAffine.CoordinateRing) =
      positivePoleMonomial (coordX W) (coordY W) n := by
  rw [← sectionPoleSheafPower_monomialBasis_succ_last
    hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n,
    sectionPoleSheafPower_poleOrderFiltrationLinearEquiv_apply_basis]
  rfl

end ModularCurves
