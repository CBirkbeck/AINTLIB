/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafProjectiveBaseChangeHOne
import ModularCurves.EllipticCurve.PoleSheafSuccessorSections

/-!
# Local pole coordinates on a projectively presented elliptic family

After shrinking the affine base, the first two positive successor quotients
have normalized lifts. These are the pole-order-two and pole-order-three
coordinates used to construct a generalized Weierstrass equation.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical coordinate on the newest rank-one summand of two consecutive
pole-section modules, after choosing a Cartier generator along the section. -/
noncomputable def
    sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
    Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)) →ₗ[Γ(S, (⊤ : S.Opens))]
      Γ(S, (⊤ : S.Opens)) :=
  (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
      hsm z hz U hU r hspan hnzd n).toLinearEquiv.toLinearMap ∘ₗ
    (Scheme.Modules.baseSectionsMap π
      (cokernel.π (sectionPoleSheafSuccHom π z hz n))).hom

@[simp]
theorem sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_apply
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1))) :
    sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
        hsm z hz U hU r hspan hnzd n x =
      (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).hom
        (Scheme.Modules.baseSectionsMap π
          (cokernel.π (sectionPoleSheafSuccHom π z hz n)) x) :=
  rfl

/-- Around every point of the affine base of a projectively presented
fibrewise elliptic family, there are normalized pole-order-two and
pole-order-three sections for one common Cartier generator. -/
theorem
    FibrewiseElliptic.exists_sectionPoleSheafPower_baseChange_projectiveClosed_local_xy
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    (s : Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    ∃ V : (Spec (.of R)).affineOpens, s ∈ V.1 ∧
      let t : V.1.toScheme ⟶ Spec (.of R) := V.1.ι
      let πV := pullback.snd π t
      let zV := sectionBaseChange z hz t
      let hzV := sectionBaseChange_snd z hz t
      let hsmV : SmoothOfRelativeDimension 1 πV :=
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
          (IsPullback.of_hasPullback π t) hsm
      ∃ (U : (pullback π t).affineOpens)
          (hU : zV ⁻¹ᵁ U.1 = ⊤)
          (r : Γ(pullback π t, U.1))
          (hspan : zV.ker.ideal U = Ideal.span {r})
          (hnzd : r ∈ nonZeroDivisors Γ(pullback π t, U.1)),
        ∃ x : Scheme.Modules.baseSections πV
            (sectionPoleSheafPower πV zV hzV 2),
          sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
              hsmV zV hzV U hU r hspan hnzd 1 x = 1 ∧
            ∃ y : Scheme.Modules.baseSections πV
                (sectionPoleSheafPower πV zV hzV 3),
              sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
                hsmV zV hzV U hU r hspan hnzd 2 y = 1 := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  obtain ⟨V, hsV, U, hU, r, hspan, hnzd⟩ :=
    exists_affineBaseChange_sectionCartierGenerator hsm z hz s
  refine ⟨V, hsV, ?_⟩
  let t : V.1.toScheme ⟶ Spec (.of R) := V.1.ι
  let πV := pullback.snd π t
  let zV := sectionBaseChange z hz t
  let hzV := sectionBaseChange_snd z hz t
  have hsmV : SmoothOfRelativeDimension 1 πV :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback π t) hsm
  letI : SmoothOfRelativeDimension 1 πV := hsmV
  have hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower πV zV hzV 1).sheaf 1) :=
    h.sectionPoleSheafPower_baseChange_projectiveClosed_subsingleton_H_one
      f hsm z hz (n := 1) (by simp) t
  have hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower πV zV hzV 2).sheaf 1) :=
    h.sectionPoleSheafPower_baseChange_projectiveClosed_subsingleton_H_one
      f hsm z hz (n := 2) (by simp) t
  obtain ⟨x, hx⟩ :=
    exists_sectionPoleSheafPower_succ_baseSection_generator
      hsmV zV hzV U hU r hspan hnzd 1 hH1
  obtain ⟨y, hy⟩ :=
    exists_sectionPoleSheafPower_succ_baseSection_generator
      hsmV zV hzV U hU r hspan hnzd 2 hH2
  exact ⟨U, hU, r, hspan, hnzd, x, hx, y, hy⟩

end ModularCurves
