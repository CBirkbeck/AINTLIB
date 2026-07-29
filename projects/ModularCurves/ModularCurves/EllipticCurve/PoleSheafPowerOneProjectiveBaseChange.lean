/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafPowerOneBaseChange
import ModularCurves.EllipticCurve.PoleSheafProjectiveBaseChange

/-!
# Nonvanishing of the first pole section after projective base change

The projective pole-section base-change equivalence carries the pure tensor of
the literal first-pole section to a nonzero section on every nonempty affine
base change.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The pure tensor of the literal first-pole section remains nonzero under
projective pole-section base change. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPowerOne_projectiveClosed_baseSectionsBaseChange_ne_zero
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {T : Scheme.{u}} [IsAffine T] [Nonempty T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz 1
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
        f hsm z hz (n := 1) (by simp) t
        ((1 : A) ⊗ₜ[B]
          (sectionPoleSheafPowerOneSection π z hz :
            Scheme.Modules.baseSections π M)) ≠ 0 := by
  dsimp only
  let πT := pullback.snd
    (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))]
    infer_instance⟩
  letI : Nonempty (CategoryTheory.Limits.pullback
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) t : Scheme.{u}) :=
    Nonempty.map (fun x : T => zT x) inferInstance
  have hsmT : SmoothOfRelativeDimension 1 πT :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback
        (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) t) hsm
  have htarget : sectionPoleSheafPowerOneSection πT zT hzT ≠ 0 :=
    sectionPoleSheafPowerOneSection_ne_zero hsmT zT hzT
  have hpure :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv_one_tmul
      f hsm z hz (n := 1) (by simp) t
        (sectionPoleSheafPowerOneSection
          (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
  rw [hpure]
  change
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t 1).hom.val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop
          (pullback.fst
            (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) t)
          (sectionPoleSheafPower
            (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz 1)
          (show Γ(sectionPoleSheafPower
              (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz 1,
              (⊤ : E.Opens)) from
            sectionPoleSheafPowerOneSection
              (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)) ≠ 0
  rw [sectionPoleSheafPowerOneSection_baseChange hsm z hz t]
  exact htarget

end ModularCurves
