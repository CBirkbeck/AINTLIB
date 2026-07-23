/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafProjectiveCech
import ModularCurves.ForMathlib.AffineModuleCechBaseChange
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFunctor

/-!
# Base change of projective pole-sheaf H1 vanishing

The bounded ordered Cech model transports projective-stage vanishing of
`H¹(O(n[0]))` through every affine base change, without a Noetherian hypothesis
on the new base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- After every affine base change, the ordered coordinate-cover Cech complex
of a positive pole sheaf on a projectively presented fibrewise elliptic family
is exact in degree one. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPower_baseChange_projectiveClosed_orderedBaseCech_exactAt_one
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
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
      (R := R) (σ := σ) j
    let UT := fun j => pullback.fst π t ⁻¹ᵁ U j
    (Scheme.Modules.orderedBaseCechComplex πT MT UT).ExactAt 1 := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  let UT := fun j => g ⁻¹ᵁ U j
  let C := Scheme.Modules.orderedBaseCechComplex π M U
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : M.IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsm z hz n
  have hsmT : SmoothOfRelativeDimension 1 πT :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback π t) hsm
  letI : SmoothOfRelativeDimension 1 πT := hsmT
  letI : MT.IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsmT zT hzT n
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage f
  obtain ⟨hflat, hfinite, hbounded, hfield, _⟩ :=
    h.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_data
      f hsm z hz hn
  letI (q : ℕ) : Module.Flat B (C.X q) := hflat q
  letI (q : ℕ) : Module.Finite B (C.homology q) := hfinite q
  let N := Fintype.card (ULift.{u} σ)
  letI : Subsingleton (C.X (N + 1)) :=
    hbounded (N + 1) (Nat.le_succ N)
  have hN : 0 < N := Fintype.card_pos_iff.mpr inferInstance
  have hexact : ∀ q, q < N →
      Function.Exact (C.d q (q + 1)).hom
        (C.d (q + 1) (q + 2)).hom := by
    intro q hq
    exact
      HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
        C N (fun i _ K _ _ => hfield K i) q hq
  have hBaseChangeExact := LinearMap.baseChange_exact_of_bounded_exact
    (fun q => C.X q) (fun q => (C.d q (q + 1)).hom)
      A N hexact 0 hN
  have hBaseChangeExact' :
      Function.Exact ((C.d 0 1).hom.baseChange A)
        ((C.d 1 2).hom.baseChange A) := by
    simpa using hBaseChangeExact
  let CA := ((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
    (.up ℕ)).obj C
  have hCA : CA.ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff' CA 0 1 2 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change (C.d 1 2).hom.baseChange A x = 0 at hx
    change ∃ y, (C.d 0 1).hom.baseChange A y = x
    exact (hBaseChangeExact' x).mp hx
  let eBase := Scheme.Modules.orderedBaseCechComplexBaseChangeIso
    π t M U hUaff
  have hPullback :
      (Scheme.Modules.orderedBaseCechComplex πT
        ((Scheme.Modules.pullback g).obj M) UT).ExactAt 1 :=
    hCA.of_iso eBase
  let ePole := sectionPoleSheafPowerBaseChangeIso hsm z hz t n
  exact hPullback.of_iso
    ((Scheme.Modules.orderedBaseCechComplexFunctor πT UT).mapIso ePole)

/-- Positive pole sheaves retain vanishing first sheaf cohomology after every
affine base change of a Noetherian projectively presented fibrewise elliptic
family. The changed affine base need not be Noetherian. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_baseChange_projectiveClosed_subsingleton_H_one
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
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower πT zT hzT n).sheaf 1) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  let UT := fun j => pullback.fst π t ⁻¹ᵁ U j
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  have hUT : IsOpenCover UT :=
    Scheme.Hom.iSup_preimage_eq_top (pullback.fst π t) hU
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage f
  have hUTaff : ∀ j, IsAffineOpen (UT j) := by
    intro j
    exact IsAffineOpen.preimage_pullback_fst π t (hUaff j)
  have hsmT : SmoothOfRelativeDimension 1 πT :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback π t) hsm
  letI : MT.IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsmT zT hzT n
  apply (Scheme.Modules.baseCechComplex_exactAt_one_iff_subsingleton_H
    πT MT UT hUT hUTaff).mp
  apply Scheme.Modules.baseCechComplex_exactAt_one_of_orderedBaseCechComplex_exactAt_one
  exact h.sectionPoleSheafPower_baseChange_projectiveClosed_orderedBaseCech_exactAt_one
    f hsm z hz hn t

end ModularCurves
