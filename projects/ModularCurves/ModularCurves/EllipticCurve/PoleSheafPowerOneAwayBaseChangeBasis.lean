/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import ModularCurves.EllipticCurve.PoleSheafPowerOneProjectiveCoordinates

/-!
# The normalized first pole basis after affine base change

For a projectively presented fibrewise elliptic curve, the canonical section
of the first pole module becomes the sole vector of a basis after passing to a
suitable principal affine neighborhood of any chosen base point.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem cancelBaseChange_one_one_tmul
    {R A K V : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] [Algebra A K]
    [IsScalarTower R A K] [AddCommGroup V] [Module R V]
    (v : V) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K V
        ((1 : K) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v)) =
      (1 : K) ⊗ₜ[R] v := by
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    one_smul]

private theorem exists_basis_of_localized_basis
    {R K V W : Type*} [CommRing R] [CommRing K]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module K W]
    (a : R) [Algebra R K] [Algebra (Localization.Away a) K]
    [IsScalarTower R (Localization.Away a) K]
    (v : V)
    (bA : Module.Basis (Fin 1) (Localization.Away a)
      (LocalizedModule.Away a V))
    (hbA : bA 0 = LocalizedModule.mkLinearMap (.powers a) V v)
    (eBC : K ⊗[R] V ≃ₗ[K] W) (w : W)
    (hw : eBC ((1 : K) ⊗ₜ[R] v) = w) :
    ∃ b : Module.Basis (Fin 1) K W, b 0 = w := by
  let A := Localization.Away a
  let eLoc : K ⊗[A] LocalizedModule.Away a V ≃ₗ[K]
      K ⊗[A] (A ⊗[R] V) :=
    (LocalizedModule.equivTensorProduct (.powers a) V).baseChange A K _ _
  let eCancel : K ⊗[A] (A ⊗[R] V) ≃ₗ[K] K ⊗[R] V :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K V
  let b : Module.Basis (Fin 1) K W :=
    (((bA.baseChange K).map eLoc).map eCancel).map eBC
  refine ⟨b, ?_⟩
  have hequiv :
      LocalizedModule.equivTensorProduct (.powers a) V
          (LocalizedModule.mk v 1) =
        (1 : A) ⊗ₜ[R] v := by
    rw [LocalizedModule.equivTensorProduct_apply_mk,
      Localization.mk_one_eq_algebraMap]
    simp
  have hbK :
      (bA.baseChange K) 0 = (1 : K) ⊗ₜ[A] bA 0 := by
    exact Module.Basis.baseChange_apply K bA 0
  have hloc :
      eLoc ((bA.baseChange K) 0) =
        (1 : K) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v) := by
    rw [hbK, hbA]
    simp only [eLoc, LinearEquiv.baseChange_tmul,
      LocalizedModule.mkLinearMap_apply]
    rw [hequiv]
  have hsource :
      eCancel (eLoc ((bA.baseChange K) 0)) =
        (1 : K) ⊗ₜ[R] v := by
    rw [hloc]
    exact cancelBaseChange_one_one_tmul v
  have hb : b 0 = eBC (eCancel (eLoc ((bA.baseChange K) 0))) := by
    simp only [b, Module.Basis.map_apply]
  calc
    b 0 = eBC (eCancel (eLoc ((bA.baseChange K) 0))) := hb
    _ = eBC ((1 : K) ⊗ₜ[R] v) := congrArg eBC hsource
    _ = w := hw

private theorem
    FibrewiseElliptic.sectionPoleSheafPowerOne_projectiveClosed_baseSectionsBaseChange_eq
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
    {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz 1
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
        f hsm z hz (n := 1) (by simp) t
        ((1 : A) ⊗ₜ[B]
          (sectionPoleSheafPowerOneSection π z hz :
            Scheme.Modules.baseSections π M)) =
      sectionPoleSheafPowerOneSection πT zT hzT := by
  dsimp only
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))]
    infer_instance⟩
  have hprojective :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv_one_tmul
      f hsm z hz (n := 1) (by simp) t
        (sectionPoleSheafPowerOneSection
          (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
  have hliteral :=
    sectionPoleSheafPowerOneSection_baseChange
      (π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      hsm z hz t
  exact hprojective.trans hliteral

/-- After every affine base change, the canonical first pole section is the
sole vector of a basis of the base-changed first pole module. -/
theorem
    FibrewiseElliptic.exists_sectionPoleSheafPowerOne_projectiveClosed_baseChange_basis
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
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    ∃ b : Module.Basis (Fin 1) Γ(T, (⊤ : T.Opens))
        (Scheme.Modules.baseSections πT
          (sectionPoleSheafPower πT zT hzT 1)),
      b 0 = sectionPoleSheafPowerOneSection πT zT hzT := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz 1
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT 1
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  let P := Scheme.Modules.baseSections π M
  letI : Algebra B A := t.appTop.hom.toAlgebra
  obtain ⟨b, hb⟩ :=
    h.exists_sectionPoleSheafPowerOne_projectiveClosed_basis
      f hsm z hz
  let eBC : A ⊗[B] P ≃ₗ[A]
      Scheme.Modules.baseSections πT MT :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
      f hsm z hz (n := 1) (by simp) t
  let bT : Module.Basis (Fin 1) A
      (Scheme.Modules.baseSections πT MT) :=
    (b.baseChange A).map eBC
  refine ⟨bT, ?_⟩
  rw [show bT 0 = eBC ((b.baseChange A) 0) by
    exact Module.Basis.map_apply (b.baseChange A) eBC 0]
  rw [Module.Basis.baseChange_apply, hb]
  exact h.sectionPoleSheafPowerOne_projectiveClosed_baseSectionsBaseChange_eq
    f hsm z hz t

/-- Around every base prime, the geometric first pole-section module admits a
singleton basis whose vector is the literal constant section after the
corresponding principal affine base change. -/
theorem
    FibrewiseElliptic.exists_sectionPoleSheafPowerOne_projectiveClosed_away_baseChange_basis
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
    (p : Ideal Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))) [p.IsPrime] :
    let S := Spec (.of R)
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let B := Γ(S, (⊤ : S.Opens))
    ∃ a : B, a ∉ p ∧
      let A := Localization.Away a
      let T := Spec (.of A)
      let t : T ⟶ S :=
        Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ S.isoSpec.inv
      let πT := pullback.snd π t
      let zT := sectionBaseChange z hz t
      let hzT := sectionBaseChange_snd z hz t
      ∃ b : Module.Basis (Fin 1) Γ(T, (⊤ : T.Opens))
          (Scheme.Modules.baseSections πT
            (sectionPoleSheafPower πT zT hzT 1)),
        b 0 = sectionPoleSheafPowerOneSection πT zT hzT := by
  dsimp only
  let S := Spec (.of R)
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz 1
  let B := Γ(S, (⊤ : S.Opens))
  let P := Scheme.Modules.baseSections π M
  let x : P := sectionPoleSheafPowerOneSection π z hz
  obtain ⟨a, ha, bA, hbA⟩ :=
    h.exists_sectionPoleSheafPowerOne_projectiveClosed_away_basis
      f hsm z hz p
  refine ⟨a, ha, ?_⟩
  let A := Localization.Away a
  let T := Spec (.of A)
  let t : T ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ S.isoSpec.inv
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT 1
  let K := Γ(T, (⊤ : T.Opens))
  letI : Algebra B K := t.appTop.hom.toAlgebra
  letI : Algebra A K :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  have hcomp :
      t.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom =
        CommRingCat.ofHom (algebraMap B A) := by
    dsimp only [t]
    rw [Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
    have hΓ : (Scheme.ΓSpecIso (.of B)).hom = S.isoSpec.hom.appTop := by
      exact (Scheme.toSpecΓ_appTop S).symm
    rw [hΓ, ← Category.assoc,
      ← Scheme.Hom.comp_appTop S.isoSpec.hom S.isoSpec.inv,
      S.isoSpec.hom_inv_id]
    simp
  have happly (r : B) :
      (Scheme.ΓSpecIso (.of A)).hom.hom (algebraMap B K r) =
        algebraMap B A r := by
    change ((t.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom).hom) r =
      (CommRingCat.ofHom (algebraMap B A)).hom r
    rw [hcomp]
  have hBAK (r : B) :
      algebraMap B K r = algebraMap A K (algebraMap B A r) := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of A)).hom).1
    rw [happly]
    change algebraMap B A r =
      (Scheme.ΓSpecIso (.of A)).hom.hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap B A r))
    simp
  letI : IsScalarTower B A K :=
    IsScalarTower.of_algebraMap_eq hBAK
  let eBC : K ⊗[B] P ≃ₗ[K]
      Scheme.Modules.baseSections πT MT :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
      f hsm z hz (n := 1) (by simp) t
  have htarget :
      eBC ((1 : K) ⊗ₜ[B] x) =
        sectionPoleSheafPowerOneSection πT zT hzT := by
    exact h.sectionPoleSheafPowerOne_projectiveClosed_baseSectionsBaseChange_eq
      f hsm z hz t
  exact exists_basis_of_localized_basis a x bA hbA eBC
    (sectionPoleSheafPowerOneSection πT zT hzT) htarget

end ModularCurves
