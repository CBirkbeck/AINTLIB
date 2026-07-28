/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.Comparison
import ModularCurves.ModularCurve.YOneAssembly
import ModularCurves.Moduli.QuotientProblem

/-!
# The Y₁ Tate-atlas classifying clause: local algebra

This file is the NEW-ATLAS workspace for the classifying part of `exists_tatePoint`
(Loeffler Corollary 3.3.5).  It deliberately stays out of `YOneAssembly.lean`: the lemmas here
package the proved ring-level Tate-normal-form result (T-E1), the relative Tate-ring map, and the
proved pointed-model comparison theorem (T-W7.1b) in the shapes needed by the atlas gluing step.
-/

open AlgebraicGeometry CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

section PullbackCongrHom

variable {C : Type*} [Category C]

/-- The forward comparison map `pullback.congrHom rfl h` induced by an equality of the second
leg, composed with the first projection, is the original first projection. -/
private theorem congrHom_hom_comp_fst {X Y Z : C} (f : X ⟶ Z) {g₁ g₂ : Y ⟶ Z} (h : g₁ = g₂)
    [HasPullback f g₁] [HasPullback f g₂] :
    (pullback.congrHom rfl h).hom ≫ pullback.fst f g₂ = pullback.fst f g₁ := by
  rw [pullback.congrHom_hom]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The forward comparison map `pullback.congrHom rfl h` induced by an equality of the second
leg, composed with the second projection, is the original second projection. -/
private theorem congrHom_hom_comp_snd {X Y Z : C} (f : X ⟶ Z) {g₁ g₂ : Y ⟶ Z} (h : g₁ = g₂)
    [HasPullback f g₁] [HasPullback f g₂] :
    (pullback.congrHom rfl h).hom ≫ pullback.snd f g₂ = pullback.snd f g₁ := by
  rw [pullback.congrHom_hom]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end PullbackCongrHom

section RelativeTateRing

variable (R : CommRingCat.{u}) {A : Type u} [CommRing A] [Algebra R A]

/-- The relative Tate-ring map attached to coefficients `(α, β)` over an `R`-algebra, provided
the corresponding Tate-normal discriminant is a unit.  Scheme-theoretically, `Spec` of this map is
the local map to the Tate atlas `tateBase R`.

This is the working `R`-relative analogue of `tateRing_homEquiv` (T-E2, the absolute ℤ-base
form of Loeffler Cor 3.3.5, in `Moduli/Representability.lean`) — the route the Y₁ tower uses. -/
noncomputable def TateAtlas.ringOverLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    tateRingOver R →+* A :=
  IsLocalization.Away.lift (tateCurveOver R).Δ
    (g := MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))
    (by simpa [WeierstrassCurve.map_Δ] using hΔ)

@[simp]
theorem TateAtlas.ringOverLift_X_zero (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    TateAtlas.ringOverLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α := by
  simp [TateAtlas.ringOverLift]

@[simp]
theorem TateAtlas.ringOverLift_X_one (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    TateAtlas.ringOverLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β := by
  simp [TateAtlas.ringOverLift]

/-- The relative Tate-ring lift bundled as an `R`-algebra map.  This is the form naturally
used by affine maps over `Spec R`. -/
noncomputable def TateAtlas.ringOverAlgLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    tateRingOver R →ₐ[R] A where
  toRingHom := TateAtlas.ringOverLift R α β hΔ
  commutes' r := by
    change TateAtlas.ringOverLift R α β hΔ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
      (MvPolynomial.C r)) = algebraMap R A r
    simp [TateAtlas.ringOverLift]

@[simp]
theorem TateAtlas.ringOverAlgLift_X_zero (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    TateAtlas.ringOverAlgLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α := by
  simp [TateAtlas.ringOverAlgLift]

@[simp]
theorem TateAtlas.ringOverAlgLift_X_one (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    TateAtlas.ringOverAlgLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β := by
  simp [TateAtlas.ringOverAlgLift]

/-- Two `R`-algebra maps out of the relative Tate atlas ring agree once they agree on the
two Tate coordinates.  This is the ring-level overlap uniqueness used by the scheme-level
gluing step for maps into `tateBase R`. -/
theorem TateAtlas.RingOver.algHom_ext (φ ψ : tateRingOver R →ₐ[R] A)
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
      ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)))
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
      ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1))) :
    φ = ψ := by
  apply AlgHom.ext
  intro x
  have hφψ : (φ : tateRingOver R →+* A) = (ψ : tateRingOver R →+* A) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (tateCurveOver R).Δ)
    apply MvPolynomial.ringHom_ext
    · intro r
      change φ (algebraMap R (tateRingOver R) r) = ψ (algebraMap R (tateRingOver R) r)
      rw [φ.commutes, ψ.commutes]
    · intro i
      fin_cases i
      · simpa using h0
      · simpa using h1
  exact RingHom.congr_fun hφψ x

/-- The relative Tate-ring lift is the unique `R`-algebra map with the prescribed Tate
coordinates.  This packages the affine uniqueness clause needed before gluing the local
`α, β` sections. -/
theorem TateAtlas.RingOver.algHom_eq_lift (φ : tateRingOver R →ₐ[R] A) (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β) :
    (φ : tateRingOver R →+* A) = TateAtlas.ringOverLift R α β hΔ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tateCurveOver R).Δ)
  apply MvPolynomial.ringHom_ext
  · intro r
    change φ (algebraMap R (tateRingOver R) r) =
      TateAtlas.ringOverLift R α β hΔ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
        (MvPolynomial.C r))
    rw [φ.commutes]
    simp [TateAtlas.ringOverLift]
  · intro i
    fin_cases i <;> simp [h0, h1, TateAtlas.ringOverLift]

/-- The algebra-map version of `TateAtlas.RingOver.algHom_eq_lift`. -/
theorem TateAtlas.RingOver.algHom_eq_algLift (φ : tateRingOver R →ₐ[R] A) (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β) :
    φ = TateAtlas.ringOverAlgLift R α β hΔ := by
  apply TateAtlas.RingOver.algHom_ext
  · simp [TateAtlas.ringOverAlgLift, h0]
  · simp [TateAtlas.ringOverAlgLift, h1]

/-- The affine scheme map to the relative Tate atlas induced by an `R`-algebra map out of
the atlas ring. -/
noncomputable def TateAtlas.baseSpecMap (φ : tateRingOver R →ₐ[R] A) :
    Spec (CommRingCat.of A) ⟶ tateBase R :=
  Spec.map (CommRingCat.ofHom (φ : tateRingOver R →+* A))

/-- The affine scheme map to `tateBase R` classified by the coefficients `(α, β)`. -/
noncomputable def TateAtlas.baseSpecMapOfCoeffs (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    Spec (CommRingCat.of A) ⟶ tateBase R :=
  TateAtlas.baseSpecMap R (TateAtlas.ringOverAlgLift R α β hΔ)

/-- Equality of affine maps into the Tate atlas is reduced to equality of the two Tate
coordinates.  This is the `Spec`-level handle consumed by the scheme gluing gate. -/
theorem TateAtlas.BaseSpecMap.ext (φ ψ : tateRingOver R →ₐ[R] A)
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
      ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)))
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
      ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1))) :
    TateAtlas.baseSpecMap R φ = TateAtlas.baseSpecMap R ψ := by
  rw [TateAtlas.RingOver.algHom_ext R φ ψ h0 h1]

/-- The affine map induced by an `R`-algebra map out of the Tate atlas ring lies over
`Spec R`. -/
theorem TateAtlas.BaseSpecMap.over (φ : tateRingOver R →ₐ[R] A) :
    TateAtlas.baseSpecMap R φ ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  unfold TateAtlas.baseSpecMap tateStructMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r ↦ φ.commutes r)

/-- The affine coefficient-classifying map to the Tate atlas lies over `Spec R`. -/
theorem TateAtlas.BaseSpecMap.OfCoeffs.over (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    TateAtlas.baseSpecMapOfCoeffs R α β hΔ ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  TateAtlas.BaseSpecMap.over R (TateAtlas.ringOverAlgLift R α β hΔ)

variable (S : Scheme.{u}) [Algebra R Γ(S, ⊤)]

/-- The global classifying map to the Tate atlas attached to global Tate coefficients
`α, β ∈ Γ(S, O_S)`.  This is the `S.toSpecΓ` form of the map produced after the local
coefficients glue in Loeffler's proof. -/
noncomputable def TateAtlas.baseMapOfGlobalCoeffs (α β : Γ(S, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    S ⟶ tateBase R :=
  S.toSpecΓ ≫ TateAtlas.baseSpecMapOfCoeffs R α β hΔ

/-- Global maps to the Tate atlas built from global coefficients are equal once the two
global Tate coefficients are equal.  This packages the last affine uniqueness check after
the sheaf-gluing step for `α` and `β`. -/
theorem TateAtlas.BaseMapOfGlobalCoeffs.ext (α β α' β' : Γ(S, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (hΔ' : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 ↦ if i = 0 then α' else β'))).Δ))
    (hα : α = α') (hβ : β = β') :
    TateAtlas.baseMapOfGlobalCoeffs R S α β hΔ =
      TateAtlas.baseMapOfGlobalCoeffs R S α' β' hΔ' := by
  unfold TateAtlas.baseMapOfGlobalCoeffs TateAtlas.baseSpecMapOfCoeffs
  rw [TateAtlas.BaseSpecMap.ext R (TateAtlas.ringOverAlgLift R α β hΔ)
    (TateAtlas.ringOverAlgLift R α' β' hΔ')]
  · simp [TateAtlas.ringOverAlgLift, hα]
  · simp [TateAtlas.ringOverAlgLift, hβ]

/-- The global coefficient map to the Tate atlas is compatible with the structure map to
`Spec R`. -/
theorem TateAtlas.BaseMapOfGlobalCoeffs.over (α β : Γ(S, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    TateAtlas.baseMapOfGlobalCoeffs R S α β hΔ ≫ tateStructMap R =
      S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(S, ⊤))) := by
  unfold TateAtlas.baseMapOfGlobalCoeffs
  rw [Category.assoc, TateAtlas.BaseSpecMap.OfCoeffs.over]

/-- The `R`-algebra on global functions induced by an object of `Ell/R`. -/
@[reducible]
noncomputable def EllObj.structAlgebra (Y : EllObj R) : Algebra R Γ(Y.base, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop).hom.toAlgebra

theorem EllObj.structAlgebra_algebraMap (Y : EllObj R) :
    letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
    algebraMap R Γ(Y.base, ⊤) =
      ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop).hom := by
  rfl

/-- If the global-functions `R`-algebra is the one induced by an object of `Ell/R`,
the corresponding `ΓSpec` structure map is exactly the object's structure morphism. -/
theorem EllObj.toSpecΓ_algebraMap (Y : EllObj R)
    [Algebra R Γ(Y.base, ⊤)]
    (halg : algebraMap R Γ(Y.base, ⊤) =
      ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop).hom) :
    Y.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y.base, ⊤))) =
      Y.structMap := by
  rw [halg]
  change Y.base.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop) =
    Y.structMap
  rw [Spec.map_comp]
  rw [← Category.assoc]
  rw [← Scheme.toSpecΓ_naturality Y.structMap]
  rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The global coefficient map gives the correct base component for an `Ell/R` morphism
when the global-functions algebra comes from the source object's structure map. -/
theorem TateAtlas.BaseMapOfGlobalCoeffs.base_w (Y : EllObj R)
    [Algebra R Γ(Y.base, ⊤)]
    (halg : algebraMap R Γ(Y.base, ⊤) =
      ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop).hom)
    (α β : Γ(Y.base, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom
      (algebraMap R Γ(Y.base, ⊤))
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    TateAtlas.baseMapOfGlobalCoeffs R Y.base α β hΔ ≫ tateStructMap R = Y.structMap := by
  rw [TateAtlas.BaseMapOfGlobalCoeffs.over]
  exact EllObj.toSpecΓ_algebraMap R Y halg

/-- The base map to the Tate atlas attached to global coefficients on an object over `Spec R`. -/
noncomputable def EllObj.TateAtlas.baseMapOfGlobalCoeffs (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    Y.base ⟶ tateBase R := by
  letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
  exact ModularCurves.TateAtlas.baseMapOfGlobalCoeffs R Y.base α β hΔ

@[simp]
theorem EllObj.TateAtlas.BaseMapOfGlobalCoeffs.base_w (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ ≫ tateStructMap R = Y.structMap := by
  letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
  exact ModularCurves.TateAtlas.BaseMapOfGlobalCoeffs.base_w R Y
    (EllObj.structAlgebra_algebraMap R Y) α β hΔ

theorem EllObj.TateAtlas.BaseMapOfGlobalCoeffs.ext (Y : EllObj R)
    (α β α' β' : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (hΔ' : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α' else β'))).Δ))
    (hα : α = α') (hβ : β = β') :
    EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ =
      EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α' β' hΔ' := by
  letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
  exact ModularCurves.TateAtlas.BaseMapOfGlobalCoeffs.ext R Y.base α β α' β' hΔ hΔ' hα hβ

/-- Glue local maps to the Tate atlas base along an open cover of an `Ell/R` object. -/
noncomputable def EllObj.TateAtlas.baseMapOfOpenCover (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j) :
    Y.base ⟶ tateBase R :=
  𝒰.glueMorphisms g hcompat

@[reassoc (attr := simp)]
theorem EllObj.TateAtlas.BaseMapOfOpenCover.ι (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (i : 𝒰.I₀) :
    𝒰.f i ≫ EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat = g i :=
  Scheme.Cover.ι_glueMorphisms 𝒰 g hcompat i

/-- If each local Tate-atlas base map lies over `Spec R`, then so does the glued map. -/
@[simp]
theorem EllObj.TateAtlas.BaseMapOfOpenCover.base_w (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap) :
    EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat ≫ tateStructMap R = Y.structMap := by
  apply Scheme.Cover.hom_ext 𝒰
  intro i
  rw [← Category.assoc, EllObj.TateAtlas.BaseMapOfOpenCover.ι, hover]

theorem EllObj.TateAtlas.BaseMapOfOpenCover.ext (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g g' : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hcompat' : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g' i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g' j)
    (hg : ∀ i : 𝒰.I₀, g i = g' i) :
    EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat =
      EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g' hcompat' := by
  apply Scheme.Cover.hom_ext 𝒰
  intro i
  rw [EllObj.TateAtlas.BaseMapOfOpenCover.ι, EllObj.TateAtlas.BaseMapOfOpenCover.ι, hg i]

/-- Build an `Ell/R` morphism into the Tate object from a base map to the Tate atlas and
the cartesian map from the source curve to the universal Tate curve. -/
noncomputable def EllObj.tateClassifyingHom (Y : EllObj R) (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero) :
    Y ⟶ tateEllObj R where
  baseHom := baseMap
  base_w := by
    simpa [tateEllObj] using base_w
  top := top
  isPullback := by
    simpa [tateEllObj] using isPullback
  zero_w := by
    simpa [tateEllObj] using zero_w

@[simp]
theorem EllObj.tateClassifyingHom.baseHom (Y : EllObj R) (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w).baseHom =
      baseMap :=
  rfl

@[simp]
theorem EllObj.tateClassifyingHom.top (Y : EllObj R) (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w).top = top :=
  rfl

theorem EllObj.tateClassifyingHom.ext (Y : EllObj R)
    (baseMap baseMap' : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (base_w' : baseMap' ≫ tateStructMap R = Y.structMap)
    (top top' : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero)
    (isPullback' : IsPullback top' Y.curve.π (tateUniversal R).π baseMap')
    (zero_w' : Y.curve.zero ≫ top' = baseMap' ≫ (tateUniversal R).zero)
    (hbase : baseMap = baseMap') (htop : top = top') :
    EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w =
      EllObj.tateClassifyingHom R Y baseMap' base_w' top' isPullback' zero_w' :=
  EllHom.ext hbase htop

/-- The classifying morphism into `tateEllObj` after the local Tate coefficients have
glued to global sections on the source base. -/
noncomputable def EllObj.tateClassifyingHom.ofGlobalCoeffs (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero) :
    Y ⟶ tateEllObj R :=
  EllObj.tateClassifyingHom R Y (EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ)
    (EllObj.TateAtlas.BaseMapOfGlobalCoeffs.base_w R Y α β hΔ) top isPullback zero_w

@[simp]
theorem EllObj.tateClassifyingHom.ofGlobalCoeffs.baseHom (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom.ofGlobalCoeffs R Y α β hΔ top isPullback zero_w).baseHom =
      EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ :=
  rfl

@[simp]
theorem EllObj.tateClassifyingHom.ofGlobalCoeffs.top (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom.ofGlobalCoeffs R Y α β hΔ top isPullback zero_w).top =
      top :=
  rfl

theorem EllObj.tateClassifyingHom.ofGlobalCoeffs.ext (Y : EllObj R)
    (α β α' β' : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ))
    (hΔ' : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 ↦ if i = 0 then α' else β'))).Δ))
    (top top' : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero)
    (isPullback' : IsPullback top' Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α' β' hΔ'))
    (zero_w' : Y.curve.zero ≫ top' =
      EllObj.TateAtlas.baseMapOfGlobalCoeffs R Y α' β' hΔ' ≫ (tateUniversal R).zero)
    (hα : α = α') (hβ : β = β') (htop : top = top') :
    EllObj.tateClassifyingHom.ofGlobalCoeffs R Y α β hΔ top isPullback zero_w =
      EllObj.tateClassifyingHom.ofGlobalCoeffs R Y α' β' hΔ' top' isPullback' zero_w' :=
  EllHom.ext (EllObj.TateAtlas.BaseMapOfGlobalCoeffs.ext R Y α β α' β' hΔ hΔ' hα hβ) htop

/-- The classifying morphism into `tateEllObj` from a Tate-base map glued over an open
cover of the source base. -/
noncomputable def EllObj.tateClassifyingHom.ofOpenCover (Y : EllObj R)
    (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero) :
    Y ⟶ tateEllObj R :=
  EllObj.tateClassifyingHom R Y (EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat)
    (EllObj.TateAtlas.BaseMapOfOpenCover.base_w R Y 𝒰 g hcompat hover) top isPullback zero_w

@[simp]
theorem EllObj.tateClassifyingHom.ofOpenCover.baseHom (Y : EllObj R)
    (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom.ofOpenCover R Y 𝒰 g hcompat hover top isPullback zero_w).baseHom =
      EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat :=
  rfl

@[simp]
theorem EllObj.tateClassifyingHom.ofOpenCover.top (Y : EllObj R)
    (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom.ofOpenCover R Y 𝒰 g hcompat hover top isPullback zero_w).top =
      top :=
  rfl

theorem EllObj.tateClassifyingHom.ofOpenCover.ext (Y : EllObj R)
    (𝒰 : Y.base.OpenCover)
    (g g' : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hcompat' : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g' i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g' j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (hover' : ∀ i : 𝒰.I₀, g' i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (top top' : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero)
    (isPullback' : IsPullback top' Y.curve.π (tateUniversal R).π
      (EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g' hcompat'))
    (zero_w' : Y.curve.zero ≫ top' =
      EllObj.TateAtlas.baseMapOfOpenCover R Y 𝒰 g' hcompat' ≫ (tateUniversal R).zero)
    (hg : ∀ i : 𝒰.I₀, g i = g' i) (htop : top = top') :
    EllObj.tateClassifyingHom.ofOpenCover R Y 𝒰 g hcompat hover top isPullback zero_w =
      EllObj.tateClassifyingHom.ofOpenCover R Y 𝒰 g' hcompat' hover' top' isPullback' zero_w' :=
  EllHom.ext (EllObj.TateAtlas.BaseMapOfOpenCover.ext R Y 𝒰 g g' hcompat hcompat' hg) htop

@[reassoc (attr := simp)]
theorem EllObj.tateClassifyingHom.pullSection_top (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero)
    (P₀ : (tateUniversal R).Section) :
    (EllHom.pullSection R
      (EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w) P₀).1 ≫ top =
        baseMap ≫ P₀.1 := by
  let f := EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w
  exact f.isPullback.lift_fst _ _ _

theorem EllObj.tateClassifyingHom.pullSection_eq (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero)
    (P₀ : (tateUniversal R).Section) (P : Y.curve.Section)
    (hP : P.1 ≫ top = baseMap ≫ P₀.1) :
    EllHom.pullSection R
      (EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w) P₀ = P := by
  let f := EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w
  refine Subtype.ext ?_
  refine f.isPullback.hom_ext ?_ ?_
  · have htop : (EllHom.pullSection R f P₀).1 ≫ f.top = f.baseHom ≫ P₀.1 :=
      f.isPullback.lift_fst _ _ _
    exact htop.trans (by simpa [f, tateEllObj] using hP.symm)
  · rw [(EllHom.pullSection R f P₀).2, P.2]

theorem EllObj.tateClassifyingHom.existsUnique_of_components (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero)
    (P₀ : (tateUniversal R).Section) (P : Y.curve.Section)
    (hP : P.1 ≫ top = baseMap ≫ P₀.1)
    (huniq : ∀ f : Y ⟶ tateEllObj R, EllHom.pullSection R f P₀ = P →
      f.baseHom = baseMap ∧ f.top = top) :
    ∃! f : Y ⟶ tateEllObj R, EllHom.pullSection R f P₀ = P := by
  let f₀ := EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w
  refine ⟨f₀, ?_, ?_⟩
  · exact EllObj.tateClassifyingHom.pullSection_eq R Y baseMap base_w top isPullback
      zero_w P₀ P hP
  · intro f hf
    rcases huniq f hf with ⟨hbase, htop⟩
    exact EllHom.ext hbase htop

/-- The Tate classifying morphism in the tautological pullback shape.  This is the
`QuotientProblem`/`pullbackAlong` reuse path flagged in v10.89. -/
noncomputable def EllObj.tateClassifyingHom.ofPullbackMap (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap) :
    Y ⟶ tateEllObj R :=
  v ≫ (tateEllObj R).pullbackAlongπ baseMap

@[simp]
theorem EllObj.tateClassifyingHom.ofPullbackMap.baseHom (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap) :
    (EllObj.tateClassifyingHom.ofPullbackMap R Y baseMap v).baseHom =
      v.baseHom ≫ baseMap :=
  rfl

theorem EllObj.tateClassifyingHom.ofPullbackMap.baseHom_of_base_id (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap)
    (hv : v.baseHom = 𝟙 Y.base) :
    (EllObj.tateClassifyingHom.ofPullbackMap R Y baseMap v).baseHom = baseMap := by
  rw [EllObj.tateClassifyingHom.ofPullbackMap.baseHom, hv]
  change 𝟙 Y.base ≫ baseMap = baseMap
  exact Category.id_comp baseMap

/-- Compare maps into the Tate pullback by projecting to `tateEllObj` and comparing
their base maps.  This is `EllObj.homPullbackAlongEquiv` specialised to the Tate object. -/
theorem EllObj.TatePullbackAlong.hom_ext (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v v' : Y ⟶ (tateEllObj R).pullbackAlong baseMap)
    (hproj : v ≫ (tateEllObj R).pullbackAlongπ baseMap =
      v' ≫ (tateEllObj R).pullbackAlongπ baseMap)
    (hbase : v.baseHom = v'.baseHom) :
    v = v' := by
  apply (EllObj.homPullbackAlongEquiv (tateEllObj R) baseMap Y).injective
  exact Subtype.ext (Prod.ext hproj hbase)

@[simp]
theorem EllObj.tateClassifyingHom.ofPullbackMap.toPullbackAlong {Y : EllObj R}
    (f : Y ⟶ tateEllObj R) :
    EllObj.tateClassifyingHom.ofPullbackMap R Y f.baseHom (EllObj.toPullbackAlong f) = f := by
  exact EllObj.toPullbackAlong_pullbackAlongπ f

theorem EllObj.tateClassifyingHom.ofPullbackMap.toPullbackAlong_comp_map {Y : EllObj R}
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap) :
    EllObj.toPullbackAlong (EllObj.tateClassifyingHom.ofPullbackMap R Y baseMap v) ≫
      (tateEllObj R).pullbackAlongMap baseMap v.baseHom = v :=
  EllObj.toPullbackAlong_pullbackAlongMap v

theorem EllObj.tateClassifyingHom.ofPullbackMap.pullSection {Y : EllObj R}
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap)
    (P₀ : (tateUniversal R).Section) :
    EllHom.pullSection R (EllObj.tateClassifyingHom.ofPullbackMap R Y baseMap v) P₀ =
      EllHom.pullSection R v
        (EllHom.pullSection R ((tateEllObj R).pullbackAlongπ baseMap) P₀) :=
  EllHom.pullSection_comp R v ((tateEllObj R).pullbackAlongπ baseMap) P₀

/-- Specialising the universal Tate curve by `TateAtlas.ringOverLift` recovers the Tate-normal curve
with coefficients `(α, β)`. -/
theorem TateAtlas.CurveLocOver.map_ringOverLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    (tateCurveLocOver R).map (TateAtlas.ringOverLift R α β hΔ) =
      (tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
        (fun i : Fin 2 ↦ if i = 0 then α else β)) := by
  simp [tateCurveLocOver, TateAtlas.ringOverLift, WeierstrassCurve.map_map]

/-- The algebra-map version of `TateAtlas.CurveLocOver.map_ringOverLift`. -/
theorem TateAtlas.CurveLocOver.map_ringOverAlgLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ)) :
    (tateCurveLocOver R).map (TateAtlas.ringOverAlgLift R α β hΔ) =
      (tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
        (fun i : Fin 2 ↦ if i = 0 then α else β)) :=
  TateAtlas.CurveLocOver.map_ringOverLift R α β hΔ

/-- A Tate-normal curve over an `R`-algebra is exactly the specialization of `tateCurveOver R`
at its coefficients `a₁` and `a₂`. -/
theorem TateAtlas.CurveOver.map_tateNormal_coeffs (W : WeierstrassCurve A)
    (hW : W.IsTateNormal) :
    (tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 ↦ if i = 0 then W.a₁ else W.a₂)) = W := by
  ext <;> simp [tateCurveOver, tateCurve, WeierstrassCurve.map, hW.1, hW.2.1, hW.2.2]

/-- The atlas-ring map attached to an elliptic Tate-normal Weierstrass curve. -/
noncomputable def TateAtlas.TateNormal.ringOverLift (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) : tateRingOver R →+* A :=
  TateAtlas.ringOverLift R W.a₁ W.a₂ (by
    rw [TateAtlas.CurveOver.map_tateNormal_coeffs R W hW]
    exact WeierstrassCurve.isUnit_Δ W)

/-- The atlas `R`-algebra map attached to an elliptic Tate-normal Weierstrass curve. -/
noncomputable def TateAtlas.TateNormal.ringOverAlgLift (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) : tateRingOver R →ₐ[R] A :=
  TateAtlas.ringOverAlgLift R W.a₁ W.a₂ (by
    rw [TateAtlas.CurveOver.map_tateNormal_coeffs R W hW]
    exact WeierstrassCurve.isUnit_Δ W)

@[simp]
theorem TateAtlas.TateNormal.ringOverLift_X_zero (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    TateAtlas.TateNormal.ringOverLift R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = W.a₁ := by
  simp [TateAtlas.TateNormal.ringOverLift]

@[simp]
theorem TateAtlas.TateNormal.ringOverLift_X_one (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    TateAtlas.TateNormal.ringOverLift R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = W.a₂ := by
  simp [TateAtlas.TateNormal.ringOverLift]

@[simp]
theorem TateAtlas.TateNormal.ringOverAlgLift_X_zero (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    TateAtlas.TateNormal.ringOverAlgLift R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = W.a₁ := by
  simp [TateAtlas.TateNormal.ringOverAlgLift]

@[simp]
theorem TateAtlas.TateNormal.ringOverAlgLift_X_one (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    TateAtlas.TateNormal.ringOverAlgLift R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = W.a₂ := by
  simp [TateAtlas.TateNormal.ringOverAlgLift]

/-- Specialising the universal Tate curve by the map attached to a Tate-normal curve recovers
that curve. -/
theorem TateAtlas.TateNormal.curveLocOver_map_ringOverLift (W : WeierstrassCurve A)
    [W.IsElliptic] (hW : W.IsTateNormal) :
    (tateCurveLocOver R).map (TateAtlas.TateNormal.ringOverLift R W hW) = W := by
  rw [tateCurveLocOver, WeierstrassCurve.map_map]
  change (tateCurveOver R).map
    ((TateAtlas.TateNormal.ringOverLift R W hW).comp
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R))) = W
  rw [show (TateAtlas.TateNormal.ringOverLift R W hW).comp
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)) =
        MvPolynomial.eval₂Hom (algebraMap R A)
          (fun i : Fin 2 ↦ if i = 0 then W.a₁ else W.a₂) by
    simp [TateAtlas.TateNormal.ringOverLift, TateAtlas.ringOverLift]]
  exact TateAtlas.CurveOver.map_tateNormal_coeffs R W hW

/-- The algebra-map version of `TateAtlas.TateNormal.curveLocOver_map_ringOverLift`. -/
theorem TateAtlas.TateNormal.curveLocOver_map_algLift (W : WeierstrassCurve A)
    [W.IsElliptic] (hW : W.IsTateNormal) :
    (tateCurveLocOver R).map (TateAtlas.TateNormal.ringOverAlgLift R W hW) = W := by
  unfold TateAtlas.TateNormal.ringOverAlgLift
  rw [TateAtlas.CurveLocOver.map_ringOverAlgLift]
  exact TateAtlas.CurveOver.map_tateNormal_coeffs R W hW

end RelativeTateRing

section LocalNormalisation

variable {A : Type u} [CommRing A]

/-- The T-E1 normalising variable change for a pointed affine chart of nowhere order `≤ 3`. -/
noncomputable def TateAtlas.TateNormal.variableChange (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    WeierstrassCurve.VariableChange A :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose

theorem TateAtlas.TateNormal.variableChange_isTateNormal (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W).IsTateNormal :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.left.1

@[simp]
theorem TateAtlas.TateNormal.variableChange_r (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    (TateAtlas.TateNormal.variableChange W x y hxy hord).r = x :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.left.2.1

@[simp]
theorem TateAtlas.TateNormal.variableChange_t (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    (TateAtlas.TateNormal.variableChange W x y hxy hord).t = y :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.left.2.2

theorem TateAtlas.TateNormal.variableChange_unique (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y) :
    C = TateAtlas.TateNormal.variableChange W x y hxy hord :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.right C hC

variable (R : CommRingCat.{u}) [Algebra R A]

/-- The local map to the Tate atlas produced from a Weierstrass chart and an affine point
of nowhere order `≤ 3`: first apply T-E1, then use the relative Tate-ring lift. -/
noncomputable def TateAtlas.Point.ringOverLift (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    tateRingOver R →+* A :=
  TateAtlas.TateNormal.ringOverLift R ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W)
    (TateAtlas.TateNormal.variableChange_isTateNormal W x y hxy hord)

/-- The local Tate atlas `R`-algebra map produced from a pointed Weierstrass chart. -/
noncomputable def TateAtlas.Point.ringOverAlgLift (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    tateRingOver R →ₐ[R] A :=
  TateAtlas.TateNormal.ringOverAlgLift R
    ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W)
    (TateAtlas.TateNormal.variableChange_isTateNormal W x y hxy hord)

@[simp]
theorem TateAtlas.Point.ringOverAlgLift_X_zero (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    TateAtlas.Point.ringOverAlgLift R W x y hxy hord
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
        ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W).a₁ := by
  simp [TateAtlas.Point.ringOverAlgLift]

@[simp]
theorem TateAtlas.Point.ringOverAlgLift_X_one (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    TateAtlas.Point.ringOverAlgLift R W x y hxy hord
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
        ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W).a₂ := by
  simp [TateAtlas.Point.ringOverAlgLift]

/-- The affine Tate-atlas map attached to a Tate-normal Weierstrass curve. -/
noncomputable def TateAtlas.TateNormal.baseSpecMap (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) : Spec (CommRingCat.of A) ⟶ tateBase R :=
  TateAtlas.baseSpecMap R (TateAtlas.TateNormal.ringOverAlgLift R W hW)

/-- The affine Tate-atlas map attached to a pointed Weierstrass chart after T-E1
normalisation. -/
noncomputable def TateAtlas.Point.baseSpecMap (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    Spec (CommRingCat.of A) ⟶ tateBase R :=
  TateAtlas.baseSpecMap R (TateAtlas.Point.ringOverAlgLift R W x y hxy hord)

/-- The Tate-normal affine chart map lies over `Spec R`. -/
theorem TateAtlas.TateNormal.baseSpecMap_tateStructMap (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    TateAtlas.TateNormal.baseSpecMap R W hW ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  TateAtlas.BaseSpecMap.over R (TateAtlas.TateNormal.ringOverAlgLift R W hW)

/-- The pointed affine chart map lies over `Spec R`. -/
theorem TateAtlas.Point.baseSpecMap_tateStructMap (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    TateAtlas.Point.baseSpecMap R W x y hxy hord ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  TateAtlas.BaseSpecMap.over R (TateAtlas.Point.ringOverAlgLift R W x y hxy hord)

/-- A map to the affine Tate atlas is the Tate-normal chart map once it has the same
Tate coefficients. -/
theorem TateAtlas.baseSpecMap_eq_tateNormal
    (φ : tateRingOver R →ₐ[R] A) (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal)
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
      W.a₁)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
      W.a₂) :
    TateAtlas.baseSpecMap R φ = TateAtlas.TateNormal.baseSpecMap R W hW := by
  unfold TateAtlas.TateNormal.baseSpecMap
  apply TateAtlas.BaseSpecMap.ext
  · simpa [TateAtlas.TateNormal.ringOverAlgLift] using h0
  · simpa [TateAtlas.TateNormal.ringOverAlgLift] using h1

/-- A map to the affine Tate atlas is the pointed chart map once it has the same
Tate-normalised coefficients. -/
theorem TateAtlas.baseSpecMap_eq_point
    (φ : tateRingOver R →ₐ[R] A) (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
      ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W).a₁)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
      ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W).a₂) :
    TateAtlas.baseSpecMap R φ = TateAtlas.Point.baseSpecMap R W x y hxy hord := by
  unfold TateAtlas.Point.baseSpecMap TateAtlas.Point.ringOverAlgLift
  exact TateAtlas.baseSpecMap_eq_tateNormal R φ
    ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W)
    (TateAtlas.TateNormal.variableChange_isTateNormal W x y hxy hord) h0 h1

/-- Any variable change that puts the same pointed chart in Tate normal form induces the
same atlas algebra map as the chosen T-E1 normalisation. -/
theorem TateAtlas.TateNormal.ringOverAlgLift.eq_point_of_variableChange
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y) :
    TateAtlas.TateNormal.ringOverAlgLift R (C • W) hC.1 =
      TateAtlas.Point.ringOverAlgLift R W x y hxy hord := by
  have hCeq := TateAtlas.TateNormal.variableChange_unique W x y hxy hord C hC
  apply TateAtlas.RingOver.algHom_ext
  · simp [TateAtlas.Point.ringOverAlgLift, hCeq]
  · simp [TateAtlas.Point.ringOverAlgLift, hCeq]

/-- Any variable change that puts the same pointed chart in Tate normal form induces the
same affine Tate-atlas map as the chosen T-E1 normalisation. -/
theorem TateAtlas.TateNormal.baseSpecMap.eq_point_of_variableChange
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y) :
    TateAtlas.TateNormal.baseSpecMap R (C • W) hC.1 =
      TateAtlas.Point.baseSpecMap R W x y hxy hord := by
  unfold TateAtlas.TateNormal.baseSpecMap TateAtlas.Point.baseSpecMap
  rw [TateAtlas.TateNormal.ringOverAlgLift.eq_point_of_variableChange R
    W x y hxy hord C hC]

/-- Any two normalising variable changes for the same pointed chart induce the same
Tate-atlas algebra map. -/
theorem TateAtlas.TateNormal.ringOverAlgLift.eq_of_variableChanges
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C C' : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y)
    (hC' : (C' • W).IsTateNormal ∧ C'.r = x ∧ C'.t = y) :
    TateAtlas.TateNormal.ringOverAlgLift R (C • W) hC.1 =
      TateAtlas.TateNormal.ringOverAlgLift R (C' • W) hC'.1 := by
  rw [TateAtlas.TateNormal.ringOverAlgLift.eq_point_of_variableChange R
    W x y hxy hord C hC]
  rw [TateAtlas.TateNormal.ringOverAlgLift.eq_point_of_variableChange R
    W x y hxy hord C' hC']

/-- Any two normalising variable changes for the same pointed chart induce the same
affine Tate-atlas map. -/
theorem TateAtlas.TateNormal.baseSpecMap.eq_of_variableChanges
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C C' : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y)
    (hC' : (C' • W).IsTateNormal ∧ C'.r = x ∧ C'.t = y) :
    TateAtlas.TateNormal.baseSpecMap R (C • W) hC.1 =
      TateAtlas.TateNormal.baseSpecMap R (C' • W) hC'.1 := by
  rw [TateAtlas.TateNormal.baseSpecMap.eq_point_of_variableChange R
    W x y hxy hord C hC]
  rw [TateAtlas.TateNormal.baseSpecMap.eq_point_of_variableChange R
    W x y hxy hord C' hC']

/-- The local atlas map classifies the T-E1 normal form of the pointed chart. -/
theorem TateAtlas.Point.curveLocOver_map_ringOverLift (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    (tateCurveLocOver R).map (TateAtlas.Point.ringOverLift R W x y hxy hord) =
      (TateAtlas.TateNormal.variableChange W x y hxy hord) • W :=
  TateAtlas.TateNormal.curveLocOver_map_ringOverLift R
    ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W)
    (TateAtlas.TateNormal.variableChange_isTateNormal W x y hxy hord)

/-- The algebra-map version of `TateAtlas.Point.curveLocOver_map_ringOverLift`. -/
theorem TateAtlas.Point.curveLocOver_map_algLift (W : WeierstrassCurve A)
    [W.IsElliptic] (x y : A) (hxy : W.toAffine.Equation x y)
    (hord : NowhereOrderLEThree W x y) :
    (tateCurveLocOver R).map (TateAtlas.Point.ringOverAlgLift R W x y hxy hord) =
      (TateAtlas.TateNormal.variableChange W x y hxy hord) • W :=
  TateAtlas.TateNormal.curveLocOver_map_algLift R
    ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W)
    (TateAtlas.TateNormal.variableChange_isTateNormal W x y hxy hord)

end LocalNormalisation

section PointedComparison

variable {A : Type u} [CommRing A]

/-- Atlas-local form of T-W7.1b: a pointed isomorphism of projective Weierstrass models is
induced by a variable change.  This is the comparison input for overlap agreement in the
scheme-level classifying clause. -/
theorem TateAtlas.Local.exists_variableChange (W W' : WeierstrassCurve A)
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ C : WeierstrassCurve.VariableChange A, ∃ hW : C • W' = W,
      e.hom = eqToHom (by rw [← hW]) ≫ (projModelVCIso C W').hom :=
  _root_.ModularCurves.pointedIso_exists_variableChange W W' e heπ hez

/-- Atlas-local form of T-W7 faithfulness: the variable-change action on projective models is
faithful once the induced pointed isomorphism is pinned. -/
theorem TateAtlas.Local.projModelVCIso_injective (C₁ C₂ : WeierstrassCurve.VariableChange A)
    (W : WeierstrassCurve A) (hW : C₁ • W = C₂ • W)
    (h : (projModelVCIso C₁ W).hom = eqToHom (by rw [hW]) ≫ (projModelVCIso C₂ W).hom) :
    C₁ = C₂ :=
  _root_.ModularCurves.projModelVCIso_injective C₁ C₂ W hW h

end PointedComparison

section OrderDictionary

/-! ### B2-ii ring core: the fibrewise-order ⟹ unit dictionary

Loeffler Prop 3.3.4's hypothesis *"`P, 2P, 3P ≠ 0` in any fibre"* (p. 13) enters T-E1
(`exists_unique_variableChange_isTateNormal`) as the unit condition `NowhereOrderLEThree`.
This section proves the bridge: over a field, vanishing of `ψ₂` at an affine point forces
`2P = 0`, and vanishing of `Ψ₃` forces `3P = 0` once `2P ≠ 0` — the converses of the vendored
`twiceNeZero_of_isUnit` / `thriceNeZero_of_isUnit` (`ForMathlib/TateNormalForm.lean`).  Hence a
point none of whose multiples `a • P` (`0 < a ≤ 3`) dies at any geometric point of `Spec A` has
its `ψ₂ψ₃`-value outside every maximal ideal of `A`, i.e. a unit. -/

variable {F : Type u} [Field F] [DecidableEq F]

/-- Over a field, vanishing of `ψ₂` at an affine point makes it `2`-torsion: `y = negY x y`,
so the point equals its own negative.  Converse of `Affine.Point.twiceNeZero_of_isUnit`. -/
lemma SmallOrder.two_zsmul_eq_zero_of_ψ₂ {W : WeierstrassCurve F} {x y : F}
    (hns : W.toAffine.Nonsingular x y) (h2 : W.ψ₂.evalEval x y = 0) :
    (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x y hns) = 0 := by
  have hy : y = W.toAffine.negY x y := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at h2
    rw [WeierstrassCurve.Affine.negY]
    linear_combination h2
  rw [two_zsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy

/-- Over a field, vanishing of the `3`-division polynomial at a non-`2`-torsion affine point
makes it `3`-torsion: the doubling formula gives `x(2P) = x`, so `2P = ±P`, and `2P = P` is
excluded.  Converse of `Affine.Point.thriceNeZero_of_isUnit`. -/
lemma SmallOrder.three_zsmul_eq_zero_of_Ψ₃ {W : WeierstrassCurve F} {x y : F}
    (hns : W.toAffine.Nonsingular x y) (hy2 : y ≠ W.toAffine.negY x y)
    (h3 : W.Ψ₃.eval x = 0) :
    (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y hns) = 0 := by
  haveI : (WeierstrassCurve.Affine.Point.some x y hns).NeZero :=
    ⟨WeierstrassCurve.Affine.Point.some_ne_zero hns⟩
  -- the `ThriceNeZero` quantity vanishes (project bridge `Ψ₃_eval_X`)
  have hkey := (WeierstrassCurve.Affine.Point.some x y hns).Ψ₃_eval_X
  simp only [WeierstrassCurve.Affine.Point.X_some, WeierstrassCurve.Affine.Point.Y_some,
    WeierstrassCurve.Affine.Point.pX, WeierstrassCurve.Affine.Point.pY, h3] at hkey
  -- the `pY`-value is nonzero
  have hd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero_of_ne hy2
  have hdval : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]; ring
  -- the doubling formula fixes the `x`-coordinate
  have hslope : W.toAffine.slope x x y y =
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy2, hdval]
  rw [hdval] at hd
  have hℓ : (2 * y + W.a₁ * x + W.a₃) * W.toAffine.slope x x y y
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hslope]
    field_simp
  have hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
    have hgoal : (2 * y + W.a₁ * x + W.a₃) ^ 2 *
        W.toAffine.addX x x (W.toAffine.slope x x y y)
        = (2 * y + W.a₁ * x + W.a₃) ^ 2 * x := by
      rw [WeierstrassCurve.Affine.addX]
      linear_combination ((2 * y + W.a₁ * x + W.a₃) * W.toAffine.slope x x y y
        + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
        + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hℓ + hkey
    exact mul_left_cancel₀ (pow_ne_zero 2 hd) hgoal
  -- `2P` in coordinates
  have hdup := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hns) hy2
  -- `x(2P) = x(P)` forces `2P = ±P`
  have hcases := WeierstrassCurve.Affine.Point.X_eq_iff
    (h₁ := WeierstrassCurve.Affine.nonsingular_add hns hns
      (fun hxy ↦ hy2 hxy.right)) (h₂ := hns) |>.mp hx2
  have h3P : (3 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns =
      (WeierstrassCurve.Affine.Point.some x y hns +
        WeierstrassCurve.Affine.Point.some x y hns) +
        WeierstrassCurve.Affine.Point.some x y hns := by
    rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, two_zsmul, one_zsmul]
  rw [h3P, hdup]
  rcases hcases with hPP | hPneg
  · -- `2P = P` forces `P = 0`, impossible for an affine point
    exfalso
    have h0 : WeierstrassCurve.Affine.Point.some x y hns = 0 := by
      have hcancel := hdup.trans hPP
      rwa [add_eq_left] at hcancel
    exact WeierstrassCurve.Affine.Point.some_ne_zero hns h0
  · rw [hPneg]
    exact neg_add_cancel _

variable {A : Type u} [CommRing A]

/-- Base change preserves the affine Weierstrass equation: the images of a solution `(x, y)`
of `W`'s equation over `A` solve the equation of the base-changed curve over any `A`-algebra. -/
private theorem toAffine_equation_baseChange (W : WeierstrassCurve A) (x y : A)
    (k : Type u) [CommRing k] [Algebra A k] (hxy : W.toAffine.Equation x y) :
    (W.baseChange k).toAffine.Equation (algebraMap A k x) (algebraMap A k y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hxy
  have hxy' := congrArg (algebraMap A k) hxy
  simp only [map_add, map_mul, map_pow] at hxy'
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    WeierstrassCurve.toAffine]
  linear_combination hxy'

/-- Base change commutes with evaluating the second division polynomial `ψ₂` at an affine
point: the value over the base change is the image of the value over `A`. -/
private theorem ψ₂_evalEval_baseChange (W : WeierstrassCurve A) (x y : A)
    (k : Type u) [CommRing k] [Algebra A k] :
    (W.baseChange k).ψ₂.evalEval (algebraMap A k x) (algebraMap A k y) =
      algebraMap A k ((W.Ψ 2).evalEval x y) := by
  rw [WeierstrassCurve.Ψ_two, WeierstrassCurve.ψ₂, WeierstrassCurve.ψ₂,
    WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.Affine.evalEval_polynomialY]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    WeierstrassCurve.toAffine, map_add, map_mul, map_ofNat]

/-- Base change commutes with evaluating the third division polynomial `Ψ₃` at an affine
point: the value over the base change is the image of the value over `A`. -/
private theorem Ψ₃_eval_baseChange (W : WeierstrassCurve A) (x y : A)
    (k : Type u) [CommRing k] [Algebra A k] :
    (W.baseChange k).Ψ₃.eval (algebraMap A k x) =
      algebraMap A k ((W.Ψ 3).evalEval x y) := by
  rw [WeierstrassCurve.Ψ_three, Polynomial.evalEval_C, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_Ψ₃, Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- **(B2-ii, the order ⟹ unit criterion)** If no multiple `a • P` (`0 < a ≤ 3`) of the affine
point `(x, y)` of the elliptic `W/A` vanishes at any geometric point of `Spec A`, then the
`ψ₂ψ₃`-value at `(x, y)` is a unit — i.e. `NowhereOrderLEThree W x y`, the input of T-E1.
A non-unit lies in a maximal ideal `m`; over `k := AlgebraicClosure (A ⧸ m)` the product of the
division-polynomial values vanishes, so `2 • P` or `3 • P` dies there by the two converses
above. -/
theorem NowhereOrderLEThree.of_forall_geom (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y)
    (h : ∀ (k : Type u) [Field k] [DecidableEq k] [IsAlgClosed k] [Algebra A k]
      (hns : (W.baseChange k).toAffine.Nonsingular (algebraMap A k x) (algebraMap A k y)),
      ∀ a : ℕ, 0 < a → a ≤ 3 →
        (a : ℤ) • (WeierstrassCurve.Affine.Point.some (algebraMap A k x)
          (algebraMap A k y) hns) ≠ 0) :
    NowhereOrderLEThree W x y := by
  classical
  rw [NowhereOrderLEThree]
  by_contra hunit
  obtain ⟨m, hmax, hm⟩ := Ideal.exists_le_maximal _ (mt Ideal.span_singleton_eq_top.mp hunit)
  haveI := hmax
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI k : Type u := AlgebraicClosure (A ⧸ m)
  letI : Algebra A k := ((algebraMap (A ⧸ m) k).comp (Ideal.Quotient.mk m)).toAlgebra
  have halg : (algebraMap A k) = (algebraMap (A ⧸ m) k).comp (Ideal.Quotient.mk m) := rfl
  -- the product of division-polynomial values dies in `k`
  have hv : algebraMap A k ((W.Ψ 2).evalEval x y * (W.Ψ 3).evalEval x y) = 0 := by
    rw [halg, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.span_le.mp hm (Set.mem_singleton _)), map_zero]
  -- fibre instances and the fibre point
  haveI : (W.baseChange k).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap A k)).IsElliptic)
  have hEk : (W.baseChange k).toAffine.Equation (algebraMap A k x) (algebraMap A k y) :=
    toAffine_equation_baseChange W x y k hxy
  have hns : (W.baseChange k).toAffine.Nonsingular (algebraMap A k x) (algebraMap A k y) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hEk
  -- the two division-polynomial values over `k`
  have hψ₂k : (W.baseChange k).ψ₂.evalEval (algebraMap A k x) (algebraMap A k y) =
      algebraMap A k ((W.Ψ 2).evalEval x y) := ψ₂_evalEval_baseChange W x y k
  have hΨ₃k : (W.baseChange k).Ψ₃.eval (algebraMap A k x) =
      algebraMap A k ((W.Ψ 3).evalEval x y) := Ψ₃_eval_baseChange W x y k
  -- the vanishing product splits
  have hprod : (W.baseChange k).ψ₂.evalEval (algebraMap A k x) (algebraMap A k y) *
      (W.baseChange k).Ψ₃.eval (algebraMap A k x) = 0 := by
    rw [hψ₂k, hΨ₃k, ← map_mul]
    exact hv
  rcases mul_eq_zero.mp hprod with h2 | h3
  · exact h k hns 2 two_pos (by norm_num)
      (by exact_mod_cast SmallOrder.two_zsmul_eq_zero_of_ψ₂ hns h2)
  · by_cases h2 : (W.baseChange k).ψ₂.evalEval (algebraMap A k x) (algebraMap A k y) = 0
    · exact h k hns 2 two_pos (by norm_num)
        (by exact_mod_cast SmallOrder.two_zsmul_eq_zero_of_ψ₂ hns h2)
    · have hy2 : algebraMap A k y ≠
          (W.baseChange k).toAffine.negY (algebraMap A k x) (algebraMap A k y) := by
        intro hy
        apply h2
        rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]
        rw [WeierstrassCurve.Affine.negY] at hy
        linear_combination hy
      exact h k hns 3 three_pos (by norm_num)
        (by exact_mod_cast SmallOrder.three_zsmul_eq_zero_of_Ψ₃ hns hy2 h3)

end OrderDictionary

section ZChartSection

/-! ### B2-i: fibrewise-nonzero points land in the `Z`-chart, with affine coordinates

Loeffler's affine-point extraction (Prop 3.3.4 proof, p. 13): a point of the projective model
that is not the point at infinity in any fibre factors through the `Z`-chart, where it is a
ring homomorphism out of the chart ring — equivalently, out of mathlib's affine coordinate
ring.  Its images of `coordX`/`coordY` are the affine coordinates, and they satisfy the
Weierstrass equation.  The chart-ring homomorphism is pinned by the factoring equation
`Spec.map (ZChart.hom) ≫ awayι = g`, from which all naturality statements follow by
faithfulness of `Spec`. -/

variable {A : Type u} [CommRing A] {K : Type u} [CommRing K] [Algebra A K]

/-- A field-valued point of `Spec K` composed with a `K`-point of the model is either in the
`Z`-chart or the zero point; if it is never the zero point, the whole `K`-point factors
through the `Z`-chart. -/
theorem ZChart.mem_of_forall_ne_zero (W : WeierstrassCurve A)
    (g : SpecPoints (projModel W) (projModelπ W) K)
    (h : ∀ (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K)),
      t ≫ g.1 ≠ (t ≫ Spec.map (CommRingCat.ofHom (algebraMap A K))) ≫ projModelZero W) :
    InZChart W g := by
  have hmem : ∀ p : Spec (CommRingCat.of K), g.1.base p ∈
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) := by
    intro p
    by_contra hp
    set t := (Spec (CommRingCat.of K)).fromSpecResidueField p with ht
    letI : Algebra A ((Spec (CommRingCat.of K)).residueField p) :=
      ((Spec.preimage (t ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)))).hom).toAlgebra
    have htA : Spec.map (CommRingCat.ofHom
        (algebraMap A ((Spec (CommRingCat.of K)).residueField p))) =
        t ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) := by
      show Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hgk : (t ≫ g.1) ≫ projModelπ W = Spec.map (CommRingCat.ofHom
        (algebraMap A ((Spec (CommRingCat.of K)).residueField p))) := by
      rw [Category.assoc, g.2, htA]
    have hnotin : ¬ InZChart W
        (⟨t ≫ g.1, hgk⟩ : SpecPoints (projModel W) (projModelπ W)
          ((Spec (CommRingCat.of K)).residueField p)) := by
      rintro ⟨h', hfac⟩
      apply hp
      have himg : g.1.base p = (Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).base (h'.base default) := by
        have hc := congrArg (fun m ↦ m.base default) hfac
        simp only [ht, Scheme.Hom.comp_apply] at hc
        have hpt : ((Spec (CommRingCat.of K)).fromSpecResidueField p).base default = p :=
          Scheme.fromSpecResidueField_apply p default
        exact (congrArg (fun q ↦ g.1.base q) hpt).symm.trans hc.symm
      rw [himg]
      have h2 : (Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).base (h'.base default) ∈
          (Proj.awayι (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
            (mk_X_mem_quotientGrading_one W 2) one_pos).opensRange :=
        Scheme.Hom.mem_opensRange.mpr ⟨h'.base default, rfl⟩
      rwa [Proj.opensRange_awayι] at h2
    have hzero : t ≫ g.1 = Spec.map (CommRingCat.ofHom
        (algebraMap A ((Spec (CommRingCat.of K)).residueField p))) ≫ projModelZero W :=
      specPoint_eq_zero_of_not_inZ W _ _ hnotin
    apply h ((Spec (CommRingCat.of K)).residueField p) t
    calc t ≫ g.1 = Spec.map (CommRingCat.ofHom
          (algebraMap A ((Spec (CommRingCat.of K)).residueField p))) ≫ projModelZero W :=
        hzero
      _ = (t ≫ Spec.map (CommRingCat.ofHom (algebraMap A K))) ≫ projModelZero W := by
        rw [htA]
  refine ⟨IsOpenImmersion.lift (Proj.awayι (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
    (mk_X_mem_quotientGrading_one W 2) one_pos) g.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  have := hmem p
  rw [← Proj.opensRange_awayι _ _ (mk_X_mem_quotientGrading_one W 2) one_pos] at this
  obtain ⟨q, hq⟩ := Scheme.Hom.mem_opensRange.mp this
  exact ⟨q, hq⟩

variable (W : WeierstrassCurve A)

/-- The chart-ring homomorphism attached to a `Z`-chart `K`-point of the model. -/
noncomputable def ZChart.hom (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* K :=
  (chartHomEquiv W 2 K ⟨g, hZ⟩).1

/-- The chart-ring homomorphism is `A`-compatible. -/
theorem ZChart.hom_compat (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    (ZChart.hom W g hZ).comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (HomogeneousLocalization.Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
      ((gradeZeroRingEquiv W) : A →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap A K :=
  (chartHomEquiv W 2 K ⟨g, hZ⟩).2

/-- **The factoring equation**: `Spec` of the chart-ring homomorphism, composed with the
chart inclusion, is the original point.  Everything else about `ZChart.hom` follows from this
by faithfulness of `Spec` and monicity of the chart inclusion. -/
theorem ZChart.spec_map_hom_awayι (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    Spec.map (CommRingCat.ofHom (ZChart.hom W g hZ)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 := by
  show _ = (⟨g, hZ⟩ : { g : SpecPoints (projModel W) (projModelπ W) K // InZChart W g }).1.1
  exact congrArg (fun z ↦ z.1.1) ((chartHomEquiv W 2 K).symm_apply_apply ⟨g, hZ⟩)

/-- The chart-ring homomorphism is the unique one satisfying the factoring equation. -/
theorem ZChart.hom_unique (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g)
    (χ : HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* K)
    (hχ : Spec.map (CommRingCat.ofHom χ) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos = g.1) :
    χ = ZChart.hom W g hZ := by
  have hmono := hχ.trans (ZChart.spec_map_hom_awayι W g hZ).symm
  rw [cancel_mono] at hmono
  have := Spec.map_injective hmono
  exact congrArg CommRingCat.Hom.hom this

/-- The evaluation homomorphism out of the affine coordinate ring attached to a `Z`-chart
point: `coordX ↦ x`, `coordY ↦ y`. -/
noncomputable def ZChart.eval (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) : W.toAffine.CoordinateRing →+* K :=
  (ZChart.hom W g hZ).comp ((chartZRingEquiv W).symm :
    W.toAffine.CoordinateRing →+* HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))

/-- The evaluation homomorphism is `A`-algebra compatible. -/
theorem ZChart.eval_algebraMap (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (r : A) :
    ZChart.eval W g hZ (algebraMap A W.toAffine.CoordinateRing r) = algebraMap A K r := by
  have h1 : (chartZRingEquiv W).symm (algebraMap A W.toAffine.CoordinateRing r) =
      (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
        (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r) := by
    rw [← chartZRingEquiv_fromZero W r, RingEquiv.symm_apply_apply]
  show (ZChart.hom W g hZ) ((chartZRingEquiv W).symm
    (algebraMap A W.toAffine.CoordinateRing r)) = algebraMap A K r
  rw [h1]
  exact RingHom.congr_fun (ZChart.hom_compat W g hZ) r

/-- The coordinates extracted from a `Z`-chart point satisfy the Weierstrass equation of the
base-changed curve. -/
theorem ZChart.eval_equation (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    (W.baseChange K).toAffine.Equation
      (ZChart.eval W g hZ (coordX W)) (ZChart.eval W g hZ (coordY W)) := by
  have hker : ZChart.eval W g hZ
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine W.toAffine.polynomial) = 0 := by
    rw [show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine W.toAffine.polynomial =
      0 from AdjoinRoot.mk_self, map_zero]
  have hofC : ∀ a : A, ZChart.eval W g hZ
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C (Polynomial.C a)))
      = algebraMap A K a := by
    intro a
    rw [show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C (Polynomial.C a)) =
        algebraMap A W.toAffine.CoordinateRing a by
      rw [show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
          (Polynomial.C (Polynomial.C a)) =
          AdjoinRoot.of W.toAffine.polynomial (Polynomial.C a) from rfl,
        ← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]]
    exact ZChart.eval_algebraMap W g hZ a
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    WeierstrassCurve.toAffine]
  have hexp : ZChart.eval W g hZ (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      W.toAffine.polynomial) =
      ZChart.eval W g hZ (coordY W) ^ 2
        + algebraMap A K W.a₁ * ZChart.eval W g hZ (coordX W) * ZChart.eval W g hZ (coordY W)
        + algebraMap A K W.a₃ * ZChart.eval W g hZ (coordY W)
        - (ZChart.eval W g hZ (coordX W) ^ 3
          + algebraMap A K W.a₂ * ZChart.eval W g hZ (coordX W) ^ 2
          + algebraMap A K W.a₄ * ZChart.eval W g hZ (coordX W)
          + algebraMap A K W.a₆) := by
    simp only [WeierstrassCurve.Affine.polynomial, map_add, map_sub, map_mul, map_pow]
    rw [show (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine) Polynomial.X =
      coordY W from rfl]
    rw [show (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine) (Polynomial.C Polynomial.X)
      = coordX W from rfl]
    simp only [hofC]
    ring
  rw [hker] at hexp
  linear_combination -hexp

/-- The coordinates satisfy the Weierstrass equation of `W` itself when the point lives over
the base ring (`W.baseChange A = W` up to definitional unfolding; this restatement keeps every
downstream `Equation`-proof slot properly typed). -/
theorem ZChart.eval_equation_self {A' : Type u} [CommRing A'] (W' : WeierstrassCurve A')
    (g : SpecPoints (projModel W') (projModelπ W') A') (hZ : InZChart W' g) :
    W'.toAffine.Equation
      (ZChart.eval W' g hZ (coordX W')) (ZChart.eval W' g hZ (coordY W')) :=
  ZChart.eval_equation W' g hZ

end ZChartSection

section MarkedChartComparison

/-! ### B2-iii/iv engine (base): two marked charts induce the same atlas map

Loeffler's *"Since `αᵢ, βᵢ` are unique, they must agree on `Uᵢ ∩ Uⱼ`"* (Prop 3.3.4,
p. 14).  A pointed isomorphism of projective models carrying one `Z`-chart point to another
is a variable change (T-W7); composing with the T-E1 normalising change of the source and
comparing with T-E1 **uniqueness** on the target forces the two Tate normal forms — hence
the two atlas algebra maps — to coincide. -/

variable {A : Type u} [CommRing A]

set_option backward.isDefEq.respectTransparency false in
/-- The `Z`-chart ring morphism (in `CommRingCat`) induced by a pointed isomorphism of
projective models: `pointedIsoΓ` conjugated by the two `basicOpenIsoAway`
identifications. -/
noncomputable def pointedIsoAwayHom {W₁ W₂ : WeierstrassCurve A}
    (ε : projModel W₁ ≅ projModel W₂)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂) :
    CommRingCat.of (HomogeneousLocalization.Away (quotientGrading (projIdeal W₂))
      ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))) ⟶
    CommRingCat.of (HomogeneousLocalization.Away (quotientGrading (projIdeal W₁))
      ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))) :=
  (Proj.basicOpenIsoAway (quotientGrading (projIdeal W₂))
      ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W₂ 2) one_pos).hom ≫
    CommRingCat.ofHom (pointedIsoΓ ε hez).toRingHom ≫
    (Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
      ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W₁ 2) one_pos).inv

/-- **The chart square of a pointed isomorphism**: `Spec` of the induced chart-ring morphism
intertwines the two chart inclusions with `ε`. -/
theorem ZChart.PointedIso.spec_map_awayι {W₁ W₂ : WeierstrassCurve A}
    (ε : projModel W₁ ≅ projModel W₂)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂) :
    Spec.map (pointedIsoAwayHom ε hez) ≫
      Proj.awayι (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos =
    Proj.awayι (quotientGrading (projIdeal W₁))
      ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W₁ 2) one_pos ≫ ε.hom := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec ε.hom
    (Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W₂ 2) one_pos)
    (Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W₁ 2) one_pos)
    (pointedIso_preimage_zChart ε hez).ge
  rw [appLE_zChart_eq_pointedIsoΓ ε hez,
    Proj_fromSpec_awayToSection_awayι (quotientGrading (projIdeal W₂))
      ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W₂ 2) one_pos,
    Proj_fromSpec_awayToSection_awayι (quotientGrading (projIdeal W₁))
      ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W₁ 2) one_pos] at h1
  have hats : ∀ (W : WeierstrassCurve A), Proj.awayToSection (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
      (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).hom := fun _ ↦ rfl
  rw [hats, hats] at h1
  -- re-ascribe `h1` so every proof argument is spelled as in the goal
  set_option backward.isDefEq.respectTransparency false in
  have h2 : Spec.map (CommRingCat.ofHom (pointedIsoΓ ε hez).toRingHom) ≫
      Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos).hom) ≫
      Proj.awayι (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos =
      (Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos).hom) ≫
      Proj.awayι (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos) ≫ ε.hom := h1
  set_option backward.isDefEq.respectTransparency false in
  have hexp : Spec.map (pointedIsoAwayHom ε hez) =
      Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos).inv) ≫
      Spec.map (CommRingCat.ofHom (pointedIsoΓ ε hez).toRingHom) ≫
      Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos).hom) := by
    show Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos).hom ≫
      CommRingCat.ofHom (pointedIsoΓ ε hez).toRingHom ≫
      (Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos).inv) = _
    rw [Spec.map_comp, Spec.map_comp, Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  rw [hexp, Category.assoc, Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  have h3 := congrArg (fun m ↦ Spec.map ((Proj.basicOpenIsoAway
    (quotientGrading (projIdeal W₁)) ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
    (mk_X_mem_quotientGrading_one W₁ 2) one_pos).inv) ≫ m) h2
  set_option backward.isDefEq.respectTransparency false in
  have h4 : Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
      ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W₁ 2) one_pos).inv) ≫
      ((Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos).hom) ≫
      Proj.awayι (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos) ≫ ε.hom) =
      Proj.awayι (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos ≫ ε.hom := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  set_option backward.isDefEq.respectTransparency false in
  exact h3.trans h4

variable {K : Type u} [CommRing K] [Algebra A K]

set_option backward.isDefEq.respectTransparency false in
/-- Transport of the chart evaluation along a pointed isomorphism of models carrying one
`Z`-chart point to another: evaluation on the target is evaluation on the source after the
induced coordinate-ring isomorphism. -/
theorem ZChart.eval_pointedIso {W₁ W₂ : WeierstrassCurve A}
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) K)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) K)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1) (a : W₂.toAffine.CoordinateRing) :
    ZChart.eval W₂ g₂ hZ₂ a =
      ZChart.eval W₁ g₁ hZ₁ (pointedIsoCoordEquiv ε heπ hez a) := by
  have hχmor : Spec.map (pointedIsoAwayHom ε hez ≫
      CommRingCat.ofHom (ZChart.hom W₁ g₁ hZ₁)) ≫
      Proj.awayι (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos = g₂.1 := by
    rw [Spec.map_comp, Category.assoc, ZChart.PointedIso.spec_map_awayι ε hez,
      ← Category.assoc, ZChart.spec_map_hom_awayι, hsec]
  have hhom := (ZChart.hom_unique W₂ g₂ hZ₂
    ((pointedIsoAwayHom ε hez ≫ CommRingCat.ofHom (ZChart.hom W₁ g₁ hZ₁)).hom)
    (by rw [CommRingCat.ofHom_hom]; exact hχmor)).symm
  show ZChart.hom W₂ g₂ hZ₂ ((chartZRingEquiv W₂).symm a) = _
  rw [hhom]
  show ZChart.hom W₁ g₁ hZ₁ ((pointedIsoAwayHom ε hez).hom ((chartZRingEquiv W₂).symm a)) =
    ZChart.hom W₁ g₁ hZ₁ ((chartZRingEquiv W₁).symm (pointedIsoCoordEquiv ε heπ hez a))
  congr 1
  have hsec' := pointedIsoCoordEquiv_sections ε heπ hez a
  simp only [chartZSectionsRingEquiv, RingEquiv.symm_trans_apply, RingEquiv.symm_symm]
    at hsec'
  have hkey := congrArg ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
      ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W₁ 2) one_pos).commRingCatIsoToRingEquiv).symm hsec'
  rw [RingEquiv.symm_apply_apply] at hkey
  have happ : ∀ z, (pointedIsoAwayHom ε hez).hom z =
      ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₁))
        ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₁ 2) one_pos).commRingCatIsoToRingEquiv).symm
      (pointedIsoΓ ε hez ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos).commRingCatIsoToRingEquiv z)) :=
    fun _ ↦ rfl
  exact (happ _).trans hkey.symm

/-- **(ENGINE core: the composite normalising change)** If the marked coordinates of two
elliptic marked charts are related by the variable-change transform `C` and `C • W₂ = W₁`,
then the composite of `W₁`'s T-E1 normalisation with `C` **is** `W₂`'s normalisation, by
T-E1 uniqueness. -/
theorem TateAtlas.TateNormal.variableChange_mul (W₁ W₂ : WeierstrassCurve A)
    [W₁.IsElliptic] [W₂.IsElliptic]
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hord₁ : NowhereOrderLEThree W₁
      (ZChart.eval W₁ g₁ hZ₁ (coordX W₁)) (ZChart.eval W₁ g₁ hZ₁ (coordY W₁)))
    (hord₂ : NowhereOrderLEThree W₂
      (ZChart.eval W₂ g₂ hZ₂ (coordX W₂)) (ZChart.eval W₂ g₂ hZ₂ (coordY W₂)))
    (C : WeierstrassCurve.VariableChange A) (hC : C • W₂ = W₁)
    (hx : ZChart.eval W₂ g₂ hZ₂ (coordX W₂) =
      (C.u : A) ^ 2 * ZChart.eval W₁ g₁ hZ₁ (coordX W₁) + C.r)
    (hy : ZChart.eval W₂ g₂ hZ₂ (coordY W₂) =
      (C.u : A) ^ 3 * ZChart.eval W₁ g₁ hZ₁ (coordY W₁) +
        C.s * (C.u : A) ^ 2 * ZChart.eval W₁ g₁ hZ₁ (coordX W₁) + C.t) :
    TateAtlas.TateNormal.variableChange W₁ _ _ (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ * C =
      TateAtlas.TateNormal.variableChange W₂ _ _ (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ := by
  have hD :
      (TateAtlas.TateNormal.variableChange W₁ _ _
          (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ * C) • W₂ =
        (TateAtlas.TateNormal.variableChange W₁ _ _
          (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁) • W₁ := by
    rw [mul_smul, hC]
  refine TateAtlas.TateNormal.variableChange_unique W₂ _ _
    (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ _ ⟨?_, ?_, ?_⟩
  · rw [hD]
    exact TateAtlas.TateNormal.variableChange_isTateNormal W₁ _ _
      (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁
  · show (TateAtlas.TateNormal.variableChange W₁ _ _
        (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁).r * (C.u : A) ^ 2 + C.r = _
    rw [TateAtlas.TateNormal.variableChange_r, hx]
    ring
  · show (TateAtlas.TateNormal.variableChange W₁ _ _
        (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁).t * (C.u : A) ^ 3 +
      (TateAtlas.TateNormal.variableChange W₁ _ _
        (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁).r * C.s * (C.u : A) ^ 2 + C.t = _
    rw [TateAtlas.TateNormal.variableChange_t, TateAtlas.TateNormal.variableChange_r, hy]
    ring

/-- The coordinate transform of a marked pointed isomorphism, in the components of its
T-W7 variable change. -/
theorem ZChart.eval_coords_of_pointedIso (W₁ W₂ : WeierstrassCurve A)
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1)
    (C : WeierstrassCurve.VariableChange A) (hC : C • W₂ = W₁)
    (hεhom : ε.hom = eqToHom (by rw [← hC]) ≫ (projModelVCIso C W₂).hom) :
    ZChart.eval W₂ g₂ hZ₂ (coordX W₂) =
      (C.u : A) ^ 2 * ZChart.eval W₁ g₁ hZ₁ (coordX W₁) + C.r ∧
    ZChart.eval W₂ g₂ hZ₂ (coordY W₂) =
      (C.u : A) ^ 3 * ZChart.eval W₁ g₁ hZ₁ (coordY W₁) +
        C.s * (C.u : A) ^ 2 * ZChart.eval W₁ g₁ hZ₁ (coordX W₁) + C.t := by
  constructor
  · have h := ZChart.eval_pointedIso ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec (coordX W₂)
    rw [transport_general hC.symm ε (projModelVCIso C W₂) heπ hez (projModelVCIso_π C W₂)
      (projModelVCIso_zero C W₂) hεhom (coordX W₂), bridge_coordX] at h
    simp only [map_add, coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap] at h
    rw [h]
    simp only [map_mul, ZChart.eval_algebraMap, Algebra.algebraMap_self_apply]
  · have h := ZChart.eval_pointedIso ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec (coordY W₂)
    rw [transport_general hC.symm ε (projModelVCIso C W₂) heπ hez (projModelVCIso_π C W₂)
      (projModelVCIso_zero C W₂) hεhom (coordY W₂), bridge_coordY] at h
    simp only [map_add, coordRingCongr_algebraMap_mul_coordY,
      coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap] at h
    rw [h]
    simp only [map_mul, ZChart.eval_algebraMap, Algebra.algebraMap_self_apply]

/-- **(ENGINE, base half — Loeffler's overlap uniqueness)** Two elliptic marked `Z`-chart
data over the same ring, linked by a pointed isomorphism of the models carrying the first
marking to the second, induce the **same** Tate-atlas algebra map: the T-W7 variable change
composed with the source's T-E1 normalisation is a normalisation of the target, so T-E1
uniqueness forces the two Tate normal forms to agree. -/
theorem TateAtlas.Point.ringOverAlgLift.eq_of_pointedIso (R : CommRingCat.{u}) [Algebra R A]
    (W₁ W₂ : WeierstrassCurve A) [W₁.IsElliptic] [W₂.IsElliptic]
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1)
    (hord₁ : NowhereOrderLEThree W₁
      (ZChart.eval W₁ g₁ hZ₁ (coordX W₁)) (ZChart.eval W₁ g₁ hZ₁ (coordY W₁)))
    (hord₂ : NowhereOrderLEThree W₂
      (ZChart.eval W₂ g₂ hZ₂ (coordX W₂)) (ZChart.eval W₂ g₂ hZ₂ (coordY W₂))) :
    TateAtlas.Point.ringOverAlgLift R W₁ _ _
        (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ =
      TateAtlas.Point.ringOverAlgLift R W₂ _ _
        (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ := by
  obtain ⟨C, hC, hεhom⟩ := pointedIso_exists_variableChange W₁ W₂ ε heπ hez
  obtain ⟨hx, hy⟩ := ZChart.eval_coords_of_pointedIso W₁ W₂ ε heπ hez g₁ g₂
    hZ₁ hZ₂ hsec C hC hεhom
  have hDC₂ := TateAtlas.TateNormal.variableChange_mul W₁ W₂ g₁ g₂ hZ₁ hZ₂
    hord₁ hord₂ C hC hx hy
  have hcurves :
      (TateAtlas.TateNormal.variableChange W₂ _ _
        (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂) • W₂ =
      (TateAtlas.TateNormal.variableChange W₁ _ _
        (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁) • W₁ := by
    rw [← hDC₂, mul_smul, hC]
  -- the two atlas algebra maps agree on the coordinates
  apply TateAtlas.RingOver.algHom_ext
  · rw [TateAtlas.Point.ringOverAlgLift_X_zero, TateAtlas.Point.ringOverAlgLift_X_zero]
    exact (congrArg WeierstrassCurve.a₁ hcurves).symm
  · rw [TateAtlas.Point.ringOverAlgLift_X_one, TateAtlas.Point.ringOverAlgLift_X_one]
    exact (congrArg WeierstrassCurve.a₂ hcurves).symm

/-- The affine `Spec`-level form of the engine: the two pointed charts induce the same
affine map to the Tate atlas. -/
theorem TateAtlas.Point.baseSpecMap.eq_of_pointedIso (R : CommRingCat.{u}) [Algebra R A]
    (W₁ W₂ : WeierstrassCurve A) [W₁.IsElliptic] [W₂.IsElliptic]
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1)
    (hord₁ : NowhereOrderLEThree W₁
      (ZChart.eval W₁ g₁ hZ₁ (coordX W₁)) (ZChart.eval W₁ g₁ hZ₁ (coordY W₁)))
    (hord₂ : NowhereOrderLEThree W₂
      (ZChart.eval W₂ g₂ hZ₂ (coordX W₂)) (ZChart.eval W₂ g₂ hZ₂ (coordY W₂))) :
    TateAtlas.Point.baseSpecMap R W₁ _ _
        (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ =
      TateAtlas.Point.baseSpecMap R W₂ _ _
        (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ := by
  unfold TateAtlas.Point.baseSpecMap
  rw [show TateAtlas.Point.ringOverAlgLift R W₁ _ _
      (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ =
    TateAtlas.Point.ringOverAlgLift R W₂ _ _
      (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ from
    TateAtlas.Point.ringOverAlgLift.eq_of_pointedIso R W₁ W₂ ε heπ hez g₁ g₂
      hZ₁ hZ₂ hsec hord₁ hord₂]

end MarkedChartComparison

section ZChartNaturality

/-! ### `Z`-chart points: ring-map naturality, extensionality, and the atlas marking

The remaining B2 apparatus on chart points: composing with `Spec` of a ring map preserves the
`Z`-chart and transforms the evaluation by composition; a `Z`-chart point is determined by its
two coordinate evaluations (`{1, y}` is a basis of the coordinate ring over `R[x]`); and the
atlas marked point `(0,0)` is a `Z`-chart point with both coordinates `0`. -/

variable {A : Type u} [CommRing A] (W : WeierstrassCurve A)
  {K K' : Type u} [CommRing K] [CommRing K'] [Algebra A K] [Algebra A K']

/-- Compose a `K`-point with `Spec` of an `A`-compatible ring map `K →+* K'`. -/
noncomputable def specPointComp (g : SpecPoints (projModel W) (projModelπ W) K)
    (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K') :
    SpecPoints (projModel W) (projModelπ W) K' :=
  ⟨Spec.map (CommRingCat.ofHom ψ) ≫ g.1, by
    rw [Category.assoc, g.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]⟩

/-- Composition with a ring map preserves the `Z`-chart. -/
theorem ZChart.mem_specPointComp (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K') :
    InZChart W (specPointComp W g ψ hψ) := by
  obtain ⟨h, hfac⟩ := hZ
  exact ⟨Spec.map (CommRingCat.ofHom ψ) ≫ h, by rw [Category.assoc, hfac]; rfl⟩

/-- The chart-ring homomorphism of a composed point is the composition. -/
theorem ZChart.hom_specPointComp (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K') :
    ZChart.hom W (specPointComp W g ψ hψ) (ZChart.mem_specPointComp W g hZ ψ hψ) =
      ψ.comp (ZChart.hom W g hZ) := by
  refine (ZChart.hom_unique W _ _ _ ?_).symm
  rw [show CommRingCat.ofHom (ψ.comp (ZChart.hom W g hZ)) =
    CommRingCat.ofHom (ZChart.hom W g hZ) ≫ CommRingCat.ofHom ψ from
    (CommRingCat.ofHom_comp _ _), Spec.map_comp, Category.assoc,
    ZChart.spec_map_hom_awayι W g hZ]
  rfl

/-- The coordinate evaluation of a composed point is the composed evaluation. -/
theorem ZChart.eval_specPointComp (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K')
    (a : W.toAffine.CoordinateRing) :
    ZChart.eval W (specPointComp W g ψ hψ) (ZChart.mem_specPointComp W g hZ ψ hψ) a =
      ψ (ZChart.eval W g hZ a) := by
  show ZChart.hom W (specPointComp W g ψ hψ) (ZChart.mem_specPointComp W g hZ ψ hψ)
    ((chartZRingEquiv W).symm a) = _
  rw [ZChart.hom_specPointComp W g hZ ψ hψ]
  rfl

/-- The `x`-coordinate evaluation is the chart-ring homomorphism at `X₀/X₂`. -/
theorem ZChart.eval_coordX (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    ZChart.eval W g hZ (coordX W) =
      ZChart.hom W g hZ (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)) := by
  show ZChart.hom W g hZ ((chartZRingEquiv W).symm (coordX W)) = _
  congr 1
  rw [RingEquiv.symm_apply_eq]
  exact (chartZRingEquiv_x W).symm

/-- The `y`-coordinate evaluation is the chart-ring homomorphism at `X₁/X₂`. -/
theorem ZChart.eval_coordY (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    ZChart.eval W g hZ (coordY W) =
      ZChart.hom W g hZ (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)) := by
  show ZChart.hom W g hZ ((chartZRingEquiv W).symm (coordY W)) = _
  congr 1
  rw [RingEquiv.symm_apply_eq]
  exact (chartZRingEquiv_y W).symm

omit [CommRing K'] [Algebra A K] [Algebra A K'] in
/-- An `A`-compatible homomorphism out of the affine coordinate ring is determined by its
values on `coordX` and `coordY` (the coordinate ring is generated by them over `A`). -/
theorem coordRingHom_ext (φ ψ : W.toAffine.CoordinateRing →+* K)
    (halg : ∀ r : A, φ (algebraMap A W.toAffine.CoordinateRing r) =
      ψ (algebraMap A W.toAffine.CoordinateRing r))
    (hX : φ (coordX W) = ψ (coordX W)) (hY : φ (coordY W) = ψ (coordY W)) : φ = ψ := by
  have hofC : ∀ a : A, φ (AdjoinRoot.of W.toAffine.polynomial (Polynomial.C a)) =
      ψ (AdjoinRoot.of W.toAffine.polynomial (Polynomial.C a)) := by
    intro a
    rw [show AdjoinRoot.of W.toAffine.polynomial (Polynomial.C a) =
      algebraMap A W.toAffine.CoordinateRing a by
      rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]]
    exact halg a
  have hof : ∀ r : Polynomial A, φ (AdjoinRoot.of W.toAffine.polynomial r) =
      ψ (AdjoinRoot.of W.toAffine.polynomial r) := by
    intro r
    induction r using Polynomial.induction_on with
    | C a => exact hofC a
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | monomial n a _ =>
      simp only [map_mul, map_pow,
        show AdjoinRoot.of W.toAffine.polynomial Polynomial.X = coordX W from rfl, hofC, hX]
  apply RingHom.ext
  intro a
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
    mul_one, map_add, map_add, map_mul, map_mul,
    show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C p) =
      AdjoinRoot.of W.toAffine.polynomial p from rfl,
    show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C q) =
      AdjoinRoot.of W.toAffine.polynomial q from rfl,
    show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X = coordY W from rfl,
    hof p, hof q, hY]

/-- **Extensionality for `Z`-chart points**: two `Z`-chart `K`-points with the same coordinate
evaluations are equal. -/
theorem ZChart.specPoint_ext (g g' : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (hZ' : InZChart W g')
    (hX : ZChart.eval W g hZ (coordX W) = ZChart.eval W g' hZ' (coordX W))
    (hY : ZChart.eval W g hZ (coordY W) = ZChart.eval W g' hZ' (coordY W)) : g = g' := by
  have hev : ZChart.eval W g hZ = ZChart.eval W g' hZ' := by
    refine coordRingHom_ext W _ _ (fun r ↦ ?_) hX hY
    rw [ZChart.eval_algebraMap, ZChart.eval_algebraMap]
  have hhom : ZChart.hom W g hZ = ZChart.hom W g' hZ' := by
    refine RingHom.ext fun z ↦ ?_
    have := RingHom.congr_fun hev (chartZRingEquiv W z)
    show ZChart.hom W g hZ z = ZChart.hom W g' hZ' z
    calc ZChart.hom W g hZ z
        = ZChart.eval W g hZ (chartZRingEquiv W z) := by
          show _ = ZChart.hom W g hZ ((chartZRingEquiv W).symm (chartZRingEquiv W z))
          rw [RingEquiv.symm_apply_apply]
      _ = ZChart.eval W g' hZ' (chartZRingEquiv W z) := this
      _ = ZChart.hom W g' hZ' z := by
          show ZChart.hom W g' hZ' ((chartZRingEquiv W).symm (chartZRingEquiv W z)) = _
          rw [RingEquiv.symm_apply_apply]
  refine Subtype.ext ?_
  rw [← ZChart.spec_map_hom_awayι W g hZ, ← ZChart.spec_map_hom_awayι W g' hZ', hhom]

end ZChartNaturality

section TateMarkedChart

/-! ### The atlas marking as a `Z`-chart point with coordinates `(0, 0)` -/

variable (R : CommRingCat.{u})

/-- The atlas marked point `(0, 0)` as a `Z`-chart point of the universal Tate model over the
atlas ring itself. -/
noncomputable def TateAtlas.P0.specPoint :
    SpecPoints (projModel (tateCurveLocOver R)) (projModelπ (tateCurveLocOver R))
      (tateRingOver R) :=
  ⟨tateP0mor R, by
    rw [tateP0mor_π R, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]⟩

/-- `tateP0mor` factors through the `Z`-chart via the `(0,0)`-solution homomorphism (the
public replay of the `[Y1-vi]` factorisation, through `chartHomEquiv_symm_coe`). -/
theorem TateAtlas.P0.mor_fac : tateP0mor R =
    Spec.map (CommRingCat.ofHom
      ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1) ≫
    Proj.awayι (quotientGrading (projIdeal (tateCurveLocOver R)))
      ((quotientGradingHom (projIdeal (tateCurveLocOver R))) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2) one_pos := by
  have hdef : tateP0mor R
      = ((chartHomEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm
        ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm
          (tateP0sol R))).1.1 := rfl
  exact hdef.trans (chartHomEquiv_symm_coe (tateCurveLocOver R) 2 _)

/-- The marked point lies in the `Z`-chart. -/
theorem ZChart.TateP0.mem : InZChart (tateCurveLocOver R) (TateAtlas.P0.specPoint R) :=
  ⟨Spec.map (CommRingCat.ofHom
    ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1),
    (TateAtlas.P0.mor_fac R).symm⟩

/-- The chart-ring homomorphism of the marked point is the `(0,0)`-solution homomorphism. -/
theorem ZChart.TateP0.hom :
    ZChart.hom (tateCurveLocOver R) (TateAtlas.P0.specPoint R) (ZChart.TateP0.mem R) =
      ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1 :=
  (ZChart.hom_unique (tateCurveLocOver R) (TateAtlas.P0.specPoint R) (ZChart.TateP0.mem R)
    _ (TateAtlas.P0.mor_fac R).symm).symm

/-- The marked point's chart coordinates vanish (`tateP0sol = (0, 0)`). -/
theorem ZChart.TateP0.hom_isLocalizationElem (j : {j : Fin 3 // j ≠ 2}) :
    ZChart.hom (tateCurveLocOver R) (TateAtlas.P0.specPoint R) (ZChart.TateP0.mem R)
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2)
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) j.1)) = 0 := by
  rw [ZChart.TateP0.hom]
  have hval := DFunLike.congr_arg
    (((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1)
    (chartCoordEquiv_mk_X (tateCurveLocOver R) 2 j)
  refine Eq.trans hval.symm ?_
  have hrfl : ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm
        (tateP0sol R)).1
        (chartCoordEquiv (tateCurveLocOver R) 2 (Ideal.Quotient.mk _ (MvPolynomial.X j)))
      = (chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)
          ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm
            (tateP0sol R))).1 j := rfl
  rw [hrfl, Equiv.apply_symm_apply]
  rfl

/-- The marked point's `x`-coordinate evaluation is `0`. -/
theorem ZChart.TateP0.eval_coordX :
    ZChart.eval (tateCurveLocOver R) (TateAtlas.P0.specPoint R) (ZChart.TateP0.mem R)
      (coordX (tateCurveLocOver R)) = 0 := by
  rw [ZChart.eval_coordX]
  exact ZChart.TateP0.hom_isLocalizationElem R ⟨0, by decide⟩

/-- The marked point's `y`-coordinate evaluation is `0`. -/
theorem ZChart.TateP0.eval_coordY :
    ZChart.eval (tateCurveLocOver R) (TateAtlas.P0.specPoint R) (ZChart.TateP0.mem R)
      (coordY (tateCurveLocOver R)) = 0 := by
  rw [ZChart.eval_coordY]
  exact ZChart.TateP0.hom_isLocalizationElem R ⟨1, by decide⟩

end TateMarkedChart

section BaseChangeChart

/-! ### `Z`-chart points along base change of the model

The chart square of `projModelBaseChange` (`isPullback_projModelBaseChange_chart`) transports
`Z`-chart points of the base-changed model to `Z`-chart points of the original, with the
coordinate evaluations unchanged.  This is the mechanism producing the classifying `top` map's
compatibility with the atlas marking. -/

variable {A : Type u} [CommRing A]

/-- `awayι` transports along an equality of the localized elements (public generic replica of
the `awayι_awayCongr_local` pattern). -/
theorem Spec_map_awayCongr_awayι {R₀ B : Type u} [CommRing R₀] [CommRing B] [Algebra R₀ B]
    (𝒜 : ℕ → Submodule R₀ B) [GradedAlgebra 𝒜] {s t : B} (h : s = t)
    (hs : s ∈ 𝒜 1) :
    Spec.map (CommRingCat.ofHom (awayCongr (𝒜 := 𝒜) h).toRingHom) ≫
      Proj.awayι 𝒜 s hs one_pos = Proj.awayι 𝒜 t (h ▸ hs) one_pos := by
  subst h
  rw [show (awayCongr (𝒜 := 𝒜) (rfl : s = s)).toRingHom = RingHom.id _ by
    rw [awayCongr_rfl]; rfl]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

variable (W : WeierstrassCurve A) {B : Type u} [CommRing B] [Algebra A B]

/-- The chart transport of `projModelBaseChange` on localization elements: `Xⱼ/X₂` maps to
`Xⱼ/X₂`. -/
theorem ZChart.BaseChange.awayCongr_isLocalizationElem (j : Fin 3) :
    awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
      (baseChangeGradedHom_mk_X W 2)
      (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W j))) =
      HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) 2)
        (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) j) := by
  rw [show HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W j)
      = HomogeneousLocalization.Away.mk (quotientGrading (projIdeal W))
          (mk_X_mem_quotientGrading_one W 2) 1
          (((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) ^ 1)
          (by rw [pow_one]; exact mk_X_mem_quotientGrading_one W j) from rfl]
  rw [HomogeneousLocalization.Away.map_mk, awayCongr_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  rw [show HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) 2)
        (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) j)
      = HomogeneousLocalization.Away.mk
          (quotientGrading (projIdeal (W.map (algebraMap A B))))
          (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) 2) 1
          (((quotientGradingHom (projIdeal (W.map (algebraMap A B)))) (MvPolynomial.X j)) ^ 1)
          (by rw [pow_one]
              exact mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) j) from rfl]
  rw [HomogeneousLocalization.Away.val_mk]
  rw [map_pow, baseChangeGradedHom_mk_X]

variable {K : Type u} [CommRing K] [Algebra B K] [Algebra A K] [IsScalarTower A B K]

/-- Push a `Z`-chart point of the base-changed model down to the original model. -/
noncomputable def specPointBaseChange
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K) :
    SpecPoints (projModel W) (projModelπ W) K :=
  ⟨g.1 ≫ projModelBaseChange (algebraMap A B) W, by
    rw [Category.assoc, projModelBaseChange_π, ← Category.assoc, g.2, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]⟩

/-- The chart square, assembled: the `Z`-chart inclusion of the base-changed model composed
with `projModelBaseChange` factors through the `Z`-chart of the original model. -/
theorem awayι_projModelBaseChange :
    Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap A B))))
      ((quotientGradingHom (projIdeal (W.map (algebraMap A B)))) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) 2) one_pos ≫
      projModelBaseChange (algebraMap A B) W =
    Spec.map (CommRingCat.ofHom
      (((awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
          (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
        (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
    Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos := by
  have hsq := (isPullback_projModelBaseChange_chart (R' := B) W 2).w
  have hcongr : Spec.map (CommRingCat.ofHom
      (awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
        (baseChangeGradedHom_mk_X W 2)).toRingHom) ≫
      Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap A B))))
        ((baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
        ((baseChangeGradedHom (algebraMap A B) W).2
          (mk_X_mem_quotientGrading_one W 2)) one_pos =
      Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap A B))))
        ((quotientGradingHom (projIdeal (W.map (algebraMap A B)))) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) 2) one_pos :=
    Spec_map_awayCongr_awayι _ (baseChangeGradedHom_mk_X W 2) _
  rw [← hcongr, Category.assoc, ← hsq, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]

/-- Base change preserves the `Z`-chart. -/
theorem ZChart.BaseChange.mem
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    InZChart W (specPointBaseChange W g) := by
  refine ⟨Spec.map (CommRingCat.ofHom (ZChart.hom (W.map (algebraMap A B)) g hZ)) ≫
    Spec.map (CommRingCat.ofHom
      (((awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
          (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
        (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))), ?_⟩
  rw [Category.assoc, ← awayι_projModelBaseChange, ← Category.assoc,
    ZChart.spec_map_hom_awayι]
  rfl

/-- The chart-ring homomorphism of a base-changed point. -/
theorem ZChart.BaseChange.hom
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    ZChart.hom W (specPointBaseChange W g) (ZChart.BaseChange.mem W g hZ) =
      (ZChart.hom (W.map (algebraMap A B)) g hZ).comp
        (((awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
            (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
          (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) := by
  refine (ZChart.hom_unique W _ _ _ ?_).symm
  rw [show CommRingCat.ofHom ((ZChart.hom (W.map (algebraMap A B)) g hZ).comp
      (((awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
          (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
        (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) =
      CommRingCat.ofHom (((awayCongr (𝒜 := quotientGrading
          (projIdeal (W.map (algebraMap A B)))) (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
        (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) ≫
      CommRingCat.ofHom (ZChart.hom (W.map (algebraMap A B)) g hZ) from
    CommRingCat.ofHom_comp _ _]
  rw [Spec.map_comp, Category.assoc, ← awayι_projModelBaseChange, ← Category.assoc,
    ZChart.spec_map_hom_awayι]
  rfl

/-- Base change leaves the coordinate evaluations unchanged. -/
theorem ZChart.BaseChange.eval_coordX
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    ZChart.eval W (specPointBaseChange W g) (ZChart.BaseChange.mem W g hZ)
      (coordX W) = ZChart.eval (W.map (algebraMap A B)) g hZ
        (coordX (W.map (algebraMap A B))) := by
  rw [ZChart.eval_coordX, ZChart.eval_coordX, ZChart.BaseChange.hom]
  show ZChart.hom (W.map (algebraMap A B)) g hZ
    (awayCongr (baseChangeGradedHom_mk_X W 2)
      (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)))) = _
  rw [ZChart.BaseChange.awayCongr_isLocalizationElem W 0]

/-- Base change leaves the coordinate evaluations unchanged (`y`-side). -/
theorem ZChart.BaseChange.eval_coordY
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    ZChart.eval W (specPointBaseChange W g) (ZChart.BaseChange.mem W g hZ)
      (coordY W) = ZChart.eval (W.map (algebraMap A B)) g hZ
        (coordY (W.map (algebraMap A B))) := by
  rw [ZChart.eval_coordY, ZChart.eval_coordY, ZChart.BaseChange.hom]
  show ZChart.hom (W.map (algebraMap A B)) g hZ
    (awayCongr (baseChangeGradedHom_mk_X W 2)
      (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)))) = _
  rw [ZChart.BaseChange.awayCongr_isLocalizationElem W 1]

end BaseChangeChart

section ProjTateMap

/-! ### The classifying model morphism of a marked chart (B2-iii at model level)

For an elliptic marked chart `(W, g)` over an `R`-algebra `A`, T-E1 normalisation exhibits
`W` as the specialisation of the universal Tate curve at the atlas algebra map, giving the
canonical model morphism `projModel W ⟶ projModel (tateCurveLocOver R)` — cartesian over the
affine atlas map, pointed, and carrying the marking to the atlas marking `(0,0)`. -/

variable {A : Type u} [CommRing A]

/-- Transport of a point along a pointed isomorphism of models. -/
noncomputable def specPointPointedIso {W₁ W₂ : WeierstrassCurve A}
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W₁) (projModelπ W₁) K) :
    SpecPoints (projModel W₂) (projModelπ W₂) K :=
  ⟨g.1 ≫ ε.hom, by rw [Category.assoc, heπ, g.2]⟩

/-- Pointed isomorphisms preserve the `Z`-chart. -/
theorem ZChart.mem_specPointPointedIso {W₁ W₂ : WeierstrassCurve A}
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W₁) (projModelπ W₁) K) (hZ : InZChart W₁ g) :
    InZChart W₂ (specPointPointedIso ε heπ g) := by
  refine ⟨Spec.map (CommRingCat.ofHom (ZChart.hom W₁ g hZ)) ≫
    Spec.map (pointedIsoAwayHom ε hez), ?_⟩
  rw [Category.assoc, ZChart.PointedIso.spec_map_awayι ε hez, ← Category.assoc,
    ZChart.spec_map_hom_awayι]
  rfl

variable (R : CommRingCat.{u}) [Algebra R A] (W : WeierstrassCurve A) [W.IsElliptic]
  (g : SpecPoints (projModel W) (projModelπ W) A) (hZ : InZChart W g)
  (hord : NowhereOrderLEThree W
    (ZChart.eval W g hZ (coordX W)) (ZChart.eval W g hZ (coordY W)))

/-- The specialisation of the universal Tate curve at the marked chart's atlas map is the
T-E1 normal form of the chart. -/
theorem TateAtlas.CurveLocOver.map_marked :
    (tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) =
      (TateAtlas.TateNormal.variableChange W _ _ (ZChart.eval_equation_self W g hZ) hord) • W :=
  TateAtlas.Point.curveLocOver_map_algLift R W _ _ (ZChart.eval_equation_self W g hZ) hord

/-- The normalising pointed isomorphism from the specialised universal Tate model onto the
chart's model. -/
noncomputable def TateAtlas.normalIso :
    projModel ((tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) ≅ projModel W :=
  eqToIso (congrArg projModel (TateAtlas.CurveLocOver.map_marked R W g hZ hord)) ≪≫
    projModelVCIso
      (TateAtlas.TateNormal.variableChange W _ _
        (ZChart.eval_equation_self W g hZ) hord) W

/-- The hom of the normalising isomorphism, in `transport_general` shape. -/
theorem TateAtlas.normalIso.hom :
    (TateAtlas.normalIso R W g hZ hord).hom =
      eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R W g hZ hord)) ≫
        (projModelVCIso
          (TateAtlas.TateNormal.variableChange W _ _
            (ZChart.eval_equation_self W g hZ) hord) W).hom := by
  rw [TateAtlas.normalIso, Iso.trans_hom, eqToIso.hom]

/-- `eqToHom` transport of the structure morphism along a curve equality. -/
theorem eqToHom_projModelπ {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂) :
    eqToHom (congrArg projModel h) ≫ projModelπ V₂ = projModelπ V₁ := by
  subst h; simp

/-- `eqToHom` transport of the zero section along a curve equality. -/
theorem eqToHom_projModelZero {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂) :
    projModelZero V₁ ≫ eqToHom (congrArg projModel h) = projModelZero V₂ := by
  subst h; simp

/-- The normalising isomorphism respects the structure morphisms. -/
theorem TateAtlas.normalIso.π :
    (TateAtlas.normalIso R W g hZ hord).hom ≫ projModelπ W =
      projModelπ ((tateCurveLocOver R).map
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) := by
  rw [TateAtlas.normalIso.hom, Category.assoc, projModelVCIso_π,
    eqToHom_projModelπ (TateAtlas.CurveLocOver.map_marked R W g hZ hord)]

/-- The normalising isomorphism respects the zero sections. -/
theorem TateAtlas.normalIso.zero :
    projModelZero ((tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) ≫
      (TateAtlas.normalIso R W g hZ hord).hom = projModelZero W := by
  rw [TateAtlas.normalIso.hom, ← Category.assoc,
    eqToHom_projModelZero (TateAtlas.CurveLocOver.map_marked R W g hZ hord), projModelVCIso_zero]

/-- The marked point, normalised into the specialised Tate model. -/
noncomputable def markedPointNormalised :
    SpecPoints (projModel ((tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)))
      (projModelπ ((tateCurveLocOver R).map
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))) A :=
  specPointPointedIso (TateAtlas.normalIso R W g hZ hord).symm
    (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact (TateAtlas.normalIso.π R W g hZ hord).symm) g

/-- The normalised marked point returns to the marking through the normalising iso. -/
theorem markedPointNormalised_sec :
    (markedPointNormalised R W g hZ hord).1 ≫ (TateAtlas.normalIso R W g hZ hord).hom = g.1 := by
  show (g.1 ≫ (TateAtlas.normalIso R W g hZ hord).inv) ≫
      (TateAtlas.normalIso R W g hZ hord).hom = g.1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The zero section respects the inverse normalising iso. -/
theorem TateAtlas.normalIso.zero_inv :
    projModelZero W ≫ (TateAtlas.normalIso R W g hZ hord).inv =
      projModelZero ((tateCurveLocOver R).map
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) := by
  rw [Iso.comp_inv_eq]
  exact (TateAtlas.normalIso.zero R W g hZ hord).symm

/-- The normalised marked point lies in the `Z`-chart. -/
theorem ZChart.markedPointNormalised_mem :
    InZChart ((tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))
      (markedPointNormalised R W g hZ hord) :=
  ZChart.mem_specPointPointedIso (TateAtlas.normalIso R W g hZ hord).symm
    (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact (TateAtlas.normalIso.π R W g hZ hord).symm)
    (by rw [Iso.symm_hom]; exact TateAtlas.normalIso.zero_inv R W g hZ hord) g hZ

/-- The normalised marked point has coordinates `(0, 0)`. -/
theorem markedPointNormalised_coords :
    ZChart.eval _ (markedPointNormalised R W g hZ hord)
      (ZChart.markedPointNormalised_mem R W g hZ hord)
      (coordX ((tateCurveLocOver R).map
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))) = 0 ∧
    ZChart.eval _ (markedPointNormalised R W g hZ hord)
      (ZChart.markedPointNormalised_mem R W g hZ hord)
      (coordY ((tateCurveLocOver R).map
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))) = 0 := by
  have heπ : (TateAtlas.normalIso R W g hZ hord).hom ≫ projModelπ W = projModelπ _ :=
    TateAtlas.normalIso.π R W g hZ hord
  have hez : projModelZero _ ≫ (TateAtlas.normalIso R W g hZ hord).hom = projModelZero W :=
    TateAtlas.normalIso.zero R W g hZ hord
  have hgsec : (markedPointNormalised R W g hZ hord).1 ≫
      (TateAtlas.normalIso R W g hZ hord).hom = g.1 := markedPointNormalised_sec R W g hZ hord
  have hX := ZChart.eval_pointedIso (TateAtlas.normalIso R W g hZ hord) heπ hez
    (markedPointNormalised R W g hZ hord) g
    (ZChart.markedPointNormalised_mem R W g hZ hord) hZ hgsec (coordX W)
  have hY := ZChart.eval_pointedIso (TateAtlas.normalIso R W g hZ hord) heπ hez
    (markedPointNormalised R W g hZ hord) g
    (ZChart.markedPointNormalised_mem R W g hZ hord) hZ hgsec (coordY W)
  rw [transport_general (TateAtlas.CurveLocOver.map_marked R W g hZ hord) _
    (projModelVCIso
      (TateAtlas.TateNormal.variableChange W _ _
        (ZChart.eval_equation_self W g hZ) hord) W)
    heπ hez (projModelVCIso_π _ W) (projModelVCIso_zero _ W)
    (TateAtlas.normalIso.hom R W g hZ hord) (coordX W), bridge_coordX] at hX
  rw [transport_general (TateAtlas.CurveLocOver.map_marked R W g hZ hord) _
    (projModelVCIso
      (TateAtlas.TateNormal.variableChange W _ _
        (ZChart.eval_equation_self W g hZ) hord) W)
    heπ hez (projModelVCIso_π _ W) (projModelVCIso_zero _ W)
    (TateAtlas.normalIso.hom R W g hZ hord) (coordY W), bridge_coordY] at hY
  simp only [map_add, coordRingCongr_algebraMap_mul_coordX,
    coordRingCongr_algebraMap_mul_coordY, coordRingCongr_algebraMap] at hX hY
  simp only [map_mul, ZChart.eval_algebraMap, Algebra.algebraMap_self_apply] at hX hY
  rw [TateAtlas.TateNormal.variableChange_r W _ _ (ZChart.eval_equation_self W g hZ) hord] at hX
  rw [TateAtlas.TateNormal.variableChange_t W _ _ (ZChart.eval_equation_self W g hZ) hord] at hY
  have hXzero : ZChart.eval _ (markedPointNormalised R W g hZ hord)
      (ZChart.markedPointNormalised_mem R W g hZ hord) (coordX _) = 0 := by
    have h2 : ((TateAtlas.TateNormal.variableChange W _ _ (ZChart.eval_equation_self W g hZ) hord).u
        : A) ^ 2 * ZChart.eval _ (markedPointNormalised R W g hZ hord)
        (ZChart.markedPointNormalised_mem R W g hZ hord) (coordX _) = 0 := by
      linear_combination -hX
    exact ((Units.mul_right_eq_zero (_ ^ 2)).mp (by exact_mod_cast h2))
  refine ⟨hXzero, ?_⟩
  rw [hXzero] at hY
  have h3 : ((TateAtlas.TateNormal.variableChange W _ _ (ZChart.eval_equation_self W g hZ) hord).u
      : A) ^ 3 * ZChart.eval _ (markedPointNormalised R W g hZ hord)
      (ZChart.markedPointNormalised_mem R W g hZ hord) (coordY _) = 0 := by
    linear_combination -hY
  exact ((Units.mul_right_eq_zero (_ ^ 3)).mp (by exact_mod_cast h3))

end ProjTateMap

section ProjTateMapAssembly

/-! ### The classifying model morphism: cartesian, pointed, marking-compatible -/

variable {A : Type u} [CommRing A] (R : CommRingCat.{u}) [Algebra R A]
  (W : WeierstrassCurve A) [W.IsElliptic]
  (g : SpecPoints (projModel W) (projModelπ W) A) (hZ : InZChart W g)
  (hord : NowhereOrderLEThree W
    (ZChart.eval W g hZ (coordX W)) (ZChart.eval W g hZ (coordY W)))

/-- The classifying morphism of a marked chart into the universal Tate model. -/
noncomputable def projTateMap : projModel W ⟶ projModel (tateCurveLocOver R) :=
  (TateAtlas.normalIso R W g hZ hord).inv ≫
    projModelBaseChange
      ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) (tateCurveLocOver R)

/-- The inverse normalising iso respects the structure morphisms. -/
theorem TateAtlas.normalIso.inv_π :
    (TateAtlas.normalIso R W g hZ hord).inv ≫ projModelπ ((tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) = projModelπ W := by
  rw [← TateAtlas.normalIso.π R W g hZ hord, Iso.inv_hom_id_assoc]

/-- The classifying morphism lies over the affine atlas map. -/
theorem projTateMap_π :
    projTateMap R W g hZ hord ≫ projModelπ (tateCurveLocOver R) =
      projModelπ W ≫
        TateAtlas.Point.baseSpecMap R W _ _ (ZChart.eval_equation_self W g hZ) hord := by
  show ((TateAtlas.normalIso R W g hZ hord).inv ≫ _) ≫ _ = _
  rw [Category.assoc, projModelBaseChange_π, ← Category.assoc, TateAtlas.normalIso.inv_π]
  rfl

/-- The classifying square is cartesian. -/
theorem projTateMap_isPullback :
    IsPullback (projTateMap R W g hZ hord) (projModelπ W) (projModelπ (tateCurveLocOver R))
      (TateAtlas.Point.baseSpecMap R W _ _ (ZChart.eval_equation_self W g hZ) hord) := by
  letI : Algebra (tateRingOver R) A :=
    ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).toAlgebra
  have sq2 : IsPullback
      (projModelBaseChange
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) (tateCurveLocOver R))
      (projModelπ ((tateCurveLocOver R).map
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)))
      (projModelπ (tateCurveLocOver R))
      (TateAtlas.Point.baseSpecMap R W _ _ (ZChart.eval_equation_self W g hZ) hord) :=
    isPullback_projModelBaseChange (tateCurveLocOver R)
  have sq1 : IsPullback ((TateAtlas.normalIso R W g hZ hord).inv) (projModelπ W)
      (projModelπ ((tateCurveLocOver R).map
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)))
      (𝟙 (Spec (CommRingCat.of A))) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact TateAtlas.normalIso.inv_π R W g hZ hord⟩
  have hpaste := sq1.paste_horiz sq2
  rw [Category.id_comp] at hpaste
  exact hpaste

/-- The classifying morphism is pointed. -/
theorem projTateMap_zero :
    projModelZero W ≫ projTateMap R W g hZ hord =
      TateAtlas.Point.baseSpecMap R W _ _ (ZChart.eval_equation_self W g hZ) hord ≫
        projModelZero (tateCurveLocOver R) := by
  letI : Algebra (tateRingOver R) A :=
    ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).toAlgebra
  show projModelZero W ≫ (TateAtlas.normalIso R W g hZ hord).inv ≫ _ = _
  rw [← Category.assoc, TateAtlas.normalIso.zero_inv R W g hZ hord]
  exact projModelZero_baseChange (tateCurveLocOver R)

/-- **The marking compatibility**: the classifying morphism carries the chart marking to
the atlas marking `(0,0)`. -/
theorem projTateMap_marking :
    g.1 ≫ projTateMap R W g hZ hord =
      TateAtlas.Point.baseSpecMap R W _ _ (ZChart.eval_equation_self W g hZ) hord ≫
        tateP0mor R := by
  letI : Algebra (tateRingOver R) A :=
    ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).toAlgebra
  have hψ : ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).comp
      (algebraMap (tateRingOver R) (tateRingOver R)) = algebraMap (tateRingOver R) A := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
    rfl
  refine Eq.trans ?_ (congrArg Subtype.val (ZChart.specPoint_ext (tateCurveLocOver R)
    (specPointBaseChange (tateCurveLocOver R) (markedPointNormalised R W g hZ hord))
    (specPointComp (tateCurveLocOver R) (TateAtlas.P0.specPoint R) _ hψ)
    (ZChart.BaseChange.mem (tateCurveLocOver R)
      (markedPointNormalised R W g hZ hord) (ZChart.markedPointNormalised_mem R W g hZ hord))
    (ZChart.mem_specPointComp (tateCurveLocOver R) (TateAtlas.P0.specPoint R)
      (ZChart.TateP0.mem R) _ hψ)
    (by
      rw [ZChart.BaseChange.eval_coordX, ZChart.eval_specPointComp,
        ZChart.TateP0.eval_coordX, map_zero]
      · exact (markedPointNormalised_coords R W g hZ hord).1
      · exact ZChart.TateP0.mem R)
    (by
      rw [ZChart.BaseChange.eval_coordY, ZChart.eval_specPointComp,
        ZChart.TateP0.eval_coordY, map_zero]
      · exact (markedPointNormalised_coords R W g hZ hord).2
      · exact ZChart.TateP0.mem R)))
  show g.1 ≫ (TateAtlas.normalIso R W g hZ hord).inv ≫ _ = _
  rw [← Category.assoc]
  rfl

end ProjTateMapAssembly

section ProjTateMapComparison

/-! ### ENGINE (top half): the classifying morphisms agree across a marked pointed iso

`projTateMap` is natural for pointed isomorphisms carrying marking to marking: the T-W7
changes of `ε` and of the canonical comparison `θ₁⁻¹ ≫ θ₂` both compose with the source's
T-E1 normalisation to the target's (`TateAtlas.TateNormal.variableChange_mul`), so they are
**equal**
by group cancellation, hence so are the isomorphisms — no separate rigidity computation. -/

variable {A : Type u} [CommRing A]

/-- `eqToIso` transport of the structure morphism along a curve equality. -/
theorem eqToIso_projModelπ {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂) :
    (eqToIso (congrArg projModel h)).hom ≫ projModelπ V₂ = projModelπ V₁ := by
  rw [eqToIso.hom]
  exact eqToHom_projModelπ h

/-- `eqToIso` transport of the zero section along a curve equality. -/
theorem eqToIso_projModelZero {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂) :
    projModelZero V₁ ≫ (eqToIso (congrArg projModel h)).hom = projModelZero V₂ := by
  rw [eqToIso.hom]
  exact eqToHom_projModelZero h

/-- Transport of a `Z`-chart point along a curve equality preserves the evaluations. -/
theorem ZChart.eval_eqToHom_point {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel V₁) (projModelπ V₁) K) (hZ : InZChart V₁ g)
    (hZ' : InZChart V₂ (specPointPointedIso (eqToIso (congrArg projModel h))
      (eqToIso_projModelπ h) g)) (a : V₂.toAffine.CoordinateRing) :
    ZChart.eval V₂ (specPointPointedIso (eqToIso (congrArg projModel h))
      (eqToIso_projModelπ h) g) hZ' a =
      ZChart.eval V₁ g hZ (coordRingCongr h.symm a) := by
  subst h
  rw [coordRingCongr_refl_apply]
  have hpt : specPointPointedIso (eqToIso (congrArg projModel (rfl : V₁ = V₁)))
      (eqToIso_projModelπ rfl) g = g := by
    refine Subtype.ext ?_
    show g.1 ≫ (eqToIso (congrArg projModel (rfl : V₁ = V₁))).hom = g.1
    rw [eqToIso.hom, eqToHom_refl, Category.comp_id]
  revert hZ'
  rw [hpt]
  intro hZ'
  rfl

/-- `eqToHom` transport of the base-change morphism along an equality of ring maps. -/
theorem eqToHom_projModelBaseChange {B : Type u} [CommRing B]
    {f₁ f₂ : B →+* A} (h : f₁ = f₂) (W : WeierstrassCurve B) :
    eqToHom (congrArg (fun ψ : B →+* A ↦ projModel (W.map ψ)) h) ≫
      projModelBaseChange f₂ W = projModelBaseChange f₁ W := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

variable (R : CommRingCat.{u}) [Algebra R A]
  (W₁ W₂ : WeierstrassCurve A) [W₁.IsElliptic] [W₂.IsElliptic]
  (ε : projModel W₁ ≅ projModel W₂)
  (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
  (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
  (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
  (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
  (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
  (hsec : g₁.1 ≫ ε.hom = g₂.1)
  (hord₁ : NowhereOrderLEThree W₁
    (ZChart.eval W₁ g₁ hZ₁ (coordX W₁)) (ZChart.eval W₁ g₁ hZ₁ (coordY W₁)))
  (hord₂ : NowhereOrderLEThree W₂
    (ZChart.eval W₂ g₂ hZ₂ (coordX W₂)) (ZChart.eval W₂ g₂ hZ₂ (coordY W₂)))

include heπ hez hsec in
/-- **(ENGINE, top half)** The classifying model morphisms of two marked charts linked by a
marked pointed isomorphism agree: `ε.hom ≫ projTateMap₂ = projTateMap₁`. -/
theorem projTateMap_eq_of_pointedIso :
    ε.hom ≫ projTateMap R W₂ g₂ hZ₂ hord₂ = projTateMap R W₁ g₁ hZ₁ hord₁ := by
  -- the atlas algebra maps agree (ENGINE, base half)
  have hφ : (TateAtlas.Point.ringOverAlgLift R W₁ _ _ (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ :
      tateRingOver R →ₐ[R] A) =
      TateAtlas.Point.ringOverAlgLift R W₂ _ _ (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ :=
    TateAtlas.Point.ringOverAlgLift.eq_of_pointedIso R W₁ W₂ ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec
      hord₁ hord₂
  have hcur : (tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W₁ _ _ (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) =
      (tateCurveLocOver R).map
      ((TateAtlas.Point.ringOverAlgLift R W₂ _ _ (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) := by
    rw [hφ]
  -- the canonical comparison isomorphism through the two normalising isos
  set χ : projModel W₁ ≅ projModel W₂ :=
    (TateAtlas.normalIso R W₁ g₁ hZ₁ hord₁).symm ≪≫ eqToIso (congrArg projModel hcur) ≪≫
      TateAtlas.normalIso R W₂ g₂ hZ₂ hord₂ with hχdef
  have hχπ : χ.hom ≫ projModelπ W₂ = projModelπ W₁ := by
    rw [hχdef]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rw [TateAtlas.normalIso.π R W₂ g₂ hZ₂ hord₂, eqToHom_projModelπ hcur]
    exact TateAtlas.normalIso.inv_π R W₁ g₁ hZ₁ hord₁
  have hχz : projModelZero W₁ ≫ χ.hom = projModelZero W₂ := by
    rw [hχdef]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
    rw [← Category.assoc, ← Category.assoc, TateAtlas.normalIso.zero_inv R W₁ g₁ hZ₁ hord₁,
      eqToHom_projModelZero hcur]
    exact TateAtlas.normalIso.zero R W₂ g₂ hZ₂ hord₂
  -- χ carries the first marking to the second, via the (0,0)-coordinate extensionality
  have hmp : specPointPointedIso (eqToIso (congrArg projModel hcur))
      (eqToIso_projModelπ hcur) (markedPointNormalised R W₁ g₁ hZ₁ hord₁) =
      markedPointNormalised R W₂ g₂ hZ₂ hord₂ := by
    have hZT := ZChart.mem_specPointPointedIso (eqToIso (congrArg projModel hcur))
      (eqToIso_projModelπ hcur) (eqToIso_projModelZero hcur)
      (markedPointNormalised R W₁ g₁ hZ₁ hord₁)
      (ZChart.markedPointNormalised_mem R W₁ g₁ hZ₁ hord₁)
    refine ZChart.specPoint_ext _ _ _ hZT
      (ZChart.markedPointNormalised_mem R W₂ g₂ hZ₂ hord₂) ?_ ?_
    · rw [ZChart.eval_eqToHom_point hcur _ (ZChart.markedPointNormalised_mem R W₁ g₁ hZ₁ hord₁)
        hZT, coordRingCongr_coordX, (markedPointNormalised_coords R W₁ g₁ hZ₁ hord₁).1,
        (markedPointNormalised_coords R W₂ g₂ hZ₂ hord₂).1]
    · rw [ZChart.eval_eqToHom_point hcur _ (ZChart.markedPointNormalised_mem R W₁ g₁ hZ₁ hord₁)
        hZT, coordRingCongr_coordY, (markedPointNormalised_coords R W₁ g₁ hZ₁ hord₁).2,
        (markedPointNormalised_coords R W₂ g₂ hZ₂ hord₂).2]
  have hχsec : g₁.1 ≫ χ.hom = g₂.1 := by
    have h1 := congrArg Subtype.val hmp
    have h2 : (g₁.1 ≫ (TateAtlas.normalIso R W₁ g₁ hZ₁ hord₁).inv) ≫
        eqToHom (congrArg projModel hcur) =
        (markedPointNormalised R W₂ g₂ hZ₂ hord₂).1 := h1
    rw [hχdef]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
    rw [← Category.assoc, ← Category.assoc, h2]
    exact markedPointNormalised_sec R W₂ g₂ hZ₂ hord₂
  -- both T-W7 changes compose to the same normalisation, hence agree
  obtain ⟨C, hC, hεhom⟩ := pointedIso_exists_variableChange W₁ W₂ ε heπ hez
  obtain ⟨C', hC', hχhom⟩ := pointedIso_exists_variableChange W₁ W₂ χ hχπ hχz
  obtain ⟨hxε, hyε⟩ := ZChart.eval_coords_of_pointedIso W₁ W₂ ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec
    C hC hεhom
  obtain ⟨hxχ, hyχ⟩ := ZChart.eval_coords_of_pointedIso W₁ W₂ χ hχπ hχz g₁ g₂ hZ₁ hZ₂ hχsec
    C' hC' hχhom
  have hCC' : C = C' := by
    have h1 := TateAtlas.TateNormal.variableChange_mul W₁ W₂ g₁ g₂ hZ₁ hZ₂
      hord₁ hord₂ C hC hxε hyε
    have h2 := TateAtlas.TateNormal.variableChange_mul W₁ W₂ g₁ g₂ hZ₁ hZ₂
      hord₁ hord₂ C' hC' hxχ hyχ
    exact mul_left_cancel (h1.trans h2.symm)
  have hhom : ε.hom = χ.hom := by
    rw [hεhom, hχhom]
    subst hCC'
    rfl
  -- conclude on the classifying morphisms
  have hbc := eqToHom_projModelBaseChange
    (congrArg (fun (ψ : tateRingOver R →ₐ[R] A) ↦ (ψ : tateRingOver R →+* A)) hφ)
    (tateCurveLocOver R)
  rw [hhom]
  show ((TateAtlas.normalIso R W₁ g₁ hZ₁ hord₁).inv ≫ eqToHom (congrArg projModel hcur) ≫
      (TateAtlas.normalIso R W₂ g₂ hZ₂ hord₂).hom) ≫ (TateAtlas.normalIso R W₂ g₂ hZ₂ hord₂).inv ≫
      projModelBaseChange ((TateAtlas.Point.ringOverAlgLift R W₂ _ _
        (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ : tateRingOver R →ₐ[R] A) :
        tateRingOver R →+* A) (tateCurveLocOver R) =
    (TateAtlas.normalIso R W₁ g₁ hZ₁ hord₁).inv ≫
      projModelBaseChange ((TateAtlas.Point.ringOverAlgLift R W₁ _ _
        (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ : tateRingOver R →ₐ[R] A) :
        tateRingOver R →+* A) (tateCurveLocOver R)
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← hbc]

end ProjTateMapComparison

section ChartPackaging

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

/-! ### `Ell/R` chart packaging (v10.109 recipe, step 1)

A `MarkedChartData` bundles one `LocallyWeierstrass` chart of `Y.curve`: an affine open
`U`, an elliptic Weierstrass curve `W` over `Γ(U)`, and the pointed trivialisation `e`.
The section `P` restricts to a `Z`-chart point of `projModel W` over `Γ(U)` whose
coordinate evaluations satisfy the T-E1 hypotheses — the geometric-fibre clauses of
`NowhereGeomOrderLEThree` transfer through the fibre bridges below. -/

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The zero point is the group zero (unwinding the `pointAddCommGroup` transport and
`one_eq_zero`). -/
theorem zeroPoint_eq_zero {T : Scheme.{u}} (g : T ⟶ S) : E.zeroPoint g = 0 := by
  letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
  refine Subtype.ext ?_
  show g ≫ E.zero = ((0 : E.Point g) : T ⟶ E.E)
  have h0 : ((0 : E.Point g) : T ⟶ E.E) =
      (toUnit (Over.mk g) ≫ η[E.asOver]).left := rfl
  rw [h0, Over.comp_left, E.one_eq_zero]
  have hw : Over.Hom.left (toUnit (Over.mk g)) ≫ (𝟙_ (Over S)).hom = g :=
    Over.w (toUnit (Over.mk g))
  exact (congrArg (· ≫ E.zero) hw.symm).trans (Category.assoc _ _ _)

end EllipticCurve

variable (R : CommRingCat.{u})

/-- One `LocallyWeierstrass` chart of the curve of an `Ell/R` object: an affine open of
the base with a pointed Weierstrass trivialisation of the restricted curve. -/
structure MarkedChartData (Y : EllObj R) where
  /-- The affine open of the base. -/
  U : Y.base.affineOpens
  /-- The Weierstrass curve over the chart ring. -/
  W : WeierstrassCurve ↑Γ(Y.base, U.1)
  /-- The chart curve is elliptic. -/
  hell : W.IsElliptic
  /-- The pointed trivialisation. -/
  e : pullback Y.curve.π U.1.ι ≅ projModel W
  /-- Compatibility with the structure morphisms. -/
  heπ : e.hom ≫ projModelπ W = pullback.snd Y.curve.π U.1.ι ≫ U.2.isoSpec.hom
  /-- Compatibility with the zero sections. -/
  hez : (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ Y.curve.zero) (𝟙 _)
    (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp])) ≫ e.hom =
    projModelZero W

attribute [instance] MarkedChartData.hell

variable {R}

namespace MarkedChartData

/-- Every point of the base lies in some marked chart (the `localModel` field). -/
theorem exists_mem (Y : EllObj R) (s : ↥Y.base) :
    ∃ D : MarkedChartData R Y, s ∈ D.U.1 := by
  obtain ⟨U, hsU, W, hell, e, heπ, hez⟩ := Y.curve.localModel s
  exact ⟨⟨U, W, hell, e, heπ, hez⟩, hsU⟩

variable {Y : EllObj R} (D : MarkedChartData R Y)

/-- The restriction of a section of `Y.curve` to the chart, as a section of the restricted
curve. -/
noncomputable def restrictSection (P : Y.curve.Section) :
    D.U.1.toScheme ⟶ pullback Y.curve.π D.U.1.ι :=
  pullback.lift (D.U.1.ι ≫ P.1) (𝟙 _)
    (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp])

/-- The section, read in the chart as a `Γ(U)`-point of the Weierstrass model. -/
noncomputable def pt (P : Y.curve.Section) :
    SpecPoints (projModel D.W) (projModelπ D.W) ↑Γ(Y.base, D.U.1) :=
  ⟨D.U.2.isoSpec.inv ≫ D.restrictSection P ≫ D.e.hom, by
    have hres : D.restrictSection P ≫ pullback.snd Y.curve.π D.U.1.ι = 𝟙 _ :=
      pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, D.heπ, ← Category.assoc (D.restrictSection P),
      hres, Category.id_comp, Iso.inv_hom_id]
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]⟩

@[simp]
theorem pt_coe (P : Y.curve.Section) :
    (D.pt P).1 = D.U.2.isoSpec.inv ≫ D.restrictSection P ≫ D.e.hom := rfl

/-- The geometric point of the base attached to a point of the chart ring. -/
noncomputable def geomPt {k : Type u} [CommRing k]
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↑Γ(Y.base, D.U.1))) :
    Spec (CommRingCat.of k) ⟶ Y.base :=
  t ≫ D.U.2.isoSpec.inv ≫ D.U.1.ι

/-- **Unwinding**: if a field point of the chart hits the model's zero, the pulled section
equals the pulled zero section on the base. -/
theorem pull_eq_zero_of_pt_eq_zero (P : Y.curve.Section) {k : Type u} [Field k]
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↑Γ(Y.base, D.U.1)))
    (heq : t ≫ (D.pt P).1 = t ≫ projModelZero D.W) :
    EllipticCurve.Point.pull Y.curve (D.geomPt t) P = 0 := by
  rw [pt_coe, D.hez.symm] at heq
  have heq2 : (t ≫ D.U.2.isoSpec.inv ≫ D.restrictSection P) ≫ D.e.hom =
      (t ≫ D.U.2.isoSpec.inv ≫ pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp])) ≫
        D.e.hom := by
    simpa only [Category.assoc] using heq
  have heq3 := (cancel_mono D.e.hom).mp heq2
  have heq4 := congrArg (fun m ↦ m ≫ pullback.fst Y.curve.π D.U.1.ι) heq3
  have hfst : D.restrictSection P ≫ pullback.fst Y.curve.π D.U.1.ι = D.U.1.ι ≫ P.1 :=
    pullback.lift_fst _ _ _
  have hfst0 : pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
      (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
      pullback.fst Y.curve.π D.U.1.ι = D.U.1.ι ≫ Y.curve.zero :=
    pullback.lift_fst _ _ _
  simp only [Category.assoc, hfst, hfst0] at heq4
  rw [← Y.curve.zeroPoint_eq_zero (D.geomPt t)]
  refine Subtype.ext ?_
  show (D.geomPt t) ≫ P.1 = (D.geomPt t) ≫ Y.curve.zero
  simpa only [geomPt, Category.assoc] using heq4

/-- **(B1 fibre bridge)** A nowhere-small-order section lies in the `Z`-chart of every
marked chart. -/
theorem pt_mem_zChart (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) : InZChart D.W (D.pt P) := by
  refine ZChart.mem_of_forall_ne_zero D.W (D.pt P) ?_
  intro k _ t heq
  -- normalise the zero side and push to the algebraic closure
  have hid : (t ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ↑Γ(Y.base, D.U.1) ↑Γ(Y.base, D.U.1)))) ≫ projModelZero D.W =
      t ≫ projModelZero D.W := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  rw [hid] at heq
  have heqb := congrArg
    (fun m ↦ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ m) heq
  simp only [← Category.assoc] at heqb
  have h0 := D.pull_eq_zero_of_pt_eq_zero P
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ t) heqb
  have h1 := hP (AlgebraicClosure k)
    (D.geomPt (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ t))
    1 one_pos (by norm_num)
  rw [Nat.cast_one, one_zsmul, h0] at h1
  exact h1 rfl

end MarkedChartData

end ChartPackaging

section FibreBridges

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

/-! ### The geometric-fibre bridges (v10.109 recipe, step 1, [T-A6b]/[T-B6′] trails)

A cartesian square over `Spec` of a ring map presents its source as the model of the mapped
curve (`pullbackChartIso`); a pointed isomorphism of elliptic-curve records over a locally
noetherian base transports sections additively (`sectionMapIso_add`, the GME 2.2.5 argument
of `PullSectionAdd` for a raw pointed iso). -/

section PullbackChartIso

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (W : WeierstrassCurve A)
  {F : Scheme.{u}} {q : F ⟶ Spec (CommRingCat.of B)} {top : F ⟶ projModel W}

variable (hsq : IsPullback top q (projModelπ W)
  (Spec.map (CommRingCat.ofHom (algebraMap A B))))

/-- A cartesian square over `Spec` of the algebra map presents its source as the model of
the base-changed curve. -/
noncomputable def pullbackChartIso : F ≅ projModel (W.map (algebraMap A B)) :=
  hsq.isoIsPullback _ _ (isPullback_projModelBaseChange W)

@[reassoc (attr := simp)]
theorem pullbackChartIso_hom_bc :
    (pullbackChartIso W hsq).hom ≫ projModelBaseChange (algebraMap A B) W = top :=
  hsq.isoIsPullback_hom_fst _ _ (isPullback_projModelBaseChange W)

@[reassoc (attr := simp)]
theorem pullbackChartIso_hom_π :
    (pullbackChartIso W hsq).hom ≫ projModelπ (W.map (algebraMap A B)) = q :=
  hsq.isoIsPullback_hom_snd _ _ (isPullback_projModelBaseChange W)

/-- The chart iso is pointed, given the zero-compatibility of the square. -/
theorem pullbackChartIso_zero (zF : Spec (CommRingCat.of B) ⟶ F)
    (hzq : zF ≫ q = 𝟙 _)
    (hztop : zF ≫ top =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ projModelZero W) :
    zF ≫ (pullbackChartIso W hsq).hom = projModelZero (W.map (algebraMap A B)) := by
  refine (isPullback_projModelBaseChange W).hom_ext ?_ ?_
  · rw [Category.assoc, pullbackChartIso_hom_bc, hztop]
    exact (projModelZero_baseChange W).symm
  · rw [Category.assoc, pullbackChartIso_hom_π, hzq, projModelZero_projModelπ]

/-- A point of the source whose `bc`-composite factors through the `Z`-chart of `W` lies in
the `Z`-chart of the base-changed model (the chart square is cartesian). -/
theorem ZChart.mem_of_comp_baseChange {K : Type u} [CommRing K] [Algebra B K]
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (h₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of
      (HomogeneousLocalization.Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))
    (hfac : h₀ ≫ Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos =
      g.1 ≫ projModelBaseChange (algebraMap A B) W) :
    InZChart (W.map (algebraMap A B)) g := by
  have hsq2 := isPullback_projModelBaseChange_chart (R' := B) W 2
  refine ⟨hsq2.lift h₀ g.1 hfac ≫ Spec.map (CommRingCat.ofHom
    (awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
      (baseChangeGradedHom_mk_X W 2).symm).toRingHom), ?_⟩
  have hcongr := Spec_map_awayCongr_awayι
    (quotientGrading (projIdeal (W.map (algebraMap A B))))
    (baseChangeGradedHom_mk_X W 2).symm
    (mk_X_mem_quotientGrading_one (W.map (algebraMap A B)) 2)
  rw [Category.assoc, hcongr]
  exact hsq2.lift_snd h₀ g.1 hfac

end PullbackChartIso

section SectionIso

variable {T : Scheme.{u}} (E₁ E₂ : EllipticCurve T)
  (iso : E₁.E ≅ E₂.E) (hπ : iso.hom ≫ E₂.π = E₁.π)

/-- Transport of sections along a pointed isomorphism of elliptic curves over the same
base. -/
noncomputable def sectionMapIso (s : E₁.Section) : E₂.Section :=
  ⟨s.1 ≫ iso.hom, by rw [Category.assoc, hπ, s.2]⟩

theorem sectionMapIso_injective : Function.Injective (sectionMapIso E₁ E₂ iso hπ) := by
  intro s s' h
  refine Subtype.ext ?_
  have h1 : s.1 ≫ iso.hom = s'.1 ≫ iso.hom := congrArg Subtype.val h
  simpa using congrArg (· ≫ iso.inv) h1

variable (hz : E₁.zero ≫ iso.hom = E₂.zero)

include hz in
/-- **(GME Cor 2.2.5 for a raw pointed iso, over a locally noetherian base)** The section
transport along a pointed isomorphism is additive (`isMonHom_of_one_comp_eq'`, the
`PullSectionAdd` argument). -/
theorem sectionMapIso_add [IsLocallyNoetherian T] (s s' : E₁.Section) :
    sectionMapIso E₁ E₂ iso hπ (s + s') =
      sectionMapIso E₁ E₂ iso hπ s + sectionMapIso E₁ E₂ iso hπ s' := by
  haveI : Smooth E₁.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E₁.π)
  haveI hP : IsProper E₁.asOver.hom := inferInstanceAs (IsProper E₁.π)
  haveI hFl : Flat E₁.asOver.hom := inferInstanceAs (Flat E₁.π)
  haveI hSep : IsSeparated E₂.asOver.hom := inferInstanceAs (IsSeparated E₂.π)
  let f : E₁.asOver ⟶ E₂.asOver := Over.homMk iso.hom hπ
  have hη : η[E₁.asOver] ≫ f = η[E₂.asOver] := by
    apply Over.OverMorphism.ext
    show (η[E₁.asOver] : _ ⟶ E₁.asOver).left ≫ iso.hom = _
    exact (congrArg (· ≫ iso.hom) E₁.one_eq_zero).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg ((𝟙_ (Over T)).hom ≫ ·) hz).trans E₂.one_eq_zero.symm
  have h64 := @isMonHom_of_one_comp_eq' T _ E₁.asOver E₂.asOver _ _ hP hFl
    E₁.toEllipticCurveGeom.universallyOConnected hSep f hη
  have h64l : (μ[E₁.asOver]).left ≫ iso.hom
      = (MonoidalCategory.tensorHom f f).left ≫ (μ[E₂.asOver]).left :=
    ((Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left h64)).trans
      (Over.comp_left _ _ _ _ _)
  have hcs : E₁.pointEquivOverHom (𝟙 T) s ≫ f
      = E₂.pointEquivOverHom (𝟙 T) (sectionMapIso E₁ E₂ iso hπ s) :=
    Over.OverMorphism.ext rfl
  have hcs' : E₁.pointEquivOverHom (𝟙 T) s' ≫ f
      = E₂.pointEquivOverHom (𝟙 T) (sectionMapIso E₁ E₂ iso hπ s') :=
    Over.OverMorphism.ext rfl
  refine Subtype.ext ?_
  have hx : (s + s').1
      = (lift (E₁.pointEquivOverHom (𝟙 T) s) (E₁.pointEquivOverHom (𝟙 T) s')).left
        ≫ (μ[E₁.asOver]).left :=
    (congrArg CommaMorphism.left (E₁.pointEquivOverHom_add (𝟙 T) s s')).trans
      (Over.comp_left _ _ _ _ _)
  have hR : (sectionMapIso E₁ E₂ iso hπ s + sectionMapIso E₁ E₂ iso hπ s').1
      = (lift (E₂.pointEquivOverHom (𝟙 T) (sectionMapIso E₁ E₂ iso hπ s))
          (E₂.pointEquivOverHom (𝟙 T) (sectionMapIso E₁ E₂ iso hπ s'))).left
        ≫ (μ[E₂.asOver]).left :=
    (congrArg CommaMorphism.left (E₂.pointEquivOverHom_add (𝟙 T) _ _)).trans
      (Over.comp_left _ _ _ _ _)
  show (s + s').1 ≫ iso.hom = _
  rw [hR]
  exact (congrArg (· ≫ iso.hom) hx).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((lift (E₁.pointEquivOverHom (𝟙 T) s)
        (E₁.pointEquivOverHom (𝟙 T) s')).left ≫ ·) h64l).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (μ[E₂.asOver]).left)
      ((Over.comp_left _ _ _ _ _).symm.trans
        (congrArg CommaMorphism.left
          ((lift_map _ _ _ _).trans
            (congrArg₂ lift hcs hcs')))))

/-- The additive bundle of the section transport. -/
noncomputable def sectionMapIsoHom [IsLocallyNoetherian T] : E₁.Section →+ E₂.Section :=
  AddMonoidHom.mk' (sectionMapIso E₁ E₂ iso hπ) (sectionMapIso_add E₁ E₂ iso hπ hz)

end SectionIso

section PointCongr

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- Points over equal base morphisms, additively. -/
noncomputable def EllipticCurve.pointCongr {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) :
    E.Point g₁ ≃+ E.Point g₂ := h ▸ AddEquiv.refl _

@[simp]
theorem EllipticCurve.pointCongr_coe {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (h : g₁ = g₂)
    (P : E.Point g₁) : (E.pointCongr h P).1 = P.1 := by subst h; rfl

end PointCongr

end FibreBridges

section FibreGeometry

/-! ### The fibre chart of a marked chart at a geometric point (recipe step 1(b))

At a field point `Spec k ⟶ Spec Γ(U)` of a marked chart, the fibre of `Y.curve` is
presented as the model of `W.map (algebraMap Γ(U) k)` (pasting the chart trivialisation
with the base-change square), and enriched to a working record through **[T-A6b]**
(`abelEnrichment_exists`). -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D.U.1) k]

/-- The `Spec` point of the chart ring. -/
noncomputable abbrev specPt : Spec (CommRingCat.of k) ⟶
    Spec (CommRingCat.of ↑Γ(Y.base, D.U.1)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D.U.1) k))

/-- The comparison from the fibre pullback to the chart pullback. -/
noncomputable def Fibre.map :
    pullback Y.curve.π (D.geomPt (D.specPt k)) ⟶ pullback Y.curve.π D.U.1.ι :=
  pullback.map Y.curve.π (D.geomPt (D.specPt k)) Y.curve.π D.U.1.ι (𝟙 _)
    (D.specPt k ≫ D.U.2.isoSpec.inv) (𝟙 _) (by simp)
    (by rw [Category.comp_id, geomPt, Category.assoc])

/-- The comparison square over the chart inclusion is cartesian. -/
theorem Fibre.map_isPullback :
    IsPullback (Fibre.map D k) (pullback.snd Y.curve.π (D.geomPt (D.specPt k)))
      (pullback.snd Y.curve.π D.U.1.ι) (D.specPt k ≫ D.U.2.isoSpec.inv) := by
  have hbig := IsPullback.of_hasPullback Y.curve.π (D.geomPt (D.specPt k))
  have hfst : Fibre.map D k ≫ pullback.fst Y.curve.π D.U.1.ι =
      pullback.fst Y.curve.π (D.geomPt (D.specPt k)) := by
    rw [Fibre.map, pullback.lift_fst, Category.comp_id]
  rw [← hfst] at hbig
  refine IsPullback.of_right hbig ?_ (IsPullback.of_hasPullback Y.curve.π D.U.1.ι)
  rw [Fibre.map, pullback.lift_snd]

/-- The fibre presented over the chart model. -/
noncomputable def Fibre.top :
    pullback Y.curve.π (D.geomPt (D.specPt k)) ⟶ projModel D.W :=
  Fibre.map D k ≫ D.e.hom

/-- The fibre square over the chart model is cartesian. -/
theorem Fibre.top_isPullback :
    IsPullback (Fibre.top D k) (pullback.snd Y.curve.π (D.geomPt (D.specPt k)))
      (projModelπ D.W) (D.specPt k) := by
  have hpaste := (Fibre.map_isPullback D k).paste_horiz
    (IsPullback.of_horiz_isIso ⟨D.heπ⟩)
  have hbase : (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.U.2.isoSpec.hom = D.specPt k := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hbase] at hpaste
  exact hpaste

/-- The fibre of the curve as the model of the base-changed chart curve. -/
noncomputable def Fibre.chartIso :
    pullback Y.curve.π (D.geomPt (D.specPt k)) ≅
      projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) :=
  pullbackChartIso D.W (Fibre.top_isPullback D k)

/-- The zero section of the fibre curve, in chart coordinates. -/
theorem Fibre.zero_comp :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).zero ≫ (Fibre.chartIso D k).hom =
      projModelZero (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) := by
  refine pullbackChartIso_zero D.W (Fibre.top_isPullback D k) _ ?_ ?_
  · exact pullback.lift_snd _ _ _
  · show pullback.lift ((D.geomPt (D.specPt k)) ≫ Y.curve.zero) (𝟙 _) _ ≫
      Fibre.map D k ≫ D.e.hom = _
    have hzmap : pullback.lift ((D.geomPt (D.specPt k)) ≫ Y.curve.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
        Fibre.map D k =
        (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
          (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Fibre.map, pullback.lift_fst, ← Category.assoc,
          pullback.lift_fst, Category.assoc, Category.comp_id, Category.assoc,
          pullback.lift_fst, geomPt]
        simp only [Category.assoc]
      · rw [Category.assoc, Fibre.map, pullback.lift_snd, ← Category.assoc,
          pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.id_comp,
          Category.comp_id]
    have hzU : pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
        D.e.hom = D.U.2.isoSpec.hom ≫ projModelZero D.W := by
      rw [← Iso.inv_comp_eq]
      exact D.hez
    rw [← Category.assoc, hzmap, Category.assoc, hzU, Category.assoc,
      Iso.inv_hom_id_assoc]

/-- The pulled section, as a section of the fibre curve. -/
noncomputable def Fibre.section (P : Y.curve.Section) :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).Section :=
  (EllipticCurve.Point.baseChangeEquiv Y.curve (D.geomPt (D.specPt k)) (𝟙 _)).symm
    (Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k))).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P))

/-- The underlying morphism of the fibre section. -/
theorem Fibre.section_coe (P : Y.curve.Section) :
    (Fibre.section D k P).1 = pullback.lift ((D.geomPt (D.specPt k)) ≫ P.1) (𝟙 _)
      (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]) := by
  have happ2 : EllipticCurve.Point.baseChangeEquiv Y.curve (D.geomPt (D.specPt k)) (𝟙 _)
      (Fibre.section D k P) = Y.curve.pointCongr (Category.id_comp _).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P) := by
    rw [Fibre.section]
    exact AddEquiv.apply_symm_apply _ _
  have h1 := EllipticCurve.Point.baseChangeEquiv_apply_coe Y.curve
    (D.geomPt (D.specPt k)) (𝟙 _) (Fibre.section D k P)
  rw [happ2, EllipticCurve.pointCongr_coe] at h1
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst]
    exact h1.symm
  · rw [pullback.lift_snd]
    exact (Fibre.section D k P).2

set_option backward.isDefEq.respectTransparency false in
/-- **The value chase**: the fibre section, read through the fibre chart and the base-change
morphism, is the chart point composed at the geometric point. -/
theorem Fibre.section_comp_bc (P : Y.curve.Section) :
    (Fibre.section D k P).1 ≫ (Fibre.chartIso D k).hom ≫
      projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      D.specPt k ≫ (D.pt P).1 := by
  have hbc := pullbackChartIso_hom_bc D.W (Fibre.top_isPullback D k)
  have h2 := congrArg (fun m ↦ (Fibre.section D k P).1 ≫ m) hbc
  refine Eq.trans (h2 : _ = _) ?_
  show (Fibre.section D k P).1 ≫ Fibre.map D k ≫ D.e.hom = _
  have hlift : (Fibre.section D k P).1 ≫ Fibre.map D k =
      (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.restrictSection P := by
    have hmf : Fibre.map D k ≫ pullback.fst Y.curve.π D.U.1.ι =
        pullback.fst Y.curve.π (D.geomPt (D.specPt k)) ≫ 𝟙 Y.curve.E :=
      pullback.lift_fst _ _ _
    have hms : Fibre.map D k ≫ pullback.snd Y.curve.π D.U.1.ι =
        pullback.snd Y.curve.π (D.geomPt (D.specPt k)) ≫
          (D.specPt k ≫ D.U.2.isoSpec.inv) :=
      pullback.lift_snd _ _ _
    have hfs1 : (Fibre.section D k P).1 ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k)) =
        D.geomPt (D.specPt k) ≫ P.1 :=
      (congrArg (· ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k)))
        (Fibre.section_coe D k P)).trans (pullback.lift_fst _ _ _)
    have hfs2 : (Fibre.section D k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k)) =
        𝟙 _ := (Fibre.section D k P).2
    have hres1 : D.restrictSection P ≫ pullback.fst Y.curve.π D.U.1.ι =
        D.U.1.ι ≫ P.1 := pullback.lift_fst _ _ _
    have hres2 : D.restrictSection P ≫ pullback.snd Y.curve.π D.U.1.ι = 𝟙 _ :=
      pullback.lift_snd _ _ _
    refine pullback.hom_ext ?_ ?_
    · calc ((Fibre.section D k P).1 ≫ Fibre.map D k) ≫ pullback.fst Y.curve.π D.U.1.ι
          = (Fibre.section D k P).1 ≫ Fibre.map D k ≫ pullback.fst Y.curve.π D.U.1.ι :=
            Category.assoc _ _ _
        _ = (Fibre.section D k P).1 ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k)) ≫
              𝟙 Y.curve.E := congrArg ((Fibre.section D k P).1 ≫ ·) hmf
        _ = ((Fibre.section D k P).1 ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k))) ≫
              𝟙 Y.curve.E := (Category.assoc _ _ _).symm
        _ = (D.geomPt (D.specPt k) ≫ P.1) ≫ 𝟙 Y.curve.E := congrArg (· ≫ 𝟙 _) hfs1
        _ = D.geomPt (D.specPt k) ≫ P.1 := Category.comp_id _
        _ = (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.U.1.ι ≫ P.1 := by
            rw [geomPt]
            simp only [Category.assoc]
        _ = (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.restrictSection P ≫
              pullback.fst Y.curve.π D.U.1.ι := by rw [← hres1]
        _ = ((D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.restrictSection P) ≫
              pullback.fst Y.curve.π D.U.1.ι := (Category.assoc _ _ _).symm
    · calc ((Fibre.section D k P).1 ≫ Fibre.map D k) ≫ pullback.snd Y.curve.π D.U.1.ι
          = (Fibre.section D k P).1 ≫ Fibre.map D k ≫ pullback.snd Y.curve.π D.U.1.ι :=
            Category.assoc _ _ _
        _ = (Fibre.section D k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k)) ≫
              (D.specPt k ≫ D.U.2.isoSpec.inv) := congrArg ((Fibre.section D k P).1 ≫ ·) hms
        _ = ((Fibre.section D k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k))) ≫
              (D.specPt k ≫ D.U.2.isoSpec.inv) := (Category.assoc _ _ _).symm
        _ = 𝟙 _ ≫ (D.specPt k ≫ D.U.2.isoSpec.inv) :=
            congrArg (· ≫ (D.specPt k ≫ D.U.2.isoSpec.inv)) hfs2
        _ = D.specPt k ≫ D.U.2.isoSpec.inv := Category.id_comp _
        _ = (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.restrictSection P ≫
              pullback.snd Y.curve.π D.U.1.ι := by rw [← hres2]
        _ = ((D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.restrictSection P) ≫
              pullback.snd Y.curve.π D.U.1.ι := (Category.assoc _ _ _).symm
  rw [← Category.assoc, hlift, pt_coe]
  simp only [Category.assoc]

end MarkedChartData

end FibreGeometry

section FibreEnrichment

/-! ### The fibre working record and the order bridge ([T-A6b] + [T-B6′] trails) -/

/-- `eqToHom` transport of the structure morphism along a geometric-record equality. -/
theorem eqToGeom_π' {S : Scheme.{u}} {G₁ G₂ : EllipticCurveGeom S} (h : G₁ = G₂) :
    G₁.π = eqToHom (congrArg EllipticCurveGeom.E h) ≫ G₂.π := by
  subst h; simp

/-- `eqToHom` transport of the zero section along a geometric-record equality. -/
theorem eqToGeom_zero' {S : Scheme.{u}} {G₁ G₂ : EllipticCurveGeom S} (h : G₁ = G₂) :
    G₁.zero = G₂.zero ≫ eqToHom (congrArg EllipticCurveGeom.E h).symm := by
  subst h; simp

/-- Affine points over equal curves, additively. -/
noncomputable def affinePointCongr {k : Type u} [Field k] [DecidableEq k]
    {V₁ V₂ : WeierstrassCurve k} (h : V₁ = V₂) :
    V₁.toAffine.Point ≃+ V₂.toAffine.Point := h ▸ AddEquiv.refl _

theorem affinePointCongr_some {k : Type u} [Field k] [DecidableEq k]
    {V₁ V₂ : WeierstrassCurve k} (h : V₁ = V₂) (x y : k)
    (hns : V₁.toAffine.Nonsingular x y) :
    affinePointCongr h (WeierstrassCurve.Affine.Point.some x y hns) =
      WeierstrassCurve.Affine.Point.some x y (h ▸ hns) := by subst h; rfl

/-- Chart evaluation only depends on the point. -/
theorem ZChart.eval_congr {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    {g g' : SpecPoints (projModel W) (projModelπ W) K} (h : g = g')
    (hZ : InZChart W g) (hZ' : InZChart W g') (a : W.toAffine.CoordinateRing) :
    ZChart.eval W g hZ a = ZChart.eval W g' hZ' a := by subst h; rfl

/-- The chart-solution coordinates are the chart-ring homomorphism at the chart
coordinates (`coord_val`, over any ring). -/
theorem chartSolution_val {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g)
    (j : {j : Fin 3 // j ≠ 2}) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 j =
      ZChart.hom W g hZ (chartCoordEquiv W 2
        (Ideal.Quotient.mk _ (MvPolynomial.X j))) := rfl

/-- The chart-solution `x`-coordinate is the `coordX`-evaluation. -/
theorem chartSolution_zero_eq_eval {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨0, by decide⟩ =
      ZChart.eval W g hZ (coordX W) := by
  rw [chartSolution_val, ZChart.eval_coordX]
  exact DFunLike.congr_arg (ZChart.hom W g hZ)
    (chartCoordEquiv_mk_X W 2 ⟨0, by decide⟩)

/-- The chart-solution `y`-coordinate is the `coordY`-evaluation. -/
theorem chartSolution_one_eq_eval {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨1, by decide⟩ =
      ZChart.eval W g hZ (coordY W) := by
  rw [chartSolution_val, ZChart.eval_coordY]
  exact DFunLike.congr_arg (ZChart.hom W g hZ)
    (chartCoordEquiv_mk_X W 2 ⟨1, by decide⟩)

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D.U.1) k]

instance : (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).IsElliptic :=
  inferInstanceAs ((D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).IsElliptic)

/-- The geometric record of the fibre model. -/
noncomputable def Fibre.geom : EllipticCurveGeom (Spec (CommRingCat.of k)) where
  E := projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
  π := projModelπ _
  zero := projModelZero _
  zero_π := projModelZero_projModelπ _
  smooth := projModel_smooth _
  proper := projModelπ_isProper _
  localModel := projModel_locallyWeierstrass _

/-- The fibre working record: the mulOver-based model record (Y1-CLOSER S3 — the [T-A6b]
gate `abelEnrichment_exists` is NO LONGER on this trail: the fibre geometry is a global
model). -/
noncomputable def Fibre.curve : EllipticCurve (Spec (CommRingCat.of k)) :=
  modelEllipticCurve (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))

/-- **Opaque interface** for the fibre record: its geometry is the fibre model. -/
theorem Fibre.curve_geom : (Fibre.curve D k).toEllipticCurveGeom = Fibre.geom D k :=
  rfl

theorem Fibre.curve_E_eq : (Fibre.curve D k).E =
    projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) :=
  congrArg EllipticCurveGeom.E (Fibre.curve_geom D k)

theorem Fibre.curve_π_eq : (Fibre.curve D k).π = eqToHom (Fibre.curve_E_eq D k) ≫
    projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) :=
  eqToGeom_π' (Fibre.curve_geom D k)

theorem Fibre.curve_zero_eq : (Fibre.curve D k).zero =
    projModelZero (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) ≫
      eqToHom (Fibre.curve_E_eq D k).symm :=
  eqToGeom_zero' (Fibre.curve_geom D k)

/-- The zero pin of the fibre record (the `hz` hypothesis of `geomFibrePointAddEquiv`,
B2 EVENT #3): the record's zero section is the model zero across `Fibre.curve_E_eq`. -/
theorem Fibre.curve_hz : (Fibre.curve D k).zero ≫ eqToHom (Fibre.curve_E_eq D k) =
    projModelZero (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) := by
  rw [Fibre.curve_zero_eq D k, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The pointed comparison from the curve fibre onto the fibre record's total space. -/
noncomputable def Fibre.curveIso :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).E ≅ (Fibre.curve D k).E :=
  Fibre.chartIso D k ≪≫ eqToIso (Fibre.curve_E_eq D k).symm

set_option backward.isDefEq.respectTransparency false in
theorem Fibre.curveIso_π : (Fibre.curveIso D k).hom ≫ (Fibre.curve D k).π =
    (Y.curve.baseChange (D.geomPt (D.specPt k))).π := by
  rw [Fibre.curveIso, Iso.trans_hom, eqToIso.hom, Fibre.curve_π_eq D k]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact pullbackChartIso_hom_π D.W (Fibre.top_isPullback D k)

set_option backward.isDefEq.respectTransparency false in
theorem Fibre.curveIso_zero :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).zero ≫ (Fibre.curveIso D k).hom =
      (Fibre.curve D k).zero := by
  rw [Fibre.curveIso, Iso.trans_hom, eqToIso.hom, Fibre.curve_zero_eq D k, ← Category.assoc]
  exact congrArg (· ≫ eqToHom (Fibre.curve_E_eq D k).symm) (Fibre.zero_comp D k)

set_option backward.isDefEq.respectTransparency false in
/-- **(B2-ii fibre bridge, [T-A6b] + [T-B6′])** A nowhere-small-order section satisfies the
T-E1 order hypothesis in every marked chart: a dying small multiple of the chart coordinates
at a geometric point would transport, through the fibre record and the geometric-fibre group
comparison, to a dying small multiple of the pulled section. -/
theorem pt_hord (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    NowhereOrderLEThree D.W
      (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W))
      (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W)) := by
  classical
  refine NowhereOrderLEThree.of_forall_geom D.W _ _
    (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) ?_
  intro k _ _ _ _ hns a ha0 ha3 hcontra
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  -- the transported section and its image point of the fibre model
  set s₁ : (Fibre.curve D k).Section :=
    sectionMapIso _ (Fibre.curve D k) (Fibre.curveIso D k) (Fibre.curveIso_π D k)
      (Fibre.section D k P) with hs₁
  have hgeom : (𝟙 (Spec (CommRingCat.of k))) = EllipticCurve.geomPoint k k := by
    rw [EllipticCurve.geomPoint, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  set sk : (Fibre.curve D k).Point (EllipticCurve.geomPoint k k) :=
    (Fibre.curve D k).pointCongr hgeom s₁ with hsk
  -- its model point
  set gfin : SpecPoints (projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))
      (projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) k :=
    EllipticCurve.pointSpecPointsEquiv (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (Fibre.curve D k) (Fibre.curve_E_eq D k) (Fibre.curve_π_eq D k) k sk with hgfin
  have hgfin1 : gfin.1 = (Fibre.section D k P).1 ≫ (Fibre.chartIso D k).hom := by
    show (sk.1 ≫ eqToHom (Fibre.curve_E_eq D k)) = _
    rw [hsk, EllipticCurve.pointCongr_coe, hs₁]
    show ((Fibre.section D k P).1 ≫ (Fibre.curveIso D k).hom) ≫ _ = _
    rw [Fibre.curveIso, Iso.trans_hom, eqToIso.hom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  -- the model point composed to the chart model is the chart point at the geometric point
  have hcomp : gfin.1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      D.specPt k ≫ (D.pt P).1 := by
    rw [hgfin1, Category.assoc]
    exact Fibre.section_comp_bc D k P
  -- membership in the Z-chart and the coordinate evaluations
  have hψcomp : (algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (algebraMap ↑Γ(Y.base, D.U.1) ↑Γ(Y.base, D.U.1)) = algebraMap ↑Γ(Y.base, D.U.1) k := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  have hZfin : InZChart (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) gfin := by
    refine ZChart.mem_of_comp_baseChange D.W gfin
      (Spec.map (CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
        (ZChart.hom D.W (D.pt P) (D.pt_mem_zChart P hP))))) ?_
    rw [show CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
        (ZChart.hom D.W (D.pt P) (D.pt_mem_zChart P hP))) =
        CommRingCat.ofHom (ZChart.hom D.W (D.pt P) (D.pt_mem_zChart P hP)) ≫
          CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D.U.1) k) from
      CommRingCat.ofHom_comp _ _]
    rw [Spec.map_comp, Category.assoc, ZChart.spec_map_hom_awayι, hcomp]
  have hbcpt : specPointBaseChange D.W gfin =
      specPointComp D.W (D.pt P) (algebraMap ↑Γ(Y.base, D.U.1) k) hψcomp := by
    refine Subtype.ext ?_
    show gfin.1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W = _
    rw [hcomp]
    rfl
  have hevalX : ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) gfin hZfin
      (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) := by
    rw [← ZChart.BaseChange.eval_coordX D.W gfin hZfin,
      ZChart.eval_congr D.W hbcpt (ZChart.BaseChange.mem D.W gfin hZfin)
        (ZChart.mem_specPointComp D.W (D.pt P) (D.pt_mem_zChart P hP) _ hψcomp),
      ZChart.eval_specPointComp]
  have hevalY : ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) gfin hZfin
      (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W)) := by
    rw [← ZChart.BaseChange.eval_coordY D.W gfin hZfin,
      ZChart.eval_congr D.W hbcpt (ZChart.BaseChange.mem D.W gfin hZfin)
        (ZChart.mem_specPointComp D.W (D.pt P) (D.pt_mem_zChart P hP) _ hψcomp),
      ZChart.eval_specPointComp]
  -- the base-changed curve over `k` is the mapped curve
  have hWk : (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).baseChange k =
      D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k) := by
    show (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).map (algebraMap k k) = _
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have hns2 : ((D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).baseChange k).toAffine.Nonsingular
      (algebraMap ↑Γ(Y.base, D.U.1) k
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)))
      (algebraMap ↑Γ(Y.base, D.U.1) k
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))) := hWk.symm ▸ hns
  -- the image of the transported point is the marked affine point
  have hval : EllipticCurve.geomFibrePointAddEquiv
      (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.curve D k)
      (Fibre.curve_E_eq D k) (Fibre.curve_π_eq D k) (Fibre.curve_hz D k) k sk =
      WeierstrassCurve.Affine.Point.some _ _ hns2 := by
    rw [EllipticCurve.geomFibrePointAddEquiv_apply]
    exact projModelPointsEquiv_some _ k gfin hZfin _ _ hns2
      (hevalX.symm.trans (chartSolution_zero_eq_eval _ gfin hZfin).symm)
      (hevalY.symm.trans (chartSolution_one_eq_eval _ gfin hZfin).symm)
  -- transport the contradiction hypothesis backwards through the additive chain
  have hcontra2 : (a : ℤ) • (WeierstrassCurve.Affine.Point.some _ _ hns2) = 0 :=
    (congrArg ((a : ℤ) • ·) (affinePointCongr_some hWk.symm _ _ hns).symm).trans
      ((map_zsmul (affinePointCongr hWk.symm) (a : ℤ) _).symm.trans
        ((congrArg (affinePointCongr hWk.symm) hcontra).trans
          (map_zero (affinePointCongr hWk.symm))))
  have hsk0 : (a : ℤ) • sk = 0 := by
    refine (EllipticCurve.geomFibrePointAddEquiv
      (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.curve D k)
      (Fibre.curve_E_eq D k) (Fibre.curve_π_eq D k) (Fibre.curve_hz D k) k).injective ?_
    refine (map_zsmul _ (a : ℤ) sk).trans (Eq.trans ?_ (map_zero _).symm)
    exact (congrArg ((a : ℤ) • ·) hval).trans hcontra2
  have hs₁0 : (a : ℤ) • s₁ = 0 := by
    refine ((Fibre.curve D k).pointCongr hgeom).injective ?_
    refine (map_zsmul _ (a : ℤ) s₁).trans (Eq.trans ?_ (map_zero _).symm)
    rw [← hsk]
    exact hsk0
  have hfs0 : (a : ℤ) • Fibre.section D k P = 0 := by
    refine sectionMapIso_injective (Y.curve.baseChange (D.geomPt (D.specPt k)))
      (Fibre.curve D k) (Fibre.curveIso D k) (Fibre.curveIso_π D k) ?_
    have hzs := map_zsmul (sectionMapIsoHom (Y.curve.baseChange (D.geomPt (D.specPt k)))
      (Fibre.curve D k) (Fibre.curveIso D k) (Fibre.curveIso_π D k) (Fibre.curveIso_zero D k))
      (a : ℤ) (Fibre.section D k P)
    have hz0 := map_zero (sectionMapIsoHom (Y.curve.baseChange (D.geomPt (D.specPt k)))
      (Fibre.curve D k) (Fibre.curveIso D k) (Fibre.curveIso_π D k) (Fibre.curveIso_zero D k))
    exact hzs.trans (hs₁0.trans hz0.symm)
  have happ2 : EllipticCurve.Point.baseChangeEquiv Y.curve (D.geomPt (D.specPt k)) (𝟙 _)
      (Fibre.section D k P) = Y.curve.pointCongr (Category.id_comp _).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P) := by
    rw [Fibre.section]
    exact AddEquiv.apply_symm_apply _ _
  have hpc0 : (a : ℤ) • Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k))).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P) = 0 :=
    ((congrArg ((a : ℤ) • ·) happ2).symm.trans
      -- `map_zsmul` on the bare `≃+` stalls the `AddMonoidHomClass` search; go through
      -- `toAddMonoidHom`, where the instance is immediate.
      ((AddMonoidHom.map_zsmul (EllipticCurve.Point.baseChangeEquiv Y.curve
        (D.geomPt (D.specPt k)) (𝟙 _)).toAddMonoidHom (a : ℤ)
          (Fibre.section D k P)).symm.trans
        ((congrArg (EllipticCurve.Point.baseChangeEquiv Y.curve
          (D.geomPt (D.specPt k)) (𝟙 _)) hfs0).trans
          ((EllipticCurve.Point.baseChangeEquiv Y.curve
            (D.geomPt (D.specPt k)) (𝟙 _)).toAddMonoidHom.map_zero))))
  have hpull0 : (a : ℤ) • EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P = 0 := by
    have h2 := (AddMonoidHom.map_zsmul (Y.curve.pointCongr
      (Category.id_comp (D.geomPt (D.specPt k)))).toAddMonoidHom (a : ℤ) _).symm.trans
      ((congrArg (Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k)))) hpc0).trans
        ((Y.curve.pointCongr
          (Category.id_comp (D.geomPt (D.specPt k)))).toAddMonoidHom.map_zero))
    have h3 : Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k)))
        (Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k))).symm
          (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P)) =
        EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P := by
      refine Subtype.ext ?_
      rw [EllipticCurve.pointCongr_coe, EllipticCurve.pointCongr_coe]
    rw [← h3]
    exact h2
  exact hP k (D.geomPt (D.specPt k)) a ha0 ha3 hpull0

end MarkedChartData

end FibreEnrichment

section LocalClassifyingData

/-! ### The local classifying data of a marked chart (recipe step 2)

Composing the chart trivialisation with the landed `projTateMap` package produces, for each
marked chart, the local Tate-base map and the local top map with their cartesian square,
zero-compatibility and marking-compatibility — the inputs of the v10.96–v10.100 gluing
handles. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  [Algebra R ↑Γ(Y.base, D.U.1)]
  (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)

/-- The local Tate-base map of a marked chart. -/
noncomputable def baseMap : D.U.1.toScheme ⟶ tateBase R :=
  D.U.2.isoSpec.hom ≫ TateAtlas.Point.baseSpecMap R D.W _ _
    (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)

/-- The local top map of a marked chart. -/
noncomputable def topMap : pullback Y.curve.π D.U.1.ι ⟶ projModel (tateCurveLocOver R) :=
  D.e.hom ≫ projTateMap R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP)

/-- The local square is cartesian. -/
theorem topMap_isPullback :
    IsPullback (D.topMap P hP) (pullback.snd Y.curve.π D.U.1.ι)
      (projModelπ (tateCurveLocOver R)) (D.baseMap P hP) :=
  (IsPullback.of_horiz_isIso ⟨D.heπ⟩).paste_horiz
    (projTateMap_isPullback R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP))

/-- The local square is pointed. -/
theorem topMap_zero :
    pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
      (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
      D.topMap P hP = D.baseMap P hP ≫ projModelZero (tateCurveLocOver R) := by
  have h1 := congrArg (fun m ↦ D.U.2.isoSpec.hom ≫ m) D.hez
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h1
  simp only [topMap, baseMap, Category.assoc]
  rw [← Category.assoc, h1, Category.assoc,
    projTateMap_zero R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP)]

/-- The local square carries the section to the atlas marking. -/
theorem topMap_marking :
    D.restrictSection P ≫ D.topMap P hP = D.baseMap P hP ≫ tateP0mor R := by
  have h1 := congrArg (fun m ↦ D.U.2.isoSpec.hom ≫ m) (D.pt_coe P)
  simp only [Iso.hom_inv_id_assoc] at h1
  simp only [topMap, baseMap, Category.assoc]
  rw [← Category.assoc, ← h1, Category.assoc,
    projTateMap_marking R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP)]

end MarkedChartData

end LocalClassifyingData

section TateAtlasNaturality

/-! ### Naturality of the pointed atlas map in the chart ring (recipe step 3 substrate)

`TateAtlas.Point.baseSpecMap` is natural under change of the chart ring: composing with
`Spec` of a ring map computes the atlas map of the mapped chart at the mapped point.
Together with the ENGINE this drives the overlap agreement of the local classifying
maps on affine test points. -/

variable {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B)

/-- Tate-normality is preserved by ring maps. -/
theorem _root_.WeierstrassCurve.IsTateNormal.map {W : WeierstrassCurve A}
    (hW : W.IsTateNormal) : (W.map ψ).IsTateNormal := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, hW.1, hW.2.1, hW.2.2, map_zero]

/-- The nowhere-small-order condition is preserved by ring maps. -/
theorem NowhereOrderLEThree.map {W : WeierstrassCurve A} {x y : A}
    (hord : NowhereOrderLEThree W x y) :
    NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y) := by
  have h2 : ((W.map ψ).Ψ 2).evalEval (ψ x) (ψ y) = ψ ((W.Ψ 2).evalEval x y) := by
    rw [WeierstrassCurve.map_Ψ, Polynomial.map_mapRingHom_evalEval]
  have h3 : ((W.map ψ).Ψ 3).evalEval (ψ x) (ψ y) = ψ ((W.Ψ 3).evalEval x y) := by
    rw [WeierstrassCurve.map_Ψ, Polynomial.map_mapRingHom_evalEval]
  show IsUnit _
  rw [h2, h3, ← map_mul]
  exact (show IsUnit _ from hord).map ψ

/-- T-E1 normalisation is natural in the chart ring. -/
theorem TateAtlas.TateNormal.variableChange_map (W : WeierstrassCurve A) [W.IsElliptic]
    [(W.map ψ).IsElliptic] (x y : A) (hxy : W.toAffine.Equation x y)
    (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    (TateAtlas.TateNormal.variableChange W x y hxy hord).map ψ =
      TateAtlas.TateNormal.variableChange (W.map ψ) (ψ x) (ψ y) hxy' hord' :=
  TateAtlas.TateNormal.variableChange_unique (W.map ψ) (ψ x) (ψ y) hxy' hord' _
    ⟨by rw [WeierstrassCurve.map_variableChange]
        exact (TateAtlas.TateNormal.variableChange_isTateNormal W x y hxy hord).map ψ,
     by simp, by simp⟩

/-- The T-E1 normalised curve is natural in the chart ring. -/
theorem TateAtlas.TateNormal.variableChange_smul_map (W : WeierstrassCurve A) [W.IsElliptic]
    [(W.map ψ).IsElliptic] (x y : A) (hxy : W.toAffine.Equation x y)
    (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    TateAtlas.TateNormal.variableChange (W.map ψ) (ψ x) (ψ y) hxy' hord' • (W.map ψ) =
      ((TateAtlas.TateNormal.variableChange W x y hxy hord) • W).map ψ := by
  rw [← TateAtlas.TateNormal.variableChange_map ψ W x y hxy hord hxy' hord',
    WeierstrassCurve.map_variableChange]

/-- The pointed atlas ring map is natural in the chart ring. -/
theorem TateAtlas.Point.ringOverLift_comp (R : CommRingCat.{u}) [Algebra ↑R A] [Algebra ↑R B]
    (hψ : ψ.comp (algebraMap ↑R A) = algebraMap ↑R B)
    (W : WeierstrassCurve A) [W.IsElliptic] [(W.map ψ).IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    ψ.comp (TateAtlas.Point.ringOverLift R W x y hxy hord) =
      TateAtlas.Point.ringOverLift R (W.map ψ) (ψ x) (ψ y) hxy' hord' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tateCurveOver R).Δ)
  apply MvPolynomial.ringHom_ext
  · intro r
    change ψ (TateAtlas.Point.ringOverAlgLift R W x y hxy hord
        (algebraMap ↑R (tateRingOver R) r)) =
      TateAtlas.Point.ringOverAlgLift R (W.map ψ) (ψ x) (ψ y) hxy' hord'
        (algebraMap ↑R (tateRingOver R) r)
    rw [AlgHom.commutes, AlgHom.commutes]
    exact RingHom.congr_fun hψ r
  · intro i
    fin_cases i
    · change ψ (TateAtlas.Point.ringOverAlgLift R W x y hxy hord
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 0))) =
        TateAtlas.Point.ringOverAlgLift R (W.map ψ) (ψ x) (ψ y) hxy' hord'
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 0))
      rw [TateAtlas.Point.ringOverAlgLift_X_zero, TateAtlas.Point.ringOverAlgLift_X_zero,
        TateAtlas.TateNormal.variableChange_smul_map ψ W x y hxy hord hxy' hord',
        WeierstrassCurve.map_a₁]
    · change ψ (TateAtlas.Point.ringOverAlgLift R W x y hxy hord
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 1))) =
        TateAtlas.Point.ringOverAlgLift R (W.map ψ) (ψ x) (ψ y) hxy' hord'
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 1))
      rw [TateAtlas.Point.ringOverAlgLift_X_one, TateAtlas.Point.ringOverAlgLift_X_one,
        TateAtlas.TateNormal.variableChange_smul_map ψ W x y hxy hord hxy' hord',
        WeierstrassCurve.map_a₂]

/-- **Affine naturality of the classifying base map**: composing the pointed atlas map with
`Spec` of a chart-ring map gives the pointed atlas map of the mapped chart. -/
theorem TateAtlas.Point.baseSpecMap_naturality
    (R : CommRingCat.{u}) [Algebra ↑R A] [Algebra ↑R B]
    (hψ : ψ.comp (algebraMap ↑R A) = algebraMap ↑R B)
    (W : WeierstrassCurve A) [W.IsElliptic] [(W.map ψ).IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    Spec.map (CommRingCat.ofHom ψ) ≫ TateAtlas.Point.baseSpecMap R W x y hxy hord =
      TateAtlas.Point.baseSpecMap R (W.map ψ) (ψ x) (ψ y) hxy' hord' := by
  show Spec.map (CommRingCat.ofHom ψ) ≫
    Spec.map (CommRingCat.ofHom (TateAtlas.Point.ringOverLift R W x y hxy hord)) =
    Spec.map (CommRingCat.ofHom (TateAtlas.Point.ringOverLift R (W.map ψ) (ψ x) (ψ y) hxy' hord'))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    TateAtlas.Point.ringOverLift_comp ψ R hψ W x y hxy hord hxy' hord']

/-- Congruence for `TateAtlas.Point.baseSpecMap` in the marked point. -/
theorem TateAtlas.Point.baseSpecMap_congr (R : CommRingCat.{u}) [Algebra ↑R A]
    (W : WeierstrassCurve A) [W.IsElliptic] {x y x' y' : A} (hx : x = x') (hy : y = y')
    (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (hxy' : W.toAffine.Equation x' y') (hord' : NowhereOrderLEThree W x' y') :
    TateAtlas.Point.baseSpecMap R W x y hxy hord =
      TateAtlas.Point.baseSpecMap R W x' y' hxy' hord' := by
  subst hx
  subst hy
  rfl

end TateAtlasNaturality

section ChartAlgebra

/-! ### The chart ring as an `R`-algebra and the over-`Spec R` compatibility -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)

/-- The chart ring as an `R`-algebra through the structure morphism. -/
@[reducible]
noncomputable def chartAlgebra : Algebra ↑R ↑Γ(Y.base, D.U.1) :=
  (((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appLE ⊤ D.U.1 (by simp)).hom).toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The defining compatibility of `chartAlgebra` with the structure morphism. -/
theorem chartAlgebra_compatible :
    letI := D.chartAlgebra
    D.U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.1.ι ≫ Y.structMap := by
  letI := D.chartAlgebra
  have halg : CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1)) =
      (Scheme.ΓSpecIso R).inv ≫ Y.structMap.appLE ⊤ D.U.1 (by simp) :=
    CommRingCat.ofHom_hom _
  have hfromTop : Spec.map ((Scheme.ΓSpecIso R).inv) =
      (isAffineOpen_top (Spec R)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hbig := IsAffineOpen.SpecMap_appLE_fromSpec Y.structMap
    (isAffineOpen_top (Spec R)) D.U.2 (by simp)
  rw [halg, Spec.map_comp, hfromTop, hbig, ← Category.assoc,
    IsAffineOpen.isoSpec_hom_fromSpec]

/-- With the structure algebra on the chart ring, the local classifying base map lies
over `Spec R` relative to the chart inclusion. -/
theorem baseMap_over (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    [Algebra ↑R ↑Γ(Y.base, D.U.1)]
    (halg : D.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.1.ι ≫ Y.structMap) :
    D.baseMap P hP ≫ tateStructMap R = D.U.1.ι ≫ Y.structMap := by
  rw [baseMap, Category.assoc, TateAtlas.Point.baseSpecMap_tateStructMap, halg]

end MarkedChartData

end ChartAlgebra

section FibrePoint

/-! ### The restricted section as a `Spec`-point of the fibre model (recipe step 3)

Over any chart-ring algebra `k` (not just fields), the restricted section defines a point
of the base-changed chart model lying in its `Z`-chart, with coordinate evaluations the
algebra images of the chart-point evaluations.  This is the affine test-point interface
for the overlap agreement of the local classifying maps. -/

/-- Composing with the identity algebra map is the algebra map. -/
theorem AlgebraMap.comp_self {A k : Type u} [CommRing A] [CommRing k]
    [Algebra A k] :
    (algebraMap A k).comp (algebraMap A A) = algebraMap A k := by
  rw [Algebra.algebraMap_self, RingHom.comp_id]

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D.U.1) k]

set_option backward.isDefEq.respectTransparency false in
/-- The restricted section as a point of the fibre model. -/
noncomputable def Fibre.pt (P : Y.curve.Section) :
    SpecPoints (projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))
      (projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) k :=
  ⟨(Fibre.section D k P).1 ≫ (Fibre.chartIso D k).hom, by
    have h1 : (Fibre.section D k P).1 ≫ ((Fibre.chartIso D k).hom ≫
        projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        (Fibre.section D k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k)) :=
      congrArg ((Fibre.section D k P).1 ≫ ·)
        (pullbackChartIso_hom_π D.W (Fibre.top_isPullback D k))
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap k k)) =
        𝟙 (Spec (CommRingCat.of k)) := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rw [Category.assoc, h2]
    exact h1.trans (Fibre.section D k P).2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The fibre point maps to the chart point at the algebra point (the value chase in
`SpecPoints` form). -/
theorem Fibre.pt_comp_bc (P : Y.curve.Section) :
    (Fibre.pt D k P).1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      D.specPt k ≫ (D.pt P).1 := by
  show ((Fibre.section D k P).1 ≫ (Fibre.chartIso D k).hom) ≫ _ = _
  rw [Category.assoc]
  exact Fibre.section_comp_bc D k P

/-- The fibre point lies in the `Z`-chart. -/
theorem Fibre.pt_mem_zChart (P : Y.curve.Section) (hZ : InZChart D.W (D.pt P)) :
    InZChart (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) := by
  refine ZChart.mem_of_comp_baseChange D.W (Fibre.pt D k P)
    (Spec.map (CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (ZChart.hom D.W (D.pt P) hZ)))) ?_
  rw [show CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (ZChart.hom D.W (D.pt P) hZ)) =
      CommRingCat.ofHom (ZChart.hom D.W (D.pt P) hZ) ≫
        CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D.U.1) k) from
    CommRingCat.ofHom_comp _ _]
  rw [Spec.map_comp, Category.assoc, ZChart.spec_map_hom_awayι, Fibre.pt_comp_bc]

/-- The base-changed fibre point is the composed chart point. -/
theorem Fibre.specPointBaseChange_pt (P : Y.curve.Section) :
    specPointBaseChange D.W (Fibre.pt D k P) =
      specPointComp D.W (D.pt P) (algebraMap ↑Γ(Y.base, D.U.1) k)
        AlgebraMap.comp_self := by
  refine Subtype.ext ?_
  show (Fibre.pt D k P).1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W = _
  rw [Fibre.pt_comp_bc]
  rfl

/-- The fibre point evaluates to the algebra image of the chart evaluation (`x`-side). -/
theorem Fibre.eval_pt_coordX (P : Y.curve.Section) (hZ : InZChart D.W (D.pt P)) :
    ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P hZ) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k (ZChart.eval D.W (D.pt P) hZ (coordX D.W)) := by
  rw [← ZChart.BaseChange.eval_coordX D.W (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P hZ),
    ZChart.eval_congr D.W (Fibre.specPointBaseChange_pt D k P)
      (ZChart.BaseChange.mem D.W _ _)
      (ZChart.mem_specPointComp D.W (D.pt P) hZ _ _),
    ZChart.eval_specPointComp]
  exact Fibre.pt_mem_zChart D k P hZ

/-- The fibre point evaluates to the algebra image of the chart evaluation (`y`-side). -/
theorem Fibre.eval_pt_coordY (P : Y.curve.Section) (hZ : InZChart D.W (D.pt P)) :
    ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P hZ) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k (ZChart.eval D.W (D.pt P) hZ (coordY D.W)) := by
  rw [← ZChart.BaseChange.eval_coordY D.W (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P hZ),
    ZChart.eval_congr D.W (Fibre.specPointBaseChange_pt D k P)
      (ZChart.BaseChange.mem D.W _ _)
      (ZChart.mem_specPointComp D.W (D.pt P) hZ _ _),
    ZChart.eval_specPointComp]
  exact Fibre.pt_mem_zChart D k P hZ

/-- The fibre point inherits the nowhere-small-order condition. -/
theorem Fibre.pt_hord (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    NowhereOrderLEThree (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))
        (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))))
      (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))
        (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) := by
  rw [Fibre.eval_pt_coordX D k P (D.pt_mem_zChart P hP),
    Fibre.eval_pt_coordY D k P (D.pt_mem_zChart P hP)]
  exact (D.pt_hord P hP).map (algebraMap ↑Γ(Y.base, D.U.1) k)

end MarkedChartData

end FibrePoint

section OverlapAgreement

/-! ### Overlap agreement of the local classifying maps (recipe step 3)

Two marked charts whose test points agree in the base induce a pointed comparison of
their fibre models carrying one fibre point to the other; the marked-chart comparison
ENGINE then forces the two pointed atlas maps to agree.  This is Loeffler's "local
uniqueness gives global existence" at the affine test-point level. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D₁ D₂ : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D₁.U.1) k] [Algebra ↑Γ(Y.base, D₂.U.1) k]
  (hgeom : D₁.geomPt (D₁.specPt k) = D₂.geomPt (D₂.specPt k))

/-- The two fibre models over an agreeing test point are canonically isomorphic. -/
noncomputable def Fibre.modelIso :
    projModel (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≅
      projModel (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) :=
  (Fibre.chartIso D₁ k).symm ≪≫ pullback.congrHom rfl hgeom ≪≫ Fibre.chartIso D₂ k

/-- The fibre-model comparison respects the structure maps. -/
theorem Fibre.modelIso_π :
    (Fibre.modelIso D₁ D₂ k hgeom).hom ≫
      projModelπ (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) =
      projModelπ (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) := by
  have h1 : (Fibre.chartIso D₂ k).hom ≫
      projModelπ (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) =
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) :=
    pullbackChartIso_hom_π D₂.W (Fibre.top_isPullback D₂ k)
  have h2 : (pullback.congrHom rfl hgeom).hom ≫
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have h3 : (Fibre.chartIso D₁ k).inv ≫
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) =
      projModelπ (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) := by
    rw [Iso.inv_comp_eq]
    exact (pullbackChartIso_hom_π D₁.W (Fibre.top_isPullback D₁ k)).symm
  rw [Fibre.modelIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  refine Eq.trans (congrArg (fun m ↦ (Fibre.chartIso D₁ k).inv ≫ m) ?_) h3
  exact Eq.trans (congrArg (fun m ↦ (pullback.congrHom rfl hgeom).hom ≫ m) h1) h2

set_option backward.isDefEq.respectTransparency false in
/-- The fibre-model comparison is pointed. -/
theorem Fibre.modelIso_zero :
    projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
      (Fibre.modelIso D₁ D₂ k hgeom).hom =
      projModelZero (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) := by
  have h1 : projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
      (Fibre.chartIso D₁ k).inv =
      (Y.curve.baseChange (D₁.geomPt (D₁.specPt k))).zero := by
    rw [Iso.comp_inv_eq]
    exact (Fibre.zero_comp D₁ k).symm
  have e1 := congrHom_hom_comp_fst Y.curve.π hgeom
  have e2 := congrHom_hom_comp_snd Y.curve.π hgeom
  have hz12 : (Y.curve.baseChange (D₁.geomPt (D₁.specPt k))).zero ≫
      (pullback.congrHom rfl hgeom).hom =
      (Y.curve.baseChange (D₂.geomPt (D₂.specPt k))).zero := by
    show pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫ _ =
      pullback.lift (D₂.geomPt (D₂.specPt k) ≫ Y.curve.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp])
    refine pullback.hom_ext ?_ ?_
    · calc (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            (pullback.congrHom rfl hgeom).hom) ≫
            pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k))
          = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            ((pullback.congrHom rfl hgeom).hom ≫
              pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k))) := Category.assoc _ _ _
        _ = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) :=
              congrArg (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫ ·) e1
        _ = D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero := pullback.lift_fst _ _ _
        _ = D₂.geomPt (D₂.specPt k) ≫ Y.curve.zero := congrArg (· ≫ Y.curve.zero) hgeom
        _ = pullback.lift (D₂.geomPt (D₂.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) := (pullback.lift_fst _ _ _).symm
    · calc (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            (pullback.congrHom rfl hgeom).hom) ≫
            pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k))
          = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            ((pullback.congrHom rfl hgeom).hom ≫
              pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k))) := Category.assoc _ _ _
        _ = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) :=
              congrArg (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫ ·) e2
        _ = 𝟙 _ := pullback.lift_snd _ _ _
        _ = pullback.lift (D₂.geomPt (D₂.specPt k) ≫ Y.curve.zero) (𝟙 _) _ ≫
            pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) := (pullback.lift_snd _ _ _).symm
  rw [Fibre.modelIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
      ((Fibre.chartIso D₁ k).inv ≫ (pullback.congrHom rfl hgeom).hom ≫
        (Fibre.chartIso D₂ k).hom)
      = (projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
          (Fibre.chartIso D₁ k).inv) ≫ (pullback.congrHom rfl hgeom).hom ≫
          (Fibre.chartIso D₂ k).hom := (Category.assoc _ _ _).symm
    _ = (Y.curve.baseChange (D₁.geomPt (D₁.specPt k))).zero ≫
          (pullback.congrHom rfl hgeom).hom ≫ (Fibre.chartIso D₂ k).hom :=
        congrArg (· ≫ (pullback.congrHom rfl hgeom).hom ≫ (Fibre.chartIso D₂ k).hom) h1
    _ = ((Y.curve.baseChange (D₁.geomPt (D₁.specPt k))).zero ≫
          (pullback.congrHom rfl hgeom).hom) ≫ (Fibre.chartIso D₂ k).hom :=
        (Category.assoc _ _ _).symm
    _ = (Y.curve.baseChange (D₂.geomPt (D₂.specPt k))).zero ≫ (Fibre.chartIso D₂ k).hom :=
        congrArg (· ≫ (Fibre.chartIso D₂ k).hom) hz12
    _ = projModelZero (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) := Fibre.zero_comp D₂ k

/-- The fibre-model comparison carries the first fibre point to the second. -/
theorem Fibre.pt_modelIso (P : Y.curve.Section) :
    (Fibre.pt D₁ k P).1 ≫ (Fibre.modelIso D₁ D₂ k hgeom).hom = (Fibre.pt D₂ k P).1 := by
  have e1 := congrHom_hom_comp_fst Y.curve.π hgeom
  have e2 := congrHom_hom_comp_snd Y.curve.π hgeom
  have hfs : (Fibre.section D₁ k P).1 ≫ (pullback.congrHom rfl hgeom).hom =
      (Fibre.section D₂ k P).1 := by
    rw [Fibre.section_coe D₁ k P, Fibre.section_coe D₂ k P]
    refine pullback.hom_ext ?_ ?_
    · calc (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫
            (pullback.congrHom rfl hgeom).hom) ≫
            pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k))
          = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫
            ((pullback.congrHom rfl hgeom).hom ≫
              pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k))) := Category.assoc _ _ _
        _ = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫
            pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) :=
              congrArg (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫ ·) e1
        _ = D₁.geomPt (D₁.specPt k) ≫ P.1 := pullback.lift_fst _ _ _
        _ = D₂.geomPt (D₂.specPt k) ≫ P.1 := congrArg (· ≫ P.1) hgeom
        _ = pullback.lift (D₂.geomPt (D₂.specPt k) ≫ P.1) (𝟙 _) _ ≫
            pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) := (pullback.lift_fst _ _ _).symm
    · calc (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫
            (pullback.congrHom rfl hgeom).hom) ≫
            pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k))
          = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫
            ((pullback.congrHom rfl hgeom).hom ≫
              pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k))) := Category.assoc _ _ _
        _ = pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫
            pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) :=
              congrArg (pullback.lift (D₁.geomPt (D₁.specPt k) ≫ P.1) (𝟙 _) _ ≫ ·) e2
        _ = 𝟙 _ := pullback.lift_snd _ _ _
        _ = pullback.lift (D₂.geomPt (D₂.specPt k) ≫ P.1) (𝟙 _) _ ≫
            pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) := (pullback.lift_snd _ _ _).symm
  show ((Fibre.section D₁ k P).1 ≫ (Fibre.chartIso D₁ k).hom) ≫ _ =
    (Fibre.section D₂ k P).1 ≫ (Fibre.chartIso D₂ k).hom
  rw [Fibre.modelIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc ((Fibre.section D₁ k P).1 ≫ (Fibre.chartIso D₁ k).hom) ≫
      ((Fibre.chartIso D₁ k).inv ≫ (pullback.congrHom rfl hgeom).hom ≫
        (Fibre.chartIso D₂ k).hom)
      = (Fibre.section D₁ k P).1 ≫ ((Fibre.chartIso D₁ k).hom ≫
          (Fibre.chartIso D₁ k).inv ≫ (pullback.congrHom rfl hgeom).hom ≫
          (Fibre.chartIso D₂ k).hom) := Category.assoc _ _ _
    _ = (Fibre.section D₁ k P).1 ≫ ((pullback.congrHom rfl hgeom).hom ≫
          (Fibre.chartIso D₂ k).hom) :=
        congrArg ((Fibre.section D₁ k P).1 ≫ ·) (Iso.hom_inv_id_assoc _ _)
    _ = ((Fibre.section D₁ k P).1 ≫ (pullback.congrHom rfl hgeom).hom) ≫
          (Fibre.chartIso D₂ k).hom := (Category.assoc _ _ _).symm
    _ = (Fibre.section D₂ k P).1 ≫ (Fibre.chartIso D₂ k).hom :=
        congrArg (· ≫ (Fibre.chartIso D₂ k).hom) hfs

include hgeom in
/-- **Overlap agreement of the pointed atlas maps** through the comparison ENGINE. -/
theorem Fibre.baseSpecMapOfPoint_pt_agree [Algebra ↑R k]
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    TateAtlas.Point.baseSpecMap R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) _ _
      (ZChart.eval_equation_self _ (Fibre.pt D₁ k P)
        (Fibre.pt_mem_zChart D₁ k P (D₁.pt_mem_zChart P hP)))
      (Fibre.pt_hord D₁ k P hP) =
    TateAtlas.Point.baseSpecMap R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) _ _
      (ZChart.eval_equation_self _ (Fibre.pt D₂ k P)
        (Fibre.pt_mem_zChart D₂ k P (D₂.pt_mem_zChart P hP)))
      (Fibre.pt_hord D₂ k P hP) :=
  TateAtlas.Point.baseSpecMap.eq_of_pointedIso R
    (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k))
    (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k))
    (Fibre.modelIso D₁ D₂ k hgeom)
    (Fibre.modelIso_π D₁ D₂ k hgeom) (Fibre.modelIso_zero D₁ D₂ k hgeom)
    (Fibre.pt D₁ k P) (Fibre.pt D₂ k P)
    (Fibre.pt_mem_zChart D₁ k P (D₁.pt_mem_zChart P hP))
    (Fibre.pt_mem_zChart D₂ k P (D₂.pt_mem_zChart P hP))
    (Fibre.pt_modelIso D₁ D₂ k hgeom P)
    (Fibre.pt_hord D₁ k P hP) (Fibre.pt_hord D₂ k P hP)

include hgeom in
/-- **The local classifying base maps agree on affine test points of the overlap.** -/
theorem Fibre.specPt_baseSpecMap_agree [Algebra ↑R k]
    [Algebra ↑R ↑Γ(Y.base, D₁.U.1)] [Algebra ↑R ↑Γ(Y.base, D₂.U.1)]
    (htower₁ : (algebraMap ↑Γ(Y.base, D₁.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) = algebraMap ↑R k)
    (htower₂ : (algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) = algebraMap ↑R k)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    D₁.specPt k ≫ (TateAtlas.Point.baseSpecMap R D₁.W _ _
        (ZChart.eval_equation_self D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP))
        (D₁.pt_hord P hP)) =
      D₂.specPt k ≫ (TateAtlas.Point.baseSpecMap R D₂.W _ _
        (ZChart.eval_equation_self D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP))
        (D₂.pt_hord P hP)) := by
  have hx₁ := Fibre.eval_pt_coordX D₁ k P (D₁.pt_mem_zChart P hP)
  have hy₁ := Fibre.eval_pt_coordY D₁ k P (D₁.pt_mem_zChart P hP)
  have hx₂ := Fibre.eval_pt_coordX D₂ k P (D₂.pt_mem_zChart P hP)
  have hy₂ := Fibre.eval_pt_coordY D₂ k P (D₂.pt_mem_zChart P hP)
  have hxy₁' : (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)).toAffine.Equation
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (ZChart.eval D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP) (coordX D₁.W)))
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (ZChart.eval D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP) (coordY D₁.W))) := by
    rw [← hx₁, ← hy₁]
    exact ZChart.eval_equation_self _ (Fibre.pt D₁ k P)
      (Fibre.pt_mem_zChart D₁ k P (D₁.pt_mem_zChart P hP))
  have hord₁' : NowhereOrderLEThree (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k))
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (ZChart.eval D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP) (coordX D₁.W)))
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (ZChart.eval D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP) (coordY D₁.W))) := by
    rw [← hx₁, ← hy₁]
    exact Fibre.pt_hord D₁ k P hP
  have hxy₂' : (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)).toAffine.Equation
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (ZChart.eval D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP) (coordX D₂.W)))
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (ZChart.eval D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP) (coordY D₂.W))) := by
    rw [← hx₂, ← hy₂]
    exact ZChart.eval_equation_self _ (Fibre.pt D₂ k P)
      (Fibre.pt_mem_zChart D₂ k P (D₂.pt_mem_zChart P hP))
  have hord₂' : NowhereOrderLEThree (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k))
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (ZChart.eval D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP) (coordX D₂.W)))
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (ZChart.eval D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP) (coordY D₂.W))) := by
    rw [← hx₂, ← hy₂]
    exact Fibre.pt_hord D₂ k P hP
  calc D₁.specPt k ≫ (TateAtlas.Point.baseSpecMap R D₁.W _ _
        (ZChart.eval_equation_self D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP)) (D₁.pt_hord P hP))
      = TateAtlas.Point.baseSpecMap R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) _ _
          hxy₁' hord₁' :=
        TateAtlas.Point.baseSpecMap_naturality (algebraMap ↑Γ(Y.base, D₁.U.1) k) R htower₁
          D₁.W _ _ (ZChart.eval_equation_self D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP))
          (D₁.pt_hord P hP) hxy₁' hord₁'
    _ = TateAtlas.Point.baseSpecMap R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) _ _
          (ZChart.eval_equation_self _ (Fibre.pt D₁ k P)
            (Fibre.pt_mem_zChart D₁ k P (D₁.pt_mem_zChart P hP)))
          (Fibre.pt_hord D₁ k P hP) :=
        TateAtlas.Point.baseSpecMap_congr R _ hx₁.symm hy₁.symm hxy₁' hord₁' _ _
    _ = TateAtlas.Point.baseSpecMap R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) _ _
          (ZChart.eval_equation_self _ (Fibre.pt D₂ k P)
            (Fibre.pt_mem_zChart D₂ k P (D₂.pt_mem_zChart P hP)))
          (Fibre.pt_hord D₂ k P hP) :=
        Fibre.baseSpecMapOfPoint_pt_agree D₁ D₂ k hgeom P hP
    _ = TateAtlas.Point.baseSpecMap R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) _ _
          hxy₂' hord₂' :=
        TateAtlas.Point.baseSpecMap_congr R _ hx₂ hy₂ _ _ hxy₂' hord₂'
    _ = D₂.specPt k ≫ (TateAtlas.Point.baseSpecMap R D₂.W _ _
          (ZChart.eval_equation_self D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP))
          (D₂.pt_hord P hP)) :=
        (TateAtlas.Point.baseSpecMap_naturality (algebraMap ↑Γ(Y.base, D₂.U.1) k) R htower₂
          D₂.W _ _ (ZChart.eval_equation_self D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP))
          (D₂.pt_hord P hP) hxy₂' hord₂').symm

end MarkedChartData

end OverlapAgreement

section ExistenceGlue

/-! ### Gluing the local classifying maps (recipe step 4)

The chart cover of the base, the overlap agreement in instance-packaged test-point form,
and the glued base map to the Tate atlas. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R}

/-- **Test-point agreement of the local classifying base maps**: two charts and two
`Spec`-maps into the chart rings whose composites into the base agree yield equal
composites with the pointed atlas maps. -/
theorem test_baseMap_agree (D₁ D₂ : MarkedChartData R Y)
    [Algebra ↑R ↑Γ(Y.base, D₁.U.1)] [Algebra ↑R ↑Γ(Y.base, D₂.U.1)]
    (halg₁ : D₁.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₁.U.1))) =
      D₁.U.1.ι ≫ Y.structMap)
    (halg₂ : D₂.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₂.U.1))) =
      D₂.U.1.ι ≫ Y.structMap)
    (k : Type u) [CommRing k]
    (c₁ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↑Γ(Y.base, D₁.U.1)))
    (c₂ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↑Γ(Y.base, D₂.U.1)))
    (hcc : c₁ ≫ D₁.U.2.isoSpec.inv ≫ D₁.U.1.ι = c₂ ≫ D₂.U.2.isoSpec.inv ≫ D₂.U.1.ι)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    c₁ ≫ (TateAtlas.Point.baseSpecMap R D₁.W _ _
        (ZChart.eval_equation_self D₁.W (D₁.pt P) (D₁.pt_mem_zChart P hP))
        (D₁.pt_hord P hP)) =
      c₂ ≫ (TateAtlas.Point.baseSpecMap R D₂.W _ _
        (ZChart.eval_equation_self D₂.W (D₂.pt P) (D₂.pt_mem_zChart P hP))
        (D₂.pt_hord P hP)) := by
  letI ha₁ : Algebra ↑Γ(Y.base, D₁.U.1) k := (Spec.preimage c₁).hom.toAlgebra
  letI ha₂ : Algebra ↑Γ(Y.base, D₂.U.1) k := (Spec.preimage c₂).hom.toAlgebra
  letI haR : Algebra ↑R k :=
    ((Spec.preimage c₁).hom.comp (algebraMap ↑R ↑Γ(Y.base, D₁.U.1))).toAlgebra
  have hof₁ : CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₁.U.1) k) = Spec.preimage c₁ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  have hof₂ : CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₂.U.1) k) = Spec.preimage c₂ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  have hsp₁ : D₁.specPt k = c₁ := by
    show Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₁.U.1) k)) = c₁
    rw [hof₁, Spec.map_preimage]
  have hsp₂ : D₂.specPt k = c₂ := by
    show Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₂.U.1) k)) = c₂
    rw [hof₂, Spec.map_preimage]
  have hgeom : D₁.geomPt (D₁.specPt k) = D₂.geomPt (D₂.specPt k) := by
    rw [geomPt, geomPt, hsp₁, hsp₂]
    exact hcc
  have htower₁ : (algebraMap ↑Γ(Y.base, D₁.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) = algebraMap ↑R k := rfl
  have hbase₁ : Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₁.U.1))) =
      D₁.U.2.isoSpec.inv ≫ D₁.U.1.ι ≫ Y.structMap := by
    rw [← halg₁, Iso.inv_hom_id_assoc]
  have hbase₂ : Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₂.U.1))) =
      D₂.U.2.isoSpec.inv ≫ D₂.U.1.ι ≫ Y.structMap := by
    rw [← halg₂, Iso.inv_hom_id_assoc]
  have htower₂ : (algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) = algebraMap ↑R k := by
    have hspec : Spec.map (CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
        (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↑R k)) := by
      rw [show CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
          (algebraMap ↑R ↑Γ(Y.base, D₂.U.1))) =
          CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) ≫
            CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₂.U.1) k) from
        CommRingCat.ofHom_comp _ _]
      rw [show CommRingCat.ofHom (algebraMap ↑R k) =
          CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) ≫
            CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₁.U.1) k) from
        CommRingCat.ofHom_comp _ _]
      rw [Spec.map_comp, Spec.map_comp, hof₁, hof₂, Spec.map_preimage, Spec.map_preimage,
        hbase₁, hbase₂]
      have hw := congrArg (fun m ↦ m ≫ Y.structMap) hcc
      simp only [Category.assoc] at hw ⊢
      exact hw.symm
    have hring := Spec.map_injective hspec
    have := congrArg CommRingCat.Hom.hom hring
    simpa using this
  have h := Fibre.specPt_baseSpecMap_agree D₁ D₂ k hgeom htower₁ htower₂ P hP
  rw [hsp₁, hsp₂] at h
  exact h

variable (Y) in
/-- The chart at a point of the base. -/
noncomputable def chartAt (s : ↥Y.base) : MarkedChartData R Y :=
  (exists_mem Y s).choose

theorem chartAt_mem (s : ↥Y.base) : s ∈ (chartAt Y s).U.1 :=
  (exists_mem Y s).choose_spec

variable (Y) in
/-- The open cover of the base by marked charts. -/
noncomputable def chartCover : Y.base.OpenCover :=
  Scheme.Cover.mkOfCovers ↥Y.base
    (fun s ↦ (chartAt Y s).U.1.toScheme)
    (fun s ↦ (chartAt Y s).U.1.ι)
    (fun s ↦ ⟨s, ⟨⟨s, chartAt_mem s⟩, rfl⟩⟩)

@[simp]
theorem chartCover_f (s : ↥Y.base) : (chartCover Y).f s = (chartAt Y s).U.1.ι := rfl

/-- The local classifying base maps of the chart cover. -/
noncomputable def coverBaseMap (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (s : ↥Y.base) : (chartCover Y).X s ⟶ tateBase R :=
  letI := (chartAt Y s).chartAlgebra
  (chartAt Y s).baseMap P hP

/-- **Overlap compatibility** of the local classifying base maps. -/
theorem coverBaseMap_compat (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (i j : (chartCover Y).I₀) :
    pullback.fst ((chartCover Y).f i) ((chartCover Y).f j) ≫ coverBaseMap P hP i =
      pullback.snd ((chartCover Y).f i) ((chartCover Y).f j) ≫ coverBaseMap P hP j := by
  letI := (chartAt Y i).chartAlgebra
  letI := (chartAt Y j).chartAlgebra
  apply Scheme.Cover.hom_ext
    (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j)))
  intro z
  set V := (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).X z
    with hV
  rw [← cancel_epi (Scheme.isoSpec V).inv]
  have hcc : ((Scheme.isoSpec V).inv ≫
        (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
        pullback.fst ((chartCover Y).f i) ((chartCover Y).f j) ≫
        (chartAt Y i).U.2.isoSpec.hom) ≫
      (chartAt Y i).U.2.isoSpec.inv ≫ (chartAt Y i).U.1.ι =
      ((Scheme.isoSpec V).inv ≫
        (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
        pullback.snd ((chartCover Y).f i) ((chartCover Y).f j) ≫
        (chartAt Y j).U.2.isoSpec.hom) ≫
      (chartAt Y j).U.2.isoSpec.inv ≫ (chartAt Y j).U.1.ι := by
    simp only [Category.assoc]
    have hw := congrArg (fun m ↦ (Scheme.isoSpec V).inv ≫
      (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫ m)
      (pullback.condition (f := (chartCover Y).f i) (g := (chartCover Y).f j))
    calc (Scheme.isoSpec V).inv ≫
        (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
        pullback.fst ((chartCover Y).f i) ((chartCover Y).f j) ≫
        (chartAt Y i).U.2.isoSpec.hom ≫ (chartAt Y i).U.2.isoSpec.inv ≫
        (chartAt Y i).U.1.ι
        = (Scheme.isoSpec V).inv ≫
          (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
          pullback.fst ((chartCover Y).f i) ((chartCover Y).f j) ≫ (chartAt Y i).U.1.ι :=
        congrArg (fun m ↦ (Scheme.isoSpec V).inv ≫
          (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
          pullback.fst ((chartCover Y).f i) ((chartCover Y).f j) ≫ m)
          (Iso.hom_inv_id_assoc (chartAt Y i).U.2.isoSpec (chartAt Y i).U.1.ι)
      _ = (Scheme.isoSpec V).inv ≫
          (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
          pullback.snd ((chartCover Y).f i) ((chartCover Y).f j) ≫ (chartAt Y j).U.1.ι :=
        hw
      _ = (Scheme.isoSpec V).inv ≫
          (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
          pullback.snd ((chartCover Y).f i) ((chartCover Y).f j) ≫
          (chartAt Y j).U.2.isoSpec.hom ≫ (chartAt Y j).U.2.isoSpec.inv ≫
          (chartAt Y j).U.1.ι :=
        (congrArg (fun m ↦ (Scheme.isoSpec V).inv ≫
          (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
          pullback.snd ((chartCover Y).f i) ((chartCover Y).f j) ≫ m)
          (Iso.hom_inv_id_assoc (chartAt Y j).U.2.isoSpec (chartAt Y j).U.1.ι)).symm
  have h := test_baseMap_agree (chartAt Y i) (chartAt Y j)
    ((chartAt Y i).chartAlgebra_compatible) ((chartAt Y j).chartAlgebra_compatible)
    ↑Γ(V, ⊤) _ _ hcc P hP
  show (Scheme.isoSpec V).inv ≫ _ ≫ pullback.fst _ _ ≫
      ((chartAt Y i).U.2.isoSpec.hom ≫ (TateAtlas.Point.baseSpecMap R (chartAt Y i).W _ _
        (ZChart.eval_equation_self (chartAt Y i).W ((chartAt Y i).pt P)
          ((chartAt Y i).pt_mem_zChart P hP)) ((chartAt Y i).pt_hord P hP))) =
    (Scheme.isoSpec V).inv ≫ _ ≫ pullback.snd _ _ ≫
      ((chartAt Y j).U.2.isoSpec.hom ≫ (TateAtlas.Point.baseSpecMap R (chartAt Y j).W _ _
        (ZChart.eval_equation_self (chartAt Y j).W ((chartAt Y j).pt P)
          ((chartAt Y j).pt_mem_zChart P hP)) ((chartAt Y j).pt_hord P hP)))
  exact h

/-- **The glued classifying base map** `Y.base ⟶ tateBase R`. -/
noncomputable def gluedBaseMap (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) : Y.base ⟶ tateBase R :=
  EllObj.TateAtlas.baseMapOfOpenCover R Y (chartCover Y) (coverBaseMap P hP)
    (coverBaseMap_compat P hP)

@[reassoc (attr := simp)]
theorem ι_gluedBaseMap (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (s : ↥Y.base) :
    (chartAt Y s).U.1.ι ≫ gluedBaseMap P hP = coverBaseMap P hP s :=
  EllObj.TateAtlas.BaseMapOfOpenCover.ι R Y (chartCover Y) (coverBaseMap P hP)
    (coverBaseMap_compat P hP) s

/-- The glued base map lies over `Spec R`. -/
theorem gluedBaseMap_over (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    gluedBaseMap P hP ≫ tateStructMap R = Y.structMap := by
  refine EllObj.TateAtlas.BaseMapOfOpenCover.base_w R Y (chartCover Y) (coverBaseMap P hP)
    (coverBaseMap_compat P hP) ?_
  intro s
  letI := (chartAt Y s).chartAlgebra
  exact (chartAt Y s).baseMap_over P hP ((chartAt Y s).chartAlgebra_compatible)

end MarkedChartData

end ExistenceGlue

section BaseChangeComp

/-! ### Composition of model base changes

`projModelBaseChange` composes along ring maps, up to the canonical identification of the
doubly-mapped curve.  Together with `projModelVCIso_map` (T-W7.0h) this yields the
naturality of the local classifying top maps in the chart ring. -/

set_option backward.isDefEq.respectTransparency false in
private lemma projMapTransportHeq {A R' : Type u} [CommRing A] [CommRing R']
    (W : WeierstrassCurve A)
    {V V' : WeierstrassCurve R'} (e : V' = V)
    (g : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V)))
    (hg : (quotientGrading (projIdeal V))₊ ≤ ((quotientGrading (projIdeal W))₊).map g)
    (g' : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V')))
    (hg' : (quotientGrading (projIdeal V'))₊ ≤ ((quotientGrading (projIdeal W))₊).map g')
    (hgg : HEq g g') :
    Proj.map g hg = eqToHom (congrArg projModel e.symm) ≫ Proj.map g' hg' := by
  subst e
  obtain rfl := eq_of_heq hgg
  simp

private lemma gradedHomHeq {A R' : Type u} [CommRing A] [CommRing R']
    (W : WeierstrassCurve A)
    {V V' : WeierstrassCurve R'} (e : V = V')
    (g : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V)))
    (g' : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V')))
    (h : ∀ x, HEq (g x) (g' x)) : HEq g g' := by
  subst e
  exact heq_of_eq (GradedRingHom.ext fun x ↦ eq_of_heq (h x))

private lemma mkHeq {R' : Type u} [CommRing R'] {V V' : WeierstrassCurve R'} (e : V = V')
    (q : MvPolynomial (Fin 3) R') :
    HEq (Ideal.Quotient.mk (projIdeal V).toIdeal q)
      (Ideal.Quotient.mk (projIdeal V').toIdeal q) := by
  subst e; rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Model base changes compose** along ring maps. -/
theorem ProjModelBaseChange.comp_eqToHom {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (W : WeierstrassCurve A) :
    projModelBaseChange ψ (W.map φ) ≫ projModelBaseChange φ W =
      eqToHom (congrArg projModel (WeierstrassCurve.map_map W φ ψ)) ≫
        projModelBaseChange (ψ.comp φ) W := by
  show Proj.map (baseChangeGradedHom ψ (W.map φ)) _ ≫ Proj.map (baseChangeGradedHom φ W) _ =
    eqToHom _ ≫ Proj.map (baseChangeGradedHom (ψ.comp φ) W) _
  rw [← Proj.map_comp]
  refine projMapTransportHeq W (WeierstrassCurve.map_map W φ ψ).symm _ _ _ _
    (gradedHomHeq W (WeierstrassCurve.map_map W φ ψ) _ _ fun x ↦ ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show HEq (baseChangeGradedHom ψ (W.map φ)
      (baseChangeGradedHom φ W (Ideal.Quotient.mk _ a)))
    (baseChangeGradedHom (ψ.comp φ) W (Ideal.Quotient.mk _ a))
  rw [baseChangeGradedHom, baseChangeGradedHom, quotientGradingMap_mk, quotientGradingMap_mk,
    baseChangeGradedHom, quotientGradingMap_mk]
  refine (mkHeq (WeierstrassCurve.map_map W φ ψ) _).trans (heq_of_eq (congrArg _ ?_))
  show (MvPolynomial.map ψ) ((MvPolynomial.map φ) a) = (MvPolynomial.map (ψ.comp φ)) a
  exact MvPolynomial.map_map φ ψ a

end BaseChangeComp

section TopNaturality

/-! ### Naturality of the classifying top map in the chart ring (recipe step 4, top)

`projTateMap` is natural under change of the chart ring: base-changing the model and
classifying with the fibre point is the same as classifying and base-changing.  The
derivation runs through `projModelVCIso_map` (T-W7.0h) and `ProjModelBaseChange.comp_eqToHom`. -/

/-- Congruence for the T-E1 normalisation in the marked point. -/
theorem TateAtlas.TateNormal.variableChange_congr {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] {x₁ y₁ x₂ y₂ : A} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (hxy₁ : W.toAffine.Equation x₁ y₁) (hord₁ : NowhereOrderLEThree W x₁ y₁)
    (hxy₂ : W.toAffine.Equation x₂ y₂) (hord₂ : NowhereOrderLEThree W x₂ y₂) :
    TateAtlas.TateNormal.variableChange W x₁ y₁ hxy₁ hord₁ =
      TateAtlas.TateNormal.variableChange W x₂ y₂ hxy₂ hord₂ := by
  subst hx
  subst hy
  rfl

/-- Congruence for the pointed atlas ring map in the marked point. -/
theorem TateAtlas.Point.ringOverLift_congr (R : CommRingCat.{u}) {A : Type u} [CommRing A]
    [Algebra ↑R A] (W : WeierstrassCurve A) [W.IsElliptic]
    {x₁ y₁ x₂ y₂ : A} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (hxy₁ : W.toAffine.Equation x₁ y₁) (hord₁ : NowhereOrderLEThree W x₁ y₁)
    (hxy₂ : W.toAffine.Equation x₂ y₂) (hord₂ : NowhereOrderLEThree W x₂ y₂) :
    TateAtlas.Point.ringOverLift R W x₁ y₁ hxy₁ hord₁ =
      TateAtlas.Point.ringOverLift R W x₂ y₂ hxy₂ hord₂ := by
  subst hx
  subst hy
  rfl

private lemma projModelBaseChange_eqToHom {A B : Type u} [CommRing A] [CommRing B]
    (ψ : A →+* B) {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂) :
    projModelBaseChange ψ V₂ ≫ eqToHom (show projModel V₂ = projModel V₁ by rw [h]) =
      eqToHom (show projModel (V₂.map ψ) = projModel (V₁.map ψ) by rw [h]) ≫
        projModelBaseChange ψ V₁ := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

private lemma projModelVCIso_inv_congr {A : Type u} [CommRing A]
    {C₁ C₂ : WeierstrassCurve.VariableChange A} (h : C₁ = C₂) (W : WeierstrassCurve A) :
    (projModelVCIso C₁ W).inv = (projModelVCIso C₂ W).inv ≫
      eqToHom (show projModel (C₂ • W) = projModel (C₁ • W) by rw [h]) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]

private lemma ProjModelBaseChange.ringHom_congr {A B : Type u} [CommRing A] [CommRing B]
    {ρ₁ ρ₂ : A →+* B} (h : ρ₁ = ρ₂) (W : WeierstrassCurve A) :
    projModelBaseChange ρ₁ W = eqToHom (by rw [h]) ≫ projModelBaseChange ρ₂ W := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

/-- The classifying top map, unfolded to its canonical three-factor composite. -/
theorem projTateMap_unfold {A : Type u} [CommRing A] (R : CommRingCat.{u}) [Algebra ↑R A]
    (W : WeierstrassCurve A) [W.IsElliptic]
    (g : SpecPoints (projModel W) (projModelπ W) A) (hZ : InZChart W g)
    (hord : NowhereOrderLEThree W
      (ZChart.eval W g hZ (coordX W)) (ZChart.eval W g hZ (coordY W))) :
    projTateMap R W g hZ hord =
      (projModelVCIso (TateAtlas.TateNormal.variableChange W _ _
        (ZChart.eval_equation_self W g hZ) hord) W).inv ≫
      eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R W g hZ hord)).symm ≫
      projModelBaseChange
        ((TateAtlas.Point.ringOverAlgLift R W _ _ (ZChart.eval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) (tateCurveLocOver R) := by
  rw [projTateMap, TateAtlas.normalIso, Iso.trans_inv, eqToIso.inv, Category.assoc]

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D.U.1) k]
  [Algebra ↑R ↑Γ(Y.base, D.U.1)] [Algebra ↑R k]

/-- **Naturality of the classifying top map**: base-changing the chart model and classifying
at the fibre point agrees with classifying at the chart point and base-changing. -/
theorem ProjModelBaseChange.projTateMap
    (htower : (algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D.U.1)) = algebraMap ↑R k)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W ≫
      projTateMap R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP) =
    projTateMap R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (Fibre.pt_hord D k P hP) := by
  have hx := Fibre.eval_pt_coordX D k P (D.pt_mem_zChart P hP)
  have hy := Fibre.eval_pt_coordY D k P (D.pt_mem_zChart P hP)
  have hxy₂ : (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).toAffine.Equation
      ((algebraMap ↑Γ(Y.base, D.U.1) k)
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)))
      ((algebraMap ↑Γ(Y.base, D.U.1) k) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY
          D.W))) := by
    rw [← hx, ← hy]
    exact ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))
  have hord₂ : NowhereOrderLEThree (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      ((algebraMap ↑Γ(Y.base, D.U.1) k)
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)))
      ((algebraMap ↑Γ(Y.base, D.U.1) k) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY
          D.W))) := by
    rw [← hx, ← hy]
    exact Fibre.pt_hord D k P hP
  -- (F2) the two T-E1 normalisations
  have hC : TateAtlas.TateNormal.variableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
            D.U.1) k))))
      (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
            D.U.1) k))))
      (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
          (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) =
      (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
      (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map
          (algebraMap ↑Γ(Y.base, D.U.1) k) :=
    (TateAtlas.TateNormal.variableChange_congr (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) hx hy
        (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) hxy₂
        hord₂).trans
      (TateAtlas.TateNormal.variableChange_map (algebraMap ↑Γ(Y.base, D.U.1) k) D.W (ZChart.eval D.W
          (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
          hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) hxy₂
            hord₂).symm
  -- (F3) the two pointed atlas ring maps
  have hL : TateAtlas.Point.ringOverLift R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
            D.U.1) k))))
      (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
            D.U.1) k))))
      (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
          (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) =
      (algebraMap ↑Γ(Y.base, D.U.1) k).comp (TateAtlas.Point.ringOverLift R D.W (ZChart.eval D.W
          (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
          hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) :=
    (TateAtlas.Point.ringOverLift_congr R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) hx hy
        (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) hxy₂
        hord₂).trans
      (TateAtlas.Point.ringOverLift_comp (algebraMap ↑Γ(Y.base, D.U.1) k) R htower D.W (ZChart.eval
          D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
          (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) hxy₂
            hord₂).symm
  -- (G1) T-W7.0h: move the base change past the variable-change isomorphism
  have hG1 := projModelVCIso_map (R := ↑Γ(Y.base, D.U.1)) (R' := k)
      (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
      (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
      (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) D.W
  -- unfold both classifying maps to their canonical composites
  rw [projTateMap_unfold R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP),
    projTateMap_unfold R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (Fibre.pt_hord D k P hP),
    ← cancel_epi (projModelVCIso ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom]
  have hstar : (projModelVCIso ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
      (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY
      D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map
      (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫
      projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
          (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
          hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
          projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
          (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
          hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
          [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1)
          k) ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
          hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
          (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W) ≫
          (projModelVCIso (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
          (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
          hP)) D.W).hom := by
    refine Eq.trans ?_ (congrArg (fun m ↦
      eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
          (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
          hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
          projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
          (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
          hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
          [WeierstrassCurve.map_variableChange]) ≫ m) hG1.symm)
    rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hslide := projModelBaseChange_eqToHom (algebraMap ↑Γ(Y.base, D.U.1) k)
      (TateAtlas.CurveLocOver.map_marked R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP))
  have hcomp := ProjModelBaseChange.comp_eqToHom ((((TateAtlas.Point.ringOverAlgLift R D.W
      (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
      (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart
      P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+*
      ↑Γ(Y.base, D.U.1))) (algebraMap ↑Γ(Y.base, D.U.1) k) (tateCurveLocOver R)
  have hL' : (algebraMap ↑Γ(Y.base, D.U.1) k).comp ((((TateAtlas.Point.ringOverAlgLift R D.W
      (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
      (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart
      P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+*
      ↑Γ(Y.base, D.U.1))) = ((((TateAtlas.Point.ringOverAlgLift R (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D
      k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) :
      tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) := hL.symm
  have hbcL : projModelBaseChange ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
      ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
      (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
      (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
      tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))))
      (tateCurveLocOver R) =
      eqToHom (show projModel ((tateCurveLocOver R).map ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
          ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
          (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
          tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))))) =
          projModel ((tateCurveLocOver R).map ((((TateAtlas.Point.ringOverAlgLift R (D.W.map
          (algebraMap ↑Γ(Y.base, D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
          (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map
          (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1)
          k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map
          (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap
          ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)))
          (Fibre.pt_hord D k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))) by rw [hL'])
          ≫ projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R (D.W.map (algebraMap
          ↑Γ(Y.base, D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D
          k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap
          ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt
          D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap
          ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1)
          k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D
          k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) :=
    ProjModelBaseChange.ringHom_congr hL' (tateCurveLocOver R)
  have hinvC : (projModelVCIso (TateAtlas.TateNormal.variableChange (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D
      k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP)) (D.W.map
      (algebraMap ↑Γ(Y.base, D.U.1) k))).inv = (projModelVCIso ((TateAtlas.TateNormal.variableChange
      D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
      (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart
      P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k))).inv ≫ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W
      (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
      (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart
      P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap
      ↑Γ(Y.base, D.U.1) k))) = projModel ((TateAtlas.TateNormal.variableChange (D.W.map (algebraMap
      ↑Γ(Y.base, D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
      (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
      D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D
      k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP)) • (D.W.map
      (algebraMap ↑Γ(Y.base, D.U.1) k))) by rw [hC]) :=
    projModelVCIso_inv_congr hC (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
  calc (projModelVCIso ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
      (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY
      D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map
      (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫
      projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W ≫ (projModelVCIso
      (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
      (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
      (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) D.W).inv ≫
      eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R D.W (D.pt P) (D.pt_mem_zChart
      P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R D.W
      (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
      (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart
      P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+*
      ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R)
      = ((projModelVCIso ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
          (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
          hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom
          ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W) ≫ (projModelVCIso
          (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
          (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) D.W).inv
          ≫ eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
          (D.pt_mem_zChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange
          ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
          (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
          (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
          tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
          (tateCurveLocOver R) :=
        (Category.assoc _ _ _).symm
    _ = (eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt
        P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1)
        k) ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W) ≫
        (projModelVCIso (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) D.W).hom) ≫ (projModelVCIso (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W
        (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord
        P hP)) D.W).inv ≫ eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R D.W (D.pt
        P) (D.pt_mem_zChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
        (tateCurveLocOver R) :=
        congrArg (· ≫ (projModelVCIso (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W
            (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
            P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
            (D.pt_hord P hP)) D.W).inv ≫ eqToHom (congrArg projModel
            (TateAtlas.CurveLocOver.map_marked R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P
            hP))).symm ≫ projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval
            D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
            (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
            (D.pt_mem_zChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) :
            tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R)) hstar
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1)
        k) ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W) ≫
        (projModelVCIso (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) D.W).hom ≫ (projModelVCIso (TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W
        (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord
        P hP)) D.W).inv ≫ eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R D.W (D.pt
        P) (D.pt_mem_zChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
        (tateCurveLocOver R) := by
        simp only [Category.assoc]
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1)
        k) ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W) ≫
        eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
        (D.pt_mem_zChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
        (tateCurveLocOver R) :=
        congrArg (fun m ↦ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W
            (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
            (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
            (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) •
            (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel
            (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
            hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
            (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) •
            D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange])
            ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k)
            ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
            hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
            (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W)
            ≫ m) (Iso.hom_inv_id_assoc _ _)
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ (projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1)
        k) ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W) ≫
        eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
        (D.pt_mem_zChart P hP) (D.pt_hord P hP))).symm) ≫ projModelBaseChange
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
        (tateCurveLocOver R) := by
        simp only [Category.assoc]
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ (eqToHom (show projModel
        (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
        (D.pt_mem_zChart P hP) (D.pt_hord P hP)]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base,
        D.U.1) k) ((tateCurveLocOver R).map ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval
        D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
        P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
        (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base,
        D.U.1))))) ≫ projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W
        (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord
        P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
        (tateCurveLocOver R) :=
        congrArg (fun m ↦ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W
            (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
            (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
            (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) •
            (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel
            (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
            hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
            (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) •
            D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange])
            ≫ m ≫ projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W
            (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
            P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
            (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+*
            ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R)) hslide
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel
        (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
        (D.pt_mem_zChart P hP) (D.pt_hord P hP)]) ≫ (projModelBaseChange (algebraMap ↑Γ(Y.base,
        D.U.1) k) ((tateCurveLocOver R).map ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval
        D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
        P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
        (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base,
        D.U.1)))) ≫ projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W
        (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
        hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord
        P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
        (tateCurveLocOver R)) := by
        simp only [Category.assoc]
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel
        (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
        (D.pt_mem_zChart P hP) (D.pt_hord P hP)]) ≫ (eqToHom (congrArg projModel
        (WeierstrassCurve.map_map (tateCurveLocOver R) ((((TateAtlas.Point.ringOverAlgLift R D.W
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
        (D.pt_mem_zChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) :
        tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (algebraMap ↑Γ(Y.base, D.U.1) k))) ≫
          projModelBaseChange ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
              ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
              hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
              (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
              tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))))
              (tateCurveLocOver R)) :=
        congrArg (fun m ↦ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W
            (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
            (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
            (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) •
            (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel
            (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
            hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
            (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) •
            D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange])
            ≫ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W
            (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
            P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
            (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel
            (((tateCurveLocOver R).map ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W
            (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
            P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
            (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+*
            ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
            [TateAtlas.CurveLocOver.map_marked R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P
            hP)]) ≫ m) hcomp
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
        [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel
        (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) • D.W).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
        (D.pt_mem_zChart P hP) (D.pt_hord P hP)]) ≫ (eqToHom (congrArg projModel
        (WeierstrassCurve.map_map (tateCurveLocOver R) ((((TateAtlas.Point.ringOverAlgLift R D.W
        (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
        (D.pt_mem_zChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) :
        tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (algebraMap ↑Γ(Y.base, D.U.1) k))) ≫ (eqToHom (show
        projModel ((tateCurveLocOver R).map ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
        ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
        (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
        tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))))) =
        projModel ((tateCurveLocOver R).map ((((TateAtlas.Point.ringOverAlgLift R (D.W.map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
        (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map
        (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
        (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map
        (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap
        ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)))
        (Fibre.pt_hord D k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))) by rw [hL']) ≫
        projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt
        D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) :
        tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R))) :=
        congrArg (fun m ↦ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W
            (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
            (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
            (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) •
            (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel
            (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
            hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
            (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP)) •
            D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange])
            ≫ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W
            (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
            P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
            (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel
            (((tateCurveLocOver R).map ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W
            (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
            P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
            (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+*
            ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw
            [TateAtlas.CurveLocOver.map_marked R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P
            hP)]) ≫ (eqToHom (congrArg projModel (WeierstrassCurve.map_map (tateCurveLocOver R)
            ((((TateAtlas.Point.ringOverAlgLift R D.W (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P
            hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordY D.W))
            (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) :
            tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))
            (algebraMap ↑Γ(Y.base, D.U.1) k))) ≫ m)) hbcL
    _ = eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        projModel ((tateCurveLocOver R).map ((((TateAtlas.Point.ringOverAlgLift R (D.W.map
        (algebraMap ↑Γ(Y.base, D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
        (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map
        (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
        (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map
        (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap
        ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)))
        (Fibre.pt_hord D k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))) by rw
        [WeierstrassCurve.map_variableChange, ← TateAtlas.CurveLocOver.map_marked R D.W (D.pt P)
        (D.pt_mem_zChart P hP) (D.pt_hord P hP), WeierstrassCurve.map_map, hL']) ≫
        projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt
        D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) :
        tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) := by
        simp only [eqToHom_trans_assoc]
    _ = (projModelVCIso ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
        (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
        (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P
        hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫
        (projModelVCIso (TateAtlas.TateNormal.variableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1)
        k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt
        D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP))
        (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).inv ≫ eqToHom (congrArg projModel
        (TateAtlas.CurveLocOver.map_marked R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D
        k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (Fibre.pt_hord D k P hP))).symm ≫
        projModelBaseChange ((((TateAtlas.Point.ringOverAlgLift R (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
        (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base,
        D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt
        D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP))) (Fibre.pt_hord D k P hP) :
        tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) := by
        rw [hinvC]
        rw [show (projModelVCIso ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W (D.pt P)
            (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP)
            (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord
            P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1)
            k))).hom ≫ ((projModelVCIso ((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W
            (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart
            P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP))
            (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base,
            D.U.1) k))).inv ≫ eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W
            (ZChart.eval D.W (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
            (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
            (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) •
            (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel
            ((TateAtlas.TateNormal.variableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
            (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
            (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap
            ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
            (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map
            (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap
            ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P
            hP))) (Fibre.pt_hord D k P hP)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) by rw
            [hC])) ≫ eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R (D.W.map
            (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P
            (D.pt_mem_zChart P hP)) (Fibre.pt_hord D k P hP))).symm ≫ projModelBaseChange
            ((((TateAtlas.Point.ringOverAlgLift R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
            (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
            (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap
            ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
            (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map
            (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap
            ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P
            hP))) (Fibre.pt_hord D k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))
            (tateCurveLocOver R) =
            (eqToHom (show projModel (((TateAtlas.TateNormal.variableChange D.W (ZChart.eval D.W
                (D.pt P) (D.pt_mem_zChart P hP) (coordX D.W)) (ZChart.eval D.W (D.pt P)
                (D.pt_mem_zChart P hP) (coordY D.W)) (ZChart.eval_equation_self D.W (D.pt P)
                (D.pt_mem_zChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) •
                (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel
                ((TateAtlas.TateNormal.variableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
                (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
                (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap
                ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
                (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map
                (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap
                ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P
                hP))) (Fibre.pt_hord D k P hP)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) by rw
                [hC]) ≫ eqToHom (congrArg projModel (TateAtlas.CurveLocOver.map_marked R (D.W.map
                (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P
                (D.pt_mem_zChart P hP)) (Fibre.pt_hord D k P hP))).symm) ≫ projModelBaseChange
                ((((TateAtlas.Point.ringOverAlgLift R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
                (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
                (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordX (D.W.map (algebraMap
                ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
                (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (coordY (D.W.map
                (algebraMap ↑Γ(Y.base, D.U.1) k)))) (ZChart.eval_equation_self (D.W.map (algebraMap
                ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P) (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P
                hP))) (Fibre.pt_hord D k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))
                (tateCurveLocOver R) from
          ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
            (Iso.hom_inv_id_assoc _ _)).trans (Category.assoc _ _ _).symm]
        rw [eqToHom_trans]

end MarkedChartData

end TopNaturality

section TopRestriction

/-! ### Fibre restriction and overlap agreement of the local classifying top maps
(recipe step 2, top glue)

Restricting a local classifying top map to the fibre over an affine test point computes
the classifying map of the fibre model at the fibre point (`Fibre.map_topMap`, through the
step-1 naturality); the comparison ENGINE then forces the two fibre restrictions of the
top maps of overlapping charts to agree (`Fibre.map_topMap_agree`); the instance-free
test-point form (`test_topMap_agree`) is the input to the `E`-cover gluing. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R}

section OneChart

variable (D : MarkedChartData R Y) (k : Type u) [CommRing k]
  [Algebra ↑Γ(Y.base, D.U.1) k] [Algebra ↑R ↑Γ(Y.base, D.U.1)] [Algebra ↑R k]

/-- **Fibre restriction of the local classifying top map**: over an affine test point the
top map computes the classifying map of the fibre model at the fibre point. -/
theorem Fibre.map_topMap
    (htower : (algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D.U.1)) = algebraMap ↑R k)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    Fibre.map D k ≫ D.topMap P hP =
      (Fibre.chartIso D k).hom ≫
        projTateMap R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (Fibre.pt D k P)
          (Fibre.pt_mem_zChart D k P (D.pt_mem_zChart P hP)) (Fibre.pt_hord D k P hP) := by
  have hbc : (Fibre.chartIso D k).hom ≫
      projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      Fibre.map D k ≫ D.e.hom :=
    pullbackChartIso_hom_bc D.W (Fibre.top_isPullback D k)
  have h1 : Fibre.map D k ≫ D.topMap P hP =
      ((Fibre.chartIso D k).hom ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W) ≫
        projTateMap R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP) := by
    rw [hbc, topMap]
    simp only [Category.assoc]
  rw [h1, Category.assoc, ProjModelBaseChange.projTateMap D k htower P hP]

end OneChart

section TwoCharts

variable (D₁ D₂ : MarkedChartData R Y) (k : Type u) [CommRing k]
  [Algebra ↑Γ(Y.base, D₁.U.1) k] [Algebra ↑Γ(Y.base, D₂.U.1) k]
  [Algebra ↑R ↑Γ(Y.base, D₁.U.1)] [Algebra ↑R ↑Γ(Y.base, D₂.U.1)] [Algebra ↑R k]

/-- **Overlap agreement of the fibre restrictions of the local classifying top maps**,
through the comparison ENGINE with `Fibre.modelIso`-data. -/
theorem Fibre.map_topMap_agree
    (htower₁ : (algebraMap ↑Γ(Y.base, D₁.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) = algebraMap ↑R k)
    (htower₂ : (algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) = algebraMap ↑R k)
    (hgeom : D₁.geomPt (D₁.specPt k) = D₂.geomPt (D₂.specPt k))
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    Fibre.map D₁ k ≫ D₁.topMap P hP =
      (pullback.congrHom rfl hgeom).hom ≫ Fibre.map D₂ k ≫ D₂.topMap P hP := by
  rw [Fibre.map_topMap D₁ k htower₁ P hP, Fibre.map_topMap D₂ k htower₂ P hP]
  have hengine : (Fibre.modelIso D₁ D₂ k hgeom).hom ≫
      projTateMap R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) (Fibre.pt D₂ k P)
        (Fibre.pt_mem_zChart D₂ k P (D₂.pt_mem_zChart P hP)) (Fibre.pt_hord D₂ k P hP) =
      projTateMap R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) (Fibre.pt D₁ k P)
        (Fibre.pt_mem_zChart D₁ k P (D₁.pt_mem_zChart P hP)) (Fibre.pt_hord D₁ k P hP) :=
    projTateMap_eq_of_pointedIso R
      (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k))
      (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k))
      (Fibre.modelIso D₁ D₂ k hgeom)
      (Fibre.modelIso_π D₁ D₂ k hgeom) (Fibre.modelIso_zero D₁ D₂ k hgeom)
      (Fibre.pt D₁ k P) (Fibre.pt D₂ k P)
      (Fibre.pt_mem_zChart D₁ k P (D₁.pt_mem_zChart P hP))
      (Fibre.pt_mem_zChart D₂ k P (D₂.pt_mem_zChart P hP))
      (Fibre.pt_modelIso D₁ D₂ k hgeom P)
      (Fibre.pt_hord D₁ k P hP) (Fibre.pt_hord D₂ k P hP)
  rw [← hengine, Fibre.modelIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end TwoCharts

/-- **Test-point agreement of the local classifying top maps**: on any scheme mapping to
the two chart pullbacks compatibly over an affine test point of the overlap, the two
local top maps agree.  This is the input to the morphism-extension over the `E`-cover. -/
theorem test_topMap_agree (D₁ D₂ : MarkedChartData R Y)
    [Algebra ↑R ↑Γ(Y.base, D₁.U.1)] [Algebra ↑R ↑Γ(Y.base, D₂.U.1)]
    (halg₁ : D₁.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₁.U.1))) =
      D₁.U.1.ι ≫ Y.structMap)
    (halg₂ : D₂.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₂.U.1))) =
      D₂.U.1.ι ≫ Y.structMap)
    (k : Type u) [CommRing k]
    (c₁ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↑Γ(Y.base, D₁.U.1)))
    (c₂ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↑Γ(Y.base, D₂.U.1)))
    (hcc : c₁ ≫ D₁.U.2.isoSpec.inv ≫ D₁.U.1.ι = c₂ ≫ D₂.U.2.isoSpec.inv ≫ D₂.U.1.ι)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    {T : Scheme.{u}} (w : T ⟶ Spec (CommRingCat.of k))
    (v₁ : T ⟶ pullback Y.curve.π D₁.U.1.ι) (v₂ : T ⟶ pullback Y.curve.π D₂.U.1.ι)
    (hv₁ : v₁ ≫ pullback.snd Y.curve.π D₁.U.1.ι = w ≫ c₁ ≫ D₁.U.2.isoSpec.inv)
    (hv₂ : v₂ ≫ pullback.snd Y.curve.π D₂.U.1.ι = w ≫ c₂ ≫ D₂.U.2.isoSpec.inv)
    (hE : v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι = v₂ ≫ pullback.fst Y.curve.π D₂.U.1.ι) :
    v₁ ≫ D₁.topMap P hP = v₂ ≫ D₂.topMap P hP := by
  letI ha₁ : Algebra ↑Γ(Y.base, D₁.U.1) k := (Spec.preimage c₁).hom.toAlgebra
  letI ha₂ : Algebra ↑Γ(Y.base, D₂.U.1) k := (Spec.preimage c₂).hom.toAlgebra
  letI haR : Algebra ↑R k :=
    ((Spec.preimage c₁).hom.comp (algebraMap ↑R ↑Γ(Y.base, D₁.U.1))).toAlgebra
  have hof₁ : CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₁.U.1) k) = Spec.preimage c₁ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  have hof₂ : CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₂.U.1) k) = Spec.preimage c₂ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  have hsp₁ : D₁.specPt k = c₁ := by
    show Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₁.U.1) k)) = c₁
    rw [hof₁, Spec.map_preimage]
  have hsp₂ : D₂.specPt k = c₂ := by
    show Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₂.U.1) k)) = c₂
    rw [hof₂, Spec.map_preimage]
  have hgeom : D₁.geomPt (D₁.specPt k) = D₂.geomPt (D₂.specPt k) := by
    rw [geomPt, geomPt, hsp₁, hsp₂]
    exact hcc
  have htower₁ : (algebraMap ↑Γ(Y.base, D₁.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) = algebraMap ↑R k := rfl
  have hbase₁ : Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₁.U.1))) =
      D₁.U.2.isoSpec.inv ≫ D₁.U.1.ι ≫ Y.structMap := by
    rw [← halg₁, Iso.inv_hom_id_assoc]
  have hbase₂ : Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₂.U.1))) =
      D₂.U.2.isoSpec.inv ≫ D₂.U.1.ι ≫ Y.structMap := by
    rw [← halg₂, Iso.inv_hom_id_assoc]
  have htower₂ : (algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) = algebraMap ↑R k := by
    have hspec : Spec.map (CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
        (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↑R k)) := by
      rw [show CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
          (algebraMap ↑R ↑Γ(Y.base, D₂.U.1))) =
          CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) ≫
            CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₂.U.1) k) from
        CommRingCat.ofHom_comp _ _]
      rw [show CommRingCat.ofHom (algebraMap ↑R k) =
          CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) ≫
            CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D₁.U.1) k) from
        CommRingCat.ofHom_comp _ _]
      rw [Spec.map_comp, Spec.map_comp, hof₁, hof₂, Spec.map_preimage, Spec.map_preimage,
        hbase₁, hbase₂]
      have hw := congrArg (fun m ↦ m ≫ Y.structMap) hcc
      simp only [Category.assoc] at hw ⊢
      exact hw.symm
    have hring := Spec.map_injective hspec
    have := congrArg CommRingCat.Hom.hom hring
    simpa using this
  -- factor the two test maps through the fibre over the agreeing test point
  have hcond : (v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι) ≫ Y.curve.π =
      w ≫ D₁.geomPt (D₁.specPt k) := by
    rw [geomPt, hsp₁]
    calc (v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι) ≫ Y.curve.π
        = v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι ≫ Y.curve.π := Category.assoc _ _ _
      _ = v₁ ≫ pullback.snd Y.curve.π D₁.U.1.ι ≫ D₁.U.1.ι := by rw [pullback.condition]
      _ = (v₁ ≫ pullback.snd Y.curve.π D₁.U.1.ι) ≫ D₁.U.1.ι := (Category.assoc _ _ _).symm
      _ = (w ≫ c₁ ≫ D₁.U.2.isoSpec.inv) ≫ D₁.U.1.ι := by rw [hv₁]
      _ = w ≫ c₁ ≫ D₁.U.2.isoSpec.inv ≫ D₁.U.1.ι := by simp only [Category.assoc]
  set ρ : T ⟶ pullback Y.curve.π (D₁.geomPt (D₁.specPt k)) :=
    pullback.lift (v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι) w hcond with hρdef
  have hρfst : ρ ≫ pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) =
      v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι := pullback.lift_fst _ _ _
  have hρsnd : ρ ≫ pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) = w :=
    pullback.lift_snd _ _ _
  have hmf₁ : Fibre.map D₁ k ≫ pullback.fst Y.curve.π D₁.U.1.ι =
      pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫ 𝟙 Y.curve.E :=
    pullback.lift_fst _ _ _
  have hms₁ : Fibre.map D₁ k ≫ pullback.snd Y.curve.π D₁.U.1.ι =
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫
        (D₁.specPt k ≫ D₁.U.2.isoSpec.inv) :=
    pullback.lift_snd _ _ _
  have hρ₁ : ρ ≫ Fibre.map D₁ k = v₁ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc]
      calc ρ ≫ Fibre.map D₁ k ≫ pullback.fst Y.curve.π D₁.U.1.ι
          = ρ ≫ pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫ 𝟙 Y.curve.E := by
            rw [hmf₁]
        _ = (ρ ≫ pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k))) ≫ 𝟙 Y.curve.E :=
            (Category.assoc _ _ _).symm
        _ = v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι := by rw [Category.comp_id, hρfst]
    · rw [Category.assoc]
      calc ρ ≫ Fibre.map D₁ k ≫ pullback.snd Y.curve.π D₁.U.1.ι
          = ρ ≫ pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫
              (D₁.specPt k ≫ D₁.U.2.isoSpec.inv) := by rw [hms₁]
        _ = (ρ ≫ pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k))) ≫
              (D₁.specPt k ≫ D₁.U.2.isoSpec.inv) := (Category.assoc _ _ _).symm
        _ = w ≫ c₁ ≫ D₁.U.2.isoSpec.inv := by rw [hρsnd, hsp₁]
        _ = v₁ ≫ pullback.snd Y.curve.π D₁.U.1.ι := hv₁.symm
  have hch₁ := congrHom_hom_comp_fst Y.curve.π hgeom
  have hch₂ := congrHom_hom_comp_snd Y.curve.π hgeom
  have hmf₂ : Fibre.map D₂ k ≫ pullback.fst Y.curve.π D₂.U.1.ι =
      pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) ≫ 𝟙 Y.curve.E :=
    pullback.lift_fst _ _ _
  have hms₂ : Fibre.map D₂ k ≫ pullback.snd Y.curve.π D₂.U.1.ι =
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) ≫
        (D₂.specPt k ≫ D₂.U.2.isoSpec.inv) :=
    pullback.lift_snd _ _ _
  have hρ₂ : (ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫ Fibre.map D₂ k = v₂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc]
      calc (ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫
            Fibre.map D₂ k ≫ pullback.fst Y.curve.π D₂.U.1.ι
          = (ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫
              pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) ≫ 𝟙 Y.curve.E := by
            rw [hmf₂]
        _ = ρ ≫ ((pullback.congrHom rfl hgeom).hom ≫
              pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k))) := by
            rw [Category.comp_id]
            exact Category.assoc _ _ _
        _ = ρ ≫ pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) := by rw [hch₁]
        _ = v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι := hρfst
        _ = v₂ ≫ pullback.fst Y.curve.π D₂.U.1.ι := hE
    · rw [Category.assoc]
      calc (ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫
            Fibre.map D₂ k ≫ pullback.snd Y.curve.π D₂.U.1.ι
          = (ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫
              pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) ≫
                (D₂.specPt k ≫ D₂.U.2.isoSpec.inv) := by rw [hms₂]
        _ = (ρ ≫ ((pullback.congrHom rfl hgeom).hom ≫
              pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)))) ≫
                (D₂.specPt k ≫ D₂.U.2.isoSpec.inv) := by
            simp only [Category.assoc]
        _ = (ρ ≫ pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k))) ≫
              (D₂.specPt k ≫ D₂.U.2.isoSpec.inv) := by rw [hch₂]
        _ = w ≫ c₂ ≫ D₂.U.2.isoSpec.inv := by rw [hρsnd, hsp₂]
        _ = v₂ ≫ pullback.snd Y.curve.π D₂.U.1.ι := hv₂.symm
  have hagree := Fibre.map_topMap_agree D₁ D₂ k htower₁ htower₂ hgeom P hP
  calc v₁ ≫ D₁.topMap P hP
      = (ρ ≫ Fibre.map D₁ k) ≫ D₁.topMap P hP := by rw [hρ₁]
    _ = ρ ≫ Fibre.map D₁ k ≫ D₁.topMap P hP := Category.assoc _ _ _
    _ = ρ ≫ (pullback.congrHom rfl hgeom).hom ≫ Fibre.map D₂ k ≫ D₂.topMap P hP := by
        rw [hagree]
    _ = ((ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫ Fibre.map D₂ k) ≫ D₂.topMap P hP := by
        simp only [Category.assoc]
    _ = v₂ ≫ D₂.topMap P hP := by rw [hρ₂]

end MarkedChartData

end TopRestriction

section TopGlue

/-! ### Gluing the local classifying top maps over the curve cover (recipe step 3)

The chart cover of the base pulls back along `Y.curve.π` to an open cover of the total
space by the chart pullbacks; the local top maps agree on the overlaps (checked over the
affine cover of the base overlap, pulled back along the projection, via
`test_topMap_agree`), so they glue to the classifying top map `Y.curve.E ⟶ projModel
(tateCurveLocOver R)`.  All statements are phrased through the honest pullback
presentations (never through the cover fields), so every goal stays type-correct at
instance-transparency; the cover-field forms are recovered by definitional unfolding at
the gluing call sites. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R}

variable (Y) in
/-- The open cover of the total space of the curve by the chart pullbacks (the pullback
of the chart cover along `Y.curve.π`, re-presented with definitionally transparent
index/piece/map fields). -/
noncomputable def curveCover : Y.curve.E.OpenCover :=
  Scheme.Cover.copy ((chartCover Y).pullback₁ Y.curve.π) ↥Y.base
    (fun s ↦ pullback Y.curve.π (chartAt Y s).U.1.ι)
    (fun s ↦ pullback.fst Y.curve.π (chartAt Y s).U.1.ι)
    (Equiv.refl _) (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.id_comp _).symm)

/-- The local classifying top maps of the curve cover. -/
noncomputable def coverTopMap (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (s : ↥Y.base) :
    pullback Y.curve.π (chartAt Y s).U.1.ι ⟶ projModel (tateCurveLocOver R) :=
  letI := (chartAt Y s).chartAlgebra
  (chartAt Y s).topMap P hP

set_option backward.isDefEq.respectTransparency false in
/-- **Overlap compatibility** of the local classifying top maps. -/
theorem coverTopMap_compat (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (i j : ↥Y.base) :
    pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ coverTopMap P hP i =
      pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ coverTopMap P hP j := by
  letI := (chartAt Y i).chartAlgebra
  letI := (chartAt Y j).chartAlgebra
  -- the curve-overlap condition
  have hQ : pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.fst Y.curve.π (chartAt Y i).U.1.ι =
      pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.fst Y.curve.π (chartAt Y j).U.1.ι := pullback.condition
  -- the comparison from the curve overlap to the base overlap
  have hgcond : (pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.snd Y.curve.π (chartAt Y i).U.1.ι) ≫ (chartAt Y i).U.1.ι =
      (pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.snd Y.curve.π (chartAt Y j).U.1.ι) ≫ (chartAt Y j).U.1.ι := by
    have h1 := congrArg (fun m ↦ pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ m)
      (pullback.condition (f := Y.curve.π) (g := (chartAt Y i).U.1.ι))
    have h2 := congrArg (fun m ↦ pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ m)
      (pullback.condition (f := Y.curve.π) (g := (chartAt Y j).U.1.ι))
    have h3 := congrArg (fun m ↦ m ≫ Y.curve.π) hQ
    simp only [Category.assoc] at h1 h2 h3 ⊢
    rw [← h1, h3, h2]
  set g : pullback (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
      (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ⟶
      pullback (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι :=
    pullback.lift
      (pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.snd Y.curve.π (chartAt Y i).U.1.ι)
      (pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.snd Y.curve.π (chartAt Y j).U.1.ι) hgcond with hgdef
  have hgfst : g ≫ pullback.fst (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι =
      pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.snd Y.curve.π (chartAt Y i).U.1.ι := by
    rw [hgdef]; exact pullback.lift_fst _ _ _
  have hgsnd : g ≫ pullback.snd (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι =
      pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
        pullback.snd Y.curve.π (chartAt Y j).U.1.ι := by
    rw [hgdef]; exact pullback.lift_snd _ _ _
  -- morphism-extension over the affine cover of the base overlap, pulled back along `g`
  set 𝒱 := Scheme.affineCover (pullback (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι) with h𝒱
  apply Scheme.Cover.hom_ext (𝒱.pullback₁ g)
  intro z
  show pullback.fst g (𝒱.f z) ≫
      pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ coverTopMap P hP i =
    pullback.fst g (𝒱.f z) ≫
      pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ coverTopMap P hP j
  rw [← Category.assoc, ← Category.assoc]
  have hTcond : pullback.fst g (𝒱.f z) ≫ g = pullback.snd g (𝒱.f z) ≫ 𝒱.f z :=
    pullback.condition
  have hcc : ((Scheme.isoSpec (𝒱.X z)).inv ≫ 𝒱.f z ≫
        pullback.fst (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι ≫
        (chartAt Y i).U.2.isoSpec.hom) ≫
        (chartAt Y i).U.2.isoSpec.inv ≫ (chartAt Y i).U.1.ι =
      ((Scheme.isoSpec (𝒱.X z)).inv ≫ 𝒱.f z ≫
        pullback.snd (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι ≫
        (chartAt Y j).U.2.isoSpec.hom) ≫
        (chartAt Y j).U.2.isoSpec.inv ≫ (chartAt Y j).U.1.ι := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hw := congrArg (fun m ↦ (Scheme.isoSpec (𝒱.X z)).inv ≫ 𝒱.f z ≫ m)
      (pullback.condition (f := (chartAt Y i).U.1.ι) (g := (chartAt Y j).U.1.ι))
    simpa only [Category.assoc] using hw
  refine test_topMap_agree (chartAt Y i) (chartAt Y j)
    ((chartAt Y i).chartAlgebra_compatible) ((chartAt Y j).chartAlgebra_compatible)
    ↑Γ(𝒱.X z, ⊤) _ _ hcc P hP
    (pullback.snd g (𝒱.f z) ≫ (Scheme.isoSpec (𝒱.X z)).hom) _ _ ?_ ?_ ?_
  · -- hv₁
    calc (pullback.fst g (𝒱.f z) ≫
          pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
            (pullback.fst Y.curve.π (chartAt Y j).U.1.ι)) ≫
          pullback.snd Y.curve.π (chartAt Y i).U.1.ι
        = pullback.fst g (𝒱.f z) ≫
            (pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
              (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
              pullback.snd Y.curve.π (chartAt Y i).U.1.ι) := Category.assoc _ _ _
      _ = pullback.fst g (𝒱.f z) ≫
            (g ≫ pullback.fst (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι) := by rw [hgfst]
      _ = (pullback.fst g (𝒱.f z) ≫ g) ≫
            pullback.fst (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι :=
          (Category.assoc _ _ _).symm
      _ = (pullback.snd g (𝒱.f z) ≫ 𝒱.f z) ≫
            pullback.fst (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι := by rw [hTcond]
      _ = pullback.snd g (𝒱.f z) ≫ 𝒱.f z ≫
            pullback.fst (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι := Category.assoc _ _ _
      _ = (pullback.snd g (𝒱.f z) ≫ (Scheme.isoSpec (𝒱.X z)).hom) ≫
            ((Scheme.isoSpec (𝒱.X z)).inv ≫ 𝒱.f z ≫
              pullback.fst (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι ≫
              (chartAt Y i).U.2.isoSpec.hom) ≫ (chartAt Y i).U.2.isoSpec.inv := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
            Category.comp_id]
  · -- hv₂
    calc (pullback.fst g (𝒱.f z) ≫
          pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
            (pullback.fst Y.curve.π (chartAt Y j).U.1.ι)) ≫
          pullback.snd Y.curve.π (chartAt Y j).U.1.ι
        = pullback.fst g (𝒱.f z) ≫
            (pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
              (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
              pullback.snd Y.curve.π (chartAt Y j).U.1.ι) := Category.assoc _ _ _
      _ = pullback.fst g (𝒱.f z) ≫
            (g ≫ pullback.snd (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι) := by rw [hgsnd]
      _ = (pullback.fst g (𝒱.f z) ≫ g) ≫
            pullback.snd (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι :=
          (Category.assoc _ _ _).symm
      _ = (pullback.snd g (𝒱.f z) ≫ 𝒱.f z) ≫
            pullback.snd (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι := by rw [hTcond]
      _ = pullback.snd g (𝒱.f z) ≫ 𝒱.f z ≫
            pullback.snd (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι := Category.assoc _ _ _
      _ = (pullback.snd g (𝒱.f z) ≫ (Scheme.isoSpec (𝒱.X z)).hom) ≫
            ((Scheme.isoSpec (𝒱.X z)).inv ≫ 𝒱.f z ≫
              pullback.snd (chartAt Y i).U.1.ι (chartAt Y j).U.1.ι ≫
              (chartAt Y j).U.2.isoSpec.hom) ≫ (chartAt Y j).U.2.isoSpec.inv := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
            Category.comp_id]
  · -- hE: same composite to the total space of the curve
    calc (pullback.fst g (𝒱.f z) ≫
          pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
            (pullback.fst Y.curve.π (chartAt Y j).U.1.ι)) ≫
          pullback.fst Y.curve.π (chartAt Y i).U.1.ι
        = pullback.fst g (𝒱.f z) ≫
            (pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
              (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
              pullback.fst Y.curve.π (chartAt Y i).U.1.ι) := Category.assoc _ _ _
      _ = pullback.fst g (𝒱.f z) ≫
            (pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
              (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫
              pullback.fst Y.curve.π (chartAt Y j).U.1.ι) := by rw [hQ]
      _ = (pullback.fst g (𝒱.f z) ≫
            pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
              (pullback.fst Y.curve.π (chartAt Y j).U.1.ι)) ≫
            pullback.fst Y.curve.π (chartAt Y j).U.1.ι := (Category.assoc _ _ _).symm

/-- **The glued classifying top map** `Y.curve.E ⟶ projModel (tateCurveLocOver R)`. -/
noncomputable def gluedTopMap (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) :
    Y.curve.E ⟶ projModel (tateCurveLocOver R) :=
  (curveCover Y).glueMorphisms (coverTopMap P hP)
    (fun i j ↦ coverTopMap_compat P hP i j)

@[reassoc (attr := simp)]
theorem ι_gluedTopMap (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (s : ↥Y.base) :
    pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ gluedTopMap P hP =
      coverTopMap P hP s :=
  Scheme.Cover.ι_glueMorphisms (curveCover Y) (coverTopMap P hP)
    (fun i j ↦ coverTopMap_compat P hP i j) s

end MarkedChartData

end TopGlue

section GluedClauses

/-! ### The clauses of the glued classifying square (recipe step 4)

The glued top map fits in a commuting square over the glued base map; the square is
cartesian (the comparison into the pullback is an isomorphism because it is one over
every chart, and being an isomorphism is Zariski-local on the target); it is pointed and
carries the section to the atlas marking (both checked over the chart cover). -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R}

/-- The glued square commutes. -/
theorem gluedTopMap_π (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    gluedTopMap P hP ≫ projModelπ (tateCurveLocOver R) =
      Y.curve.π ≫ gluedBaseMap P hP := by
  have hs : ∀ s : ↥Y.base,
      pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫
        (gluedTopMap P hP ≫ projModelπ (tateCurveLocOver R)) =
      pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ (Y.curve.π ≫ gluedBaseMap P hP) := by
    intro s
    letI := (chartAt Y s).chartAlgebra
    have h1 : pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫
        (gluedTopMap P hP ≫ projModelπ (tateCurveLocOver R)) =
        coverTopMap P hP s ≫ projModelπ (tateCurveLocOver R) := by
      rw [← Category.assoc, ι_gluedTopMap]
    have h2 : coverTopMap P hP s ≫ projModelπ (tateCurveLocOver R) =
        pullback.snd Y.curve.π (chartAt Y s).U.1.ι ≫ (chartAt Y s).baseMap P hP :=
      ((chartAt Y s).topMap_isPullback P hP).w
    have h3 : pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫
        (Y.curve.π ≫ gluedBaseMap P hP) =
        pullback.snd Y.curve.π (chartAt Y s).U.1.ι ≫
          ((chartAt Y s).U.1.ι ≫ gluedBaseMap P hP) := by
      rw [← Category.assoc, pullback.condition (f := Y.curve.π) (g := (chartAt Y s).U.1.ι),
        Category.assoc]
    rw [h1, h2, h3, ι_gluedBaseMap]
    exact rfl
  apply Scheme.Cover.hom_ext (curveCover Y)
  intro s
  exact hs s

/-- The glued square is pointed. -/
theorem gluedTopMap_zero (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    Y.curve.zero ≫ gluedTopMap P hP =
      gluedBaseMap P hP ≫ projModelZero (tateCurveLocOver R) := by
  have hs : ∀ s : ↥Y.base,
      (chartAt Y s).U.1.ι ≫ (Y.curve.zero ≫ gluedTopMap P hP) =
      (chartAt Y s).U.1.ι ≫ (gluedBaseMap P hP ≫ projModelZero (tateCurveLocOver R)) := by
    intro s
    letI := (chartAt Y s).chartAlgebra
    have hlift : (pullback.lift ((chartAt Y s).U.1.ι ≫ Y.curve.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) :
          (chartAt Y s).U.1.toScheme ⟶ pullback Y.curve.π (chartAt Y s).U.1.ι) ≫
        pullback.fst Y.curve.π (chartAt Y s).U.1.ι =
        (chartAt Y s).U.1.ι ≫ Y.curve.zero := pullback.lift_fst _ _ _
    calc (chartAt Y s).U.1.ι ≫ (Y.curve.zero ≫ gluedTopMap P hP)
        = ((chartAt Y s).U.1.ι ≫ Y.curve.zero) ≫ gluedTopMap P hP :=
          (Category.assoc _ _ _).symm
      _ = (pullback.lift ((chartAt Y s).U.1.ι ≫ Y.curve.zero) (𝟙 _)
            (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
            pullback.fst Y.curve.π (chartAt Y s).U.1.ι) ≫ gluedTopMap P hP := by
          rw [hlift]
      _ = pullback.lift ((chartAt Y s).U.1.ι ≫ Y.curve.zero) (𝟙 _)
            (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
            (pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ gluedTopMap P hP) :=
          Category.assoc _ _ _
      _ = pullback.lift ((chartAt Y s).U.1.ι ≫ Y.curve.zero) (𝟙 _)
            (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
            coverTopMap P hP s := by rw [ι_gluedTopMap]
      _ = (chartAt Y s).baseMap P hP ≫ projModelZero (tateCurveLocOver R) :=
          (chartAt Y s).topMap_zero P hP
      _ = ((chartAt Y s).U.1.ι ≫ gluedBaseMap P hP) ≫
            projModelZero (tateCurveLocOver R) := by rw [ι_gluedBaseMap]; exact rfl
      _ = (chartAt Y s).U.1.ι ≫ (gluedBaseMap P hP ≫ projModelZero (tateCurveLocOver R)) :=
          Category.assoc _ _ _
  apply Scheme.Cover.hom_ext (chartCover Y)
  intro s
  exact hs s

/-- The glued square carries the section to the atlas marking. -/
theorem gluedTopMap_marking (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    P.1 ≫ gluedTopMap P hP = gluedBaseMap P hP ≫ tateP0mor R := by
  have hs : ∀ s : ↥Y.base,
      (chartAt Y s).U.1.ι ≫ (P.1 ≫ gluedTopMap P hP) =
      (chartAt Y s).U.1.ι ≫ (gluedBaseMap P hP ≫ tateP0mor R) := by
    intro s
    letI := (chartAt Y s).chartAlgebra
    have hres : (chartAt Y s).restrictSection P ≫
        pullback.fst Y.curve.π (chartAt Y s).U.1.ι = (chartAt Y s).U.1.ι ≫ P.1 :=
      pullback.lift_fst _ _ _
    calc (chartAt Y s).U.1.ι ≫ (P.1 ≫ gluedTopMap P hP)
        = ((chartAt Y s).U.1.ι ≫ P.1) ≫ gluedTopMap P hP := (Category.assoc _ _ _).symm
      _ = ((chartAt Y s).restrictSection P ≫
            pullback.fst Y.curve.π (chartAt Y s).U.1.ι) ≫ gluedTopMap P hP := by
          rw [hres]
      _ = (chartAt Y s).restrictSection P ≫
            (pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ gluedTopMap P hP) :=
          Category.assoc _ _ _
      _ = (chartAt Y s).restrictSection P ≫ coverTopMap P hP s := by rw [ι_gluedTopMap]
      _ = (chartAt Y s).baseMap P hP ≫ tateP0mor R := (chartAt Y s).topMap_marking P hP
      _ = ((chartAt Y s).U.1.ι ≫ gluedBaseMap P hP) ≫ tateP0mor R := by
          rw [ι_gluedBaseMap]; exact rfl
      _ = (chartAt Y s).U.1.ι ≫ (gluedBaseMap P hP ≫ tateP0mor R) := Category.assoc _ _ _
  apply Scheme.Cover.hom_ext (chartCover Y)
  intro s
  exact hs s

/-- **The glued square is cartesian**: the comparison into the pullback is an isomorphism
chart-locally (by `topMap_isPullback`), and being an isomorphism is Zariski-local on the
target. -/
theorem gluedTopMap_isPullback (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) :
    IsPullback (gluedTopMap P hP) Y.curve.π (projModelπ (tateCurveLocOver R))
      (gluedBaseMap P hP) := by
  set χ : Y.curve.E ⟶ pullback (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP) :=
    pullback.lift (gluedTopMap P hP) Y.curve.π (gluedTopMap_π P hP) with hχdef
  have hχfst : χ ≫ pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP) =
      gluedTopMap P hP := by rw [hχdef]; exact pullback.lift_fst _ _ _
  have hχsnd : χ ≫ pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP) =
      Y.curve.π := by rw [hχdef]; exact pullback.lift_snd _ _ _
  have hpiece : ∀ s : ↥Y.base, IsIso (pullback.snd χ
      (pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
        (chartAt Y s).U.1.ι)) := by
    intro s
    letI := (chartAt Y s).chartAlgebra
    -- the W-piece square, pasted to the cospan (projModelπ, baseMap)
    have hW : IsPullback
        (pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι ≫
          pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
        (pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι)
        (projModelπ (tateCurveLocOver R)) ((chartAt Y s).baseMap P hP) := by
      have h3 := (IsPullback.of_hasPullback
          (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι).paste_horiz
        (IsPullback.of_hasPullback (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
      rw [ι_gluedBaseMap P hP s] at h3
      exact h3
    -- the two pullback presentations over the chart
    have htop := (chartAt Y s).topMap_isPullback P hP
    -- the Q-side pasting: the χ-pullback of the piece is a pullback of π along the chart
    have hQ2 := (IsPullback.of_hasPullback χ
        (pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι)).paste_vert
      (IsPullback.of_hasPullback
        (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
        (chartAt Y s).U.1.ι)
    rw [hχsnd] at hQ2
    -- the comparison equals the composite of the two canonical pullback isomorphisms
    set σ := htop.isoIsPullback _ _ hW with hσdef
    set τ := hQ2.isoIsPullback _ _
      (IsPullback.of_hasPullback Y.curve.π (chartAt Y s).U.1.ι) with hτdef
    have hσfst : σ.hom ≫
        (pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι ≫
          pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)) =
        (chartAt Y s).topMap P hP := by
      rw [hσdef]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _
    have hσsnd : σ.hom ≫
        pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι =
        pullback.snd Y.curve.π (chartAt Y s).U.1.ι := by
      rw [hσdef]; exact IsPullback.isoIsPullback_hom_snd _ _ _ _
    have hτfst : τ.hom ≫ pullback.fst Y.curve.π (chartAt Y s).U.1.ι =
        pullback.fst χ (pullback.fst
          (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι) := by
      rw [hτdef]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _
    have hτsnd : τ.hom ≫ pullback.snd Y.curve.π (chartAt Y s).U.1.ι =
        pullback.snd χ (pullback.fst
          (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι) ≫
          pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
            (chartAt Y s).U.1.ι := by
      rw [hτdef]; exact IsPullback.isoIsPullback_hom_snd _ _ _ _
    have hQcond : pullback.fst χ (pullback.fst
          (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι) ≫ χ =
        pullback.snd χ (pullback.fst
          (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι) ≫
          pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
            (chartAt Y s).U.1.ι := pullback.condition
    have hkey : pullback.snd χ
        (pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
          (chartAt Y s).U.1.ι) = τ.hom ≫ σ.hom := by
      refine pullback.hom_ext ?_ ?_
      · -- compare into the W-piece, itself by the universal property of W
        refine pullback.hom_ext ?_ ?_
        · -- the projModel component
          calc (pullback.snd χ (pullback.fst
                (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                (chartAt Y s).U.1.ι) ≫
                pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R))
                  (gluedBaseMap P hP)) (chartAt Y s).U.1.ι) ≫
                pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)
              = (pullback.fst χ (pullback.fst
                  (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                  (chartAt Y s).U.1.ι) ≫ χ) ≫
                  pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP) := by
                rw [hQcond]
            _ = pullback.fst χ (pullback.fst
                  (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                  (chartAt Y s).U.1.ι) ≫
                  (χ ≫ pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)) :=
                Category.assoc _ _ _
            _ = pullback.fst χ (pullback.fst
                  (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                  (chartAt Y s).U.1.ι) ≫ gluedTopMap P hP := by rw [hχfst]
            _ = (τ.hom ≫ pullback.fst Y.curve.π (chartAt Y s).U.1.ι) ≫
                  gluedTopMap P hP := by rw [hτfst]
            _ = τ.hom ≫ (pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫
                  gluedTopMap P hP) := Category.assoc _ _ _
            _ = τ.hom ≫ coverTopMap P hP s := by rw [ι_gluedTopMap]
            _ = τ.hom ≫ (σ.hom ≫
                  (pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R))
                    (gluedBaseMap P hP)) (chartAt Y s).U.1.ι ≫
                    pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))) := by
                rw [hσfst]; rfl
            _ = ((τ.hom ≫ σ.hom) ≫
                  pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R))
                    (gluedBaseMap P hP)) (chartAt Y s).U.1.ι) ≫
                  pullback.fst (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP) := by
                simp only [Category.assoc]
        · -- the base component
          calc (pullback.snd χ (pullback.fst
                (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                (chartAt Y s).U.1.ι) ≫
                pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R))
                  (gluedBaseMap P hP)) (chartAt Y s).U.1.ι) ≫
                pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)
              = (pullback.fst χ (pullback.fst
                  (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                  (chartAt Y s).U.1.ι) ≫ χ) ≫
                  pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP) := by
                rw [hQcond]
            _ = pullback.fst χ (pullback.fst
                  (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                  (chartAt Y s).U.1.ι) ≫
                  (χ ≫ pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)) :=
                Category.assoc _ _ _
            _ = pullback.fst χ (pullback.fst
                  (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
                  (chartAt Y s).U.1.ι) ≫ Y.curve.π := by rw [hχsnd]
            _ = (τ.hom ≫ pullback.fst Y.curve.π (chartAt Y s).U.1.ι) ≫ Y.curve.π := by
                rw [hτfst]
            _ = τ.hom ≫ (pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ Y.curve.π) :=
                Category.assoc _ _ _
            _ = τ.hom ≫ (pullback.snd Y.curve.π (chartAt Y s).U.1.ι ≫
                  (chartAt Y s).U.1.ι) := by
                rw [pullback.condition (f := Y.curve.π) (g := (chartAt Y s).U.1.ι)]
            _ = τ.hom ≫ ((σ.hom ≫
                  pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R))
                    (gluedBaseMap P hP)) (chartAt Y s).U.1.ι) ≫
                  (chartAt Y s).U.1.ι) := by rw [hσsnd]
            _ = (τ.hom ≫ σ.hom) ≫
                  (pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R))
                    (gluedBaseMap P hP)) (chartAt Y s).U.1.ι ≫
                    (chartAt Y s).U.1.ι) := by simp only [Category.assoc]
            _ = (τ.hom ≫ σ.hom) ≫
                  (pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R))
                    (gluedBaseMap P hP)) (chartAt Y s).U.1.ι ≫
                    pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)) := by
                rw [pullback.condition (f := pullback.snd (projModelπ (tateCurveLocOver R))
                  (gluedBaseMap P hP)) (g := (chartAt Y s).U.1.ι)]
            _ = ((τ.hom ≫ σ.hom) ≫
                  pullback.fst (pullback.snd (projModelπ (tateCurveLocOver R))
                    (gluedBaseMap P hP)) (chartAt Y s).U.1.ι) ≫
                  pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP) :=
                (Category.assoc _ _ _).symm
      · -- the chart component
        calc pullback.snd χ (pullback.fst
              (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP))
              (chartAt Y s).U.1.ι) ≫
              pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R))
                (gluedBaseMap P hP)) (chartAt Y s).U.1.ι
            = τ.hom ≫ pullback.snd Y.curve.π (chartAt Y s).U.1.ι := hτsnd.symm
          _ = τ.hom ≫ (σ.hom ≫
                pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R))
                  (gluedBaseMap P hP)) (chartAt Y s).U.1.ι) := by rw [hσsnd]
          _ = (τ.hom ≫ σ.hom) ≫
                pullback.snd (pullback.snd (projModelπ (tateCurveLocOver R))
                  (gluedBaseMap P hP)) (chartAt Y s).U.1.ι := (Category.assoc _ _ _).symm
    rw [hkey]
    infer_instance
  haveI hiso : IsIso χ := by
    have h := IsZariskiLocalAtTarget.of_openCover
      (P := MorphismProperty.isomorphisms Scheme)
      (f := χ) ((chartCover Y).pullback₁
        (pullback.snd (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)))
      (fun s ↦ hpiece s)
    exact h
  exact IsPullback.of_iso_pullback ⟨gluedTopMap_π P hP⟩ (asIso χ) hχfst hχsnd

end MarkedChartData

end GluedClauses

section GluedHom

/-! ### The classifying `Ell/R` morphism of the glued data (recipe step 4, assembly)

The glued base and top maps assemble to an `Ell/R` morphism `Y ⟶ tateEllObj R` through
the `tateUniversal ≟ tateGeom` bridge, and pulling the marked point back along it
recovers the section — the existence half of the classifying clause. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R}

/-- The glued cartesian square, transported across the `tateUniversal` bridge. -/
theorem gluedTopMapEll_isPullback (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) :
    IsPullback (gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm) Y.curve.π
      ((tateUniversal R).π) (gluedBaseMap P hP) := by
  have hsq : CommSq (eqToHom (tateUniversal_E_eq R).symm)
      (projModelπ (tateCurveLocOver R)) ((tateUniversal R).π) (𝟙 (tateBase R)) :=
    ⟨by rw [tateUniversal_eqToHom_π, Category.comp_id]⟩
  have h := (gluedTopMap_isPullback P hP).paste_horiz (IsPullback.of_horiz_isIso hsq)
  rw [Category.comp_id] at h
  exact h

/-- The glued pointedness, transported across the `tateUniversal` bridge. -/
theorem gluedTopMapEll_zero (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) :
    Y.curve.zero ≫ (gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm) =
      gluedBaseMap P hP ≫ (tateUniversal R).zero := by
  have hz : (tateUniversal R).zero =
      projModelZero (tateCurveLocOver R) ≫ eqToHom (tateUniversal_E_eq R).symm :=
    eqToGeom_zero' (tateUniversal_geom R)
  rw [hz, ← Category.assoc, gluedTopMap_zero P hP, Category.assoc]

/-- **The classifying `Ell/R` morphism** of a nowhere-small-order section. -/
noncomputable def gluedHom (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) : Y ⟶ tateEllObj R :=
  EllObj.tateClassifyingHom R Y (gluedBaseMap P hP) (gluedBaseMap_over P hP)
    (gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm)
    (gluedTopMapEll_isPullback P hP) (gluedTopMapEll_zero P hP)

@[simp]
theorem gluedHom_baseHom (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    (gluedHom P hP).baseHom = gluedBaseMap P hP := rfl

@[simp]
theorem gluedHom_top (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    (gluedHom P hP).top = gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm := rfl

/-- **The existence half of the classifying clause**: pulling the marked point back along
the glued classifying morphism recovers the section. -/
theorem gluedHom_pullSection (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) :
    EllHom.pullSection R (gluedHom P hP) (tateMarkedPoint R) = P := by
  refine EllObj.tateClassifyingHom.pullSection_eq R Y (gluedBaseMap P hP)
    (gluedBaseMap_over P hP) (gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm)
    (gluedTopMapEll_isPullback P hP) (gluedTopMapEll_zero P hP) (tateMarkedPoint R) P ?_
  show P.1 ≫ gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm =
    gluedBaseMap P hP ≫ (tateMarkedPoint R).1
  have hm : (tateMarkedPoint R).1 = tateP0mor R ≫ eqToHom (tateUniversal_E_eq R).symm :=
    rfl
  rw [hm, ← Category.assoc, gluedTopMap_marking P hP, Category.assoc]

end MarkedChartData

end GluedHom

section SelfClassification

/-! ### Self-classification of the pulled-back universal curve (recipe step 5 substrate)

The T-E1 normalisation of the base-changed universal Tate curve at a `(0,0)`-marked point
is the identity variable change, so its classifying top map is the base-change morphism
itself.  This is the crux that pins the `top` component of an arbitrary classifying
morphism against the glued one. -/

variable {A : Type u} [CommRing A]

/-- The atlas curve coefficient `a₁` is the first universal coefficient. -/
theorem TateAtlas.CurveLocOver.a₁ (R : CommRingCat.{u}) :
    (tateCurveLocOver R).a₁ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0) := by
  simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map, tateCurve]
  simp

/-- The atlas curve coefficient `a₂` is the second universal coefficient. -/
theorem TateAtlas.CurveLocOver.a₂ (R : CommRingCat.{u}) :
    (tateCurveLocOver R).a₂ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1) := by
  simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map, tateCurve]
  simp

/-- The universal Tate-normal curve over `R[A,B]` is Tate-normal. -/
theorem TateAtlas.CurveOver.isTateNormal (R : CommRingCat.{u}) :
    (tateCurveOver R).IsTateNormal := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [tateCurveOver, tateCurve, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

/-- The atlas curve is Tate-normal. -/
theorem TateAtlas.CurveLocOver.isTateNormal (R : CommRingCat.{u}) :
    (tateCurveLocOver R).IsTateNormal :=
  (TateAtlas.CurveOver.isTateNormal R).map
    (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R))

variable (R : CommRingCat.{u}) [Algebra ↑R A] [Algebra (tateRingOver R) A]

omit [Algebra ↑R A] in
/-- Auxiliary for `projTateMap_map_tate`: at the `(0,0)`-marking the T-E1 normalisation of
the base-changed universal Tate curve is the identity variable change. Isolated so the
concrete Tate coefficients unfold in a dedicated elaboration unit. -/
private lemma projTateMap_map_tate_hC1
    [((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).IsElliptic]
    (g : SpecPoints (projModel ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)))
      (projModelπ ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) A)
    (hZ : InZChart ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) g)
    (hx : ZChart.eval _ g hZ
      (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) = 0)
    (hy : ZChart.eval _ g hZ
      (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) = 0)
    (hord : NowhereOrderLEThree ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
      (ZChart.eval _ g hZ (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (ZChart.eval _ g hZ
        (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))) :
    TateAtlas.TateNormal.variableChange
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
      (ZChart.eval _ g hZ (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (ZChart.eval _ g hZ (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (ZChart.eval_equation_self _ g hZ) hord = 1 := by
  have htn : ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).IsTateNormal :=
    (TateAtlas.CurveLocOver.isTateNormal R).map (algebraMap (tateRingOver R) A)
  refine (TateAtlas.TateNormal.variableChange_unique _ _ _
    (ZChart.eval_equation_self _ g hZ) hord 1 ⟨?_, ?_, ?_⟩).symm
  · rw [one_smul]
    exact htn
  · exact hx.symm
  · exact hy.symm

/-- Auxiliary for `projTateMap_map_tate`: the pointed atlas algebra map at the `(0,0)`-marking
of the base-changed universal Tate curve is the base-change algebra map itself. Isolated so the
concrete Tate coefficients unfold in a dedicated elaboration unit. -/
private lemma projTateMap_map_tate_hL
    [((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).IsElliptic]
    (htower : (algebraMap (tateRingOver R) A).comp (algebraMap ↑R (tateRingOver R)) =
      algebraMap ↑R A)
    (g : SpecPoints (projModel ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)))
      (projModelπ ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) A)
    (hZ : InZChart ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) g)
    (hord : NowhereOrderLEThree ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
      (ZChart.eval _ g hZ (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (ZChart.eval _ g hZ
        (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)))))
    (hC1 : TateAtlas.TateNormal.variableChange
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
      (ZChart.eval _ g hZ (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (ZChart.eval _ g hZ (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (ZChart.eval_equation_self _ g hZ) hord = 1) :
    ((TateAtlas.Point.ringOverAlgLift R
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) _ _
      (ZChart.eval_equation_self _ g hZ) hord : tateRingOver R →ₐ[R] A) :
        tateRingOver R →+* A) = algebraMap (tateRingOver R) A := by
  have hAlg : ∀ r : ↑R, algebraMap (tateRingOver R) A
      (algebraMap ↑R (tateRingOver R) r) = algebraMap ↑R A r := fun r ↦ by
    rw [← htower]; rfl
  have hext := TateAtlas.RingOver.algHom_ext R
    (TateAtlas.Point.ringOverAlgLift R
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) _ _
      (ZChart.eval_equation_self _ g hZ) hord)
    ({ toRingHom := algebraMap (tateRingOver R) A, commutes' := hAlg } :
      tateRingOver R →ₐ[R] A) ?_ ?_
  · exact congrArg (fun φ : tateRingOver R →ₐ[R] A ↦ (φ : tateRingOver R →+* A)) hext
  · rw [TateAtlas.Point.ringOverAlgLift_X_zero, hC1, one_smul]
    show ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).a₁ =
      algebraMap (tateRingOver R) A
        (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 0))
    rw [WeierstrassCurve.map_a₁, TateAtlas.CurveLocOver.a₁]
  · rw [TateAtlas.Point.ringOverAlgLift_X_one, hC1, one_smul]
    show ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).a₂ =
      algebraMap (tateRingOver R) A
        (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 1))
    rw [WeierstrassCurve.map_a₂, TateAtlas.CurveLocOver.a₂]

/-- **Self-classification**: the classifying top map of the base-changed universal Tate
curve at a `(0,0)`-marked point is the base-change morphism. -/
theorem projTateMap_map_tate
    [((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).IsElliptic]
    (htower : (algebraMap (tateRingOver R) A).comp (algebraMap ↑R (tateRingOver R)) =
      algebraMap ↑R A)
    (g : SpecPoints (projModel ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)))
      (projModelπ ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) A)
    (hZ : InZChart ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) g)
    (hx : ZChart.eval _ g hZ
      (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) = 0)
    (hy : ZChart.eval _ g hZ
      (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) = 0)
    (hord : NowhereOrderLEThree ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
      (ZChart.eval _ g hZ (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (ZChart.eval _ g hZ
        (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))) :
    projTateMap R ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) g hZ hord =
      projModelBaseChange (algebraMap (tateRingOver R) A) (tateCurveLocOver R) := by
  -- the T-E1 normalisation at the (0,0)-marking is the identity variable change
  have hC1 := projTateMap_map_tate_hC1 R g hZ hx hy hord
  -- the pointed atlas algebra map is the algebra map itself
  have hL := projTateMap_map_tate_hL R htower g hZ hord hC1
  rw [projTateMap_unfold R ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
    g hZ hord]
  have hinv1 := projModelVCIso_inv_congr hC1
    ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
  have hinv2 : (projModelVCIso (1 : WeierstrassCurve.VariableChange A)
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))).inv =
      eqToHom (congrArg projModel (one_smul (WeierstrassCurve.VariableChange A)
        ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)))).symm := by
    rw [← cancel_epi (projModelVCIso (1 : WeierstrassCurve.VariableChange A)
        ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))).hom,
      Iso.hom_inv_id, projModelVCIso_one, eqToHom_trans, eqToHom_refl]
  have hbcL := ProjModelBaseChange.ringHom_congr hL (tateCurveLocOver R)
  rw [hinv1, hinv2, hbcL]
  rw [Category.assoc, eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

end SelfClassification

section InducedChart

/-! ### The chart induced by a classifying square (recipe step 5, T7 substrate)

Any cartesian pointed square from `Y.curve` to the universal Tate curve induces, on each
affine chart of the base, a second marked chart of `Y.curve`: the model is the universal
Tate curve base-changed along the affine restriction of the base map, the trivialisation
is the restricted square.  The data is taken in raw component form (a base map to
`tateBase R` and a top map to the projective model, with the cartesian/pointedness
witnesses), so every statement lives in the honest pullback spelling; a classifying
`Ell/R` morphism `f` instantiates them by its fields at the assembly site. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (fb : Y.base ⟶ tateBase R) (ftop : Y.curve.E ⟶ (tateUniversal R).E)

/-- The affine test map of a chart under a classifying base map. -/
noncomputable def classifyingSpecMap : Spec (CommRingCat.of ↑Γ(Y.base, D.U.1)) ⟶
    tateBase R :=
  D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ fb

variable (hPB : IsPullback ftop Y.curve.π ((tateUniversal R).π) fb)

include hPB in
/-- The restricted cartesian square of a classifying square over a chart. -/
theorem classifying_isPullback :
    IsPullback (pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R))
      (pullback.snd Y.curve.π D.U.1.ι ≫ D.U.2.isoSpec.hom)
      (projModelπ (tateCurveLocOver R))
      (D.classifyingSpecMap fb) := by
  have h1 : IsPullback (pullback.fst Y.curve.π D.U.1.ι ≫ ftop)
      (pullback.snd Y.curve.π D.U.1.ι) ((tateUniversal R).π) (D.U.1.ι ≫ fb) :=
    (IsPullback.of_hasPullback Y.curve.π D.U.1.ι).paste_horiz hPB
  have h2 : IsPullback (eqToHom (tateUniversal_E_eq R)) ((tateUniversal R).π)
      (projModelπ (tateCurveLocOver R)) (𝟙 (tateBase R)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact (tateUniversal_π_eq R).symm⟩
  have h3 := h1.paste_horiz h2
  rw [Category.comp_id] at h3
  have h4 : IsPullback (D.U.1.ι ≫ fb) (D.U.2.isoSpec.hom) (𝟙 (tateBase R))
      (D.classifyingSpecMap fb) :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id, classifyingSpecMap, Iso.hom_inv_id_assoc]⟩
  have h5 := h3.paste_vert h4
  rw [Category.comp_id] at h5
  simpa only [Category.assoc] using h5

include hPB in
/-- The restricted square with the classifying test map in algebra form. -/
theorem classifying_isPullback' :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    IsPullback (pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R))
      (pullback.snd Y.curve.π D.U.1.ι ≫ D.U.2.isoSpec.hom)
      (projModelπ (tateCurveLocOver R))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))) := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  have hof : CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)) =
      Spec.preimage (D.classifyingSpecMap fb) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  rw [hof, Spec.map_preimage]
  exact D.classifying_isPullback fb ftop hPB

variable (hzw : Y.curve.zero ≫ ftop = fb ≫ (tateUniversal R).zero)

/-- **The induced marked chart** of a classifying square over a chart of the base. -/
noncomputable def inducedChart : MarkedChartData R Y :=
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  { U := D.U
    W := (tateCurveLocOver R).map (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
    hell := inferInstanceAs
      (((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).IsElliptic)
    e := pullbackChartIso (tateCurveLocOver R) (D.classifying_isPullback' fb ftop hPB)
    heπ := pullbackChartIso_hom_π (tateCurveLocOver R)
      (D.classifying_isPullback' fb ftop hPB)
    hez := by
      refine pullbackChartIso_zero (tateCurveLocOver R)
        (D.classifying_isPullback' fb ftop hPB) _ ?_ ?_
      · -- the zero lift splits the chart projection
        rw [← Category.assoc]
        have hs : (D.U.2.isoSpec.inv ≫ pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
            (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id,
              Category.id_comp])) ≫ pullback.snd Y.curve.π D.U.1.ι =
            D.U.2.isoSpec.inv := by
          rw [Category.assoc, pullback.lift_snd, Category.comp_id]
        rw [hs, Iso.inv_hom_id]
      · -- the zero lift hits the atlas zero through the classifying square
        have hz : (tateUniversal R).zero =
            projModelZero (tateCurveLocOver R) ≫ eqToHom (tateUniversal_E_eq R).symm :=
          eqToGeom_zero' (tateUniversal_geom R)
        have hof : CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)) =
            Spec.preimage (D.classifyingSpecMap fb) := by
          rw [RingHom.algebraMap_toAlgebra]
          exact CommRingCat.ofHom_hom _
        rw [hof, Spec.map_preimage]
        calc (D.U.2.isoSpec.inv ≫ pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
              (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id,
                Category.id_comp])) ≫
              (pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R))
            = D.U.2.isoSpec.inv ≫ (pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
                (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id,
                  Category.id_comp]) ≫ pullback.fst Y.curve.π D.U.1.ι) ≫
                ftop ≫ eqToHom (tateUniversal_E_eq R) := by
              simp only [Category.assoc]
          _ = D.U.2.isoSpec.inv ≫ (D.U.1.ι ≫ Y.curve.zero) ≫
                ftop ≫ eqToHom (tateUniversal_E_eq R) := by
              rw [pullback.lift_fst]
          _ = D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ (Y.curve.zero ≫ ftop) ≫
                eqToHom (tateUniversal_E_eq R) := by
              simp only [Category.assoc]
          _ = D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ (fb ≫ (tateUniversal R).zero) ≫
                eqToHom (tateUniversal_E_eq R) := by
              rw [hzw]
          _ = (D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ fb) ≫ (tateUniversal R).zero ≫
                eqToHom (tateUniversal_E_eq R) := by
              simp only [Category.assoc]
          _ = D.classifyingSpecMap fb ≫ projModelZero (tateCurveLocOver R) := by
              rw [hz]
              simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
              rfl }

@[simp]
theorem inducedChart_U : (D.inducedChart fb ftop hPB hzw).U = D.U := rfl

variable (P : Y.curve.Section)

/-- The section, read in the induced chart, with its honest model spelling. -/
noncomputable def inducedPt :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    SpecPoints
      (projModel ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))))
      (projModelπ ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))))
      ↑Γ(Y.base, D.U.1) :=
  (D.inducedChart fb ftop hPB hzw).pt P

/-- The induced point lies in the `Z`-chart. -/
theorem inducedPt_mem_zChart (hP : Y.curve.NowhereGeomOrderLEThree P) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    InZChart ((tateCurveLocOver R).map
      (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
      (D.inducedPt fb ftop hPB hzw P) :=
  (D.inducedChart fb ftop hPB hzw).pt_mem_zChart P hP

/-- **The induced point hits the atlas marking under base change** (the pulled-back
marking equation, in chart coordinates). -/
theorem inducedPt_comp_bc (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    (D.inducedPt fb ftop hPB hzw P).1 ≫
      projModelBaseChange (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
        (tateCurveLocOver R) =
      D.classifyingSpecMap fb ≫ tateP0mor R := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  have hbc : (pullbackChartIso (tateCurveLocOver R)
      (D.classifying_isPullback' fb ftop hPB)).hom ≫
      projModelBaseChange (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
        (tateCurveLocOver R) =
      pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R) :=
    pullbackChartIso_hom_bc (tateCurveLocOver R) (D.classifying_isPullback' fb ftop hPB)
  have hres : D.restrictSection P ≫ pullback.fst Y.curve.π D.U.1.ι =
      D.U.1.ι ≫ P.1 := pullback.lift_fst _ _ _
  have hm : (tateMarkedPoint R).1 = tateP0mor R ≫ eqToHom (tateUniversal_E_eq R).symm :=
    rfl
  show (D.U.2.isoSpec.inv ≫ D.restrictSection P ≫
      (pullbackChartIso (tateCurveLocOver R)
        (D.classifying_isPullback' fb ftop hPB)).hom) ≫
      projModelBaseChange (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
        (tateCurveLocOver R) =
    D.classifyingSpecMap fb ≫ tateP0mor R
  calc (D.U.2.isoSpec.inv ≫ D.restrictSection P ≫
      (pullbackChartIso (tateCurveLocOver R)
        (D.classifying_isPullback' fb ftop hPB)).hom) ≫
      projModelBaseChange (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
        (tateCurveLocOver R)
      = D.U.2.isoSpec.inv ≫ D.restrictSection P ≫
          ((pullbackChartIso (tateCurveLocOver R)
            (D.classifying_isPullback' fb ftop hPB)).hom ≫
            projModelBaseChange (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
              (tateCurveLocOver R)) := by simp only [Category.assoc]
    _ = D.U.2.isoSpec.inv ≫ D.restrictSection P ≫
          pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R) := by
        rw [hbc]
    _ = D.U.2.isoSpec.inv ≫ (D.restrictSection P ≫ pullback.fst Y.curve.π D.U.1.ι) ≫
          ftop ≫ eqToHom (tateUniversal_E_eq R) := by simp only [Category.assoc]
    _ = D.U.2.isoSpec.inv ≫ (D.U.1.ι ≫ P.1) ≫ ftop ≫
          eqToHom (tateUniversal_E_eq R) := by rw [hres]
    _ = D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ (P.1 ≫ ftop) ≫
          eqToHom (tateUniversal_E_eq R) := by simp only [Category.assoc]
    _ = D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ (fb ≫ (tateMarkedPoint R).1) ≫
          eqToHom (tateUniversal_E_eq R) := by rw [hmark]
    _ = (D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ fb) ≫ (tateMarkedPoint R).1 ≫
          eqToHom (tateUniversal_E_eq R) := by simp only [Category.assoc]
    _ = D.classifyingSpecMap fb ≫ tateP0mor R := by
        rw [hm]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
        rfl

/-- The base-changed induced point is the composed atlas marking. -/
theorem specPointBaseChange_inducedPt (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    specPointBaseChange (tateCurveLocOver R) (D.inducedPt fb ftop hPB hzw P) =
      specPointComp (tateCurveLocOver R) (TateAtlas.P0.specPoint R)
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
        AlgebraMap.comp_self := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  have hof : CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)) =
      Spec.preimage (D.classifyingSpecMap fb) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  refine Subtype.ext ?_
  show (D.inducedPt fb ftop hPB hzw P).1 ≫
      projModelBaseChange (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
        (tateCurveLocOver R) =
    Spec.map (CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))) ≫
      (TateAtlas.P0.specPoint R).1
  rw [D.inducedPt_comp_bc fb ftop hPB hzw P hmark, hof, Spec.map_preimage]
  rfl

/-- The induced point evaluates to `0` (`x`-side). -/
theorem inducedPt_coordX (hP : Y.curve.NowhereGeomOrderLEThree P)
    (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    ZChart.eval ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
      (D.inducedPt fb ftop hPB hzw P) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
      (coordX ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))) = 0 := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  rw [← ZChart.BaseChange.eval_coordX (tateCurveLocOver R)
      (D.inducedPt fb ftop hPB hzw P) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP),
    ZChart.eval_congr (tateCurveLocOver R)
      (D.specPointBaseChange_inducedPt fb ftop hPB hzw P hmark)
      (ZChart.BaseChange.mem (tateCurveLocOver R) _ _)
      (ZChart.mem_specPointComp (tateCurveLocOver R) (TateAtlas.P0.specPoint R)
        (ZChart.TateP0.mem R) _ _),
    ZChart.eval_specPointComp, ZChart.TateP0.eval_coordX, map_zero]
  · exact ZChart.TateP0.mem R
  · exact D.inducedPt_mem_zChart fb ftop hPB hzw P hP

/-- The induced point evaluates to `0` (`y`-side). -/
theorem inducedPt_coordY (hP : Y.curve.NowhereGeomOrderLEThree P)
    (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    ZChart.eval ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
      (D.inducedPt fb ftop hPB hzw P) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
      (coordY ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))) = 0 := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  rw [← ZChart.BaseChange.eval_coordY (tateCurveLocOver R)
      (D.inducedPt fb ftop hPB hzw P) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP),
    ZChart.eval_congr (tateCurveLocOver R)
      (D.specPointBaseChange_inducedPt fb ftop hPB hzw P hmark)
      (ZChart.BaseChange.mem (tateCurveLocOver R) _ _)
      (ZChart.mem_specPointComp (tateCurveLocOver R) (TateAtlas.P0.specPoint R)
        (ZChart.TateP0.mem R) _ _),
    ZChart.eval_specPointComp, ZChart.TateP0.eval_coordY, map_zero]
  · exact ZChart.TateP0.mem R
  · exact D.inducedPt_mem_zChart fb ftop hPB hzw P hP

end MarkedChartData

end InducedChart

section SameChartEngine

/-! ### The comparison ENGINE on a common chart (recipe step 5, T7)

Two marked-chart presentations of the curve over the *same* affine open, carrying the
same restricted section, classify identically — both halves of the ENGINE, in unbundled
form so that both the chart fields of a `MarkedChartData` and the honest induced data can
instantiate it. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} {U : Y.base.affineOpens}
  [Algebra ↑R ↑Γ(Y.base, U.1)]
  (W₁ W₂ : WeierstrassCurve ↑Γ(Y.base, U.1)) [W₁.IsElliptic] [W₂.IsElliptic]
  (e₁ : pullback Y.curve.π U.1.ι ≅ projModel W₁)
  (e₂ : pullback Y.curve.π U.1.ι ≅ projModel W₂)
  (heπ₁ : e₁.hom ≫ projModelπ W₁ = pullback.snd Y.curve.π U.1.ι ≫ U.2.isoSpec.hom)
  (heπ₂ : e₂.hom ≫ projModelπ W₂ = pullback.snd Y.curve.π U.1.ι ≫ U.2.isoSpec.hom)
  (hez₁ : (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ Y.curve.zero) (𝟙 _)
    (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp])) ≫
      e₁.hom = projModelZero W₁)
  (hez₂ : (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ Y.curve.zero) (𝟙 _)
    (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp])) ≫
      e₂.hom = projModelZero W₂)
  (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) ↑Γ(Y.base, U.1))
  (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) ↑Γ(Y.base, U.1))
  (v : U.1.toScheme ⟶ pullback Y.curve.π U.1.ι)
  (hg₁ : g₁.1 = U.2.isoSpec.inv ≫ v ≫ e₁.hom)
  (hg₂ : g₂.1 = U.2.isoSpec.inv ≫ v ≫ e₂.hom)
  (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
  (hord₁ : NowhereOrderLEThree W₁
    (ZChart.eval W₁ g₁ hZ₁ (coordX W₁)) (ZChart.eval W₁ g₁ hZ₁ (coordY W₁)))
  (hord₂ : NowhereOrderLEThree W₂
    (ZChart.eval W₂ g₂ hZ₂ (coordX W₂)) (ZChart.eval W₂ g₂ hZ₂ (coordY W₂)))

include heπ₁ heπ₂ hez₁ hez₂ hg₁ hg₂ in
/-- **Same-chart agreement of the pointed atlas maps.** -/
theorem SameU.baseSpecMap_agree :
    TateAtlas.Point.baseSpecMap R W₁ _ _ (ZChart.eval_equation_self W₁ g₁ hZ₁) hord₁ =
      TateAtlas.Point.baseSpecMap R W₂ _ _ (ZChart.eval_equation_self W₂ g₂ hZ₂) hord₂ := by
  have heπ : (e₁.symm ≪≫ e₂).hom ≫ projModelπ W₂ = projModelπ W₁ := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, heπ₂, ← heπ₁, Iso.inv_hom_id_assoc]
  have hez : projModelZero W₁ ≫ (e₁.symm ≪≫ e₂).hom = projModelZero W₂ := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← hez₁, ← hez₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hsec : g₁.1 ≫ (e₁.symm ≪≫ e₂).hom = g₂.1 := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [hg₁, hg₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact TateAtlas.Point.baseSpecMap.eq_of_pointedIso R W₁ W₂ (e₁.symm ≪≫ e₂) heπ hez
    g₁ g₂ hZ₁ hZ₂ hsec hord₁ hord₂

include heπ₁ heπ₂ hez₁ hez₂ hg₁ hg₂ in
/-- **Same-chart agreement of the classifying top maps.** -/
theorem sameU_projTateMap_agree :
    e₁.hom ≫ projTateMap R W₁ g₁ hZ₁ hord₁ = e₂.hom ≫ projTateMap R W₂ g₂ hZ₂ hord₂ := by
  have heπ : (e₁.symm ≪≫ e₂).hom ≫ projModelπ W₂ = projModelπ W₁ := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, heπ₂, ← heπ₁, Iso.inv_hom_id_assoc]
  have hez : projModelZero W₁ ≫ (e₁.symm ≪≫ e₂).hom = projModelZero W₂ := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← hez₁, ← hez₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hsec : g₁.1 ≫ (e₁.symm ≪≫ e₂).hom = g₂.1 := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [hg₁, hg₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hengine := projTateMap_eq_of_pointedIso R W₁ W₂ (e₁.symm ≪≫ e₂) heπ hez
    g₁ g₂ hZ₁ hZ₂ hsec hord₁ hord₂
  rw [← hengine]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end MarkedChartData

end SameChartEngine

section InducedChartPins

/-! ### The classifying pins of the induced chart (recipe step 5, T7) -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (fb : Y.base ⟶ tateBase R) (ftop : Y.curve.E ⟶ (tateUniversal R).E)
  (hPB : IsPullback ftop Y.curve.π ((tateUniversal R).π) fb)
  (hzw : Y.curve.zero ≫ ftop = fb ≫ (tateUniversal R).zero)
  (P : Y.curve.Section)

/-- The atlas structure map is `Spec` of the atlas algebra. -/
theorem tateStructMap_eq_algebraMap (R : CommRingCat.{u}) :
    tateStructMap R = Spec.map (CommRingCat.ofHom (algebraMap ↑R (tateRingOver R))) := by
  rw [tateStructMap]
  refine congrArg Spec.map ?_
  ext r
  show algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.C r) =
    algebraMap ↑R (tateRingOver R) r
  rw [IsScalarTower.algebraMap_eq ↑R (MvPolynomial (Fin 2) ↑R) (tateRingOver R)]
  simp [MvPolynomial.algebraMap_eq]

/-- The nowhere-small-order condition of the induced point (through the induced chart's
geometric-fibre machinery, `[T-A6b]`/`[T-B6′]` trails). -/
theorem inducedPt_hord (hP : Y.curve.NowhereGeomOrderLEThree P) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    NowhereOrderLEThree ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
      (ZChart.eval _ (D.inducedPt fb ftop hPB hzw P)
        (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
        (coordX ((tateCurveLocOver R).map
          (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))))
      (ZChart.eval _ (D.inducedPt fb ftop hPB hzw P)
        (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
        (coordY ((tateCurveLocOver R).map
          (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))))) :=
  (D.inducedChart fb ftop hPB hzw).pt_hord P hP

variable [Algebra ↑R ↑Γ(Y.base, D.U.1)]

/-- The induced atlas algebra is an `R`-algebra tower. -/
theorem inducedChart_tower
    (halg : D.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.1.ι ≫ Y.structMap)
    (hbw : fb ≫ tateStructMap R = Y.structMap) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)).comp
      (algebraMap ↑R (tateRingOver R)) = algebraMap ↑R ↑Γ(Y.base, D.U.1) := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  have hof : CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)) =
      Spec.preimage (D.classifyingSpecMap fb) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.2.isoSpec.inv ≫ D.U.1.ι ≫ Y.structMap := by
    rw [← halg, Iso.inv_hom_id_assoc]
  have hspec : Spec.map (CommRingCat.ofHom
      ((algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)).comp
        (algebraMap ↑R (tateRingOver R)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) := by
    rw [show CommRingCat.ofHom ((algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)).comp
        (algebraMap ↑R (tateRingOver R))) =
        CommRingCat.ofHom (algebraMap ↑R (tateRingOver R)) ≫
          CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)) from
      CommRingCat.ofHom_comp _ _]
    rw [Spec.map_comp, hof, Spec.map_preimage, ← tateStructMap_eq_algebraMap, hbase]
    show D.classifyingSpecMap fb ≫ tateStructMap R = _
    rw [classifyingSpecMap]
    simp only [Category.assoc]
    rw [hbw]
  have hring := Spec.map_injective hspec
  have := congrArg CommRingCat.Hom.hom hring
  simpa using this

/-- **The base pin**: the pointed atlas map of the induced point is the classifying test
map. -/
theorem Induced.baseSpecMapOfPoint
    (halg : D.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.1.ι ≫ Y.structMap)
    (hbw : fb ≫ tateStructMap R = Y.structMap)
    (hP : Y.curve.NowhereGeomOrderLEThree P)
    (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    TateAtlas.Point.baseSpecMap R ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))) _ _
      (ZChart.eval_equation_self _ (D.inducedPt fb ftop hPB hzw P)
        (D.inducedPt_mem_zChart fb ftop hPB hzw P hP))
      (D.inducedPt_hord fb ftop hPB hzw P hP) =
      D.classifyingSpecMap fb := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  have htower := D.inducedChart_tower fb halg hbw
  have hof : CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)) =
      Spec.preimage (D.classifyingSpecMap fb) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom _
  have htn : ((tateCurveLocOver R).map
      (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).IsTateNormal :=
    (TateAtlas.CurveLocOver.isTateNormal R).map _
  have hC1 : TateAtlas.TateNormal.variableChange
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
      _ _ (ZChart.eval_equation_self _ (D.inducedPt fb ftop hPB hzw P)
        (D.inducedPt_mem_zChart fb ftop hPB hzw P hP))
      (D.inducedPt_hord fb ftop hPB hzw P hP) = 1 := by
    refine (TateAtlas.TateNormal.variableChange_unique _ _ _
      (ZChart.eval_equation_self _ (D.inducedPt fb ftop hPB hzw P)
        (D.inducedPt_mem_zChart fb ftop hPB hzw P hP))
      (D.inducedPt_hord fb ftop hPB hzw P hP) 1 ⟨?_, ?_, ?_⟩).symm
    · rw [one_smul]
      exact htn
    · exact (D.inducedPt_coordX fb ftop hPB hzw P hP hmark).symm
    · exact (D.inducedPt_coordY fb ftop hPB hzw P hP hmark).symm
  have hAlg : ∀ r : ↑R, algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)
      (algebraMap ↑R (tateRingOver R) r) = algebraMap ↑R ↑Γ(Y.base, D.U.1) r := fun r ↦ by
    rw [← htower]; rfl
  have h := TateAtlas.baseSpecMap_eq_point R
    ({ toRingHom := algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1), commutes' := hAlg } :
      tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))
    ((tateCurveLocOver R).map (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
    _ _ (ZChart.eval_equation_self _ (D.inducedPt fb ftop hPB hzw P)
      (D.inducedPt_mem_zChart fb ftop hPB hzw P hP))
    (D.inducedPt_hord fb ftop hPB hzw P hP) ?_ ?_
  · rw [← h]
    show Spec.map (CommRingCat.ofHom (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))) =
      D.classifyingSpecMap fb
    rw [hof, Spec.map_preimage]
  · rw [hC1, one_smul]
    show algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)
      (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 0)) =
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).a₁
    rw [WeierstrassCurve.map_a₁, TateAtlas.CurveLocOver.a₁]
  · rw [hC1, one_smul]
    show algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)
      (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 1)) =
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).a₂
    rw [WeierstrassCurve.map_a₂, TateAtlas.CurveLocOver.a₂]

/-- **The top pin**: the classifying top map of the induced point is the base-change
morphism (self-classification). -/
theorem projTateMap_inducedPt
    (halg : D.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.1.ι ≫ Y.structMap)
    (hbw : fb ≫ tateStructMap R = Y.structMap)
    (hP : Y.curve.NowhereGeomOrderLEThree P)
    (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
      (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
    projTateMap R ((tateCurveLocOver R).map
        (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
      (D.inducedPt fb ftop hPB hzw P) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
      (D.inducedPt_hord fb ftop hPB hzw P hP) =
      projModelBaseChange (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))
        (tateCurveLocOver R) := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  exact projTateMap_map_tate R (D.inducedChart_tower fb halg hbw)
    (D.inducedPt fb ftop hPB hzw P) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
    (D.inducedPt_coordX fb ftop hPB hzw P hP hmark)
    (D.inducedPt_coordY fb ftop hPB hzw P hP hmark)
    (D.inducedPt_hord fb ftop hPB hzw P hP)

include hPB hzw in
/-- **The chart-level base pin**: on any marked chart, the local classifying base map of
the section agrees with the restriction of any classifying base map (same-chart ENGINE
against the induced chart, then the base pin). -/
theorem chart_baseMap_eq
    (halg : D.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.1.ι ≫ Y.structMap)
    (hbw : fb ≫ tateStructMap R = Y.structMap)
    (hP : Y.curve.NowhereGeomOrderLEThree P)
    (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    D.baseMap P hP = D.U.1.ι ≫ fb := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  haveI : ((tateCurveLocOver R).map
      (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).IsElliptic :=
    inferInstanceAs (((tateCurveLocOver R).map
      (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).IsElliptic)
  have hagree := SameU.baseSpecMap_agree
    D.W ((tateCurveLocOver R).map (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
    D.e (pullbackChartIso (tateCurveLocOver R) (D.classifying_isPullback' fb ftop hPB))
    D.heπ
    (pullbackChartIso_hom_π (tateCurveLocOver R) (D.classifying_isPullback' fb ftop hPB))
    D.hez ((D.inducedChart fb ftop hPB hzw).hez)
    (D.pt P) (D.inducedPt fb ftop hPB hzw P) (D.restrictSection P)
    (D.pt_coe P) ((D.inducedChart fb ftop hPB hzw).pt_coe P)
    (D.pt_mem_zChart P hP) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
    (D.pt_hord P hP) (D.inducedPt_hord fb ftop hPB hzw P hP)
  show D.U.2.isoSpec.hom ≫ TateAtlas.Point.baseSpecMap R D.W _ _
      (ZChart.eval_equation_self D.W (D.pt P) (D.pt_mem_zChart P hP)) (D.pt_hord P hP) =
    D.U.1.ι ≫ fb
  rw [hagree, Induced.baseSpecMapOfPoint D fb ftop hPB hzw P halg hbw hP hmark,
    classifyingSpecMap, Iso.hom_inv_id_assoc]

include hPB hzw in
/-- **The chart-level top pin**: on any marked chart, the local classifying top map of
the section agrees with the restriction of any classifying top map. -/
theorem chart_topMap_eq
    (halg : D.U.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑R ↑Γ(Y.base, D.U.1))) =
      D.U.1.ι ≫ Y.structMap)
    (hbw : fb ≫ tateStructMap R = Y.structMap)
    (hP : Y.curve.NowhereGeomOrderLEThree P)
    (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    D.topMap P hP =
      pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R) := by
  letI : Algebra (tateRingOver R) ↑Γ(Y.base, D.U.1) :=
    (Spec.preimage (D.classifyingSpecMap fb)).hom.toAlgebra
  haveI : ((tateCurveLocOver R).map
      (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).IsElliptic :=
    inferInstanceAs (((tateCurveLocOver R).map
      (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1))).IsElliptic)
  have hagree := sameU_projTateMap_agree
    D.W ((tateCurveLocOver R).map (algebraMap (tateRingOver R) ↑Γ(Y.base, D.U.1)))
    D.e (pullbackChartIso (tateCurveLocOver R) (D.classifying_isPullback' fb ftop hPB))
    D.heπ
    (pullbackChartIso_hom_π (tateCurveLocOver R) (D.classifying_isPullback' fb ftop hPB))
    D.hez ((D.inducedChart fb ftop hPB hzw).hez)
    (D.pt P) (D.inducedPt fb ftop hPB hzw P) (D.restrictSection P)
    (D.pt_coe P) ((D.inducedChart fb ftop hPB hzw).pt_coe P)
    (D.pt_mem_zChart P hP) (D.inducedPt_mem_zChart fb ftop hPB hzw P hP)
    (D.pt_hord P hP) (D.inducedPt_hord fb ftop hPB hzw P hP)
  show D.e.hom ≫ projTateMap R D.W (D.pt P) (D.pt_mem_zChart P hP) (D.pt_hord P hP) =
    pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R)
  rw [hagree, D.projTateMap_inducedPt fb ftop hPB hzw P halg hbw hP hmark]
  exact pullbackChartIso_hom_bc (tateCurveLocOver R)
    (D.classifying_isPullback' fb ftop hPB)

end MarkedChartData

end InducedChartPins

section ClassifyingClause

/-! ### The classifying clause (recipe step 5, assembly)

The components of any classifying morphism agree with the glued ones over both covers,
so the glued morphism is the *unique* classifying morphism — `exists_tatePoint`'s
∀-clause. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R}

/-- **Uniqueness of the classifying components**: any cartesian pointed square over
`Spec R` pulling the atlas marking back to the section has the glued base and top maps. -/
theorem components_unique (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (fb : Y.base ⟶ tateBase R) (ftop : Y.curve.E ⟶ (tateUniversal R).E)
    (hPB : IsPullback ftop Y.curve.π ((tateUniversal R).π) fb)
    (hzw : Y.curve.zero ≫ ftop = fb ≫ (tateUniversal R).zero)
    (hbw : fb ≫ tateStructMap R = Y.structMap)
    (hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) :
    fb = gluedBaseMap P hP ∧
      ftop = gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm := by
  constructor
  · have hs : ∀ s : ↥Y.base, (chartAt Y s).U.1.ι ≫ fb =
        (chartAt Y s).U.1.ι ≫ gluedBaseMap P hP := by
      intro s
      letI := (chartAt Y s).chartAlgebra
      rw [ι_gluedBaseMap]
      have h := (chartAt Y s).chart_baseMap_eq fb ftop hPB hzw P
        ((chartAt Y s).chartAlgebra_compatible) hbw hP hmark
      rw [← h]
      exact rfl
    apply Scheme.Cover.hom_ext (chartCover Y)
    intro s
    exact hs s
  · have hs : ∀ s : ↥Y.base, pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ ftop =
        pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫
          (gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm) := by
      intro s
      letI := (chartAt Y s).chartAlgebra
      have h := (chartAt Y s).chart_topMap_eq fb ftop hPB hzw P
        ((chartAt Y s).chartAlgebra_compatible) hbw hP hmark
      have h2 := congrArg (fun m ↦ m ≫ eqToHom (tateUniversal_E_eq R).symm) h
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h2
      rw [← Category.assoc, ι_gluedTopMap, ← h2]
      exact rfl
    apply Scheme.Cover.hom_ext (curveCover Y)
    intro s
    exact hs s

/-- **The Tate atlas classifying clause** (`exists_tatePoint`'s ∀-part, Loeffler
Cor 3.3.5 / Prop 3.3.4): every nowhere-small-order section arises from a unique
classifying `Ell/R` morphism by pulling back the atlas marking. -/
theorem tateMarkedPoint_classifies (R : CommRingCat.{u}) (Y : EllObj R)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    ∃! fc : Y ⟶ tateEllObj R, EllHom.pullSection R fc (tateMarkedPoint R) = P := by
  refine EllObj.tateClassifyingHom.existsUnique_of_components R Y
    (gluedBaseMap P hP) (gluedBaseMap_over P hP)
    (gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm)
    (gluedTopMapEll_isPullback P hP) (gluedTopMapEll_zero P hP)
    (tateMarkedPoint R) P ?_ ?_
  · show P.1 ≫ gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm =
      gluedBaseMap P hP ≫ (tateMarkedPoint R).1
    have hm : (tateMarkedPoint R).1 =
        tateP0mor R ≫ eqToHom (tateUniversal_E_eq R).symm := rfl
    rw [hm, ← Category.assoc, gluedTopMap_marking P hP, Category.assoc]
  · intro f hf
    have hmark : P.1 ≫ f.top = f.baseHom ≫ (tateMarkedPoint R).1 :=
      (congrArg (fun Q : Y.curve.Section ↦ Q.1 ≫ f.top) hf).symm.trans
        (f.isPullback.lift_fst _ _ _)
    have h := components_unique P hP f.baseHom f.top f.isPullback f.zero_w f.base_w hmark
    exact ⟨h.1, h.2⟩

end MarkedChartData

end ClassifyingClause

end ModularCurves
