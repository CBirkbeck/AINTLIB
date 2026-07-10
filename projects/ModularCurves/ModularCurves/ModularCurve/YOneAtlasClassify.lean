import ModularCurves.ModularCurve.YOneAssembly
import ModularCurves.Moduli.QuotientProblem
import ModularCurves.EllipticCurve.Comparison

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

section RelativeTateRing

variable (R : CommRingCat.{u}) {A : Type u} [CommRing A] [Algebra R A]

/-- The relative Tate-ring map attached to coefficients `(α, β)` over an `R`-algebra, provided
the corresponding Tate-normal discriminant is a unit.  Scheme-theoretically, `Spec` of this map is
the local map to the Tate atlas `tateBase R`. -/
noncomputable def tateRingOverLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateRingOver R →+* A :=
  IsLocalization.Away.lift (tateCurveOver R).Δ
    (g := MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))
    (by simpa [WeierstrassCurve.map_Δ] using hΔ)

@[simp]
theorem tateRingOverLift_X_zero (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateRingOverLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α := by
  simp [tateRingOverLift]

@[simp]
theorem tateRingOverLift_X_one (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateRingOverLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β := by
  simp [tateRingOverLift]

/-- The relative Tate-ring lift bundled as an `R`-algebra map.  This is the form naturally
used by affine maps over `Spec R`. -/
noncomputable def tateRingOverAlgLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateRingOver R →ₐ[R] A where
  toRingHom := tateRingOverLift R α β hΔ
  commutes' r := by
    change tateRingOverLift R α β hΔ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
      (MvPolynomial.C r)) = algebraMap R A r
    simp [tateRingOverLift]

@[simp]
theorem tateRingOverAlgLift_X_zero (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateRingOverAlgLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α := by
  simp [tateRingOverAlgLift]

@[simp]
theorem tateRingOverAlgLift_X_one (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateRingOverAlgLift R α β hΔ
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β := by
  simp [tateRingOverAlgLift]

/-- Two `R`-algebra maps out of the relative Tate atlas ring agree once they agree on the
two Tate coordinates.  This is the ring-level overlap uniqueness used by the scheme-level
gluing step for maps into `tateBase R`. -/
theorem tateRingOver_algHom_ext (φ ψ : tateRingOver R →ₐ[R] A)
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
theorem tateRingOver_algHom_eq_lift (φ : tateRingOver R →ₐ[R] A) (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β) :
    (φ : tateRingOver R →+* A) = tateRingOverLift R α β hΔ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tateCurveOver R).Δ)
  apply MvPolynomial.ringHom_ext
  · intro r
    change φ (algebraMap R (tateRingOver R) r) =
      tateRingOverLift R α β hΔ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
        (MvPolynomial.C r))
    rw [φ.commutes]
    simp [tateRingOverLift]
  · intro i
    fin_cases i <;> simp [h0, h1, tateRingOverLift]

/-- The algebra-map version of `tateRingOver_algHom_eq_lift`. -/
theorem tateRingOver_algHom_eq_algLift (φ : tateRingOver R →ₐ[R] A) (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = α)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = β) :
    φ = tateRingOverAlgLift R α β hΔ := by
  apply tateRingOver_algHom_ext
  · simp [tateRingOverAlgLift, h0]
  · simp [tateRingOverAlgLift, h1]

/-- The affine scheme map to the relative Tate atlas induced by an `R`-algebra map out of
the atlas ring. -/
noncomputable def tateBaseSpecMap (φ : tateRingOver R →ₐ[R] A) :
    Spec (CommRingCat.of A) ⟶ tateBase R :=
  Spec.map (CommRingCat.ofHom (φ : tateRingOver R →+* A))

/-- The affine scheme map to `tateBase R` classified by the coefficients `(α, β)`. -/
noncomputable def tateBaseSpecMapOfCoeffs (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    Spec (CommRingCat.of A) ⟶ tateBase R :=
  tateBaseSpecMap R (tateRingOverAlgLift R α β hΔ)

/-- Equality of affine maps into the Tate atlas is reduced to equality of the two Tate
coordinates.  This is the `Spec`-level handle consumed by the scheme gluing gate. -/
theorem tateBaseSpecMap_ext (φ ψ : tateRingOver R →ₐ[R] A)
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
      ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)))
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
      ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1))) :
    tateBaseSpecMap R φ = tateBaseSpecMap R ψ := by
  rw [tateRingOver_algHom_ext R φ ψ h0 h1]

/-- The affine map induced by an `R`-algebra map out of the Tate atlas ring lies over
`Spec R`. -/
theorem tateBaseSpecMap_tateStructMap (φ : tateRingOver R →ₐ[R] A) :
    tateBaseSpecMap R φ ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  unfold tateBaseSpecMap tateStructMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => φ.commutes r)

/-- The affine coefficient-classifying map to the Tate atlas lies over `Spec R`. -/
theorem tateBaseSpecMapOfCoeffs_tateStructMap (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateBaseSpecMapOfCoeffs R α β hΔ ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  tateBaseSpecMap_tateStructMap R (tateRingOverAlgLift R α β hΔ)

variable (S : Scheme.{u}) [Algebra R Γ(S, ⊤)]

/-- The global classifying map to the Tate atlas attached to global Tate coefficients
`α, β ∈ Γ(S, O_S)`.  This is the `S.toSpecΓ` form of the map produced after the local
coefficients glue in Loeffler's proof. -/
noncomputable def tateBaseMapOfGlobalCoeffs (α β : Γ(S, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    S ⟶ tateBase R :=
  S.toSpecΓ ≫ tateBaseSpecMapOfCoeffs R α β hΔ

/-- Global maps to the Tate atlas built from global coefficients are equal once the two
global Tate coefficients are equal.  This packages the last affine uniqueness check after
the sheaf-gluing step for `α` and `β`. -/
theorem tateBaseMapOfGlobalCoeffs_ext (α β α' β' : Γ(S, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (hΔ' : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 => if i = 0 then α' else β'))).Δ))
    (hα : α = α') (hβ : β = β') :
    tateBaseMapOfGlobalCoeffs R S α β hΔ =
      tateBaseMapOfGlobalCoeffs R S α' β' hΔ' := by
  unfold tateBaseMapOfGlobalCoeffs tateBaseSpecMapOfCoeffs
  rw [tateBaseSpecMap_ext R (tateRingOverAlgLift R α β hΔ)
    (tateRingOverAlgLift R α' β' hΔ')]
  · simp [tateRingOverAlgLift, hα]
  · simp [tateRingOverAlgLift, hβ]

/-- The global coefficient map to the Tate atlas is compatible with the structure map to
`Spec R`. -/
theorem tateBaseMapOfGlobalCoeffs_tateStructMap (α β : Γ(S, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(S, ⊤))
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateBaseMapOfGlobalCoeffs R S α β hΔ ≫ tateStructMap R =
      S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(S, ⊤))) := by
  unfold tateBaseMapOfGlobalCoeffs
  rw [Category.assoc, tateBaseSpecMapOfCoeffs_tateStructMap]

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
theorem EllObj.toSpecΓ_algebraMap_eq_structMap (Y : EllObj R)
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
theorem tateBaseMapOfGlobalCoeffs_base_w (Y : EllObj R)
    [Algebra R Γ(Y.base, ⊤)]
    (halg : algebraMap R Γ(Y.base, ⊤) =
      ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop).hom)
    (α β : Γ(Y.base, ⊤))
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom
      (algebraMap R Γ(Y.base, ⊤))
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    tateBaseMapOfGlobalCoeffs R Y.base α β hΔ ≫ tateStructMap R = Y.structMap := by
  rw [tateBaseMapOfGlobalCoeffs_tateStructMap]
  exact EllObj.toSpecΓ_algebraMap_eq_structMap R Y halg

/-- The base map to the Tate atlas attached to global coefficients on an object over `Spec R`. -/
noncomputable def EllObj.tateBaseMapOfGlobalCoeffs (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    Y.base ⟶ tateBase R := by
  letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
  exact ModularCurves.tateBaseMapOfGlobalCoeffs R Y.base α β hΔ

@[simp]
theorem EllObj.tateBaseMapOfGlobalCoeffs_base_w (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ ≫ tateStructMap R = Y.structMap := by
  letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
  exact ModularCurves.tateBaseMapOfGlobalCoeffs_base_w R Y
    (EllObj.structAlgebra_algebraMap R Y) α β hΔ

theorem EllObj.tateBaseMapOfGlobalCoeffs_ext (Y : EllObj R)
    (α β α' β' : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (hΔ' : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α' else β'))).Δ))
    (hα : α = α') (hβ : β = β') :
    EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ =
      EllObj.tateBaseMapOfGlobalCoeffs R Y α' β' hΔ' := by
  letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
  exact ModularCurves.tateBaseMapOfGlobalCoeffs_ext R Y.base α β α' β' hΔ hΔ' hα hβ

/-- Glue local maps to the Tate atlas base along an open cover of an `Ell/R` object. -/
noncomputable def EllObj.tateBaseMapOfOpenCover (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j) :
    Y.base ⟶ tateBase R :=
  𝒰.glueMorphisms g hcompat

@[reassoc (attr := simp)]
theorem EllObj.ι_tateBaseMapOfOpenCover (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (i : 𝒰.I₀) :
    𝒰.f i ≫ EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat = g i :=
  Scheme.Cover.ι_glueMorphisms 𝒰 g hcompat i

/-- If each local Tate-atlas base map lies over `Spec R`, then so does the glued map. -/
@[simp]
theorem EllObj.tateBaseMapOfOpenCover_base_w (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap) :
    EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat ≫ tateStructMap R = Y.structMap := by
  apply Scheme.Cover.hom_ext 𝒰
  intro i
  rw [← Category.assoc, EllObj.ι_tateBaseMapOfOpenCover, hover]

theorem EllObj.tateBaseMapOfOpenCover_ext (Y : EllObj R) (𝒰 : Y.base.OpenCover)
    (g g' : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hcompat' : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g' i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g' j)
    (hg : ∀ i : 𝒰.I₀, g i = g' i) :
    EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat =
      EllObj.tateBaseMapOfOpenCover R Y 𝒰 g' hcompat' := by
  apply Scheme.Cover.hom_ext 𝒰
  intro i
  rw [EllObj.ι_tateBaseMapOfOpenCover, EllObj.ι_tateBaseMapOfOpenCover, hg i]

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
theorem EllObj.tateClassifyingHom_baseHom (Y : EllObj R) (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w).baseHom =
      baseMap :=
  rfl

@[simp]
theorem EllObj.tateClassifyingHom_top (Y : EllObj R) (baseMap : Y.base ⟶ tateBase R)
    (base_w : baseMap ≫ tateStructMap R = Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap)
    (zero_w : Y.curve.zero ≫ top = baseMap ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHom R Y baseMap base_w top isPullback zero_w).top = top :=
  rfl

theorem EllObj.tateClassifyingHom_ext (Y : EllObj R)
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
noncomputable def EllObj.tateClassifyingHomOfGlobalCoeffs (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero) :
    Y ⟶ tateEllObj R :=
  EllObj.tateClassifyingHom R Y (EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ)
    (EllObj.tateBaseMapOfGlobalCoeffs_base_w R Y α β hΔ) top isPullback zero_w

@[simp]
theorem EllObj.tateClassifyingHomOfGlobalCoeffs_baseHom (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHomOfGlobalCoeffs R Y α β hΔ top isPullback zero_w).baseHom =
      EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ :=
  rfl

@[simp]
theorem EllObj.tateClassifyingHomOfGlobalCoeffs_top (Y : EllObj R)
    (α β : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHomOfGlobalCoeffs R Y α β hΔ top isPullback zero_w).top =
      top :=
  rfl

theorem EllObj.tateClassifyingHomOfGlobalCoeffs_ext (Y : EllObj R)
    (α β α' β' : Γ(Y.base, ⊤))
    (hΔ : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α else β))).Δ))
    (hΔ' : letI : Algebra R Γ(Y.base, ⊤) := Y.structAlgebra
      IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R Γ(Y.base, ⊤))
        (fun i : Fin 2 => if i = 0 then α' else β'))).Δ))
    (top top' : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ ≫ (tateUniversal R).zero)
    (isPullback' : IsPullback top' Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfGlobalCoeffs R Y α' β' hΔ'))
    (zero_w' : Y.curve.zero ≫ top' =
      EllObj.tateBaseMapOfGlobalCoeffs R Y α' β' hΔ' ≫ (tateUniversal R).zero)
    (hα : α = α') (hβ : β = β') (htop : top = top') :
    EllObj.tateClassifyingHomOfGlobalCoeffs R Y α β hΔ top isPullback zero_w =
      EllObj.tateClassifyingHomOfGlobalCoeffs R Y α' β' hΔ' top' isPullback' zero_w' :=
  EllHom.ext (EllObj.tateBaseMapOfGlobalCoeffs_ext R Y α β α' β' hΔ hΔ' hα hβ) htop

/-- The classifying morphism into `tateEllObj` from a Tate-base map glued over an open
cover of the source base. -/
noncomputable def EllObj.tateClassifyingHomOfOpenCover (Y : EllObj R)
    (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero) :
    Y ⟶ tateEllObj R :=
  EllObj.tateClassifyingHom R Y (EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat)
    (EllObj.tateBaseMapOfOpenCover_base_w R Y 𝒰 g hcompat hover) top isPullback zero_w

@[simp]
theorem EllObj.tateClassifyingHomOfOpenCover_baseHom (Y : EllObj R)
    (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHomOfOpenCover R Y 𝒰 g hcompat hover top isPullback zero_w).baseHom =
      EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat :=
  rfl

@[simp]
theorem EllObj.tateClassifyingHomOfOpenCover_top (Y : EllObj R)
    (𝒰 : Y.base.OpenCover)
    (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ tateBase R)
    (hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i : 𝒰.I₀, g i ≫ tateStructMap R = 𝒰.f i ≫ Y.structMap)
    (top : Y.curve.E ⟶ (tateUniversal R).E)
    (isPullback : IsPullback top Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero) :
    (EllObj.tateClassifyingHomOfOpenCover R Y 𝒰 g hcompat hover top isPullback zero_w).top =
      top :=
  rfl

theorem EllObj.tateClassifyingHomOfOpenCover_ext (Y : EllObj R)
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
      (EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat))
    (zero_w : Y.curve.zero ≫ top =
      EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat ≫ (tateUniversal R).zero)
    (isPullback' : IsPullback top' Y.curve.π (tateUniversal R).π
      (EllObj.tateBaseMapOfOpenCover R Y 𝒰 g' hcompat'))
    (zero_w' : Y.curve.zero ≫ top' =
      EllObj.tateBaseMapOfOpenCover R Y 𝒰 g' hcompat' ≫ (tateUniversal R).zero)
    (hg : ∀ i : 𝒰.I₀, g i = g' i) (htop : top = top') :
    EllObj.tateClassifyingHomOfOpenCover R Y 𝒰 g hcompat hover top isPullback zero_w =
      EllObj.tateClassifyingHomOfOpenCover R Y 𝒰 g' hcompat' hover' top' isPullback' zero_w' :=
  EllHom.ext (EllObj.tateBaseMapOfOpenCover_ext R Y 𝒰 g g' hcompat hcompat' hg) htop

@[reassoc (attr := simp)]
theorem EllObj.tateClassifyingHom_pullSection_top (Y : EllObj R)
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

theorem EllObj.tateClassifyingHom_pullSection_eq (Y : EllObj R)
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

theorem EllObj.tateClassifyingHom_existsUnique_of_components (Y : EllObj R)
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
  · exact EllObj.tateClassifyingHom_pullSection_eq R Y baseMap base_w top isPullback
      zero_w P₀ P hP
  · intro f hf
    rcases huniq f hf with ⟨hbase, htop⟩
    exact EllHom.ext hbase htop

/-- The Tate classifying morphism in the tautological pullback shape.  This is the
`QuotientProblem`/`pullbackAlong` reuse path flagged in v10.89. -/
noncomputable def EllObj.tateClassifyingHomOfPullbackMap (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap) :
    Y ⟶ tateEllObj R :=
  v ≫ (tateEllObj R).pullbackAlongπ baseMap

@[simp]
theorem EllObj.tateClassifyingHomOfPullbackMap_baseHom (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap) :
    (EllObj.tateClassifyingHomOfPullbackMap R Y baseMap v).baseHom =
      v.baseHom ≫ baseMap :=
  rfl

theorem EllObj.tateClassifyingHomOfPullbackMap_baseHom_of_base_id (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap)
    (hv : v.baseHom = 𝟙 Y.base) :
    (EllObj.tateClassifyingHomOfPullbackMap R Y baseMap v).baseHom = baseMap := by
  rw [EllObj.tateClassifyingHomOfPullbackMap_baseHom, hv]
  change 𝟙 Y.base ≫ baseMap = baseMap
  exact Category.id_comp baseMap

/-- Compare maps into the Tate pullback by projecting to `tateEllObj` and comparing
their base maps.  This is `EllObj.homPullbackAlongEquiv` specialised to the Tate object. -/
theorem EllObj.tatePullbackAlong_hom_ext (Y : EllObj R)
    (baseMap : Y.base ⟶ tateBase R)
    (v v' : Y ⟶ (tateEllObj R).pullbackAlong baseMap)
    (hproj : v ≫ (tateEllObj R).pullbackAlongπ baseMap =
      v' ≫ (tateEllObj R).pullbackAlongπ baseMap)
    (hbase : v.baseHom = v'.baseHom) :
    v = v' := by
  apply (EllObj.homPullbackAlongEquiv (tateEllObj R) baseMap Y).injective
  exact Subtype.ext (Prod.ext hproj hbase)

@[simp]
theorem EllObj.tateClassifyingHomOfPullbackMap_toPullbackAlong {Y : EllObj R}
    (f : Y ⟶ tateEllObj R) :
    EllObj.tateClassifyingHomOfPullbackMap R Y f.baseHom (EllObj.toPullbackAlong f) = f := by
  exact EllObj.toPullbackAlong_pullbackAlongπ f

theorem EllObj.toPullbackAlong_tateClassifyingHomOfPullbackMap {Y : EllObj R}
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap) :
    EllObj.toPullbackAlong (EllObj.tateClassifyingHomOfPullbackMap R Y baseMap v) ≫
      (tateEllObj R).pullbackAlongMap baseMap v.baseHom = v :=
  EllObj.toPullbackAlong_pullbackAlongMap v

theorem EllObj.tateClassifyingHomOfPullbackMap_pullSection {Y : EllObj R}
    (baseMap : Y.base ⟶ tateBase R)
    (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap)
    (P₀ : (tateUniversal R).Section) :
    EllHom.pullSection R (EllObj.tateClassifyingHomOfPullbackMap R Y baseMap v) P₀ =
      EllHom.pullSection R v
        (EllHom.pullSection R ((tateEllObj R).pullbackAlongπ baseMap) P₀) :=
  EllHom.pullSection_comp R v ((tateEllObj R).pullbackAlongπ baseMap) P₀

/-- Specialising the universal Tate curve by `tateRingOverLift` recovers the Tate-normal curve
with coefficients `(α, β)`. -/
theorem tateCurveLocOver_map_tateRingOverLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    (tateCurveLocOver R).map (tateRingOverLift R α β hΔ) =
      (tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
        (fun i : Fin 2 => if i = 0 then α else β)) := by
  simp [tateCurveLocOver, tateRingOverLift, WeierstrassCurve.map_map]

/-- The algebra-map version of `tateCurveLocOver_map_tateRingOverLift`. -/
theorem tateCurveLocOver_map_tateRingOverAlgLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    (tateCurveLocOver R).map (tateRingOverAlgLift R α β hΔ) =
      (tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
        (fun i : Fin 2 => if i = 0 then α else β)) :=
  tateCurveLocOver_map_tateRingOverLift R α β hΔ

/-- A Tate-normal curve over an `R`-algebra is exactly the specialization of `tateCurveOver R`
at its coefficients `a₁` and `a₂`. -/
theorem tateCurveOver_map_tateNormal_coeffs (W : WeierstrassCurve A)
    (hW : W.IsTateNormal) :
    (tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then W.a₁ else W.a₂)) = W := by
  ext <;> simp [tateCurveOver, tateCurve, WeierstrassCurve.map, hW.1, hW.2.1, hW.2.2]

/-- The atlas-ring map attached to an elliptic Tate-normal Weierstrass curve. -/
noncomputable def tateRingOverLiftOfTateNormal (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) : tateRingOver R →+* A :=
  tateRingOverLift R W.a₁ W.a₂ (by
    rw [tateCurveOver_map_tateNormal_coeffs R W hW]
    exact WeierstrassCurve.isUnit_Δ W)

/-- The atlas `R`-algebra map attached to an elliptic Tate-normal Weierstrass curve. -/
noncomputable def tateRingOverAlgLiftOfTateNormal (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) : tateRingOver R →ₐ[R] A :=
  tateRingOverAlgLift R W.a₁ W.a₂ (by
    rw [tateCurveOver_map_tateNormal_coeffs R W hW]
    exact WeierstrassCurve.isUnit_Δ W)

@[simp]
theorem tateRingOverLiftOfTateNormal_X_zero (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    tateRingOverLiftOfTateNormal R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = W.a₁ := by
  simp [tateRingOverLiftOfTateNormal]

@[simp]
theorem tateRingOverLiftOfTateNormal_X_one (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    tateRingOverLiftOfTateNormal R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = W.a₂ := by
  simp [tateRingOverLiftOfTateNormal]

@[simp]
theorem tateRingOverAlgLiftOfTateNormal_X_zero (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    tateRingOverAlgLiftOfTateNormal R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) = W.a₁ := by
  simp [tateRingOverAlgLiftOfTateNormal]

@[simp]
theorem tateRingOverAlgLiftOfTateNormal_X_one (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    tateRingOverAlgLiftOfTateNormal R W hW
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) = W.a₂ := by
  simp [tateRingOverAlgLiftOfTateNormal]

/-- Specialising the universal Tate curve by the map attached to a Tate-normal curve recovers
that curve. -/
theorem tateCurveLocOver_map_tateRingOverLiftOfTateNormal (W : WeierstrassCurve A)
    [W.IsElliptic] (hW : W.IsTateNormal) :
    (tateCurveLocOver R).map (tateRingOverLiftOfTateNormal R W hW) = W := by
  rw [tateCurveLocOver, WeierstrassCurve.map_map]
  change (tateCurveOver R).map
    ((tateRingOverLiftOfTateNormal R W hW).comp
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R))) = W
  rw [show (tateRingOverLiftOfTateNormal R W hW).comp
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)) =
        MvPolynomial.eval₂Hom (algebraMap R A)
          (fun i : Fin 2 => if i = 0 then W.a₁ else W.a₂) by
    simp [tateRingOverLiftOfTateNormal, tateRingOverLift]]
  exact tateCurveOver_map_tateNormal_coeffs R W hW

/-- The algebra-map version of `tateCurveLocOver_map_tateRingOverLiftOfTateNormal`. -/
theorem tateCurveLocOver_map_tateRingOverAlgLiftOfTateNormal (W : WeierstrassCurve A)
    [W.IsElliptic] (hW : W.IsTateNormal) :
    (tateCurveLocOver R).map (tateRingOverAlgLiftOfTateNormal R W hW) = W := by
  unfold tateRingOverAlgLiftOfTateNormal
  rw [tateCurveLocOver_map_tateRingOverAlgLift]
  exact tateCurveOver_map_tateNormal_coeffs R W hW

end RelativeTateRing

section LocalNormalisation

variable {A : Type u} [CommRing A]

/-- The T-E1 normalising variable change for a pointed affine chart of nowhere order `≤ 3`. -/
noncomputable def tateNormalVariableChange (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    WeierstrassCurve.VariableChange A :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose

theorem tateNormalVariableChange_isTateNormal (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    ((tateNormalVariableChange W x y hxy hord) • W).IsTateNormal :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.left.1

@[simp]
theorem tateNormalVariableChange_r (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    (tateNormalVariableChange W x y hxy hord).r = x :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.left.2.1

@[simp]
theorem tateNormalVariableChange_t (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    (tateNormalVariableChange W x y hxy hord).t = y :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.left.2.2

theorem tateNormalVariableChange_unique (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y) :
    C = tateNormalVariableChange W x y hxy hord :=
  (exists_unique_variableChange_isTateNormal W x y hxy hord).choose_spec.right C hC

variable (R : CommRingCat.{u}) [Algebra R A]

/-- The local map to the Tate atlas produced from a Weierstrass chart and an affine point
of nowhere order `≤ 3`: first apply T-E1, then use the relative Tate-ring lift. -/
noncomputable def tateRingOverLiftOfPoint (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    tateRingOver R →+* A :=
  tateRingOverLiftOfTateNormal R ((tateNormalVariableChange W x y hxy hord) • W)
    (tateNormalVariableChange_isTateNormal W x y hxy hord)

/-- The local Tate atlas `R`-algebra map produced from a pointed Weierstrass chart. -/
noncomputable def tateRingOverAlgLiftOfPoint (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    tateRingOver R →ₐ[R] A :=
  tateRingOverAlgLiftOfTateNormal R ((tateNormalVariableChange W x y hxy hord) • W)
    (tateNormalVariableChange_isTateNormal W x y hxy hord)

@[simp]
theorem tateRingOverAlgLiftOfPoint_X_zero (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    tateRingOverAlgLiftOfPoint R W x y hxy hord
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
        ((tateNormalVariableChange W x y hxy hord) • W).a₁ := by
  simp [tateRingOverAlgLiftOfPoint]

@[simp]
theorem tateRingOverAlgLiftOfPoint_X_one (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    tateRingOverAlgLiftOfPoint R W x y hxy hord
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
        ((tateNormalVariableChange W x y hxy hord) • W).a₂ := by
  simp [tateRingOverAlgLiftOfPoint]

/-- The affine Tate-atlas map attached to a Tate-normal Weierstrass curve. -/
noncomputable def tateBaseSpecMapOfTateNormal (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) : Spec (CommRingCat.of A) ⟶ tateBase R :=
  tateBaseSpecMap R (tateRingOverAlgLiftOfTateNormal R W hW)

/-- The affine Tate-atlas map attached to a pointed Weierstrass chart after T-E1
normalisation. -/
noncomputable def tateBaseSpecMapOfPoint (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    Spec (CommRingCat.of A) ⟶ tateBase R :=
  tateBaseSpecMap R (tateRingOverAlgLiftOfPoint R W x y hxy hord)

/-- The Tate-normal affine chart map lies over `Spec R`. -/
theorem tateBaseSpecMapOfTateNormal_tateStructMap (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal) :
    tateBaseSpecMapOfTateNormal R W hW ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  tateBaseSpecMap_tateStructMap R (tateRingOverAlgLiftOfTateNormal R W hW)

/-- The pointed affine chart map lies over `Spec R`. -/
theorem tateBaseSpecMapOfPoint_tateStructMap (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    tateBaseSpecMapOfPoint R W x y hxy hord ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  tateBaseSpecMap_tateStructMap R (tateRingOverAlgLiftOfPoint R W x y hxy hord)

/-- A map to the affine Tate atlas is the Tate-normal chart map once it has the same
Tate coefficients. -/
theorem tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal
    (φ : tateRingOver R →ₐ[R] A) (W : WeierstrassCurve A) [W.IsElliptic]
    (hW : W.IsTateNormal)
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
      W.a₁)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
      W.a₂) :
    tateBaseSpecMap R φ = tateBaseSpecMapOfTateNormal R W hW := by
  unfold tateBaseSpecMapOfTateNormal
  apply tateBaseSpecMap_ext
  · simpa [tateRingOverAlgLiftOfTateNormal] using h0
  · simpa [tateRingOverAlgLiftOfTateNormal] using h1

/-- A map to the affine Tate atlas is the pointed chart map once it has the same
Tate-normalised coefficients. -/
theorem tateBaseSpecMap_eq_tateBaseSpecMapOfPoint
    (φ : tateRingOver R →ₐ[R] A) (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (h0 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0)) =
      ((tateNormalVariableChange W x y hxy hord) • W).a₁)
    (h1 : φ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) =
      ((tateNormalVariableChange W x y hxy hord) • W).a₂) :
    tateBaseSpecMap R φ = tateBaseSpecMapOfPoint R W x y hxy hord := by
  unfold tateBaseSpecMapOfPoint tateRingOverAlgLiftOfPoint
  exact tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal R φ
    ((tateNormalVariableChange W x y hxy hord) • W)
    (tateNormalVariableChange_isTateNormal W x y hxy hord) h0 h1

/-- Any variable change that puts the same pointed chart in Tate normal form induces the
same atlas algebra map as the chosen T-E1 normalisation. -/
theorem tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y) :
    tateRingOverAlgLiftOfTateNormal R (C • W) hC.1 =
      tateRingOverAlgLiftOfPoint R W x y hxy hord := by
  have hCeq := tateNormalVariableChange_unique W x y hxy hord C hC
  apply tateRingOver_algHom_ext
  · simp [tateRingOverAlgLiftOfPoint, hCeq]
  · simp [tateRingOverAlgLiftOfPoint, hCeq]

/-- Any variable change that puts the same pointed chart in Tate normal form induces the
same affine Tate-atlas map as the chosen T-E1 normalisation. -/
theorem tateBaseSpecMapOfTateNormal_eq_tateBaseSpecMapOfPoint_of_variableChange
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y) :
    tateBaseSpecMapOfTateNormal R (C • W) hC.1 =
      tateBaseSpecMapOfPoint R W x y hxy hord := by
  unfold tateBaseSpecMapOfTateNormal tateBaseSpecMapOfPoint
  rw [tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange R
    W x y hxy hord C hC]

/-- Any two normalising variable changes for the same pointed chart induce the same
Tate-atlas algebra map. -/
theorem tateRingOverAlgLiftOfTateNormal_eq_of_variableChanges
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C C' : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y)
    (hC' : (C' • W).IsTateNormal ∧ C'.r = x ∧ C'.t = y) :
    tateRingOverAlgLiftOfTateNormal R (C • W) hC.1 =
      tateRingOverAlgLiftOfTateNormal R (C' • W) hC'.1 := by
  rw [tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange R
    W x y hxy hord C hC]
  rw [tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange R
    W x y hxy hord C' hC']

/-- Any two normalising variable changes for the same pointed chart induce the same
affine Tate-atlas map. -/
theorem tateBaseSpecMapOfTateNormal_eq_of_variableChanges
    (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (C C' : WeierstrassCurve.VariableChange A)
    (hC : (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y)
    (hC' : (C' • W).IsTateNormal ∧ C'.r = x ∧ C'.t = y) :
    tateBaseSpecMapOfTateNormal R (C • W) hC.1 =
      tateBaseSpecMapOfTateNormal R (C' • W) hC'.1 := by
  rw [tateBaseSpecMapOfTateNormal_eq_tateBaseSpecMapOfPoint_of_variableChange R
    W x y hxy hord C hC]
  rw [tateBaseSpecMapOfTateNormal_eq_tateBaseSpecMapOfPoint_of_variableChange R
    W x y hxy hord C' hC']

/-- The local atlas map classifies the T-E1 normal form of the pointed chart. -/
theorem tateCurveLocOver_map_tateRingOverLiftOfPoint (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    (tateCurveLocOver R).map (tateRingOverLiftOfPoint R W x y hxy hord) =
      (tateNormalVariableChange W x y hxy hord) • W :=
  tateCurveLocOver_map_tateRingOverLiftOfTateNormal R
    ((tateNormalVariableChange W x y hxy hord) • W)
    (tateNormalVariableChange_isTateNormal W x y hxy hord)

/-- The algebra-map version of `tateCurveLocOver_map_tateRingOverLiftOfPoint`. -/
theorem tateCurveLocOver_map_tateRingOverAlgLiftOfPoint (W : WeierstrassCurve A)
    [W.IsElliptic] (x y : A) (hxy : W.toAffine.Equation x y)
    (hord : NowhereOrderLEThree W x y) :
    (tateCurveLocOver R).map (tateRingOverAlgLiftOfPoint R W x y hxy hord) =
      (tateNormalVariableChange W x y hxy hord) • W :=
  tateCurveLocOver_map_tateRingOverAlgLiftOfTateNormal R
    ((tateNormalVariableChange W x y hxy hord) • W)
    (tateNormalVariableChange_isTateNormal W x y hxy hord)

end LocalNormalisation

section PointedComparison

variable {A : Type u} [CommRing A]

/-- Atlas-local form of T-W7.1b: a pointed isomorphism of projective Weierstrass models is
induced by a variable change.  This is the comparison input for overlap agreement in the
scheme-level classifying clause. -/
theorem atlasLocalPointedIso_exists_variableChange (W W' : WeierstrassCurve A)
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ C : WeierstrassCurve.VariableChange A, ∃ hW : C • W' = W,
      e.hom = eqToHom (by rw [← hW]) ≫ (projModelVCIso C W').hom :=
  pointedIso_exists_variableChange W W' e heπ hez

/-- Atlas-local form of T-W7 faithfulness: the variable-change action on projective models is
faithful once the induced pointed isomorphism is pinned. -/
theorem atlasLocal_projModelVCIso_injective (C₁ C₂ : WeierstrassCurve.VariableChange A)
    (W : WeierstrassCurve A) (hW : C₁ • W = C₂ • W)
    (h : (projModelVCIso C₁ W).hom = eqToHom (by rw [hW]) ≫ (projModelVCIso C₂ W).hom) :
    C₁ = C₂ :=
  projModelVCIso_injective C₁ C₂ W hW h

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
lemma two_zsmul_some_eq_zero_of_ψ₂_eq_zero {W : WeierstrassCurve F} {x y : F}
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
lemma three_zsmul_some_eq_zero_of_Ψ₃_eq_zero {W : WeierstrassCurve F} {x y : F}
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
      (fun hxy => hy2 hxy.right)) (h₂ := hns) |>.mp hx2
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

/-- **(B2-ii, the order ⟹ unit criterion)** If no multiple `a • P` (`0 < a ≤ 3`) of the affine
point `(x, y)` of the elliptic `W/A` vanishes at any geometric point of `Spec A`, then the
`ψ₂ψ₃`-value at `(x, y)` is a unit — i.e. `NowhereOrderLEThree W x y`, the input of T-E1.
A non-unit lies in a maximal ideal `m`; over `k := AlgebraicClosure (A ⧸ m)` the product of the
division-polynomial values vanishes, so `2 • P` or `3 • P` dies there by the two converses
above. -/
theorem nowhereOrderLEThree_of_forall_geom (W : WeierstrassCurve A) [W.IsElliptic]
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
  have hEk : (W.baseChange k).toAffine.Equation (algebraMap A k x) (algebraMap A k y) := by
    rw [WeierstrassCurve.Affine.equation_iff] at hxy
    have hxy' := congrArg (algebraMap A k) hxy
    simp only [map_add, map_mul, map_pow] at hxy'
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      WeierstrassCurve.toAffine]
    linear_combination hxy'
  have hns : (W.baseChange k).toAffine.Nonsingular (algebraMap A k x) (algebraMap A k y) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hEk
  -- the two division-polynomial values over `k`
  have hψ₂k : (W.baseChange k).ψ₂.evalEval (algebraMap A k x) (algebraMap A k y) =
      algebraMap A k ((W.Ψ 2).evalEval x y) := by
    rw [WeierstrassCurve.Ψ_two, WeierstrassCurve.ψ₂, WeierstrassCurve.ψ₂,
      WeierstrassCurve.Affine.evalEval_polynomialY,
      WeierstrassCurve.Affine.evalEval_polynomialY]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      WeierstrassCurve.toAffine, map_add, map_mul, map_ofNat]
  have hΨ₃k : (W.baseChange k).Ψ₃.eval (algebraMap A k x) =
      algebraMap A k ((W.Ψ 3).evalEval x y) := by
    rw [WeierstrassCurve.Ψ_three, Polynomial.evalEval_C, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_Ψ₃, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  -- the vanishing product splits
  have hprod : (W.baseChange k).ψ₂.evalEval (algebraMap A k x) (algebraMap A k y) *
      (W.baseChange k).Ψ₃.eval (algebraMap A k x) = 0 := by
    rw [hψ₂k, hΨ₃k, ← map_mul]
    exact hv
  rcases mul_eq_zero.mp hprod with h2 | h3
  · exact h k hns 2 two_pos (by norm_num)
      (by exact_mod_cast two_zsmul_some_eq_zero_of_ψ₂_eq_zero hns h2)
  · by_cases h2 : (W.baseChange k).ψ₂.evalEval (algebraMap A k x) (algebraMap A k y) = 0
    · exact h k hns 2 two_pos (by norm_num)
        (by exact_mod_cast two_zsmul_some_eq_zero_of_ψ₂_eq_zero hns h2)
    · have hy2 : algebraMap A k y ≠
          (W.baseChange k).toAffine.negY (algebraMap A k x) (algebraMap A k y) := by
        intro hy
        apply h2
        rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]
        rw [WeierstrassCurve.Affine.negY] at hy
        linear_combination hy
      exact h k hns 3 three_pos (by norm_num)
        (by exact_mod_cast three_zsmul_some_eq_zero_of_Ψ₃_eq_zero hns hy2 h3)

end OrderDictionary

section ZChartSection

/-! ### B2-i: fibrewise-nonzero points land in the `Z`-chart, with affine coordinates

Loeffler's affine-point extraction (Prop 3.3.4 proof, p. 13): a point of the projective model
that is not the point at infinity in any fibre factors through the `Z`-chart, where it is a
ring homomorphism out of the chart ring — equivalently, out of mathlib's affine coordinate
ring.  Its images of `coordX`/`coordY` are the affine coordinates, and they satisfy the
Weierstrass equation.  The chart-ring homomorphism is pinned by the factoring equation
`Spec.map (zChartHom) ≫ awayι = g`, from which all naturality statements follow by
faithfulness of `Spec`. -/

variable {A : Type u} [CommRing A] {K : Type u} [CommRing K] [Algebra A K]

/-- A field-valued point of `Spec K` composed with a `K`-point of the model is either in the
`Z`-chart or the zero point; if it is never the zero point, the whole `K`-point factors
through the `Z`-chart. -/
theorem inZChart_of_forall_ne_zero (W : WeierstrassCurve A)
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
        have hc := congrArg (fun m => m.base default) hfac
        simp only [ht, Scheme.Hom.comp_apply] at hc
        have hpt : ((Spec (CommRingCat.of K)).fromSpecResidueField p).base default = p :=
          Scheme.fromSpecResidueField_apply p default
        exact (congrArg (fun q => g.1.base q) hpt).symm.trans hc.symm
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
noncomputable def zChartHom (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* K :=
  (chartHomEquiv W 2 K ⟨g, hZ⟩).1

/-- The chart-ring homomorphism is `A`-compatible. -/
theorem zChartHom_compat (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    (zChartHom W g hZ).comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (HomogeneousLocalization.Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
      ((gradeZeroRingEquiv W) : A →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap A K :=
  (chartHomEquiv W 2 K ⟨g, hZ⟩).2

/-- **The factoring equation**: `Spec` of the chart-ring homomorphism, composed with the
chart inclusion, is the original point.  Everything else about `zChartHom` follows from this
by faithfulness of `Spec` and monicity of the chart inclusion. -/
theorem Spec_map_zChartHom_awayι (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    Spec.map (CommRingCat.ofHom (zChartHom W g hZ)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 := by
  show _ = (⟨g, hZ⟩ : { g : SpecPoints (projModel W) (projModelπ W) K // InZChart W g }).1.1
  exact congrArg (fun z => z.1.1) ((chartHomEquiv W 2 K).symm_apply_apply ⟨g, hZ⟩)

/-- The chart-ring homomorphism is the unique one satisfying the factoring equation. -/
theorem zChartHom_unique (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g)
    (χ : HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* K)
    (hχ : Spec.map (CommRingCat.ofHom χ) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos = g.1) :
    χ = zChartHom W g hZ := by
  have hmono := hχ.trans (Spec_map_zChartHom_awayι W g hZ).symm
  rw [cancel_mono] at hmono
  have := Spec.map_injective hmono
  exact congrArg CommRingCat.Hom.hom this

/-- The evaluation homomorphism out of the affine coordinate ring attached to a `Z`-chart
point: `coordX ↦ x`, `coordY ↦ y`. -/
noncomputable def zChartEval (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) : W.toAffine.CoordinateRing →+* K :=
  (zChartHom W g hZ).comp ((chartZRingEquiv W).symm :
    W.toAffine.CoordinateRing →+* HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))

/-- The evaluation homomorphism is `A`-algebra compatible. -/
theorem zChartEval_algebraMap (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (r : A) :
    zChartEval W g hZ (algebraMap A W.toAffine.CoordinateRing r) = algebraMap A K r := by
  have h1 : (chartZRingEquiv W).symm (algebraMap A W.toAffine.CoordinateRing r) =
      (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
        (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r) := by
    rw [← chartZRingEquiv_fromZero W r, RingEquiv.symm_apply_apply]
  show (zChartHom W g hZ) ((chartZRingEquiv W).symm
    (algebraMap A W.toAffine.CoordinateRing r)) = algebraMap A K r
  rw [h1]
  exact RingHom.congr_fun (zChartHom_compat W g hZ) r

/-- The coordinates extracted from a `Z`-chart point satisfy the Weierstrass equation of the
base-changed curve. -/
theorem zChartEval_equation (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    (W.baseChange K).toAffine.Equation
      (zChartEval W g hZ (coordX W)) (zChartEval W g hZ (coordY W)) := by
  have hker : zChartEval W g hZ
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine W.toAffine.polynomial) = 0 := by
    rw [show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine W.toAffine.polynomial =
      0 from AdjoinRoot.mk_self, map_zero]
  have hofC : ∀ a : A, zChartEval W g hZ
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C (Polynomial.C a)))
      = algebraMap A K a := by
    intro a
    rw [show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C (Polynomial.C a)) =
        algebraMap A W.toAffine.CoordinateRing a from by
      rw [show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
          (Polynomial.C (Polynomial.C a)) =
          AdjoinRoot.of W.toAffine.polynomial (Polynomial.C a) from rfl,
        ← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]]
    exact zChartEval_algebraMap W g hZ a
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    WeierstrassCurve.toAffine]
  have hexp : zChartEval W g hZ (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      W.toAffine.polynomial) =
      zChartEval W g hZ (coordY W) ^ 2
        + algebraMap A K W.a₁ * zChartEval W g hZ (coordX W) * zChartEval W g hZ (coordY W)
        + algebraMap A K W.a₃ * zChartEval W g hZ (coordY W)
        - (zChartEval W g hZ (coordX W) ^ 3
          + algebraMap A K W.a₂ * zChartEval W g hZ (coordX W) ^ 2
          + algebraMap A K W.a₄ * zChartEval W g hZ (coordX W)
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
theorem zChartEval_equation_self {A' : Type u} [CommRing A'] (W' : WeierstrassCurve A')
    (g : SpecPoints (projModel W') (projModelπ W') A') (hZ : InZChart W' g) :
    W'.toAffine.Equation
      (zChartEval W' g hZ (coordX W')) (zChartEval W' g hZ (coordY W')) :=
  zChartEval_equation W' g hZ

end ZChartSection

section MarkedChartComparison

/-! ### B2-iii/iv engine (base): two marked charts induce the same atlas map

Loeffler's *"Since `αᵢ, βᵢ` are unique, they must agree on `Uᵢ ∩ Uⱼ`"* (Prop 3.3.4,
p. 14).  A pointed isomorphism of projective models carrying one `Z`-chart point to another
is a variable change (T-W7); composing with the T-E1 normalising change of the source and
comparing with T-E1 **uniqueness** on the target forces the two Tate normal forms — hence
the two atlas algebra maps — to coincide. -/

variable {A : Type u} [CommRing A]

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
theorem Spec_map_pointedIsoAwayHom_awayι {W₁ W₂ : WeierstrassCurve A}
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
        (mk_X_mem_quotientGrading_one W 2) one_pos).hom := fun _ => rfl
  rw [hats, hats] at h1
  -- re-ascribe `h1` so every proof argument is spelled as in the goal
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
    rfl
  rw [hexp, Category.assoc, Category.assoc]
  have h3 := congrArg (fun m => Spec.map ((Proj.basicOpenIsoAway
    (quotientGrading (projIdeal W₁)) ((quotientGradingHom (projIdeal W₁)) (MvPolynomial.X 2))
    (mk_X_mem_quotientGrading_one W₁ 2) one_pos).inv) ≫ m) h2
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
  exact h3.trans h4

variable {K : Type u} [CommRing K] [Algebra A K]

/-- Transport of the chart evaluation along a pointed isomorphism of models carrying one
`Z`-chart point to another: evaluation on the target is evaluation on the source after the
induced coordinate-ring isomorphism. -/
theorem zChartEval_pointedIso {W₁ W₂ : WeierstrassCurve A}
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) K)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) K)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1) (a : W₂.toAffine.CoordinateRing) :
    zChartEval W₂ g₂ hZ₂ a =
      zChartEval W₁ g₁ hZ₁ (pointedIsoCoordEquiv ε heπ hez a) := by
  have hχmor : Spec.map (pointedIsoAwayHom ε hez ≫
      CommRingCat.ofHom (zChartHom W₁ g₁ hZ₁)) ≫
      Proj.awayι (quotientGrading (projIdeal W₂))
        ((quotientGradingHom (projIdeal W₂)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W₂ 2) one_pos = g₂.1 := by
    rw [Spec.map_comp, Category.assoc, Spec_map_pointedIsoAwayHom_awayι ε hez,
      ← Category.assoc, Spec_map_zChartHom_awayι, hsec]
  have hhom := (zChartHom_unique W₂ g₂ hZ₂
    ((pointedIsoAwayHom ε hez ≫ CommRingCat.ofHom (zChartHom W₁ g₁ hZ₁)).hom)
    (by rw [CommRingCat.ofHom_hom]; exact hχmor)).symm
  show zChartHom W₂ g₂ hZ₂ ((chartZRingEquiv W₂).symm a) = _
  rw [hhom]
  show zChartHom W₁ g₁ hZ₁ ((pointedIsoAwayHom ε hez).hom ((chartZRingEquiv W₂).symm a)) =
    zChartHom W₁ g₁ hZ₁ ((chartZRingEquiv W₁).symm (pointedIsoCoordEquiv ε heπ hez a))
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
    fun _ => rfl
  exact (happ _).trans hkey.symm

/-- **(ENGINE core: the composite normalising change)** If the marked coordinates of two
elliptic marked charts are related by the variable-change transform `C` and `C • W₂ = W₁`,
then the composite of `W₁`'s T-E1 normalisation with `C` **is** `W₂`'s normalisation, by
T-E1 uniqueness. -/
theorem tateNormalVariableChange_mul (W₁ W₂ : WeierstrassCurve A)
    [W₁.IsElliptic] [W₂.IsElliptic]
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hord₁ : NowhereOrderLEThree W₁
      (zChartEval W₁ g₁ hZ₁ (coordX W₁)) (zChartEval W₁ g₁ hZ₁ (coordY W₁)))
    (hord₂ : NowhereOrderLEThree W₂
      (zChartEval W₂ g₂ hZ₂ (coordX W₂)) (zChartEval W₂ g₂ hZ₂ (coordY W₂)))
    (C : WeierstrassCurve.VariableChange A) (hC : C • W₂ = W₁)
    (hx : zChartEval W₂ g₂ hZ₂ (coordX W₂) =
      (C.u : A) ^ 2 * zChartEval W₁ g₁ hZ₁ (coordX W₁) + C.r)
    (hy : zChartEval W₂ g₂ hZ₂ (coordY W₂) =
      (C.u : A) ^ 3 * zChartEval W₁ g₁ hZ₁ (coordY W₁) +
        C.s * (C.u : A) ^ 2 * zChartEval W₁ g₁ hZ₁ (coordX W₁) + C.t) :
    tateNormalVariableChange W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ * C =
      tateNormalVariableChange W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ := by
  have hD : (tateNormalVariableChange W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ * C) •
      W₂ =
      (tateNormalVariableChange W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁) • W₁ := by
    rw [mul_smul, hC]
  refine tateNormalVariableChange_unique W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ _
    ⟨?_, ?_, ?_⟩
  · rw [hD]
    exact tateNormalVariableChange_isTateNormal W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁
  · show (tateNormalVariableChange W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁).r *
      (C.u : A) ^ 2 + C.r = _
    rw [tateNormalVariableChange_r, hx]
    ring
  · show (tateNormalVariableChange W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁).t *
      (C.u : A) ^ 3 + (tateNormalVariableChange W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁)
        hord₁).r * C.s * (C.u : A) ^ 2 + C.t = _
    rw [tateNormalVariableChange_t, tateNormalVariableChange_r, hy]
    ring

/-- The coordinate transform of a marked pointed isomorphism, in the components of its
T-W7 variable change. -/
theorem zChartEval_coords_of_pointedIso (W₁ W₂ : WeierstrassCurve A)
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1)
    (C : WeierstrassCurve.VariableChange A) (hC : C • W₂ = W₁)
    (hεhom : ε.hom = eqToHom (by rw [← hC]) ≫ (projModelVCIso C W₂).hom) :
    zChartEval W₂ g₂ hZ₂ (coordX W₂) =
      (C.u : A) ^ 2 * zChartEval W₁ g₁ hZ₁ (coordX W₁) + C.r ∧
    zChartEval W₂ g₂ hZ₂ (coordY W₂) =
      (C.u : A) ^ 3 * zChartEval W₁ g₁ hZ₁ (coordY W₁) +
        C.s * (C.u : A) ^ 2 * zChartEval W₁ g₁ hZ₁ (coordX W₁) + C.t := by
  constructor
  · have h := zChartEval_pointedIso ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec (coordX W₂)
    rw [transport_general hC.symm ε (projModelVCIso C W₂) heπ hez (projModelVCIso_π C W₂)
      (projModelVCIso_zero C W₂) hεhom (coordX W₂), bridge_coordX] at h
    simp only [map_add, coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap] at h
    rw [h]
    simp only [map_mul, zChartEval_algebraMap, Algebra.algebraMap_self_apply]
  · have h := zChartEval_pointedIso ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec (coordY W₂)
    rw [transport_general hC.symm ε (projModelVCIso C W₂) heπ hez (projModelVCIso_π C W₂)
      (projModelVCIso_zero C W₂) hεhom (coordY W₂), bridge_coordY] at h
    simp only [map_add, coordRingCongr_algebraMap_mul_coordY,
      coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap] at h
    rw [h]
    simp only [map_mul, zChartEval_algebraMap, Algebra.algebraMap_self_apply]

/-- **(ENGINE, base half — Loeffler's overlap uniqueness)** Two elliptic marked `Z`-chart
data over the same ring, linked by a pointed isomorphism of the models carrying the first
marking to the second, induce the **same** Tate-atlas algebra map: the T-W7 variable change
composed with the source's T-E1 normalisation is a normalisation of the target, so T-E1
uniqueness forces the two Tate normal forms to agree. -/
theorem tateRingOverAlgLiftOfPoint_eq_of_pointedIso (R : CommRingCat.{u}) [Algebra R A]
    (W₁ W₂ : WeierstrassCurve A) [W₁.IsElliptic] [W₂.IsElliptic]
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1)
    (hord₁ : NowhereOrderLEThree W₁
      (zChartEval W₁ g₁ hZ₁ (coordX W₁)) (zChartEval W₁ g₁ hZ₁ (coordY W₁)))
    (hord₂ : NowhereOrderLEThree W₂
      (zChartEval W₂ g₂ hZ₂ (coordX W₂)) (zChartEval W₂ g₂ hZ₂ (coordY W₂))) :
    tateRingOverAlgLiftOfPoint R W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ =
      tateRingOverAlgLiftOfPoint R W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ := by
  obtain ⟨C, hC, hεhom⟩ := pointedIso_exists_variableChange W₁ W₂ ε heπ hez
  obtain ⟨hx, hy⟩ := zChartEval_coords_of_pointedIso W₁ W₂ ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec
    C hC hεhom
  have hDC₂ := tateNormalVariableChange_mul W₁ W₂ g₁ g₂ hZ₁ hZ₂ hord₁ hord₂ C hC hx hy
  have hcurves : (tateNormalVariableChange W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂)
      hord₂) • W₂ =
      (tateNormalVariableChange W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁) • W₁ := by
    rw [← hDC₂, mul_smul, hC]
  -- the two atlas algebra maps agree on the coordinates
  apply tateRingOver_algHom_ext
  · rw [tateRingOverAlgLiftOfPoint_X_zero, tateRingOverAlgLiftOfPoint_X_zero]
    exact (congrArg WeierstrassCurve.a₁ hcurves).symm
  · rw [tateRingOverAlgLiftOfPoint_X_one, tateRingOverAlgLiftOfPoint_X_one]
    exact (congrArg WeierstrassCurve.a₂ hcurves).symm

/-- The affine `Spec`-level form of the engine: the two pointed charts induce the same
affine map to the Tate atlas. -/
theorem tateBaseSpecMapOfPoint_eq_of_pointedIso (R : CommRingCat.{u}) [Algebra R A]
    (W₁ W₂ : WeierstrassCurve A) [W₁.IsElliptic] [W₂.IsElliptic]
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    (g₁ : SpecPoints (projModel W₁) (projModelπ W₁) A)
    (g₂ : SpecPoints (projModel W₂) (projModelπ W₂) A)
    (hZ₁ : InZChart W₁ g₁) (hZ₂ : InZChart W₂ g₂)
    (hsec : g₁.1 ≫ ε.hom = g₂.1)
    (hord₁ : NowhereOrderLEThree W₁
      (zChartEval W₁ g₁ hZ₁ (coordX W₁)) (zChartEval W₁ g₁ hZ₁ (coordY W₁)))
    (hord₂ : NowhereOrderLEThree W₂
      (zChartEval W₂ g₂ hZ₂ (coordX W₂)) (zChartEval W₂ g₂ hZ₂ (coordY W₂))) :
    tateBaseSpecMapOfPoint R W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ =
      tateBaseSpecMapOfPoint R W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ := by
  unfold tateBaseSpecMapOfPoint
  rw [show tateRingOverAlgLiftOfPoint R W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ =
    tateRingOverAlgLiftOfPoint R W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ from
    tateRingOverAlgLiftOfPoint_eq_of_pointedIso R W₁ W₂ ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec
      hord₁ hord₂]

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
theorem inZChart_specPointComp (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K') :
    InZChart W (specPointComp W g ψ hψ) := by
  obtain ⟨h, hfac⟩ := hZ
  exact ⟨Spec.map (CommRingCat.ofHom ψ) ≫ h, by rw [Category.assoc, hfac]; rfl⟩

/-- The chart-ring homomorphism of a composed point is the composition. -/
theorem zChartHom_specPointComp (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K') :
    zChartHom W (specPointComp W g ψ hψ) (inZChart_specPointComp W g hZ ψ hψ) =
      ψ.comp (zChartHom W g hZ) := by
  refine (zChartHom_unique W _ _ _ ?_).symm
  rw [show CommRingCat.ofHom (ψ.comp (zChartHom W g hZ)) =
    CommRingCat.ofHom (zChartHom W g hZ) ≫ CommRingCat.ofHom ψ from
    (CommRingCat.ofHom_comp _ _), Spec.map_comp, Category.assoc,
    Spec_map_zChartHom_awayι W g hZ]
  rfl

/-- The coordinate evaluation of a composed point is the composed evaluation. -/
theorem zChartEval_specPointComp (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K')
    (a : W.toAffine.CoordinateRing) :
    zChartEval W (specPointComp W g ψ hψ) (inZChart_specPointComp W g hZ ψ hψ) a =
      ψ (zChartEval W g hZ a) := by
  show zChartHom W (specPointComp W g ψ hψ) (inZChart_specPointComp W g hZ ψ hψ)
    ((chartZRingEquiv W).symm a) = _
  rw [zChartHom_specPointComp W g hZ ψ hψ]
  rfl

/-- The `x`-coordinate evaluation is the chart-ring homomorphism at `X₀/X₂`. -/
theorem zChartEval_coordX (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    zChartEval W g hZ (coordX W) =
      zChartHom W g hZ (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)) := by
  show zChartHom W g hZ ((chartZRingEquiv W).symm (coordX W)) = _
  congr 1
  rw [RingEquiv.symm_apply_eq]
  exact (chartZRingEquiv_x W).symm

/-- The `y`-coordinate evaluation is the chart-ring homomorphism at `X₁/X₂`. -/
theorem zChartEval_coordY (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    zChartEval W g hZ (coordY W) =
      zChartHom W g hZ (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)) := by
  show zChartHom W g hZ ((chartZRingEquiv W).symm (coordY W)) = _
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
      algebraMap A W.toAffine.CoordinateRing a from by
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
theorem specPoint_ext_of_zChartEval (g g' : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) (hZ' : InZChart W g')
    (hX : zChartEval W g hZ (coordX W) = zChartEval W g' hZ' (coordX W))
    (hY : zChartEval W g hZ (coordY W) = zChartEval W g' hZ' (coordY W)) : g = g' := by
  have hev : zChartEval W g hZ = zChartEval W g' hZ' := by
    refine coordRingHom_ext W _ _ (fun r => ?_) hX hY
    rw [zChartEval_algebraMap, zChartEval_algebraMap]
  have hhom : zChartHom W g hZ = zChartHom W g' hZ' := by
    refine RingHom.ext fun z => ?_
    have := RingHom.congr_fun hev (chartZRingEquiv W z)
    show zChartHom W g hZ z = zChartHom W g' hZ' z
    calc zChartHom W g hZ z
        = zChartEval W g hZ (chartZRingEquiv W z) := by
          show _ = zChartHom W g hZ ((chartZRingEquiv W).symm (chartZRingEquiv W z))
          rw [RingEquiv.symm_apply_apply]
      _ = zChartEval W g' hZ' (chartZRingEquiv W z) := this
      _ = zChartHom W g' hZ' z := by
          show zChartHom W g' hZ' ((chartZRingEquiv W).symm (chartZRingEquiv W z)) = _
          rw [RingEquiv.symm_apply_apply]
  refine Subtype.ext ?_
  rw [← Spec_map_zChartHom_awayι W g hZ, ← Spec_map_zChartHom_awayι W g' hZ', hhom]

end ZChartNaturality

section TateMarkedChart

/-! ### The atlas marking as a `Z`-chart point with coordinates `(0, 0)` -/

variable (R : CommRingCat.{u})

/-- The atlas marked point `(0, 0)` as a `Z`-chart point of the universal Tate model over the
atlas ring itself. -/
noncomputable def tateP0SpecPoint :
    SpecPoints (projModel (tateCurveLocOver R)) (projModelπ (tateCurveLocOver R))
      (tateRingOver R) :=
  ⟨tateP0mor R, by
    rw [tateP0mor_π R, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]⟩

/-- `tateP0mor` factors through the `Z`-chart via the `(0,0)`-solution homomorphism (the
public replay of the `[Y1-vi]` factorisation, through `chartHomEquiv_symm_coe`). -/
theorem tateP0mor_fac : tateP0mor R =
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
theorem tateP0SpecPoint_inZChart : InZChart (tateCurveLocOver R) (tateP0SpecPoint R) :=
  ⟨Spec.map (CommRingCat.ofHom
    ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1),
    (tateP0mor_fac R).symm⟩

/-- The chart-ring homomorphism of the marked point is the `(0,0)`-solution homomorphism. -/
theorem zChartHom_tateP0SpecPoint :
    zChartHom (tateCurveLocOver R) (tateP0SpecPoint R) (tateP0SpecPoint_inZChart R) =
      ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1 :=
  (zChartHom_unique (tateCurveLocOver R) (tateP0SpecPoint R) (tateP0SpecPoint_inZChart R)
    _ (tateP0mor_fac R).symm).symm

/-- The marked point's chart coordinates vanish (`tateP0sol = (0, 0)`). -/
theorem zChartHom_tateP0SpecPoint_isLocalizationElem (j : {j : Fin 3 // j ≠ 2}) :
    zChartHom (tateCurveLocOver R) (tateP0SpecPoint R) (tateP0SpecPoint_inZChart R)
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2)
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) j.1)) = 0 := by
  rw [zChartHom_tateP0SpecPoint]
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
theorem zChartEval_tateP0SpecPoint_coordX :
    zChartEval (tateCurveLocOver R) (tateP0SpecPoint R) (tateP0SpecPoint_inZChart R)
      (coordX (tateCurveLocOver R)) = 0 := by
  rw [zChartEval_coordX]
  exact zChartHom_tateP0SpecPoint_isLocalizationElem R ⟨0, by decide⟩

/-- The marked point's `y`-coordinate evaluation is `0`. -/
theorem zChartEval_tateP0SpecPoint_coordY :
    zChartEval (tateCurveLocOver R) (tateP0SpecPoint R) (tateP0SpecPoint_inZChart R)
      (coordY (tateCurveLocOver R)) = 0 := by
  rw [zChartEval_coordY]
  exact zChartHom_tateP0SpecPoint_isLocalizationElem R ⟨1, by decide⟩

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
  rw [show (awayCongr (𝒜 := 𝒜) (rfl : s = s)).toRingHom = RingHom.id _ from by
    rw [awayCongr_rfl]; rfl]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

variable (W : WeierstrassCurve A) {B : Type u} [CommRing B] [Algebra A B]

/-- The chart transport of `projModelBaseChange` on localization elements: `Xⱼ/X₂` maps to
`Xⱼ/X₂`. -/
theorem awayCongr_baseChangeMap_isLocalizationElem (j : Fin 3) :
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
theorem inZChart_specPointBaseChange
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    InZChart W (specPointBaseChange W g) := by
  refine ⟨Spec.map (CommRingCat.ofHom (zChartHom (W.map (algebraMap A B)) g hZ)) ≫
    Spec.map (CommRingCat.ofHom
      (((awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
          (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
        (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))), ?_⟩
  rw [Category.assoc, ← awayι_projModelBaseChange, ← Category.assoc,
    Spec_map_zChartHom_awayι]
  rfl

/-- The chart-ring homomorphism of a base-changed point. -/
theorem zChartHom_specPointBaseChange
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    zChartHom W (specPointBaseChange W g) (inZChart_specPointBaseChange W g hZ) =
      (zChartHom (W.map (algebraMap A B)) g hZ).comp
        (((awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
            (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
          (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) := by
  refine (zChartHom_unique W _ _ _ ?_).symm
  rw [show CommRingCat.ofHom ((zChartHom (W.map (algebraMap A B)) g hZ).comp
      (((awayCongr (𝒜 := quotientGrading (projIdeal (W.map (algebraMap A B))))
          (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
        (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) =
      CommRingCat.ofHom (((awayCongr (𝒜 := quotientGrading
          (projIdeal (W.map (algebraMap A B)))) (baseChangeGradedHom_mk_X W 2)).toRingHom).comp
        (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) ≫
      CommRingCat.ofHom (zChartHom (W.map (algebraMap A B)) g hZ) from
    CommRingCat.ofHom_comp _ _]
  rw [Spec.map_comp, Category.assoc, ← awayι_projModelBaseChange, ← Category.assoc,
    Spec_map_zChartHom_awayι]
  rfl

/-- Base change leaves the coordinate evaluations unchanged. -/
theorem zChartEval_specPointBaseChange_coordX
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    zChartEval W (specPointBaseChange W g) (inZChart_specPointBaseChange W g hZ)
      (coordX W) = zChartEval (W.map (algebraMap A B)) g hZ
        (coordX (W.map (algebraMap A B))) := by
  rw [zChartEval_coordX, zChartEval_coordX, zChartHom_specPointBaseChange]
  show zChartHom (W.map (algebraMap A B)) g hZ
    (awayCongr (baseChangeGradedHom_mk_X W 2)
      (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)))) = _
  rw [awayCongr_baseChangeMap_isLocalizationElem W 0]

/-- Base change leaves the coordinate evaluations unchanged (`y`-side). -/
theorem zChartEval_specPointBaseChange_coordY
    (g : SpecPoints (projModel (W.map (algebraMap A B)))
      (projModelπ (W.map (algebraMap A B))) K)
    (hZ : InZChart (W.map (algebraMap A B)) g) :
    zChartEval W (specPointBaseChange W g) (inZChart_specPointBaseChange W g hZ)
      (coordY W) = zChartEval (W.map (algebraMap A B)) g hZ
        (coordY (W.map (algebraMap A B))) := by
  rw [zChartEval_coordY, zChartEval_coordY, zChartHom_specPointBaseChange]
  show zChartHom (W.map (algebraMap A B)) g hZ
    (awayCongr (baseChangeGradedHom_mk_X W 2)
      (HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap A B) W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)))) = _
  rw [awayCongr_baseChangeMap_isLocalizationElem W 1]

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
theorem inZChart_specPointPointedIso {W₁ W₂ : WeierstrassCurve A}
    (ε : projModel W₁ ≅ projModel W₂)
    (heπ : ε.hom ≫ projModelπ W₂ = projModelπ W₁)
    (hez : projModelZero W₁ ≫ ε.hom = projModelZero W₂)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W₁) (projModelπ W₁) K) (hZ : InZChart W₁ g) :
    InZChart W₂ (specPointPointedIso ε heπ g) := by
  refine ⟨Spec.map (CommRingCat.ofHom (zChartHom W₁ g hZ)) ≫
    Spec.map (pointedIsoAwayHom ε hez), ?_⟩
  rw [Category.assoc, Spec_map_pointedIsoAwayHom_awayι ε hez, ← Category.assoc,
    Spec_map_zChartHom_awayι]
  rfl

variable (R : CommRingCat.{u}) [Algebra R A] (W : WeierstrassCurve A) [W.IsElliptic]
  (g : SpecPoints (projModel W) (projModelπ W) A) (hZ : InZChart W g)
  (hord : NowhereOrderLEThree W
    (zChartEval W g hZ (coordX W)) (zChartEval W g hZ (coordY W)))

/-- The specialisation of the universal Tate curve at the marked chart's atlas map is the
T-E1 normal form of the chart. -/
theorem tateCurveLocOver_map_marked :
    (tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) =
      (tateNormalVariableChange W _ _ (zChartEval_equation_self W g hZ) hord) • W :=
  tateCurveLocOver_map_tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord

/-- The normalising pointed isomorphism from the specialised universal Tate model onto the
chart's model. -/
noncomputable def tateNormalIso :
    projModel ((tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) ≅ projModel W :=
  eqToIso (congrArg projModel (tateCurveLocOver_map_marked R W g hZ hord)) ≪≫
    projModelVCIso (tateNormalVariableChange W _ _ (zChartEval_equation_self W g hZ) hord) W

/-- The hom of the normalising isomorphism, in `transport_general` shape. -/
theorem tateNormalIso_hom :
    (tateNormalIso R W g hZ hord).hom =
      eqToHom (congrArg projModel (tateCurveLocOver_map_marked R W g hZ hord)) ≫
        (projModelVCIso
          (tateNormalVariableChange W _ _ (zChartEval_equation_self W g hZ) hord) W).hom := by
  rw [tateNormalIso, Iso.trans_hom, eqToIso.hom]

/-- `eqToHom` transport of the structure morphism along a curve equality. -/
theorem eqToHom_projModelπ {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂) :
    eqToHom (congrArg projModel h) ≫ projModelπ V₂ = projModelπ V₁ := by
  subst h; simp

/-- `eqToHom` transport of the zero section along a curve equality. -/
theorem eqToHom_projModelZero {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂) :
    projModelZero V₁ ≫ eqToHom (congrArg projModel h) = projModelZero V₂ := by
  subst h; simp

/-- The normalising isomorphism respects the structure morphisms. -/
theorem tateNormalIso_π :
    (tateNormalIso R W g hZ hord).hom ≫ projModelπ W =
      projModelπ ((tateCurveLocOver R).map
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) := by
  rw [tateNormalIso_hom, Category.assoc, projModelVCIso_π,
    eqToHom_projModelπ (tateCurveLocOver_map_marked R W g hZ hord)]

/-- The normalising isomorphism respects the zero sections. -/
theorem tateNormalIso_zero :
    projModelZero ((tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) ≫
      (tateNormalIso R W g hZ hord).hom = projModelZero W := by
  rw [tateNormalIso_hom, ← Category.assoc,
    eqToHom_projModelZero (tateCurveLocOver_map_marked R W g hZ hord), projModelVCIso_zero]

/-- The marked point, normalised into the specialised Tate model. -/
noncomputable def markedPointNormalised :
    SpecPoints (projModel ((tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)))
      (projModelπ ((tateCurveLocOver R).map
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))) A :=
  specPointPointedIso (tateNormalIso R W g hZ hord).symm
    (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact (tateNormalIso_π R W g hZ hord).symm) g

/-- The normalised marked point returns to the marking through the normalising iso. -/
theorem markedPointNormalised_sec :
    (markedPointNormalised R W g hZ hord).1 ≫ (tateNormalIso R W g hZ hord).hom = g.1 := by
  show (g.1 ≫ (tateNormalIso R W g hZ hord).inv) ≫ (tateNormalIso R W g hZ hord).hom = g.1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The zero section respects the inverse normalising iso. -/
theorem tateNormalIso_zero_inv :
    projModelZero W ≫ (tateNormalIso R W g hZ hord).inv =
      projModelZero ((tateCurveLocOver R).map
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) := by
  rw [Iso.comp_inv_eq]
  exact (tateNormalIso_zero R W g hZ hord).symm

/-- The normalised marked point lies in the `Z`-chart. -/
theorem markedPointNormalised_inZChart :
    InZChart ((tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))
      (markedPointNormalised R W g hZ hord) :=
  inZChart_specPointPointedIso (tateNormalIso R W g hZ hord).symm
    (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact (tateNormalIso_π R W g hZ hord).symm)
    (by rw [Iso.symm_hom]; exact tateNormalIso_zero_inv R W g hZ hord) g hZ

/-- The normalised marked point has coordinates `(0, 0)`. -/
theorem markedPointNormalised_coords :
    zChartEval _ (markedPointNormalised R W g hZ hord)
      (markedPointNormalised_inZChart R W g hZ hord)
      (coordX ((tateCurveLocOver R).map
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))) = 0 ∧
    zChartEval _ (markedPointNormalised R W g hZ hord)
      (markedPointNormalised_inZChart R W g hZ hord)
      (coordY ((tateCurveLocOver R).map
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A))) = 0 := by
  have heπ : (tateNormalIso R W g hZ hord).hom ≫ projModelπ W = projModelπ _ :=
    tateNormalIso_π R W g hZ hord
  have hez : projModelZero _ ≫ (tateNormalIso R W g hZ hord).hom = projModelZero W :=
    tateNormalIso_zero R W g hZ hord
  have hgsec : (markedPointNormalised R W g hZ hord).1 ≫
      (tateNormalIso R W g hZ hord).hom = g.1 := markedPointNormalised_sec R W g hZ hord
  have hX := zChartEval_pointedIso (tateNormalIso R W g hZ hord) heπ hez
    (markedPointNormalised R W g hZ hord) g
    (markedPointNormalised_inZChart R W g hZ hord) hZ hgsec (coordX W)
  have hY := zChartEval_pointedIso (tateNormalIso R W g hZ hord) heπ hez
    (markedPointNormalised R W g hZ hord) g
    (markedPointNormalised_inZChart R W g hZ hord) hZ hgsec (coordY W)
  rw [transport_general (tateCurveLocOver_map_marked R W g hZ hord) _
    (projModelVCIso (tateNormalVariableChange W _ _ (zChartEval_equation_self W g hZ) hord) W)
    heπ hez (projModelVCIso_π _ W) (projModelVCIso_zero _ W)
    (tateNormalIso_hom R W g hZ hord) (coordX W), bridge_coordX] at hX
  rw [transport_general (tateCurveLocOver_map_marked R W g hZ hord) _
    (projModelVCIso (tateNormalVariableChange W _ _ (zChartEval_equation_self W g hZ) hord) W)
    heπ hez (projModelVCIso_π _ W) (projModelVCIso_zero _ W)
    (tateNormalIso_hom R W g hZ hord) (coordY W), bridge_coordY] at hY
  simp only [map_add, coordRingCongr_algebraMap_mul_coordX,
    coordRingCongr_algebraMap_mul_coordY, coordRingCongr_algebraMap] at hX hY
  simp only [map_mul, zChartEval_algebraMap, Algebra.algebraMap_self_apply] at hX hY
  rw [tateNormalVariableChange_r W _ _ (zChartEval_equation_self W g hZ) hord] at hX
  rw [tateNormalVariableChange_t W _ _ (zChartEval_equation_self W g hZ) hord] at hY
  have hXzero : zChartEval _ (markedPointNormalised R W g hZ hord)
      (markedPointNormalised_inZChart R W g hZ hord) (coordX _) = 0 := by
    have h2 : ((tateNormalVariableChange W _ _ (zChartEval_equation_self W g hZ) hord).u
        : A) ^ 2 * zChartEval _ (markedPointNormalised R W g hZ hord)
        (markedPointNormalised_inZChart R W g hZ hord) (coordX _) = 0 := by
      linear_combination -hX
    exact ((Units.mul_right_eq_zero (_ ^ 2)).mp (by exact_mod_cast h2))
  refine ⟨hXzero, ?_⟩
  rw [hXzero] at hY
  have h3 : ((tateNormalVariableChange W _ _ (zChartEval_equation_self W g hZ) hord).u
      : A) ^ 3 * zChartEval _ (markedPointNormalised R W g hZ hord)
      (markedPointNormalised_inZChart R W g hZ hord) (coordY _) = 0 := by
    linear_combination -hY
  exact ((Units.mul_right_eq_zero (_ ^ 3)).mp (by exact_mod_cast h3))

end ProjTateMap

section ProjTateMapAssembly

/-! ### The classifying model morphism: cartesian, pointed, marking-compatible -/

variable {A : Type u} [CommRing A] (R : CommRingCat.{u}) [Algebra R A]
  (W : WeierstrassCurve A) [W.IsElliptic]
  (g : SpecPoints (projModel W) (projModelπ W) A) (hZ : InZChart W g)
  (hord : NowhereOrderLEThree W
    (zChartEval W g hZ (coordX W)) (zChartEval W g hZ (coordY W)))

/-- The classifying morphism of a marked chart into the universal Tate model. -/
noncomputable def projTateMap : projModel W ⟶ projModel (tateCurveLocOver R) :=
  (tateNormalIso R W g hZ hord).inv ≫
    projModelBaseChange
      ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) (tateCurveLocOver R)

/-- The inverse normalising iso respects the structure morphisms. -/
theorem tateNormalIso_inv_π :
    (tateNormalIso R W g hZ hord).inv ≫ projModelπ ((tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)) = projModelπ W := by
  rw [← tateNormalIso_π R W g hZ hord, Iso.inv_hom_id_assoc]

/-- The classifying morphism lies over the affine atlas map. -/
theorem projTateMap_π :
    projTateMap R W g hZ hord ≫ projModelπ (tateCurveLocOver R) =
      projModelπ W ≫
        tateBaseSpecMapOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord := by
  show ((tateNormalIso R W g hZ hord).inv ≫ _) ≫ _ = _
  rw [Category.assoc, projModelBaseChange_π, ← Category.assoc, tateNormalIso_inv_π]
  rfl

/-- The classifying square is cartesian. -/
theorem projTateMap_isPullback :
    IsPullback (projTateMap R W g hZ hord) (projModelπ W) (projModelπ (tateCurveLocOver R))
      (tateBaseSpecMapOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord) := by
  letI : Algebra (tateRingOver R) A :=
    ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).toAlgebra
  have sq2 : IsPullback
      (projModelBaseChange
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) (tateCurveLocOver R))
      (projModelπ ((tateCurveLocOver R).map
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)))
      (projModelπ (tateCurveLocOver R))
      (tateBaseSpecMapOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord) :=
    isPullback_projModelBaseChange (tateCurveLocOver R)
  have sq1 : IsPullback ((tateNormalIso R W g hZ hord).inv) (projModelπ W)
      (projModelπ ((tateCurveLocOver R).map
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A)))
      (𝟙 (Spec (CommRingCat.of A))) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact tateNormalIso_inv_π R W g hZ hord⟩
  have hpaste := sq1.paste_horiz sq2
  rw [Category.id_comp] at hpaste
  exact hpaste

/-- The classifying morphism is pointed. -/
theorem projTateMap_zero :
    projModelZero W ≫ projTateMap R W g hZ hord =
      tateBaseSpecMapOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord ≫
        projModelZero (tateCurveLocOver R) := by
  letI : Algebra (tateRingOver R) A :=
    ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).toAlgebra
  show projModelZero W ≫ (tateNormalIso R W g hZ hord).inv ≫ _ = _
  rw [← Category.assoc, tateNormalIso_zero_inv R W g hZ hord]
  exact projModelZero_baseChange (tateCurveLocOver R)

/-- **The marking compatibility**: the classifying morphism carries the chart marking to
the atlas marking `(0,0)`. -/
theorem projTateMap_marking :
    g.1 ≫ projTateMap R W g hZ hord =
      tateBaseSpecMapOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord ≫
        tateP0mor R := by
  letI : Algebra (tateRingOver R) A :=
    ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).toAlgebra
  have hψ : ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
      tateRingOver R →ₐ[R] A) : tateRingOver R →+* A).comp
      (algebraMap (tateRingOver R) (tateRingOver R)) = algebraMap (tateRingOver R) A := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
    rfl
  refine Eq.trans ?_ (congrArg Subtype.val (specPoint_ext_of_zChartEval (tateCurveLocOver R)
    (specPointBaseChange (tateCurveLocOver R) (markedPointNormalised R W g hZ hord))
    (specPointComp (tateCurveLocOver R) (tateP0SpecPoint R) _ hψ)
    (inZChart_specPointBaseChange (tateCurveLocOver R)
      (markedPointNormalised R W g hZ hord) (markedPointNormalised_inZChart R W g hZ hord))
    (inZChart_specPointComp (tateCurveLocOver R) (tateP0SpecPoint R)
      (tateP0SpecPoint_inZChart R) _ hψ)
    (by
      rw [zChartEval_specPointBaseChange_coordX, zChartEval_specPointComp,
        zChartEval_tateP0SpecPoint_coordX, map_zero]
      · exact (markedPointNormalised_coords R W g hZ hord).1
      · exact tateP0SpecPoint_inZChart R)
    (by
      rw [zChartEval_specPointBaseChange_coordY, zChartEval_specPointComp,
        zChartEval_tateP0SpecPoint_coordY, map_zero]
      · exact (markedPointNormalised_coords R W g hZ hord).2
      · exact tateP0SpecPoint_inZChart R)))
  show g.1 ≫ (tateNormalIso R W g hZ hord).inv ≫ _ = _
  rw [← Category.assoc]
  rfl

end ProjTateMapAssembly

section ProjTateMapComparison

/-! ### ENGINE (top half): the classifying morphisms agree across a marked pointed iso

`projTateMap` is natural for pointed isomorphisms carrying marking to marking: the T-W7
changes of `ε` and of the canonical comparison `θ₁⁻¹ ≫ θ₂` both compose with the source's
T-E1 normalisation to the target's (`tateNormalVariableChange_mul`), so they are **equal**
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
theorem zChartEval_eqToHom_point {V₁ V₂ : WeierstrassCurve A} (h : V₁ = V₂)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel V₁) (projModelπ V₁) K) (hZ : InZChart V₁ g)
    (hZ' : InZChart V₂ (specPointPointedIso (eqToIso (congrArg projModel h))
      (eqToIso_projModelπ h) g)) (a : V₂.toAffine.CoordinateRing) :
    zChartEval V₂ (specPointPointedIso (eqToIso (congrArg projModel h))
      (eqToIso_projModelπ h) g) hZ' a =
      zChartEval V₁ g hZ (coordRingCongr h.symm a) := by
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
    eqToHom (congrArg (fun ψ : B →+* A => projModel (W.map ψ)) h) ≫
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
    (zChartEval W₁ g₁ hZ₁ (coordX W₁)) (zChartEval W₁ g₁ hZ₁ (coordY W₁)))
  (hord₂ : NowhereOrderLEThree W₂
    (zChartEval W₂ g₂ hZ₂ (coordX W₂)) (zChartEval W₂ g₂ hZ₂ (coordY W₂)))

include heπ hez hsec in
/-- **(ENGINE, top half)** The classifying model morphisms of two marked charts linked by a
marked pointed isomorphism agree: `ε.hom ≫ projTateMap₂ = projTateMap₁`. -/
theorem projTateMap_eq_of_pointedIso :
    ε.hom ≫ projTateMap R W₂ g₂ hZ₂ hord₂ = projTateMap R W₁ g₁ hZ₁ hord₁ := by
  -- the atlas algebra maps agree (ENGINE, base half)
  have hφ : (tateRingOverAlgLiftOfPoint R W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ :
      tateRingOver R →ₐ[R] A) =
      tateRingOverAlgLiftOfPoint R W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ :=
    tateRingOverAlgLiftOfPoint_eq_of_pointedIso R W₁ W₂ ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec
      hord₁ hord₂
  have hcur : (tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W₁ _ _ (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) =
      (tateCurveLocOver R).map
      ((tateRingOverAlgLiftOfPoint R W₂ _ _ (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ :
        tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) := by
    rw [hφ]
  -- the canonical comparison isomorphism through the two normalising isos
  set χ : projModel W₁ ≅ projModel W₂ :=
    (tateNormalIso R W₁ g₁ hZ₁ hord₁).symm ≪≫ eqToIso (congrArg projModel hcur) ≪≫
      tateNormalIso R W₂ g₂ hZ₂ hord₂ with hχdef
  have hχπ : χ.hom ≫ projModelπ W₂ = projModelπ W₁ := by
    rw [hχdef]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rw [tateNormalIso_π R W₂ g₂ hZ₂ hord₂, eqToHom_projModelπ hcur]
    exact tateNormalIso_inv_π R W₁ g₁ hZ₁ hord₁
  have hχz : projModelZero W₁ ≫ χ.hom = projModelZero W₂ := by
    rw [hχdef]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
    rw [← Category.assoc, ← Category.assoc, tateNormalIso_zero_inv R W₁ g₁ hZ₁ hord₁,
      eqToHom_projModelZero hcur]
    exact tateNormalIso_zero R W₂ g₂ hZ₂ hord₂
  -- χ carries the first marking to the second, via the (0,0)-coordinate extensionality
  have hmp : specPointPointedIso (eqToIso (congrArg projModel hcur))
      (eqToIso_projModelπ hcur) (markedPointNormalised R W₁ g₁ hZ₁ hord₁) =
      markedPointNormalised R W₂ g₂ hZ₂ hord₂ := by
    have hZT := inZChart_specPointPointedIso (eqToIso (congrArg projModel hcur))
      (eqToIso_projModelπ hcur) (eqToIso_projModelZero hcur)
      (markedPointNormalised R W₁ g₁ hZ₁ hord₁)
      (markedPointNormalised_inZChart R W₁ g₁ hZ₁ hord₁)
    refine specPoint_ext_of_zChartEval _ _ _ hZT
      (markedPointNormalised_inZChart R W₂ g₂ hZ₂ hord₂) ?_ ?_
    · rw [zChartEval_eqToHom_point hcur _ (markedPointNormalised_inZChart R W₁ g₁ hZ₁ hord₁)
        hZT, coordRingCongr_coordX, (markedPointNormalised_coords R W₁ g₁ hZ₁ hord₁).1,
        (markedPointNormalised_coords R W₂ g₂ hZ₂ hord₂).1]
    · rw [zChartEval_eqToHom_point hcur _ (markedPointNormalised_inZChart R W₁ g₁ hZ₁ hord₁)
        hZT, coordRingCongr_coordY, (markedPointNormalised_coords R W₁ g₁ hZ₁ hord₁).2,
        (markedPointNormalised_coords R W₂ g₂ hZ₂ hord₂).2]
  have hχsec : g₁.1 ≫ χ.hom = g₂.1 := by
    have h1 := congrArg Subtype.val hmp
    have h2 : (g₁.1 ≫ (tateNormalIso R W₁ g₁ hZ₁ hord₁).inv) ≫
        eqToHom (congrArg projModel hcur) =
        (markedPointNormalised R W₂ g₂ hZ₂ hord₂).1 := h1
    rw [hχdef]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
    rw [← Category.assoc, ← Category.assoc, h2]
    exact markedPointNormalised_sec R W₂ g₂ hZ₂ hord₂
  -- both T-W7 changes compose to the same normalisation, hence agree
  obtain ⟨C, hC, hεhom⟩ := pointedIso_exists_variableChange W₁ W₂ ε heπ hez
  obtain ⟨C', hC', hχhom⟩ := pointedIso_exists_variableChange W₁ W₂ χ hχπ hχz
  obtain ⟨hxε, hyε⟩ := zChartEval_coords_of_pointedIso W₁ W₂ ε heπ hez g₁ g₂ hZ₁ hZ₂ hsec
    C hC hεhom
  obtain ⟨hxχ, hyχ⟩ := zChartEval_coords_of_pointedIso W₁ W₂ χ hχπ hχz g₁ g₂ hZ₁ hZ₂ hχsec
    C' hC' hχhom
  have hCC' : C = C' := by
    have h1 := tateNormalVariableChange_mul W₁ W₂ g₁ g₂ hZ₁ hZ₂ hord₁ hord₂ C hC hxε hyε
    have h2 := tateNormalVariableChange_mul W₁ W₂ g₁ g₂ hZ₁ hZ₂ hord₁ hord₂ C' hC' hxχ hyχ
    exact mul_left_cancel (h1.trans h2.symm)
  have hhom : ε.hom = χ.hom := by
    rw [hεhom, hχhom]
    subst hCC'
    rfl
  -- conclude on the classifying morphisms
  have hbc := eqToHom_projModelBaseChange
    (congrArg (fun (ψ : tateRingOver R →ₐ[R] A) => (ψ : tateRingOver R →+* A)) hφ)
    (tateCurveLocOver R)
  rw [hhom]
  show ((tateNormalIso R W₁ g₁ hZ₁ hord₁).inv ≫ eqToHom (congrArg projModel hcur) ≫
      (tateNormalIso R W₂ g₂ hZ₂ hord₂).hom) ≫ (tateNormalIso R W₂ g₂ hZ₂ hord₂).inv ≫
      projModelBaseChange ((tateRingOverAlgLiftOfPoint R W₂ _ _
        (zChartEval_equation_self W₂ g₂ hZ₂) hord₂ : tateRingOver R →ₐ[R] A) :
        tateRingOver R →+* A) (tateCurveLocOver R) =
    (tateNormalIso R W₁ g₁ hZ₁ hord₁).inv ≫
      projModelBaseChange ((tateRingOverAlgLiftOfPoint R W₁ _ _
        (zChartEval_equation_self W₁ g₁ hZ₁) hord₁ : tateRingOver R →ₐ[R] A) :
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
  have heq4 := congrArg (fun m => m ≫ pullback.fst Y.curve.π D.U.1.ι) heq3
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
theorem pt_inZChart (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) : InZChart D.W (D.pt P) := by
  refine inZChart_of_forall_ne_zero D.W (D.pt P) ?_
  intro k _ t heq
  -- normalise the zero side and push to the algebraic closure
  have hid : (t ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ↑Γ(Y.base, D.U.1) ↑Γ(Y.base, D.U.1)))) ≫ projModelZero D.W =
      t ≫ projModelZero D.W := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  rw [hid] at heq
  have heqb := congrArg
    (fun m => Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ m) heq
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
theorem inZChart_of_comp_baseChange {K : Type u} [CommRing K] [Algebra B K]
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
noncomputable def fibreMap :
    pullback Y.curve.π (D.geomPt (D.specPt k)) ⟶ pullback Y.curve.π D.U.1.ι :=
  pullback.map Y.curve.π (D.geomPt (D.specPt k)) Y.curve.π D.U.1.ι (𝟙 _)
    (D.specPt k ≫ D.U.2.isoSpec.inv) (𝟙 _) (by simp)
    (by rw [Category.comp_id, geomPt, Category.assoc])

/-- The comparison square over the chart inclusion is cartesian. -/
theorem fibreMap_isPullback :
    IsPullback (D.fibreMap k) (pullback.snd Y.curve.π (D.geomPt (D.specPt k)))
      (pullback.snd Y.curve.π D.U.1.ι) (D.specPt k ≫ D.U.2.isoSpec.inv) := by
  have hbig := IsPullback.of_hasPullback Y.curve.π (D.geomPt (D.specPt k))
  have hfst : D.fibreMap k ≫ pullback.fst Y.curve.π D.U.1.ι =
      pullback.fst Y.curve.π (D.geomPt (D.specPt k)) := by
    rw [fibreMap, pullback.lift_fst, Category.comp_id]
  rw [← hfst] at hbig
  refine IsPullback.of_right hbig ?_ (IsPullback.of_hasPullback Y.curve.π D.U.1.ι)
  rw [fibreMap, pullback.lift_snd]

/-- The fibre presented over the chart model. -/
noncomputable def fibreTop :
    pullback Y.curve.π (D.geomPt (D.specPt k)) ⟶ projModel D.W :=
  D.fibreMap k ≫ D.e.hom

/-- The fibre square over the chart model is cartesian. -/
theorem fibreTop_isPullback :
    IsPullback (D.fibreTop k) (pullback.snd Y.curve.π (D.geomPt (D.specPt k)))
      (projModelπ D.W) (D.specPt k) := by
  have hpaste := (D.fibreMap_isPullback k).paste_horiz
    (IsPullback.of_horiz_isIso ⟨D.heπ⟩)
  have hbase : (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.U.2.isoSpec.hom = D.specPt k := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hbase] at hpaste
  exact hpaste

/-- The fibre of the curve as the model of the base-changed chart curve. -/
noncomputable def fibreChartIso :
    pullback Y.curve.π (D.geomPt (D.specPt k)) ≅
      projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) :=
  pullbackChartIso D.W (D.fibreTop_isPullback k)

/-- The zero section of the fibre curve, in chart coordinates. -/
theorem fibre_zero_comp :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).zero ≫ (D.fibreChartIso k).hom =
      projModelZero (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) := by
  refine pullbackChartIso_zero D.W (D.fibreTop_isPullback k) _ ?_ ?_
  · exact pullback.lift_snd _ _ _
  · show pullback.lift ((D.geomPt (D.specPt k)) ≫ Y.curve.zero) (𝟙 _) _ ≫
      D.fibreMap k ≫ D.e.hom = _
    have hzmap : pullback.lift ((D.geomPt (D.specPt k)) ≫ Y.curve.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
        D.fibreMap k =
        (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
          (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, fibreMap, pullback.lift_fst, ← Category.assoc,
          pullback.lift_fst, Category.assoc, Category.comp_id, Category.assoc,
          pullback.lift_fst, geomPt]
        simp only [Category.assoc]
      · rw [Category.assoc, fibreMap, pullback.lift_snd, ← Category.assoc,
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
noncomputable def fibreSection (P : Y.curve.Section) :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).Section :=
  (EllipticCurve.Point.baseChangeEquiv Y.curve (D.geomPt (D.specPt k)) (𝟙 _)).symm
    (Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k))).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P))

/-- The underlying morphism of the fibre section. -/
theorem fibreSection_coe (P : Y.curve.Section) :
    (D.fibreSection k P).1 = pullback.lift ((D.geomPt (D.specPt k)) ≫ P.1) (𝟙 _)
      (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]) := by
  have happ2 : EllipticCurve.Point.baseChangeEquiv Y.curve (D.geomPt (D.specPt k)) (𝟙 _)
      (D.fibreSection k P) = Y.curve.pointCongr (Category.id_comp _).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P) := by
    rw [fibreSection]
    exact AddEquiv.apply_symm_apply _ _
  have h1 := EllipticCurve.Point.baseChangeEquiv_apply_coe Y.curve
    (D.geomPt (D.specPt k)) (𝟙 _) (D.fibreSection k P)
  rw [happ2, EllipticCurve.pointCongr_coe] at h1
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst]
    exact h1.symm
  · rw [pullback.lift_snd]
    exact (D.fibreSection k P).2

/-- **The value chase**: the fibre section, read through the fibre chart and the base-change
morphism, is the chart point composed at the geometric point. -/
theorem fibreSection_comp_bc (P : Y.curve.Section) :
    (D.fibreSection k P).1 ≫ (D.fibreChartIso k).hom ≫
      projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      D.specPt k ≫ (D.pt P).1 := by
  have hbc := pullbackChartIso_hom_bc D.W (D.fibreTop_isPullback k)
  have h2 := congrArg (fun m => (D.fibreSection k P).1 ≫ m) hbc
  refine Eq.trans (h2 : _ = _) ?_
  show (D.fibreSection k P).1 ≫ D.fibreMap k ≫ D.e.hom = _
  have hlift : (D.fibreSection k P).1 ≫ D.fibreMap k =
      (D.specPt k ≫ D.U.2.isoSpec.inv) ≫ D.restrictSection P := by
    have hmf : D.fibreMap k ≫ pullback.fst Y.curve.π D.U.1.ι =
        pullback.fst Y.curve.π (D.geomPt (D.specPt k)) ≫ 𝟙 Y.curve.E :=
      pullback.lift_fst _ _ _
    have hms : D.fibreMap k ≫ pullback.snd Y.curve.π D.U.1.ι =
        pullback.snd Y.curve.π (D.geomPt (D.specPt k)) ≫
          (D.specPt k ≫ D.U.2.isoSpec.inv) :=
      pullback.lift_snd _ _ _
    have hfs1 : (D.fibreSection k P).1 ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k)) =
        D.geomPt (D.specPt k) ≫ P.1 :=
      (congrArg (· ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k)))
        (D.fibreSection_coe k P)).trans (pullback.lift_fst _ _ _)
    have hfs2 : (D.fibreSection k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k)) =
        𝟙 _ := (D.fibreSection k P).2
    have hres1 : D.restrictSection P ≫ pullback.fst Y.curve.π D.U.1.ι =
        D.U.1.ι ≫ P.1 := pullback.lift_fst _ _ _
    have hres2 : D.restrictSection P ≫ pullback.snd Y.curve.π D.U.1.ι = 𝟙 _ :=
      pullback.lift_snd _ _ _
    refine pullback.hom_ext ?_ ?_
    · calc ((D.fibreSection k P).1 ≫ D.fibreMap k) ≫ pullback.fst Y.curve.π D.U.1.ι
          = (D.fibreSection k P).1 ≫ D.fibreMap k ≫ pullback.fst Y.curve.π D.U.1.ι :=
            Category.assoc _ _ _
        _ = (D.fibreSection k P).1 ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k)) ≫
              𝟙 Y.curve.E := congrArg ((D.fibreSection k P).1 ≫ ·) hmf
        _ = ((D.fibreSection k P).1 ≫ pullback.fst Y.curve.π (D.geomPt (D.specPt k))) ≫
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
    · calc ((D.fibreSection k P).1 ≫ D.fibreMap k) ≫ pullback.snd Y.curve.π D.U.1.ι
          = (D.fibreSection k P).1 ≫ D.fibreMap k ≫ pullback.snd Y.curve.π D.U.1.ι :=
            Category.assoc _ _ _
        _ = (D.fibreSection k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k)) ≫
              (D.specPt k ≫ D.U.2.isoSpec.inv) := congrArg ((D.fibreSection k P).1 ≫ ·) hms
        _ = ((D.fibreSection k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k))) ≫
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
theorem zChartEval_congr {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    {g g' : SpecPoints (projModel W) (projModelπ W) K} (h : g = g')
    (hZ : InZChart W g) (hZ' : InZChart W g') (a : W.toAffine.CoordinateRing) :
    zChartEval W g hZ a = zChartEval W g' hZ' a := by subst h; rfl

/-- The chart-solution coordinates are the chart-ring homomorphism at the chart
coordinates (`coord_val`, over any ring). -/
theorem chartSolution_val {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g)
    (j : {j : Fin 3 // j ≠ 2}) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 j =
      zChartHom W g hZ (chartCoordEquiv W 2
        (Ideal.Quotient.mk _ (MvPolynomial.X j))) := rfl

/-- The chart-solution `x`-coordinate is the `coordX`-evaluation. -/
theorem chartSolution_zero_eq_eval {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨0, by decide⟩ =
      zChartEval W g hZ (coordX W) := by
  rw [chartSolution_val, zChartEval_coordX]
  exact DFunLike.congr_arg (zChartHom W g hZ)
    (chartCoordEquiv_mk_X W 2 ⟨0, by decide⟩)

/-- The chart-solution `y`-coordinate is the `coordY`-evaluation. -/
theorem chartSolution_one_eq_eval {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {K : Type u} [CommRing K] [Algebra A K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨1, by decide⟩ =
      zChartEval W g hZ (coordY W) := by
  rw [chartSolution_val, zChartEval_coordY]
  exact DFunLike.congr_arg (zChartHom W g hZ)
    (chartCoordEquiv_mk_X W 2 ⟨1, by decide⟩)

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D.U.1) k]

instance : (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).IsElliptic :=
  inferInstanceAs ((D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).IsElliptic)

/-- The geometric record of the fibre model. -/
noncomputable def fibreGeom : EllipticCurveGeom (Spec (CommRingCat.of k)) where
  E := projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
  π := projModelπ _
  zero := projModelZero _
  zero_π := projModelZero_projModelπ _
  smooth := projModel_smooth _
  proper := projModelπ_isProper _
  localModel := projModel_locallyWeierstrass _

/-- **[T-A6b]** The fibre working record, through `abelEnrichment_exists`. -/
noncomputable def fibreCurve : EllipticCurve (Spec (CommRingCat.of k)) :=
  (EllipticCurve.abelEnrichment_exists (D.fibreGeom k)).choose

/-- **Opaque interface** for the fibre record: its geometry is the fibre model. -/
theorem fibreCurve_geom : (D.fibreCurve k).toEllipticCurveGeom = D.fibreGeom k :=
  (EllipticCurve.abelEnrichment_exists (D.fibreGeom k)).choose_spec

theorem fibreCurve_E_eq : (D.fibreCurve k).E =
    projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) :=
  congrArg EllipticCurveGeom.E (D.fibreCurve_geom k)

theorem fibreCurve_π_eq : (D.fibreCurve k).π = eqToHom (D.fibreCurve_E_eq k) ≫
    projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) :=
  eqToGeom_π' (D.fibreCurve_geom k)

theorem fibreCurve_zero_eq : (D.fibreCurve k).zero =
    projModelZero (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) ≫
      eqToHom (D.fibreCurve_E_eq k).symm :=
  eqToGeom_zero' (D.fibreCurve_geom k)

/-- The pointed comparison from the curve fibre onto the fibre record's total space. -/
noncomputable def fibreCurveIso :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).E ≅ (D.fibreCurve k).E :=
  D.fibreChartIso k ≪≫ eqToIso (D.fibreCurve_E_eq k).symm

theorem fibreCurveIso_π : (D.fibreCurveIso k).hom ≫ (D.fibreCurve k).π =
    (Y.curve.baseChange (D.geomPt (D.specPt k))).π := by
  rw [fibreCurveIso, Iso.trans_hom, eqToIso.hom, D.fibreCurve_π_eq k]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact pullbackChartIso_hom_π D.W (D.fibreTop_isPullback k)

theorem fibreCurveIso_zero :
    (Y.curve.baseChange (D.geomPt (D.specPt k))).zero ≫ (D.fibreCurveIso k).hom =
      (D.fibreCurve k).zero := by
  rw [fibreCurveIso, Iso.trans_hom, eqToIso.hom, D.fibreCurve_zero_eq k, ← Category.assoc]
  exact congrArg (· ≫ eqToHom (D.fibreCurve_E_eq k).symm) (D.fibre_zero_comp k)

/-- **(B2-ii fibre bridge, [T-A6b] + [T-B6′])** A nowhere-small-order section satisfies the
T-E1 order hypothesis in every marked chart: a dying small multiple of the chart coordinates
at a geometric point would transport, through the fibre record and the geometric-fibre group
comparison, to a dying small multiple of the pulled section. -/
theorem pt_hord (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    NowhereOrderLEThree D.W
      (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W))
      (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) := by
  classical
  refine nowhereOrderLEThree_of_forall_geom D.W _ _
    (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) ?_
  intro k _ _ _ _ hns a ha0 ha3 hcontra
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  -- the transported section and its image point of the fibre model
  set s₁ : (D.fibreCurve k).Section :=
    sectionMapIso _ (D.fibreCurve k) (D.fibreCurveIso k) (D.fibreCurveIso_π k)
      (D.fibreSection k P) with hs₁
  have hgeom : (𝟙 (Spec (CommRingCat.of k))) = EllipticCurve.geomPoint k k := by
    rw [EllipticCurve.geomPoint, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  set sk : (D.fibreCurve k).Point (EllipticCurve.geomPoint k k) :=
    (D.fibreCurve k).pointCongr hgeom s₁ with hsk
  -- its model point
  set gfin : SpecPoints (projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))
      (projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) k :=
    EllipticCurve.pointSpecPointsEquiv (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (D.fibreCurve k) (D.fibreCurve_E_eq k) (D.fibreCurve_π_eq k) k sk with hgfin
  have hgfin1 : gfin.1 = (D.fibreSection k P).1 ≫ (D.fibreChartIso k).hom := by
    show (sk.1 ≫ eqToHom (D.fibreCurve_E_eq k)) = _
    rw [hsk, EllipticCurve.pointCongr_coe, hs₁]
    show ((D.fibreSection k P).1 ≫ (D.fibreCurveIso k).hom) ≫ _ = _
    rw [fibreCurveIso, Iso.trans_hom, eqToIso.hom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  -- the model point composed to the chart model is the chart point at the geometric point
  have hcomp : gfin.1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      D.specPt k ≫ (D.pt P).1 := by
    rw [hgfin1, Category.assoc]
    exact D.fibreSection_comp_bc k P
  -- membership in the Z-chart and the coordinate evaluations
  have hψcomp : (algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (algebraMap ↑Γ(Y.base, D.U.1) ↑Γ(Y.base, D.U.1)) = algebraMap ↑Γ(Y.base, D.U.1) k := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  have hZfin : InZChart (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) gfin := by
    refine inZChart_of_comp_baseChange D.W gfin
      (Spec.map (CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
        (zChartHom D.W (D.pt P) (D.pt_inZChart P hP))))) ?_
    rw [show CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
        (zChartHom D.W (D.pt P) (D.pt_inZChart P hP))) =
        CommRingCat.ofHom (zChartHom D.W (D.pt P) (D.pt_inZChart P hP)) ≫
          CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D.U.1) k) from
      CommRingCat.ofHom_comp _ _]
    rw [Spec.map_comp, Category.assoc, Spec_map_zChartHom_awayι, hcomp]
  have hbcpt : specPointBaseChange D.W gfin =
      specPointComp D.W (D.pt P) (algebraMap ↑Γ(Y.base, D.U.1) k) hψcomp := by
    refine Subtype.ext ?_
    show gfin.1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W = _
    rw [hcomp]
    rfl
  have hevalX : zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) gfin hZfin
      (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k
        (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) := by
    rw [← zChartEval_specPointBaseChange_coordX D.W gfin hZfin,
      zChartEval_congr D.W hbcpt (inZChart_specPointBaseChange D.W gfin hZfin)
        (inZChart_specPointComp D.W (D.pt P) (D.pt_inZChart P hP) _ hψcomp),
      zChartEval_specPointComp]
  have hevalY : zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) gfin hZfin
      (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k
        (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) := by
    rw [← zChartEval_specPointBaseChange_coordY D.W gfin hZfin,
      zChartEval_congr D.W hbcpt (inZChart_specPointBaseChange D.W gfin hZfin)
        (inZChart_specPointComp D.W (D.pt P) (D.pt_inZChart P hP) _ hψcomp),
      zChartEval_specPointComp]
  -- the base-changed curve over `k` is the mapped curve
  have hWk : (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).baseChange k =
      D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k) := by
    show (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).map (algebraMap k k) = _
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have hns2 : ((D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).baseChange k).toAffine.Nonsingular
      (algebraMap ↑Γ(Y.base, D.U.1) k
        (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)))
      (algebraMap ↑Γ(Y.base, D.U.1) k
        (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W))) := hWk.symm ▸ hns
  -- the image of the transported point is the marked affine point
  have hval : EllipticCurve.geomFibrePointAddEquiv
      (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibreCurve k)
      (D.fibreCurve_E_eq k) (D.fibreCurve_π_eq k) k sk =
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
      (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibreCurve k)
      (D.fibreCurve_E_eq k) (D.fibreCurve_π_eq k) k).injective ?_
    refine (map_zsmul _ (a : ℤ) sk).trans (Eq.trans ?_ (map_zero _).symm)
    exact (congrArg ((a : ℤ) • ·) hval).trans hcontra2
  have hs₁0 : (a : ℤ) • s₁ = 0 := by
    refine ((D.fibreCurve k).pointCongr hgeom).injective ?_
    refine (map_zsmul _ (a : ℤ) s₁).trans (Eq.trans ?_ (map_zero _).symm)
    rw [← hsk]
    exact hsk0
  have hfs0 : (a : ℤ) • D.fibreSection k P = 0 := by
    refine sectionMapIso_injective (Y.curve.baseChange (D.geomPt (D.specPt k)))
      (D.fibreCurve k) (D.fibreCurveIso k) (D.fibreCurveIso_π k) ?_
    have hzs := map_zsmul (sectionMapIsoHom (Y.curve.baseChange (D.geomPt (D.specPt k)))
      (D.fibreCurve k) (D.fibreCurveIso k) (D.fibreCurveIso_π k) (D.fibreCurveIso_zero k))
      (a : ℤ) (D.fibreSection k P)
    have hz0 := map_zero (sectionMapIsoHom (Y.curve.baseChange (D.geomPt (D.specPt k)))
      (D.fibreCurve k) (D.fibreCurveIso k) (D.fibreCurveIso_π k) (D.fibreCurveIso_zero k))
    exact hzs.trans (hs₁0.trans hz0.symm)
  have happ2 : EllipticCurve.Point.baseChangeEquiv Y.curve (D.geomPt (D.specPt k)) (𝟙 _)
      (D.fibreSection k P) = Y.curve.pointCongr (Category.id_comp _).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P) := by
    rw [fibreSection]
    exact AddEquiv.apply_symm_apply _ _
  have hpc0 : (a : ℤ) • Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k))).symm
      (EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P) = 0 :=
    ((congrArg ((a : ℤ) • ·) happ2).symm.trans
      ((map_zsmul (EllipticCurve.Point.baseChangeEquiv Y.curve
        (D.geomPt (D.specPt k)) (𝟙 _)) (a : ℤ) (D.fibreSection k P)).symm.trans
        ((congrArg (EllipticCurve.Point.baseChangeEquiv Y.curve
          (D.geomPt (D.specPt k)) (𝟙 _)) hfs0).trans
          (map_zero (EllipticCurve.Point.baseChangeEquiv Y.curve
            (D.geomPt (D.specPt k)) (𝟙 _))))))
  have hpull0 : (a : ℤ) • EllipticCurve.Point.pull Y.curve (D.geomPt (D.specPt k)) P = 0 := by
    have h2 := (map_zsmul (Y.curve.pointCongr
      (Category.id_comp (D.geomPt (D.specPt k)))) (a : ℤ) _).symm.trans
      ((congrArg (Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k)))) hpc0).trans
        (map_zero (Y.curve.pointCongr (Category.id_comp (D.geomPt (D.specPt k))))))
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
  D.U.2.isoSpec.hom ≫ tateBaseSpecMapOfPoint R D.W _ _
    (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)

/-- The local top map of a marked chart. -/
noncomputable def topMap : pullback Y.curve.π D.U.1.ι ⟶ projModel (tateCurveLocOver R) :=
  D.e.hom ≫ projTateMap R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)

/-- The local square is cartesian. -/
theorem topMap_isPullback :
    IsPullback (D.topMap P hP) (pullback.snd Y.curve.π D.U.1.ι)
      (projModelπ (tateCurveLocOver R)) (D.baseMap P hP) :=
  (IsPullback.of_horiz_isIso ⟨D.heπ⟩).paste_horiz
    (projTateMap_isPullback R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))

/-- The local square is pointed. -/
theorem topMap_zero :
    pullback.lift (D.U.1.ι ≫ Y.curve.zero) (𝟙 _)
      (by rw [Category.assoc, Y.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
      D.topMap P hP = D.baseMap P hP ≫ projModelZero (tateCurveLocOver R) := by
  have h1 := congrArg (fun m => D.U.2.isoSpec.hom ≫ m) D.hez
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h1
  simp only [topMap, baseMap, Category.assoc]
  rw [← Category.assoc, h1, Category.assoc,
    projTateMap_zero R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]

/-- The local square carries the section to the atlas marking. -/
theorem topMap_marking :
    D.restrictSection P ≫ D.topMap P hP = D.baseMap P hP ≫ tateP0mor R := by
  have h1 := congrArg (fun m => D.U.2.isoSpec.hom ≫ m) (D.pt_coe P)
  simp only [Iso.hom_inv_id_assoc] at h1
  simp only [topMap, baseMap, Category.assoc]
  rw [← Category.assoc, ← h1, Category.assoc,
    projTateMap_marking R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]

end MarkedChartData

end LocalClassifyingData

section TateAtlasNaturality

/-! ### Naturality of the pointed atlas map in the chart ring (recipe step 3 substrate)

`tateBaseSpecMapOfPoint` is natural under change of the chart ring: composing with
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
theorem tateNormalVariableChange_map (W : WeierstrassCurve A) [W.IsElliptic]
    [(W.map ψ).IsElliptic] (x y : A) (hxy : W.toAffine.Equation x y)
    (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    (tateNormalVariableChange W x y hxy hord).map ψ =
      tateNormalVariableChange (W.map ψ) (ψ x) (ψ y) hxy' hord' :=
  tateNormalVariableChange_unique (W.map ψ) (ψ x) (ψ y) hxy' hord' _
    ⟨by rw [WeierstrassCurve.map_variableChange]
        exact (tateNormalVariableChange_isTateNormal W x y hxy hord).map ψ,
     by simp, by simp⟩

/-- The T-E1 normalised curve is natural in the chart ring. -/
theorem tateNormalVariableChange_smul_map (W : WeierstrassCurve A) [W.IsElliptic]
    [(W.map ψ).IsElliptic] (x y : A) (hxy : W.toAffine.Equation x y)
    (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    tateNormalVariableChange (W.map ψ) (ψ x) (ψ y) hxy' hord' • (W.map ψ) =
      ((tateNormalVariableChange W x y hxy hord) • W).map ψ := by
  rw [← tateNormalVariableChange_map ψ W x y hxy hord hxy' hord',
    WeierstrassCurve.map_variableChange]

/-- The pointed atlas ring map is natural in the chart ring. -/
theorem tateRingOverLiftOfPoint_comp (R : CommRingCat.{u}) [Algebra ↑R A] [Algebra ↑R B]
    (hψ : ψ.comp (algebraMap ↑R A) = algebraMap ↑R B)
    (W : WeierstrassCurve A) [W.IsElliptic] [(W.map ψ).IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    ψ.comp (tateRingOverLiftOfPoint R W x y hxy hord) =
      tateRingOverLiftOfPoint R (W.map ψ) (ψ x) (ψ y) hxy' hord' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tateCurveOver R).Δ)
  apply MvPolynomial.ringHom_ext
  · intro r
    change ψ (tateRingOverAlgLiftOfPoint R W x y hxy hord
        (algebraMap ↑R (tateRingOver R) r)) =
      tateRingOverAlgLiftOfPoint R (W.map ψ) (ψ x) (ψ y) hxy' hord'
        (algebraMap ↑R (tateRingOver R) r)
    rw [AlgHom.commutes, AlgHom.commutes]
    exact RingHom.congr_fun hψ r
  · intro i
    fin_cases i
    · change ψ (tateRingOverAlgLiftOfPoint R W x y hxy hord
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 0))) =
        tateRingOverAlgLiftOfPoint R (W.map ψ) (ψ x) (ψ y) hxy' hord'
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 0))
      rw [tateRingOverAlgLiftOfPoint_X_zero, tateRingOverAlgLiftOfPoint_X_zero,
        tateNormalVariableChange_smul_map ψ W x y hxy hord hxy' hord',
        WeierstrassCurve.map_a₁]
    · change ψ (tateRingOverAlgLiftOfPoint R W x y hxy hord
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 1))) =
        tateRingOverAlgLiftOfPoint R (W.map ψ) (ψ x) (ψ y) hxy' hord'
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 1))
      rw [tateRingOverAlgLiftOfPoint_X_one, tateRingOverAlgLiftOfPoint_X_one,
        tateNormalVariableChange_smul_map ψ W x y hxy hord hxy' hord',
        WeierstrassCurve.map_a₂]

/-- **Affine naturality of the classifying base map**: composing the pointed atlas map with
`Spec` of a chart-ring map gives the pointed atlas map of the mapped chart. -/
theorem tateBaseSpecMapOfPoint_naturality (R : CommRingCat.{u}) [Algebra ↑R A] [Algebra ↑R B]
    (hψ : ψ.comp (algebraMap ↑R A) = algebraMap ↑R B)
    (W : WeierstrassCurve A) [W.IsElliptic] [(W.map ψ).IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (hxy' : (W.map ψ).toAffine.Equation (ψ x) (ψ y))
    (hord' : NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)) :
    Spec.map (CommRingCat.ofHom ψ) ≫ tateBaseSpecMapOfPoint R W x y hxy hord =
      tateBaseSpecMapOfPoint R (W.map ψ) (ψ x) (ψ y) hxy' hord' := by
  show Spec.map (CommRingCat.ofHom ψ) ≫
    Spec.map (CommRingCat.ofHom (tateRingOverLiftOfPoint R W x y hxy hord)) =
    Spec.map (CommRingCat.ofHom (tateRingOverLiftOfPoint R (W.map ψ) (ψ x) (ψ y) hxy' hord'))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    tateRingOverLiftOfPoint_comp ψ R hψ W x y hxy hord hxy' hord']

/-- Congruence for `tateBaseSpecMapOfPoint` in the marked point. -/
theorem tateBaseSpecMapOfPoint_congr (R : CommRingCat.{u}) [Algebra ↑R A]
    (W : WeierstrassCurve A) [W.IsElliptic] {x y x' y' : A} (hx : x = x') (hy : y = y')
    (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y)
    (hxy' : W.toAffine.Equation x' y') (hord' : NowhereOrderLEThree W x' y') :
    tateBaseSpecMapOfPoint R W x y hxy hord =
      tateBaseSpecMapOfPoint R W x' y' hxy' hord' := by
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
  rw [baseMap, Category.assoc, tateBaseSpecMapOfPoint_tateStructMap, halg]

end MarkedChartData

end ChartAlgebra

section FibrePoint

/-! ### The restricted section as a `Spec`-point of the fibre model (recipe step 3)

Over any chart-ring algebra `k` (not just fields), the restricted section defines a point
of the base-changed chart model lying in its `Z`-chart, with coordinate evaluations the
algebra images of the chart-point evaluations.  This is the affine test-point interface
for the overlap agreement of the local classifying maps. -/

/-- Composing with the identity algebra map is the algebra map. -/
theorem algebraMap_comp_algebraMap_self {A k : Type u} [CommRing A] [CommRing k]
    [Algebra A k] :
    (algebraMap A k).comp (algebraMap A A) = algebraMap A k := by
  rw [Algebra.algebraMap_self, RingHom.comp_id]

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D.U.1) k]

/-- The restricted section as a point of the fibre model. -/
noncomputable def fibrePt (P : Y.curve.Section) :
    SpecPoints (projModel (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))
      (projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) k :=
  ⟨(D.fibreSection k P).1 ≫ (D.fibreChartIso k).hom, by
    have h1 : (D.fibreSection k P).1 ≫ ((D.fibreChartIso k).hom ≫
        projModelπ (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
        (D.fibreSection k P).1 ≫ pullback.snd Y.curve.π (D.geomPt (D.specPt k)) :=
      congrArg ((D.fibreSection k P).1 ≫ ·)
        (pullbackChartIso_hom_π D.W (D.fibreTop_isPullback k))
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap k k)) =
        𝟙 (Spec (CommRingCat.of k)) := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rw [Category.assoc, h2]
    exact h1.trans (D.fibreSection k P).2⟩

/-- The fibre point maps to the chart point at the algebra point (the value chase in
`SpecPoints` form). -/
theorem fibrePt_comp_bc (P : Y.curve.Section) :
    (D.fibrePt k P).1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      D.specPt k ≫ (D.pt P).1 := by
  show ((D.fibreSection k P).1 ≫ (D.fibreChartIso k).hom) ≫ _ = _
  rw [Category.assoc]
  exact D.fibreSection_comp_bc k P

/-- The fibre point lies in the `Z`-chart. -/
theorem fibrePt_inZChart (P : Y.curve.Section) (hZ : InZChart D.W (D.pt P)) :
    InZChart (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) := by
  refine inZChart_of_comp_baseChange D.W (D.fibrePt k P)
    (Spec.map (CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (zChartHom D.W (D.pt P) hZ)))) ?_
  rw [show CommRingCat.ofHom ((algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (zChartHom D.W (D.pt P) hZ)) =
      CommRingCat.ofHom (zChartHom D.W (D.pt P) hZ) ≫
        CommRingCat.ofHom (algebraMap ↑Γ(Y.base, D.U.1) k) from
    CommRingCat.ofHom_comp _ _]
  rw [Spec.map_comp, Category.assoc, Spec_map_zChartHom_awayι, fibrePt_comp_bc]

/-- The base-changed fibre point is the composed chart point. -/
theorem specPointBaseChange_fibrePt (P : Y.curve.Section) :
    specPointBaseChange D.W (D.fibrePt k P) =
      specPointComp D.W (D.pt P) (algebraMap ↑Γ(Y.base, D.U.1) k)
        algebraMap_comp_algebraMap_self := by
  refine Subtype.ext ?_
  show (D.fibrePt k P).1 ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W = _
  rw [fibrePt_comp_bc]
  rfl

/-- The fibre point evaluates to the algebra image of the chart evaluation (`x`-side). -/
theorem zChartEval_fibrePt_coordX (P : Y.curve.Section) (hZ : InZChart D.W (D.pt P)) :
    zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
      (D.fibrePt_inZChart k P hZ) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k (zChartEval D.W (D.pt P) hZ (coordX D.W)) := by
  rw [← zChartEval_specPointBaseChange_coordX D.W (D.fibrePt k P)
      (D.fibrePt_inZChart k P hZ),
    zChartEval_congr D.W (D.specPointBaseChange_fibrePt k P)
      (inZChart_specPointBaseChange D.W _ _)
      (inZChart_specPointComp D.W (D.pt P) hZ _ _),
    zChartEval_specPointComp]
  exact D.fibrePt_inZChart k P hZ

/-- The fibre point evaluates to the algebra image of the chart evaluation (`y`-side). -/
theorem zChartEval_fibrePt_coordY (P : Y.curve.Section) (hZ : InZChart D.W (D.pt P)) :
    zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
      (D.fibrePt_inZChart k P hZ) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) =
      algebraMap ↑Γ(Y.base, D.U.1) k (zChartEval D.W (D.pt P) hZ (coordY D.W)) := by
  rw [← zChartEval_specPointBaseChange_coordY D.W (D.fibrePt k P)
      (D.fibrePt_inZChart k P hZ),
    zChartEval_congr D.W (D.specPointBaseChange_fibrePt k P)
      (inZChart_specPointBaseChange D.W _ _)
      (inZChart_specPointComp D.W (D.pt P) hZ _ _),
    zChartEval_specPointComp]
  exact D.fibrePt_inZChart k P hZ

/-- The fibre point inherits the nowhere-small-order condition. -/
theorem fibrePt_hord (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    NowhereOrderLEThree (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
        (D.fibrePt_inZChart k P (D.pt_inZChart P hP))
        (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))))
      (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
        (D.fibrePt_inZChart k P (D.pt_inZChart P hP))
        (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) := by
  rw [D.zChartEval_fibrePt_coordX k P (D.pt_inZChart P hP),
    D.zChartEval_fibrePt_coordY k P (D.pt_inZChart P hP)]
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
noncomputable def fibreModelIso :
    projModel (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≅
      projModel (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) :=
  (D₁.fibreChartIso k).symm ≪≫ pullback.congrHom rfl hgeom ≪≫ D₂.fibreChartIso k

/-- The fibre-model comparison respects the structure maps. -/
theorem fibreModelIso_π :
    (fibreModelIso D₁ D₂ k hgeom).hom ≫
      projModelπ (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) =
      projModelπ (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) := by
  have h1 : (D₂.fibreChartIso k).hom ≫
      projModelπ (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) =
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) :=
    pullbackChartIso_hom_π D₂.W (D₂.fibreTop_isPullback k)
  have h2 : (pullback.congrHom rfl hgeom).hom ≫
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have h3 : (D₁.fibreChartIso k).inv ≫
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) =
      projModelπ (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) := by
    rw [Iso.inv_comp_eq]
    exact (pullbackChartIso_hom_π D₁.W (D₁.fibreTop_isPullback k)).symm
  rw [fibreModelIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  refine Eq.trans (congrArg (fun m => (D₁.fibreChartIso k).inv ≫ m) ?_) h3
  exact Eq.trans (congrArg (fun m => (pullback.congrHom rfl hgeom).hom ≫ m) h1) h2

/-- The fibre-model comparison is pointed. -/
theorem fibreModelIso_zero :
    projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
      (fibreModelIso D₁ D₂ k hgeom).hom =
      projModelZero (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) := by
  have h1 : projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
      (D₁.fibreChartIso k).inv =
      (Y.curve.baseChange (D₁.geomPt (D₁.specPt k))).zero := by
    rw [Iso.comp_inv_eq]
    exact (D₁.fibre_zero_comp k).symm
  have e1 : (pullback.congrHom rfl hgeom).hom ≫
      pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have e2 : (pullback.congrHom rfl hgeom).hom ≫
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
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
  rw [fibreModelIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
      ((D₁.fibreChartIso k).inv ≫ (pullback.congrHom rfl hgeom).hom ≫
        (D₂.fibreChartIso k).hom)
      = (projModelZero (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) ≫
          (D₁.fibreChartIso k).inv) ≫ (pullback.congrHom rfl hgeom).hom ≫
          (D₂.fibreChartIso k).hom := (Category.assoc _ _ _).symm
    _ = (Y.curve.baseChange (D₁.geomPt (D₁.specPt k))).zero ≫
          (pullback.congrHom rfl hgeom).hom ≫ (D₂.fibreChartIso k).hom :=
        congrArg (· ≫ (pullback.congrHom rfl hgeom).hom ≫ (D₂.fibreChartIso k).hom) h1
    _ = ((Y.curve.baseChange (D₁.geomPt (D₁.specPt k))).zero ≫
          (pullback.congrHom rfl hgeom).hom) ≫ (D₂.fibreChartIso k).hom :=
        (Category.assoc _ _ _).symm
    _ = (Y.curve.baseChange (D₂.geomPt (D₂.specPt k))).zero ≫ (D₂.fibreChartIso k).hom :=
        congrArg (· ≫ (D₂.fibreChartIso k).hom) hz12
    _ = projModelZero (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) := D₂.fibre_zero_comp k

/-- The fibre-model comparison carries the first fibre point to the second. -/
theorem fibrePt_fibreModelIso (P : Y.curve.Section) :
    (D₁.fibrePt k P).1 ≫ (fibreModelIso D₁ D₂ k hgeom).hom = (D₂.fibrePt k P).1 := by
  have e1 : (pullback.congrHom rfl hgeom).hom ≫
      pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have e2 : (pullback.congrHom rfl hgeom).hom ≫
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hfs : (D₁.fibreSection k P).1 ≫ (pullback.congrHom rfl hgeom).hom =
      (D₂.fibreSection k P).1 := by
    rw [D₁.fibreSection_coe k P, D₂.fibreSection_coe k P]
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
  show ((D₁.fibreSection k P).1 ≫ (D₁.fibreChartIso k).hom) ≫ _ =
    (D₂.fibreSection k P).1 ≫ (D₂.fibreChartIso k).hom
  rw [fibreModelIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc ((D₁.fibreSection k P).1 ≫ (D₁.fibreChartIso k).hom) ≫
      ((D₁.fibreChartIso k).inv ≫ (pullback.congrHom rfl hgeom).hom ≫
        (D₂.fibreChartIso k).hom)
      = (D₁.fibreSection k P).1 ≫ ((D₁.fibreChartIso k).hom ≫
          (D₁.fibreChartIso k).inv ≫ (pullback.congrHom rfl hgeom).hom ≫
          (D₂.fibreChartIso k).hom) := Category.assoc _ _ _
    _ = (D₁.fibreSection k P).1 ≫ ((pullback.congrHom rfl hgeom).hom ≫
          (D₂.fibreChartIso k).hom) :=
        congrArg ((D₁.fibreSection k P).1 ≫ ·) (Iso.hom_inv_id_assoc _ _)
    _ = ((D₁.fibreSection k P).1 ≫ (pullback.congrHom rfl hgeom).hom) ≫
          (D₂.fibreChartIso k).hom := (Category.assoc _ _ _).symm
    _ = (D₂.fibreSection k P).1 ≫ (D₂.fibreChartIso k).hom :=
        congrArg (· ≫ (D₂.fibreChartIso k).hom) hfs

include hgeom in
/-- **Overlap agreement of the pointed atlas maps** through the comparison ENGINE. -/
theorem tateBaseSpecMapOfPoint_fibrePt_agree [Algebra ↑R k]
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    tateBaseSpecMapOfPoint R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) _ _
      (zChartEval_equation_self _ (D₁.fibrePt k P)
        (D₁.fibrePt_inZChart k P (D₁.pt_inZChart P hP)))
      (D₁.fibrePt_hord k P hP) =
    tateBaseSpecMapOfPoint R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) _ _
      (zChartEval_equation_self _ (D₂.fibrePt k P)
        (D₂.fibrePt_inZChart k P (D₂.pt_inZChart P hP)))
      (D₂.fibrePt_hord k P hP) :=
  tateBaseSpecMapOfPoint_eq_of_pointedIso R
    (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k))
    (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k))
    (fibreModelIso D₁ D₂ k hgeom)
    (fibreModelIso_π D₁ D₂ k hgeom) (fibreModelIso_zero D₁ D₂ k hgeom)
    (D₁.fibrePt k P) (D₂.fibrePt k P)
    (D₁.fibrePt_inZChart k P (D₁.pt_inZChart P hP))
    (D₂.fibrePt_inZChart k P (D₂.pt_inZChart P hP))
    (fibrePt_fibreModelIso D₁ D₂ k hgeom P)
    (D₁.fibrePt_hord k P hP) (D₂.fibrePt_hord k P hP)

include hgeom in
/-- **The local classifying base maps agree on affine test points of the overlap.** -/
theorem specPt_tateBaseSpecMapOfPoint_agree [Algebra ↑R k]
    [Algebra ↑R ↑Γ(Y.base, D₁.U.1)] [Algebra ↑R ↑Γ(Y.base, D₂.U.1)]
    (htower₁ : (algebraMap ↑Γ(Y.base, D₁.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) = algebraMap ↑R k)
    (htower₂ : (algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) = algebraMap ↑R k)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    D₁.specPt k ≫ (tateBaseSpecMapOfPoint R D₁.W _ _
        (zChartEval_equation_self D₁.W (D₁.pt P) (D₁.pt_inZChart P hP))
        (D₁.pt_hord P hP)) =
      D₂.specPt k ≫ (tateBaseSpecMapOfPoint R D₂.W _ _
        (zChartEval_equation_self D₂.W (D₂.pt P) (D₂.pt_inZChart P hP))
        (D₂.pt_hord P hP)) := by
  have hx₁ := D₁.zChartEval_fibrePt_coordX k P (D₁.pt_inZChart P hP)
  have hy₁ := D₁.zChartEval_fibrePt_coordY k P (D₁.pt_inZChart P hP)
  have hx₂ := D₂.zChartEval_fibrePt_coordX k P (D₂.pt_inZChart P hP)
  have hy₂ := D₂.zChartEval_fibrePt_coordY k P (D₂.pt_inZChart P hP)
  have hxy₁' : (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)).toAffine.Equation
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (zChartEval D₁.W (D₁.pt P) (D₁.pt_inZChart P hP) (coordX D₁.W)))
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (zChartEval D₁.W (D₁.pt P) (D₁.pt_inZChart P hP) (coordY D₁.W))) := by
    rw [← hx₁, ← hy₁]
    exact zChartEval_equation_self _ (D₁.fibrePt k P)
      (D₁.fibrePt_inZChart k P (D₁.pt_inZChart P hP))
  have hord₁' : NowhereOrderLEThree (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k))
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (zChartEval D₁.W (D₁.pt P) (D₁.pt_inZChart P hP) (coordX D₁.W)))
      (algebraMap ↑Γ(Y.base, D₁.U.1) k
        (zChartEval D₁.W (D₁.pt P) (D₁.pt_inZChart P hP) (coordY D₁.W))) := by
    rw [← hx₁, ← hy₁]
    exact D₁.fibrePt_hord k P hP
  have hxy₂' : (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)).toAffine.Equation
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (zChartEval D₂.W (D₂.pt P) (D₂.pt_inZChart P hP) (coordX D₂.W)))
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (zChartEval D₂.W (D₂.pt P) (D₂.pt_inZChart P hP) (coordY D₂.W))) := by
    rw [← hx₂, ← hy₂]
    exact zChartEval_equation_self _ (D₂.fibrePt k P)
      (D₂.fibrePt_inZChart k P (D₂.pt_inZChart P hP))
  have hord₂' : NowhereOrderLEThree (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k))
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (zChartEval D₂.W (D₂.pt P) (D₂.pt_inZChart P hP) (coordX D₂.W)))
      (algebraMap ↑Γ(Y.base, D₂.U.1) k
        (zChartEval D₂.W (D₂.pt P) (D₂.pt_inZChart P hP) (coordY D₂.W))) := by
    rw [← hx₂, ← hy₂]
    exact D₂.fibrePt_hord k P hP
  calc D₁.specPt k ≫ (tateBaseSpecMapOfPoint R D₁.W _ _
        (zChartEval_equation_self D₁.W (D₁.pt P) (D₁.pt_inZChart P hP)) (D₁.pt_hord P hP))
      = tateBaseSpecMapOfPoint R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) _ _
          hxy₁' hord₁' :=
        tateBaseSpecMapOfPoint_naturality (algebraMap ↑Γ(Y.base, D₁.U.1) k) R htower₁
          D₁.W _ _ (zChartEval_equation_self D₁.W (D₁.pt P) (D₁.pt_inZChart P hP))
          (D₁.pt_hord P hP) hxy₁' hord₁'
    _ = tateBaseSpecMapOfPoint R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) _ _
          (zChartEval_equation_self _ (D₁.fibrePt k P)
            (D₁.fibrePt_inZChart k P (D₁.pt_inZChart P hP)))
          (D₁.fibrePt_hord k P hP) :=
        tateBaseSpecMapOfPoint_congr R _ hx₁.symm hy₁.symm hxy₁' hord₁' _ _
    _ = tateBaseSpecMapOfPoint R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) _ _
          (zChartEval_equation_self _ (D₂.fibrePt k P)
            (D₂.fibrePt_inZChart k P (D₂.pt_inZChart P hP)))
          (D₂.fibrePt_hord k P hP) :=
        tateBaseSpecMapOfPoint_fibrePt_agree D₁ D₂ k hgeom P hP
    _ = tateBaseSpecMapOfPoint R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) _ _
          hxy₂' hord₂' :=
        tateBaseSpecMapOfPoint_congr R _ hx₂ hy₂ _ _ hxy₂' hord₂'
    _ = D₂.specPt k ≫ (tateBaseSpecMapOfPoint R D₂.W _ _
          (zChartEval_equation_self D₂.W (D₂.pt P) (D₂.pt_inZChart P hP))
          (D₂.pt_hord P hP)) :=
        (tateBaseSpecMapOfPoint_naturality (algebraMap ↑Γ(Y.base, D₂.U.1) k) R htower₂
          D₂.W _ _ (zChartEval_equation_self D₂.W (D₂.pt P) (D₂.pt_inZChart P hP))
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
    c₁ ≫ (tateBaseSpecMapOfPoint R D₁.W _ _
        (zChartEval_equation_self D₁.W (D₁.pt P) (D₁.pt_inZChart P hP))
        (D₁.pt_hord P hP)) =
      c₂ ≫ (tateBaseSpecMapOfPoint R D₂.W _ _
        (zChartEval_equation_self D₂.W (D₂.pt P) (D₂.pt_inZChart P hP))
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
      have hw := congrArg (fun m => m ≫ Y.structMap) hcc
      simp only [Category.assoc] at hw ⊢
      exact hw.symm
    have hring := Spec.map_injective hspec
    have := congrArg CommRingCat.Hom.hom hring
    simpa using this
  have h := specPt_tateBaseSpecMapOfPoint_agree D₁ D₂ k hgeom htower₁ htower₂ P hP
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
    (fun s => (chartAt Y s).U.1.toScheme)
    (fun s => (chartAt Y s).U.1.ι)
    (fun s => ⟨s, ⟨⟨s, chartAt_mem s⟩, rfl⟩⟩)

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
    have hw := congrArg (fun m => (Scheme.isoSpec V).inv ≫
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
        congrArg (fun m => (Scheme.isoSpec V).inv ≫
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
        (congrArg (fun m => (Scheme.isoSpec V).inv ≫
          (Scheme.affineCover (pullback ((chartCover Y).f i) ((chartCover Y).f j))).f z ≫
          pullback.snd ((chartCover Y).f i) ((chartCover Y).f j) ≫ m)
          (Iso.hom_inv_id_assoc (chartAt Y j).U.2.isoSpec (chartAt Y j).U.1.ι)).symm
  have h := test_baseMap_agree (chartAt Y i) (chartAt Y j)
    ((chartAt Y i).chartAlgebra_compatible) ((chartAt Y j).chartAlgebra_compatible)
    ↑Γ(V, ⊤) _ _ hcc P hP
  show (Scheme.isoSpec V).inv ≫ _ ≫ pullback.fst _ _ ≫
      ((chartAt Y i).U.2.isoSpec.hom ≫ (tateBaseSpecMapOfPoint R (chartAt Y i).W _ _
        (zChartEval_equation_self (chartAt Y i).W ((chartAt Y i).pt P)
          ((chartAt Y i).pt_inZChart P hP)) ((chartAt Y i).pt_hord P hP))) =
    (Scheme.isoSpec V).inv ≫ _ ≫ pullback.snd _ _ ≫
      ((chartAt Y j).U.2.isoSpec.hom ≫ (tateBaseSpecMapOfPoint R (chartAt Y j).W _ _
        (zChartEval_equation_self (chartAt Y j).W ((chartAt Y j).pt P)
          ((chartAt Y j).pt_inZChart P hP)) ((chartAt Y j).pt_hord P hP)))
  exact h

/-- **The glued classifying base map** `Y.base ⟶ tateBase R`. -/
noncomputable def gluedBaseMap (P : Y.curve.Section)
    (hP : Y.curve.NowhereGeomOrderLEThree P) : Y.base ⟶ tateBase R :=
  EllObj.tateBaseMapOfOpenCover R Y (chartCover Y) (coverBaseMap P hP)
    (coverBaseMap_compat P hP)

@[reassoc (attr := simp)]
theorem ι_gluedBaseMap (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (s : ↥Y.base) :
    (chartAt Y s).U.1.ι ≫ gluedBaseMap P hP = coverBaseMap P hP s :=
  EllObj.ι_tateBaseMapOfOpenCover R Y (chartCover Y) (coverBaseMap P hP)
    (coverBaseMap_compat P hP) s

/-- The glued base map lies over `Spec R`. -/
theorem gluedBaseMap_over (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    gluedBaseMap P hP ≫ tateStructMap R = Y.structMap := by
  refine EllObj.tateBaseMapOfOpenCover_base_w R Y (chartCover Y) (coverBaseMap P hP)
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
  exact heq_of_eq (GradedRingHom.ext fun x => eq_of_heq (h x))

private lemma mkHeq {R' : Type u} [CommRing R'] {V V' : WeierstrassCurve R'} (e : V = V')
    (q : MvPolynomial (Fin 3) R') :
    HEq (Ideal.Quotient.mk (projIdeal V).toIdeal q)
      (Ideal.Quotient.mk (projIdeal V').toIdeal q) := by
  subst e; rfl

/-- **Model base changes compose** along ring maps. -/
theorem projModelBaseChange_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (W : WeierstrassCurve A) :
    projModelBaseChange ψ (W.map φ) ≫ projModelBaseChange φ W =
      eqToHom (congrArg projModel (WeierstrassCurve.map_map W φ ψ)) ≫
        projModelBaseChange (ψ.comp φ) W := by
  show Proj.map (baseChangeGradedHom ψ (W.map φ)) _ ≫ Proj.map (baseChangeGradedHom φ W) _ =
    eqToHom _ ≫ Proj.map (baseChangeGradedHom (ψ.comp φ) W) _
  rw [← Proj.map_comp]
  refine projMapTransportHeq W (WeierstrassCurve.map_map W φ ψ).symm _ _ _ _
    (gradedHomHeq W (WeierstrassCurve.map_map W φ ψ) _ _ fun x => ?_)
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
derivation runs through `projModelVCIso_map` (T-W7.0h) and `projModelBaseChange_comp`. -/

/-- Congruence for the T-E1 normalisation in the marked point. -/
theorem tateNormalVariableChange_congr {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] {x₁ y₁ x₂ y₂ : A} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (hxy₁ : W.toAffine.Equation x₁ y₁) (hord₁ : NowhereOrderLEThree W x₁ y₁)
    (hxy₂ : W.toAffine.Equation x₂ y₂) (hord₂ : NowhereOrderLEThree W x₂ y₂) :
    tateNormalVariableChange W x₁ y₁ hxy₁ hord₁ =
      tateNormalVariableChange W x₂ y₂ hxy₂ hord₂ := by
  subst hx
  subst hy
  rfl

/-- Congruence for the pointed atlas ring map in the marked point. -/
theorem tateRingOverLiftOfPoint_congr (R : CommRingCat.{u}) {A : Type u} [CommRing A]
    [Algebra ↑R A] (W : WeierstrassCurve A) [W.IsElliptic]
    {x₁ y₁ x₂ y₂ : A} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (hxy₁ : W.toAffine.Equation x₁ y₁) (hord₁ : NowhereOrderLEThree W x₁ y₁)
    (hxy₂ : W.toAffine.Equation x₂ y₂) (hord₂ : NowhereOrderLEThree W x₂ y₂) :
    tateRingOverLiftOfPoint R W x₁ y₁ hxy₁ hord₁ =
      tateRingOverLiftOfPoint R W x₂ y₂ hxy₂ hord₂ := by
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

private lemma projModelBaseChange_ringHom_congr {A B : Type u} [CommRing A] [CommRing B]
    {ρ₁ ρ₂ : A →+* B} (h : ρ₁ = ρ₂) (W : WeierstrassCurve A) :
    projModelBaseChange ρ₁ W = eqToHom (by rw [h]) ≫ projModelBaseChange ρ₂ W := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

/-- The classifying top map, unfolded to its canonical three-factor composite. -/
theorem projTateMap_unfold {A : Type u} [CommRing A] (R : CommRingCat.{u}) [Algebra ↑R A]
    (W : WeierstrassCurve A) [W.IsElliptic]
    (g : SpecPoints (projModel W) (projModelπ W) A) (hZ : InZChart W g)
    (hord : NowhereOrderLEThree W
      (zChartEval W g hZ (coordX W)) (zChartEval W g hZ (coordY W))) :
    projTateMap R W g hZ hord =
      (projModelVCIso (tateNormalVariableChange W _ _
        (zChartEval_equation_self W g hZ) hord) W).inv ≫
      eqToHom (congrArg projModel (tateCurveLocOver_map_marked R W g hZ hord)).symm ≫
      projModelBaseChange
        ((tateRingOverAlgLiftOfPoint R W _ _ (zChartEval_equation_self W g hZ) hord :
          tateRingOver R →ₐ[R] A) : tateRingOver R →+* A) (tateCurveLocOver R) := by
  rw [projTateMap, tateNormalIso, Iso.trans_inv, eqToIso.inv, Category.assoc]

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R} (D : MarkedChartData R Y)
  (k : Type u) [CommRing k] [Algebra ↑Γ(Y.base, D.U.1) k]
  [Algebra ↑R ↑Γ(Y.base, D.U.1)] [Algebra ↑R k]

/-- **Naturality of the classifying top map**: base-changing the chart model and classifying
at the fibre point agrees with classifying at the chart point and base-changing. -/
theorem projModelBaseChange_projTateMap
    (htower : (algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D.U.1)) = algebraMap ↑R k)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W ≫
      projTateMap R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP) =
    projTateMap R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
      (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (D.fibrePt_hord k P hP) := by
  have hx := D.zChartEval_fibrePt_coordX k P (D.pt_inZChart P hP)
  have hy := D.zChartEval_fibrePt_coordY k P (D.pt_inZChart P hP)
  have hxy₂ : (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).toAffine.Equation
      ((algebraMap ↑Γ(Y.base, D.U.1) k) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)))
      ((algebraMap ↑Γ(Y.base, D.U.1) k) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W))) := by
    rw [← hx, ← hy]
    exact zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))
  have hord₂ : NowhereOrderLEThree (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      ((algebraMap ↑Γ(Y.base, D.U.1) k) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)))
      ((algebraMap ↑Γ(Y.base, D.U.1) k) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W))) := by
    rw [← hx, ← hy]
    exact D.fibrePt_hord k P hP
  -- (F2) the two T-E1 normalisations
  have hC : tateNormalVariableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
        (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))))
      (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
        (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))))
      (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) =
      (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W))
      (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k) :=
    (tateNormalVariableChange_congr (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) hx hy (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) hxy₂ hord₂).trans
      (tateNormalVariableChange_map (algebraMap ↑Γ(Y.base, D.U.1) k) D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W))
        (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) hxy₂ hord₂).symm
  -- (F3) the two pointed atlas ring maps
  have hL : tateRingOverLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
      (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
        (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))))
      (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
        (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))))
      (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) =
      (algebraMap ↑Γ(Y.base, D.U.1) k).comp (tateRingOverLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W))
        (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) :=
    (tateRingOverLiftOfPoint_congr R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) hx hy (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) hxy₂ hord₂).trans
      (tateRingOverLiftOfPoint_comp (algebraMap ↑Γ(Y.base, D.U.1) k) R htower D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W))
        (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) hxy₂ hord₂).symm
  -- (G1) T-W7.0h: move the base change past the variable-change isomorphism
  have hG1 := projModelVCIso_map (R := ↑Γ(Y.base, D.U.1)) (R' := k) (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W
  -- unfold both classifying maps to their canonical composites
  rw [projTateMap_unfold R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP),
    projTateMap_unfold R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
      (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (D.fibrePt_hord k P hP),
    ← cancel_epi (projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom]
  have hstar : (projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W) ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).hom := by
    refine Eq.trans ?_ (congrArg (fun m =>
      eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ m) hG1.symm)
    rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hslide := projModelBaseChange_eqToHom (algebraMap ↑Γ(Y.base, D.U.1) k) (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))
  have hcomp := projModelBaseChange_comp ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (algebraMap ↑Γ(Y.base, D.U.1) k) (tateCurveLocOver R)
  have hL' : (algebraMap ↑Γ(Y.base, D.U.1) k).comp ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) = ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) := hL.symm
  have hbcL : projModelBaseChange ((algebraMap ↑Γ(Y.base, D.U.1) k).comp ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))) (tateCurveLocOver R) =
      eqToHom (show projModel ((tateCurveLocOver R).map ((algebraMap ↑Γ(Y.base, D.U.1) k).comp ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))))) = projModel ((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))) by rw [hL']) ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) :=
    projModelBaseChange_ringHom_congr hL' (tateCurveLocOver R)
  have hinvC : (projModelVCIso (tateNormalVariableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).inv = (projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).inv ≫ eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel ((tateNormalVariableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) by rw [hC]) :=
    projModelVCIso_inv_congr hC (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))
  calc (projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).inv ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R)
      = ((projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W) ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).inv ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R) :=
        (Category.assoc _ _ _).symm
    _ = (eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W) ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).hom) ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).inv ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R) :=
        congrArg (· ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).inv ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R)) hstar
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W) ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).hom ≫ (projModelVCIso (tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) D.W).inv ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R) := by
        simp only [Category.assoc]
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W) ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R) :=
        congrArg (fun m => eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W) ≫ m) (Iso.hom_inv_id_assoc _ _)
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ (projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W) ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP))).symm) ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R) := by
        simp only [Category.assoc]
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ (eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]) ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))))) ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R) :=
        congrArg (fun m => eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ m ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R)) hslide
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]) ≫ (projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) ((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))) ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (tateCurveLocOver R)) := by
        simp only [Category.assoc]
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]) ≫ (eqToHom (congrArg projModel (WeierstrassCurve.map_map (tateCurveLocOver R) ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (algebraMap ↑Γ(Y.base, D.U.1) k))) ≫
          projModelBaseChange ((algebraMap ↑Γ(Y.base, D.U.1) k).comp ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))) (tateCurveLocOver R)) :=
        congrArg (fun m => eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]) ≫ m) hcomp
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]) ≫ (eqToHom (congrArg projModel (WeierstrassCurve.map_map (tateCurveLocOver R) ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (algebraMap ↑Γ(Y.base, D.U.1) k))) ≫ (eqToHom (show projModel ((tateCurveLocOver R).map ((algebraMap ↑Γ(Y.base, D.U.1) k).comp ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))))) = projModel ((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))) by rw [hL']) ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R))) :=
        congrArg (fun m => eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [WeierstrassCurve.map_variableChange]) ≫ eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)) • D.W).map (algebraMap ↑Γ(Y.base, D.U.1) k)) = projModel (((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1)))).map (algebraMap ↑Γ(Y.base, D.U.1) k)) by rw [tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP)]) ≫ (eqToHom (congrArg projModel (WeierstrassCurve.map_map (tateCurveLocOver R) ((((tateRingOverAlgLiftOfPoint R D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP) : tateRingOver R →ₐ[R] ↑Γ(Y.base, D.U.1))) : tateRingOver R →+* ↑Γ(Y.base, D.U.1))) (algebraMap ↑Γ(Y.base, D.U.1) k))) ≫ m)) hbcL
    _ = eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel ((tateCurveLocOver R).map ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k))) by rw [WeierstrassCurve.map_variableChange, ← tateCurveLocOver_map_marked R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP), WeierstrassCurve.map_map, hL']) ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) := by
        simp only [eqToHom_trans_assoc, eqToHom_trans]
    _ = (projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫ (projModelVCIso (tateNormalVariableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).inv ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (D.fibrePt_hord k P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) := by
        rw [hinvC]
        rw [show (projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).hom ≫ ((projModelVCIso ((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))).inv ≫ eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel ((tateNormalVariableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) by rw [hC])) ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (D.fibrePt_hord k P hP))).symm ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) =
            (eqToHom (show projModel (((tateNormalVariableChange D.W (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordX D.W)) (zChartEval D.W (D.pt P) (D.pt_inZChart P hP) (coordY D.W)) (zChartEval_equation_self D.W (D.pt P) (D.pt_inZChart P hP)) (D.pt_hord P hP)).map (algebraMap ↑Γ(Y.base, D.U.1) k)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) = projModel ((tateNormalVariableChange (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP)) • (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k))) by rw [hC]) ≫ eqToHom (congrArg projModel (tateCurveLocOver_map_marked R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (D.fibrePt_hord k P hP))).symm) ≫ projModelBaseChange ((((tateRingOverAlgLiftOfPoint R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordX (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (coordY (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)))) (zChartEval_equation_self (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P) (D.fibrePt_inZChart k P (D.pt_inZChart P hP))) (D.fibrePt_hord k P hP) : tateRingOver R →ₐ[R] k)) : tateRingOver R →+* k)) (tateCurveLocOver R) from
          ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
            (Iso.hom_inv_id_assoc _ _)).trans (Category.assoc _ _ _).symm]
        rw [eqToHom_trans]

end MarkedChartData

end TopNaturality

section TopRestriction

/-! ### Fibre restriction and overlap agreement of the local classifying top maps
(recipe step 2, top glue)

Restricting a local classifying top map to the fibre over an affine test point computes
the classifying map of the fibre model at the fibre point (`fibreMap_topMap`, through the
step-1 naturality); the comparison ENGINE then forces the two fibre restrictions of the
top maps of overlapping charts to agree (`fibreMap_topMap_agree`); the instance-free
test-point form (`test_topMap_agree`) is the input to the `E`-cover gluing. -/

namespace MarkedChartData

variable {R : CommRingCat.{u}} {Y : EllObj R}

section OneChart

variable (D : MarkedChartData R Y) (k : Type u) [CommRing k]
  [Algebra ↑Γ(Y.base, D.U.1) k] [Algebra ↑R ↑Γ(Y.base, D.U.1)] [Algebra ↑R k]

/-- **Fibre restriction of the local classifying top map**: over an affine test point the
top map computes the classifying map of the fibre model at the fibre point. -/
theorem fibreMap_topMap
    (htower : (algebraMap ↑Γ(Y.base, D.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D.U.1)) = algebraMap ↑R k)
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    D.fibreMap k ≫ D.topMap P hP =
      (D.fibreChartIso k).hom ≫
        projTateMap R (D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)) (D.fibrePt k P)
          (D.fibrePt_inZChart k P (D.pt_inZChart P hP)) (D.fibrePt_hord k P hP) := by
  have hbc : (D.fibreChartIso k).hom ≫
      projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W =
      D.fibreMap k ≫ D.e.hom :=
    pullbackChartIso_hom_bc D.W (D.fibreTop_isPullback k)
  have h1 : D.fibreMap k ≫ D.topMap P hP =
      ((D.fibreChartIso k).hom ≫ projModelBaseChange (algebraMap ↑Γ(Y.base, D.U.1) k) D.W) ≫
        projTateMap R D.W (D.pt P) (D.pt_inZChart P hP) (D.pt_hord P hP) := by
    rw [hbc, topMap]
    simp only [Category.assoc]
  rw [h1, Category.assoc, projModelBaseChange_projTateMap D k htower P hP]

end OneChart

section TwoCharts

variable (D₁ D₂ : MarkedChartData R Y) (k : Type u) [CommRing k]
  [Algebra ↑Γ(Y.base, D₁.U.1) k] [Algebra ↑Γ(Y.base, D₂.U.1) k]
  [Algebra ↑R ↑Γ(Y.base, D₁.U.1)] [Algebra ↑R ↑Γ(Y.base, D₂.U.1)] [Algebra ↑R k]

/-- **Overlap agreement of the fibre restrictions of the local classifying top maps**,
through the comparison ENGINE with `fibreModelIso`-data. -/
theorem fibreMap_topMap_agree
    (htower₁ : (algebraMap ↑Γ(Y.base, D₁.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₁.U.1)) = algebraMap ↑R k)
    (htower₂ : (algebraMap ↑Γ(Y.base, D₂.U.1) k).comp
      (algebraMap ↑R ↑Γ(Y.base, D₂.U.1)) = algebraMap ↑R k)
    (hgeom : D₁.geomPt (D₁.specPt k) = D₂.geomPt (D₂.specPt k))
    (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) :
    D₁.fibreMap k ≫ D₁.topMap P hP =
      (pullback.congrHom rfl hgeom).hom ≫ D₂.fibreMap k ≫ D₂.topMap P hP := by
  rw [fibreMap_topMap D₁ k htower₁ P hP, fibreMap_topMap D₂ k htower₂ P hP]
  have hengine : (fibreModelIso D₁ D₂ k hgeom).hom ≫
      projTateMap R (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k)) (D₂.fibrePt k P)
        (D₂.fibrePt_inZChart k P (D₂.pt_inZChart P hP)) (D₂.fibrePt_hord k P hP) =
      projTateMap R (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k)) (D₁.fibrePt k P)
        (D₁.fibrePt_inZChart k P (D₁.pt_inZChart P hP)) (D₁.fibrePt_hord k P hP) :=
    projTateMap_eq_of_pointedIso R
      (D₁.W.map (algebraMap ↑Γ(Y.base, D₁.U.1) k))
      (D₂.W.map (algebraMap ↑Γ(Y.base, D₂.U.1) k))
      (fibreModelIso D₁ D₂ k hgeom)
      (fibreModelIso_π D₁ D₂ k hgeom) (fibreModelIso_zero D₁ D₂ k hgeom)
      (D₁.fibrePt k P) (D₂.fibrePt k P)
      (D₁.fibrePt_inZChart k P (D₁.pt_inZChart P hP))
      (D₂.fibrePt_inZChart k P (D₂.pt_inZChart P hP))
      (fibrePt_fibreModelIso D₁ D₂ k hgeom P)
      (D₁.fibrePt_hord k P hP) (D₂.fibrePt_hord k P hP)
  rw [← hengine, fibreModelIso]
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
      have hw := congrArg (fun m => m ≫ Y.structMap) hcc
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
  have hmf₁ : D₁.fibreMap k ≫ pullback.fst Y.curve.π D₁.U.1.ι =
      pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫ 𝟙 Y.curve.E :=
    pullback.lift_fst _ _ _
  have hms₁ : D₁.fibreMap k ≫ pullback.snd Y.curve.π D₁.U.1.ι =
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫
        (D₁.specPt k ≫ D₁.U.2.isoSpec.inv) :=
    pullback.lift_snd _ _ _
  have hρ₁ : ρ ≫ D₁.fibreMap k = v₁ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc]
      calc ρ ≫ D₁.fibreMap k ≫ pullback.fst Y.curve.π D₁.U.1.ι
          = ρ ≫ pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫ 𝟙 Y.curve.E := by
            rw [hmf₁]
        _ = (ρ ≫ pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k))) ≫ 𝟙 Y.curve.E :=
            (Category.assoc _ _ _).symm
        _ = v₁ ≫ pullback.fst Y.curve.π D₁.U.1.ι := by rw [Category.comp_id, hρfst]
    · rw [Category.assoc]
      calc ρ ≫ D₁.fibreMap k ≫ pullback.snd Y.curve.π D₁.U.1.ι
          = ρ ≫ pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) ≫
              (D₁.specPt k ≫ D₁.U.2.isoSpec.inv) := by rw [hms₁]
        _ = (ρ ≫ pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k))) ≫
              (D₁.specPt k ≫ D₁.U.2.isoSpec.inv) := (Category.assoc _ _ _).symm
        _ = w ≫ c₁ ≫ D₁.U.2.isoSpec.inv := by rw [hρsnd, hsp₁]
        _ = v₁ ≫ pullback.snd Y.curve.π D₁.U.1.ι := hv₁.symm
  have hch₁ : (pullback.congrHom rfl hgeom).hom ≫
      pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.fst Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hch₂ : (pullback.congrHom rfl hgeom).hom ≫
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) =
      pullback.snd Y.curve.π (D₁.geomPt (D₁.specPt k)) := by
    rw [pullback.congrHom_hom]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hmf₂ : D₂.fibreMap k ≫ pullback.fst Y.curve.π D₂.U.1.ι =
      pullback.fst Y.curve.π (D₂.geomPt (D₂.specPt k)) ≫ 𝟙 Y.curve.E :=
    pullback.lift_fst _ _ _
  have hms₂ : D₂.fibreMap k ≫ pullback.snd Y.curve.π D₂.U.1.ι =
      pullback.snd Y.curve.π (D₂.geomPt (D₂.specPt k)) ≫
        (D₂.specPt k ≫ D₂.U.2.isoSpec.inv) :=
    pullback.lift_snd _ _ _
  have hρ₂ : (ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫ D₂.fibreMap k = v₂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc]
      calc (ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫
            D₂.fibreMap k ≫ pullback.fst Y.curve.π D₂.U.1.ι
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
            D₂.fibreMap k ≫ pullback.snd Y.curve.π D₂.U.1.ι
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
  have hagree := fibreMap_topMap_agree D₁ D₂ k htower₁ htower₂ hgeom P hP
  calc v₁ ≫ D₁.topMap P hP
      = (ρ ≫ D₁.fibreMap k) ≫ D₁.topMap P hP := by rw [hρ₁]
    _ = ρ ≫ D₁.fibreMap k ≫ D₁.topMap P hP := Category.assoc _ _ _
    _ = ρ ≫ (pullback.congrHom rfl hgeom).hom ≫ D₂.fibreMap k ≫ D₂.topMap P hP := by
        rw [hagree]
    _ = ((ρ ≫ (pullback.congrHom rfl hgeom).hom) ≫ D₂.fibreMap k) ≫ D₂.topMap P hP := by
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
    (fun s => pullback Y.curve.π (chartAt Y s).U.1.ι)
    (fun s => pullback.fst Y.curve.π (chartAt Y s).U.1.ι)
    (Equiv.refl _) (fun _ => Iso.refl _) (fun _ => (Category.id_comp _).symm)

/-- The local classifying top maps of the curve cover. -/
noncomputable def coverTopMap (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (s : ↥Y.base) :
    pullback Y.curve.π (chartAt Y s).U.1.ι ⟶ projModel (tateCurveLocOver R) :=
  letI := (chartAt Y s).chartAlgebra
  (chartAt Y s).topMap P hP

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
    have h1 := congrArg (fun m => pullback.fst (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ m)
      (pullback.condition (f := Y.curve.π) (g := (chartAt Y i).U.1.ι))
    have h2 := congrArg (fun m => pullback.snd (pullback.fst Y.curve.π (chartAt Y i).U.1.ι)
        (pullback.fst Y.curve.π (chartAt Y j).U.1.ι) ≫ m)
      (pullback.condition (f := Y.curve.π) (g := (chartAt Y j).U.1.ι))
    have h3 := congrArg (fun m => m ≫ Y.curve.π) hQ
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
    have hw := congrArg (fun m => (Scheme.isoSpec (𝒱.X z)).inv ≫ 𝒱.f z ≫ m)
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
    (fun i j => coverTopMap_compat P hP i j)

@[reassoc (attr := simp)]
theorem ι_gluedTopMap (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P)
    (s : ↥Y.base) :
    pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ gluedTopMap P hP =
      coverTopMap P hP s :=
  Scheme.Cover.ι_glueMorphisms (curveCover Y) (coverTopMap P hP)
    (fun i j => coverTopMap_compat P hP i j) s

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
      (fun s => hpiece s)
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
  refine EllObj.tateClassifyingHom_pullSection_eq R Y (gluedBaseMap P hP)
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

private lemma projModelVCIso_hom_congrC {C₁ C₂ : WeierstrassCurve.VariableChange A}
    (h : C₁ = C₂) (W : WeierstrassCurve A) :
    (projModelVCIso C₁ W).hom =
      eqToHom (show projModel (C₁ • W) = projModel (C₂ • W) by rw [h]) ≫
        (projModelVCIso C₂ W).hom := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

private lemma projModelVCIso_hom_congrW (C : WeierstrassCurve.VariableChange A)
    {V V' : WeierstrassCurve A} (h : V = V') :
    (projModelVCIso C V).hom =
      eqToHom (show projModel (C • V) = projModel (C • V') by rw [h]) ≫
        (projModelVCIso C V').hom ≫
        eqToHom (show projModel V' = projModel V by rw [h]) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The model isomorphism of the identity variable change is the canonical transport. -/
theorem projModelVCIso_one (W : WeierstrassCurve A) :
    (projModelVCIso (1 : WeierstrassCurve.VariableChange A) W).hom =
      eqToHom (congrArg projModel (one_smul _ W)) := by
  have hmul := projModelVCIso_mul (1 : WeierstrassCurve.VariableChange A) 1 W
  have hC := projModelVCIso_hom_congrC
    (show (1 : WeierstrassCurve.VariableChange A) * 1 = 1 from mul_one 1) W
  have hW := projModelVCIso_hom_congrW (1 : WeierstrassCurve.VariableChange A)
    (one_smul (WeierstrassCurve.VariableChange A) W)
  rw [hC, hW] at hmul
  -- hmul : e₀ ≫ h = e₁ ≫ (e₂ ≫ h ≫ e₃) ≫ h
  simp only [Category.assoc, eqToHom_trans_assoc] at hmul
  -- both prefix eqToHoms coincide by proof irrelevance; cancel them
  have hmul2 := (cancel_epi (eqToHom (show projModel
      (((1 : WeierstrassCurve.VariableChange A) * 1) • W) =
      projModel ((1 : WeierstrassCurve.VariableChange A) • W) by rw [mul_one]))).mp hmul
  -- hmul2 : h = h ≫ e₃ ≫ h
  have hmul3 : (𝟙 (projModel ((1 : WeierstrassCurve.VariableChange A) • W)) ≫
      (projModelVCIso (1 : WeierstrassCurve.VariableChange A) W).hom) =
      ((projModelVCIso (1 : WeierstrassCurve.VariableChange A) W).hom ≫
        eqToHom (show projModel W =
          projModel ((1 : WeierstrassCurve.VariableChange A) • W) by
            rw [one_smul])) ≫
        (projModelVCIso (1 : WeierstrassCurve.VariableChange A) W).hom := by
    rw [Category.id_comp]
    simpa only [Category.assoc] using hmul2
  have hmul4 := (cancel_mono
    (projModelVCIso (1 : WeierstrassCurve.VariableChange A) W).hom).mp hmul3
  -- hmul4 : 𝟙 = h ≫ e₃
  have := congrArg (fun m => m ≫ eqToHom (show
      projModel ((1 : WeierstrassCurve.VariableChange A) • W) = projModel W by
        rw [one_smul])) hmul4
  simpa only [Category.id_comp, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using this.symm

/-- The atlas curve coefficient `a₁` is the first universal coefficient. -/
theorem tateCurveLocOver_a₁ (R : CommRingCat.{u}) :
    (tateCurveLocOver R).a₁ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 0) := by
  simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map, tateCurve]
  simp

/-- The atlas curve coefficient `a₂` is the second universal coefficient. -/
theorem tateCurveLocOver_a₂ (R : CommRingCat.{u}) :
    (tateCurveLocOver R).a₂ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1) := by
  simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map, tateCurve]
  simp

/-- The universal Tate-normal curve over `R[A,B]` is Tate-normal. -/
theorem tateCurveOver_isTateNormal (R : CommRingCat.{u}) :
    (tateCurveOver R).IsTateNormal := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [tateCurveOver, tateCurve, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

/-- The atlas curve is Tate-normal. -/
theorem tateCurveLocOver_isTateNormal (R : CommRingCat.{u}) :
    (tateCurveLocOver R).IsTateNormal :=
  (tateCurveOver_isTateNormal R).map
    (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R))

variable (R : CommRingCat.{u}) [Algebra ↑R A] [Algebra (tateRingOver R) A]

/-- **Self-classification**: the classifying top map of the base-changed universal Tate
curve at a `(0,0)`-marked point is the base-change morphism. -/
theorem projTateMap_map_tate
    [((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).IsElliptic]
    (htower : (algebraMap (tateRingOver R) A).comp (algebraMap ↑R (tateRingOver R)) =
      algebraMap ↑R A)
    (g : SpecPoints (projModel ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)))
      (projModelπ ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) A)
    (hZ : InZChart ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) g)
    (hx : zChartEval _ g hZ
      (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) = 0)
    (hy : zChartEval _ g hZ
      (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))) = 0)
    (hord : NowhereOrderLEThree ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
      (zChartEval _ g hZ (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (zChartEval _ g hZ
        (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))) :
    projTateMap R ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) g hZ hord =
      projModelBaseChange (algebraMap (tateRingOver R) A) (tateCurveLocOver R) := by
  have htn : ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).IsTateNormal :=
    (tateCurveLocOver_isTateNormal R).map (algebraMap (tateRingOver R) A)
  -- the T-E1 normalisation at the (0,0)-marking is the identity variable change
  have hC1 : tateNormalVariableChange
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))
      (zChartEval _ g hZ (coordX ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (zChartEval _ g hZ (coordY ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A))))
      (zChartEval_equation_self _ g hZ) hord = 1 := by
    refine (tateNormalVariableChange_unique _ _ _
      (zChartEval_equation_self _ g hZ) hord 1 ⟨?_, ?_, ?_⟩).symm
    · rw [one_smul]
      exact htn
    · exact hx.symm
    · exact hy.symm
  -- the pointed atlas algebra map is the algebra map itself
  have hL : ((tateRingOverAlgLiftOfPoint R
      ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) _ _
      (zChartEval_equation_self _ g hZ) hord : tateRingOver R →ₐ[R] A) :
        tateRingOver R →+* A) = algebraMap (tateRingOver R) A := by
    have hAlg : ∀ r : ↑R, algebraMap (tateRingOver R) A
        (algebraMap ↑R (tateRingOver R) r) = algebraMap ↑R A r := fun r => by
      rw [← htower]; rfl
    have hext := tateRingOver_algHom_ext R
      (tateRingOverAlgLiftOfPoint R
        ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)) _ _
        (zChartEval_equation_self _ g hZ) hord)
      ({ toRingHom := algebraMap (tateRingOver R) A, commutes' := hAlg } :
        tateRingOver R →ₐ[R] A) ?_ ?_
    · exact congrArg (fun φ : tateRingOver R →ₐ[R] A => (φ : tateRingOver R →+* A)) hext
    · rw [tateRingOverAlgLiftOfPoint_X_zero, hC1, one_smul]
      show ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).a₁ =
        algebraMap (tateRingOver R) A
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 0))
      rw [WeierstrassCurve.map_a₁, tateCurveLocOver_a₁]
    · rw [tateRingOverAlgLiftOfPoint_X_one, hC1, one_smul]
      show ((tateCurveLocOver R).map (algebraMap (tateRingOver R) A)).a₂ =
        algebraMap (tateRingOver R) A
          (algebraMap (MvPolynomial (Fin 2) ↑R) (tateRingOver R) (MvPolynomial.X 1))
      rw [WeierstrassCurve.map_a₂, tateCurveLocOver_a₂]
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
  have hbcL := projModelBaseChange_ringHom_congr hL (tateCurveLocOver R)
  rw [hinv1, hinv2, hbcL]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

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

end MarkedChartData

end InducedChart

end ModularCurves
