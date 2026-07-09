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

end ModularCurves
