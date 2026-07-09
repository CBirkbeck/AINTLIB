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

end ModularCurves
