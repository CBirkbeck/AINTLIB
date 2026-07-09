import ModularCurves.ModularCurve.YOneAssembly
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

/-- Specialising the universal Tate curve by `tateRingOverLift` recovers the Tate-normal curve
with coefficients `(α, β)`. -/
theorem tateCurveLocOver_map_tateRingOverLift (α β : A)
    (hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
      (fun i : Fin 2 => if i = 0 then α else β))).Δ)) :
    (tateCurveLocOver R).map (tateRingOverLift R α β hΔ) =
      (tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap R A)
        (fun i : Fin 2 => if i = 0 then α else β)) := by
  simp [tateCurveLocOver, tateRingOverLift, WeierstrassCurve.map_map]

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

/-- The local atlas map classifies the T-E1 normal form of the pointed chart. -/
theorem tateCurveLocOver_map_tateRingOverLiftOfPoint (W : WeierstrassCurve A) [W.IsElliptic]
    (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    (tateCurveLocOver R).map (tateRingOverLiftOfPoint R W x y hxy hord) =
      (tateNormalVariableChange W x y hxy hord) • W :=
  tateCurveLocOver_map_tateRingOverLiftOfTateNormal R
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

end ModularCurves
