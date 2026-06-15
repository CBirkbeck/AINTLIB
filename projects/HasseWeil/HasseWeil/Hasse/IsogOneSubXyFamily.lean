/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback.SilvermanIV14

/-!
# Substantive `xy_family` for `isogOneSub_negFrobenius`

The Hasse-critical case of the Layer-2 fixed-field theorem
(`Hasse/PointFix.lean`). For the genuine isogeny `β = isogOneSub_negFrobenius W hq`
with pullback `addPullbackAlgHom_negFrobenius W hq`, this file ships the
substantive σ-commutation + curve-group-law chain that discharges the
witness-parametric `xy_family` hypothesis on `x_gen` and `y_gen`.

The geometric content is `(P + k) + (−π)(P + k) = P + (−π)(P)` whenever
`π(k) = k`, which holds for all `k ∈ E(F_q)` by `frobeniusIsog_apply`.
At the K(E)-lifted level this becomes invariance of `addPullback_x` and
`addPullback_y` for the negFrobenius isogeny under
`translateAlgEquivOfPoint W k.val`.

## Layered structure

1. **Witness-parametric reducer** (this file): converts the abstract
   `xy_family` hypothesis required by `pullback_fieldRange_eq_fixedField_*`
   (in `Hasse/PointFix.lean`) into the concrete identities
   `τ_k addPullback_x = addPullback_x` and `τ_k addPullback_y = addPullback_y`
   via the per-isogeny evaluation lemmas
   `addPullbackAlgHom_negFrobenius_x_gen_eq` /
   `addPullbackAlgHom_negFrobenius_y_gen_eq`.

2. **σ-commutation + curve-group-law chain** (this file, follow-up commits):
   discharges those concrete identities for each kernel element,
   distributing `translateAlgEquivOfPoint W k.val` over the
   `addX` / `addY` formulas via the AlgHom structure.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- **xy_family for `isogOneSub_negFrobenius` (witness-parametric)**: given
the addPullback-translation invariance for x and y, derive the
abstract `xy_family` hypothesis on `β.pullback x_gen` and
`β.pullback y_gen`.

This is the bridge between the abstract Layer-2 framework and the
concrete σ-commutation + curve-group-law content. Discharging the
hypothesis closes the substantive non-zero kernel xy-invariance arc. -/
theorem xy_family_isogOneSub_negFrobenius_of_addPullback_invariance (hq : 2 ≤ Fintype.card K)
    (h_inv : ∀ k : (isogOneSub_negFrobenius W hq).kernel,
      (translateAlgEquivOfPoint W k.val
          (addPullback_x W (negFrobeniusIsog W)) =
        addPullback_x W (negFrobeniusIsog W)) ∧
      (translateAlgEquivOfPoint W k.val
          (addPullback_y W (negFrobeniusIsog W)) =
        addPullback_y W (negFrobeniusIsog W))) :
    ∀ k : (isogOneSub_negFrobenius W hq).kernel,
      (translateAlgEquivOfPoint W k.val
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
        (isogOneSub_negFrobenius W hq).pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val
          ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) =
        (isogOneSub_negFrobenius W hq).pullback (y_gen W)) := by
  intro k
  rw [isogOneSub_negFrobenius_pullback,
      addPullbackAlgHom_negFrobenius_x_gen_eq,
      addPullbackAlgHom_negFrobenius_y_gen_eq]
  exact h_inv k

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- The base-change `W_KE W` is preserved under any K-AlgHom on `KE`. -/
theorem W_KE_map_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    (W_KE W).map f.toRingHom = W_KE W :=
  WeierstrassCurve.map_baseChange W (S := K) (A := W.toAffine.FunctionField)
    (B := W.toAffine.FunctionField) f

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- A K-AlgHom on `KE` distributes through `(W_KE).toAffine.addX`:
`f (addX x₁ x₂ ℓ) = addX (f x₁) (f x₂) (f ℓ)`. -/
theorem map_addX_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (x₁ x₂ ℓ : W.toAffine.FunctionField) :
    f ((W_KE W).toAffine.addX x₁ x₂ ℓ) =
      (W_KE W).toAffine.addX (f x₁) (f x₂) (f ℓ) := by
  conv_rhs => rw [← W_KE_map_K_algHom W f]
  exact (WeierstrassCurve.Affine.map_addX (W' := W_KE W)
    (f := f.toRingHom) (x₁ := x₁) (x₂ := x₂) (ℓ := ℓ)).symm

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- A K-AlgHom on `KE` distributes through `(W_KE).toAffine.negY`:
`f (negY x y) = negY (f x) (f y)`. -/
theorem map_negY_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (x y : W.toAffine.FunctionField) :
    f ((W_KE W).toAffine.negY x y) = (W_KE W).toAffine.negY (f x) (f y) := by
  conv_rhs => rw [← W_KE_map_K_algHom W f]
  exact (WeierstrassCurve.Affine.map_negY (W' := W_KE W)
    (f := f.toRingHom) (x := x) (y := y)).symm

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- A K-AlgHom on `KE` distributes through `(W_KE).toAffine.addY`:
`f (addY x₁ x₂ y₁ ℓ) = addY (f x₁) (f x₂) (f y₁) (f ℓ)`. -/
theorem map_addY_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (x₁ x₂ y₁ ℓ : W.toAffine.FunctionField) :
    f ((W_KE W).toAffine.addY x₁ x₂ y₁ ℓ) =
      (W_KE W).toAffine.addY (f x₁) (f x₂) (f y₁) (f ℓ) := by
  conv_rhs => rw [← W_KE_map_K_algHom W f]
  exact (WeierstrassCurve.Affine.map_addY (W' := W_KE W)
    (f := f.toRingHom) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (ℓ := ℓ)).symm

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- A K-AlgHom on `KE` distributes through `(W_KE).toAffine.slope`:
`f (slope x₁ x₂ y₁ y₂) = slope (f x₁) (f x₂) (f y₁) (f y₂)`. -/
theorem map_slope_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (x₁ x₂ y₁ y₂ : W.toAffine.FunctionField) :
    f ((W_KE W).toAffine.slope x₁ x₂ y₁ y₂) =
      (W_KE W).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) := by
  conv_rhs => rw [← W_KE_map_K_algHom W f]
  exact (WeierstrassCurve.Affine.map_slope (W := W_KE W) f.toRingHom x₁ x₂ y₁ y₂).symm

omit [Fintype K] in
/-- A K-AlgHom on `KE` distributes through `addSlope W α`:
`f (addSlope W α) = slope(f x_gen, f (α.pullback x_gen), f y_gen, f (α.pullback y_gen))`. -/
theorem map_addSlope_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (α : Isogeny W.toAffine W.toAffine) :
    f (addSlope W α) =
      (W_KE W).toAffine.slope (f (x_gen W)) (f (α.pullback (x_gen W)))
        (f (y_gen W)) (f (α.pullback (y_gen W))) := by
  unfold addSlope
  exact map_slope_K_algHom W f (x_gen W) (α.pullback (x_gen W))
    (y_gen W) (α.pullback (y_gen W))

omit [Fintype K] in
/-- A K-AlgHom on `KE` distributes through `addPullback_x W α`:
`f (addPullback_x W α) = addX(f x_gen, f (α.pullback x_gen), f (addSlope W α))`. -/
theorem map_addPullback_x_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (α : Isogeny W.toAffine W.toAffine) :
    f (addPullback_x W α) =
      (W_KE W).toAffine.addX (f (x_gen W)) (f (α.pullback (x_gen W)))
        (f (addSlope W α)) := by
  unfold addPullback_x
  exact map_addX_K_algHom W f (x_gen W) (α.pullback (x_gen W)) (addSlope W α)

omit [Fintype K] in
/-- A K-AlgHom on `KE` distributes through `addPullback_y W α`:
`f (addPullback_y W α) = addY(f x_gen, f (α.pullback x_gen), f y_gen, f (addSlope W α))`. -/
theorem map_addPullback_y_K_algHom (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (α : Isogeny W.toAffine W.toAffine) :
    f (addPullback_y W α) =
      (W_KE W).toAffine.addY (f (x_gen W)) (f (α.pullback (x_gen W)))
        (f (y_gen W)) (f (addSlope W α)) := by
  unfold addPullback_y
  exact map_addY_K_algHom W f (x_gen W) (α.pullback (x_gen W)) (y_gen W) (addSlope W α)

/-- **σ-commutation (x-coord)**: `f ((negFrobeniusIsog W).pullback x_gen) =
(f x_gen) ^ Fintype.card K`. -/
theorem map_negFrobeniusIsog_pullback_x_gen_K_algHom
    (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    f ((negFrobeniusIsog W).pullback (x_gen W)) =
      (f (x_gen W)) ^ Fintype.card K := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply, map_pow]

/-- **σ-commutation (y-coord)**: `f ((negFrobeniusIsog W).pullback y_gen)`
expands as `-(f y_gen)^q − a₁·(f x_gen)^q − a₃`. -/
theorem map_negFrobeniusIsog_pullback_y_gen_K_algHom
    (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    f ((negFrobeniusIsog W).pullback (y_gen W)) =
      -((f (y_gen W)) ^ Fintype.card K)
        - algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (f (x_gen W)) ^ Fintype.card K
        - algebraMap K W.toAffine.FunctionField W.toAffine.a₃ := by
  rw [negFrobeniusIsog_pullback_y_gen]
  simp only [map_sub, map_neg, map_mul, map_pow, frobeniusIsog_pullback_apply,
    AlgHom.commutes]

/-- **Assembled `f`-image of `addSlope W (negFrobeniusIsog W)`**: the slope
between `(f x_gen, f y_gen)` and `((f x_gen)^q, -(f y_gen)^q − a₁·(f x_gen)^q − a₃)`
on the W_KE curve. -/
theorem map_addSlope_negFrobeniusIsog_K_algHom
    (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    f (addSlope W (negFrobeniusIsog W)) =
      (W_KE W).toAffine.slope (f (x_gen W)) ((f (x_gen W)) ^ Fintype.card K)
        (f (y_gen W))
        (-((f (y_gen W)) ^ Fintype.card K)
          - algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (f (x_gen W)) ^ Fintype.card K
          - algebraMap K W.toAffine.FunctionField W.toAffine.a₃) := by
  rw [map_addSlope_K_algHom W f (negFrobeniusIsog W),
      map_negFrobeniusIsog_pullback_x_gen_K_algHom W f,
      map_negFrobeniusIsog_pullback_y_gen_K_algHom W f]

/-- **Assembled `f`-image of `addPullback_x W (negFrobeniusIsog W)`**: the
addX-formula on the translated coordinates, fully expanded. -/
theorem map_addPullback_x_negFrobeniusIsog_K_algHom
    (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    f (addPullback_x W (negFrobeniusIsog W)) =
      (W_KE W).toAffine.addX (f (x_gen W)) ((f (x_gen W)) ^ Fintype.card K)
        (f (addSlope W (negFrobeniusIsog W))) := by
  rw [map_addPullback_x_K_algHom W f (negFrobeniusIsog W),
      map_negFrobeniusIsog_pullback_x_gen_K_algHom W f]

/-- **Assembled `f`-image of `addPullback_y W (negFrobeniusIsog W)`**: the
addY-formula on the translated coordinates, fully expanded. -/
theorem map_addPullback_y_negFrobeniusIsog_K_algHom
    (f : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    f (addPullback_y W (negFrobeniusIsog W)) =
      (W_KE W).toAffine.addY (f (x_gen W)) ((f (x_gen W)) ^ Fintype.card K)
        (f (y_gen W)) (f (addSlope W (negFrobeniusIsog W))) := by
  rw [map_addPullback_y_K_algHom W f (negFrobeniusIsog W),
      map_negFrobeniusIsog_pullback_x_gen_K_algHom W f]

/-- **τ_k-image of `addPullback_x` at negFrob**: the τ-translated form of
the x-coord of `(P_gen + (-π) P_gen)`. The substantive `xy_family` claim
requires this to equal the original `addPullback_x` when `k ∈ ker β`. -/
theorem translateAlgEquivOfPoint_addPullback_x_negFrobeniusIsog (k : W.toAffine.Point) :
    translateAlgEquivOfPoint W k (addPullback_x W (negFrobeniusIsog W)) =
      (W_KE W).toAffine.addX
        (translateAlgEquivOfPoint W k (x_gen W))
        ((translateAlgEquivOfPoint W k (x_gen W)) ^ Fintype.card K)
        (translateAlgEquivOfPoint W k (addSlope W (negFrobeniusIsog W))) :=
  map_addPullback_x_negFrobeniusIsog_K_algHom W
    (translateAlgEquivOfPoint W k).toAlgHom

/-- **τ_k-image of `addPullback_y` at negFrob**: the τ-translated form of
the y-coord of `(P_gen + (-π) P_gen)`. Companion of the x-coord version. -/
theorem translateAlgEquivOfPoint_addPullback_y_negFrobeniusIsog (k : W.toAffine.Point) :
    translateAlgEquivOfPoint W k (addPullback_y W (negFrobeniusIsog W)) =
      (W_KE W).toAffine.addY
        (translateAlgEquivOfPoint W k (x_gen W))
        ((translateAlgEquivOfPoint W k (x_gen W)) ^ Fintype.card K)
        (translateAlgEquivOfPoint W k (y_gen W))
        (translateAlgEquivOfPoint W k (addSlope W (negFrobeniusIsog W))) :=
  map_addPullback_y_negFrobeniusIsog_K_algHom W
    (translateAlgEquivOfPoint W k).toAlgHom

/-- **τ_k-image of `addSlope W (negFrobeniusIsog W)`**: the τ-translated
form of the slope. Companion identifying the slope ingredient. -/
theorem translateAlgEquivOfPoint_addSlope_negFrobeniusIsog (k : W.toAffine.Point) :
    translateAlgEquivOfPoint W k (addSlope W (negFrobeniusIsog W)) =
      (W_KE W).toAffine.slope
        (translateAlgEquivOfPoint W k (x_gen W))
        ((translateAlgEquivOfPoint W k (x_gen W)) ^ Fintype.card K)
        (translateAlgEquivOfPoint W k (y_gen W))
        (-((translateAlgEquivOfPoint W k (y_gen W)) ^ Fintype.card K)
          - algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (translateAlgEquivOfPoint W k (x_gen W)) ^ Fintype.card K
          - algebraMap K W.toAffine.FunctionField W.toAffine.a₃) :=
  map_addSlope_negFrobeniusIsog_K_algHom W
    (translateAlgEquivOfPoint W k).toAlgHom

/-- **`xy_family` for `isogOneSub_negFrobenius` (witness-parametric on the
addX/addY identity)**: given the curve-level `addX/addY` identity for
the τ-translated coordinates equals the original, derive the abstract
`xy_family` hypothesis required by the Layer-2 framework.

The hypothesis `h_addX_inv` / `h_addY_inv` is exactly the algebraic
content of `(P_gen + lift k) - π(P_gen + lift k) = P_gen - π(P_gen)` at
the W_KE-curve level — the curve-group-law identity in `addX/addY` form
when `lift k` commutes with `π_KE` (which holds for K-rational k by
Frobenius-fixes-K plus base-change preservation). -/
theorem xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance (hq : 2 ≤ Fintype.card K)
    (h_addX_inv : ∀ k : (isogOneSub_negFrobenius W hq).kernel,
      (W_KE W).toAffine.addX
        (translateAlgEquivOfPoint W k.val (x_gen W))
        ((translateAlgEquivOfPoint W k.val (x_gen W)) ^ Fintype.card K)
        (translateAlgEquivOfPoint W k.val (addSlope W (negFrobeniusIsog W))) =
        addPullback_x W (negFrobeniusIsog W))
    (h_addY_inv : ∀ k : (isogOneSub_negFrobenius W hq).kernel,
      (W_KE W).toAffine.addY
        (translateAlgEquivOfPoint W k.val (x_gen W))
        ((translateAlgEquivOfPoint W k.val (x_gen W)) ^ Fintype.card K)
        (translateAlgEquivOfPoint W k.val (y_gen W))
        (translateAlgEquivOfPoint W k.val (addSlope W (negFrobeniusIsog W))) =
        addPullback_y W (negFrobeniusIsog W)) :
    ∀ k : (isogOneSub_negFrobenius W hq).kernel,
      (translateAlgEquivOfPoint W k.val
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
        (isogOneSub_negFrobenius W hq).pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val
          ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) =
        (isogOneSub_negFrobenius W hq).pullback (y_gen W)) := by
  apply xy_family_isogOneSub_negFrobenius_of_addPullback_invariance
  intro k
  refine ⟨?_, ?_⟩
  · rw [translateAlgEquivOfPoint_addPullback_x_negFrobeniusIsog]
    exact h_addX_inv k
  · rw [translateAlgEquivOfPoint_addPullback_y_negFrobeniusIsog]
    exact h_addY_inv k

omit [DecidableEq K] [W.toAffine.IsElliptic] in
/-- **Frobenius algebraMap composition**: the q-th power Frobenius
post-composed with `Algebra.ofId K KE` equals `Algebra.ofId K KE`. -/
theorem frobeniusAlgHom_comp_algebraMap :
    (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).comp
      (Algebra.ofId K W.toAffine.FunctionField) =
    Algebra.ofId K W.toAffine.FunctionField :=
  Subsingleton.elim _ _

omit [W.toAffine.IsElliptic] in
/-- **Frobenius fixes lifted K-rational points at `W_KE`**: applying the
`Affine.Point.map` of the Frobenius K-AlgHom to `liftPointToKE W k`
returns `liftPointToKE W k` unchanged. Curve-level form of "π fixes K-rationals"
at the `W_KE`-point level. -/
theorem frobenius_KE_lift_eq_lift (k : W.toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField)
      (liftPointToKE W k) = liftPointToKE W k := by
  unfold liftPointToKE
  change WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField)
        (WeierstrassCurve.Affine.Point.map (W' := W)
          (Algebra.ofId K W.toAffine.FunctionField) k) = _
  rw [WeierstrassCurve.Affine.Point.map_map, frobeniusAlgHom_comp_algebraMap]
  rfl

/-- **Frobenius on `W_KE` packaged as an AddMonoidHom**: `Affine.Point.map`
of the q-th power Frobenius K-AlgHom on KE, with explicit
`(W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point` typing for clean
arithmetic interaction. -/
noncomputable def frobeniusW_KE :
    (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField)

omit [W.toAffine.IsElliptic] in
/-- **`frobeniusW_KE` fixes lifted K-rational points**: the additive form
of `frobenius_KE_lift_eq_lift`. -/
@[simp] theorem frobeniusW_KE_lift (k : W.toAffine.Point) :
    frobeniusW_KE W (liftPointToKE W k) = liftPointToKE W k :=
  frobenius_KE_lift_eq_lift W k

omit [W.toAffine.IsElliptic] in
/-- **`frobeniusW_KE(P + lift k) = frobeniusW_KE(P) + lift k`**: combines
the AddMonoidHom structure of `frobeniusW_KE` with `frobeniusW_KE_lift`.
This is the curve-level "Frobenius commutes with translation by lift k". -/
theorem frobeniusW_KE_add_lift (P : (W_KE W).toAffine.Point) (k : W.toAffine.Point) :
    frobeniusW_KE W (P + liftPointToKE W k) =
      frobeniusW_KE W P + liftPointToKE W k := by
  rw [(frobeniusW_KE W).map_add, frobeniusW_KE_lift]

omit [W.toAffine.IsElliptic] in
/-- **`(P + lift k) - frobeniusW_KE(P + lift k) = P - frobeniusW_KE(P)`**:
the W_KE-curve identity for the `id − π` isogeny composed with translation
by `lift k`. -/
theorem id_sub_frobeniusW_KE_add_lift_eq (P : (W_KE W).toAffine.Point) (k : W.toAffine.Point) :
    (P + liftPointToKE W k) - frobeniusW_KE W (P + liftPointToKE W k) =
      P - frobeniusW_KE W P := by
  rw [frobeniusW_KE_add_lift]
  abel

omit [DecidableEq K] [W.toAffine.IsElliptic] in
/-- **`frobeniusW_KE` on `some`**: applies `frob` (q-th power) to both
coordinates. -/
theorem frobeniusW_KE_some (x y : W.toAffine.FunctionField)
    (h : (W_KE W).toAffine.Nonsingular x y) :
    frobeniusW_KE W (Affine.Point.some x y h) =
      Affine.Point.some
        ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) x)
        ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) y)
        ((WeierstrassCurve.Affine.baseChange_nonsingular _
          (RingHom.injective
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom) x y).mpr h) := by
  unfold frobeniusW_KE
  exact WeierstrassCurve.Affine.Point.map_some
    (f := FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) h

/-- **`negY (frob x_gen) (frob y_gen) = negFrob.pullback y_gen`**: the
W_KE-level identity matching the negation-of-Frobenius-image y-coord
with the explicit negFrob pullback. -/
theorem negY_frob_x_gen_frob_y_gen_eq_negFrob_pullback_y :
    (W_KE W).toAffine.negY
        (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W))
        (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (y_gen W)) =
      (negFrobeniusIsog W).pullback (y_gen W) := by
  rw [negFrobeniusIsog_pullback_y_gen, frobeniusIsog_pullback_apply,
      frobeniusIsog_pullback_apply, FiniteField.coe_frobeniusAlgHom]
  unfold WeierstrassCurve.Affine.negY
  rfl

/-- **`frob (x_gen W) = (negFrobeniusIsog W).pullback (x_gen W)`**: the
x-coord of `Frobenius_KE(genericPoint)` matches `negFrob.pullback x_gen`. -/
theorem frob_x_gen_eq_negFrob_pullback_x :
    FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W) =
      (negFrobeniusIsog W).pullback (x_gen W) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply,
      FiniteField.coe_frobeniusAlgHom]

omit [DecidableEq K] in
/-- **`x_gen ≠ frob x_gen` at W_KE level**: needed to apply `add_of_X_ne`
when computing `genericPoint - frobeniusW_KE(genericPoint)`. -/
theorem x_gen_ne_frob_x_gen :
    x_gen W ≠ FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W) := by
  classical
  intro h_eq
  apply x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W
  rw [frobeniusIsog_pullback_apply]
  rw [FiniteField.coe_frobeniusAlgHom] at h_eq
  exact sub_eq_zero.mpr h_eq

/-- **`addPullback_x` re-expressed via Frobenius coords**: identifies
`addPullback_x W (negFrobeniusIsog W)` with the curve-sum addX-formula
where the second-summand coords use the explicit `frob x_gen` and
`negY (frob x_gen) (frob y_gen)` form. -/
theorem addPullback_x_negFrobenius_eq_curve_addX :
    addPullback_x W (negFrobeniusIsog W) =
      (W_KE W).toAffine.addX (x_gen W)
        (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W))
        ((W_KE W).toAffine.slope (x_gen W)
          (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W))
          (y_gen W)
          ((W_KE W).toAffine.negY
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W))
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (y_gen W)))) := by
  unfold addPullback_x addSlope
  rw [← frob_x_gen_eq_negFrob_pullback_x W,
      ← negY_frob_x_gen_frob_y_gen_eq_negFrob_pullback_y W]

/-- **`addPullback_y` re-expressed via Frobenius coords**: companion to
`addPullback_x_negFrobenius_eq_curve_addX`. -/
theorem addPullback_y_negFrobenius_eq_curve_addY :
    addPullback_y W (negFrobeniusIsog W) =
      (W_KE W).toAffine.addY (x_gen W)
        (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W))
        (y_gen W)
        ((W_KE W).toAffine.slope (x_gen W)
          (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W))
          (y_gen W)
          ((W_KE W).toAffine.negY
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (x_gen W))
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField (y_gen W)))) := by
  unfold addPullback_y addSlope
  rw [← frob_x_gen_eq_negFrob_pullback_x W,
      ← negY_frob_x_gen_frob_y_gen_eq_negFrob_pullback_y W]

/-- **The W_KE-curve subtraction `generic - frob(generic)`** evaluates to a
`some(addPullback_x, addPullback_y, h_sum)` form. -/
theorem genericPoint_sub_frobeniusW_KE_apply :
    genericPoint W - frobeniusW_KE W (genericPoint W) =
      Affine.Point.some
        (addPullback_x W (negFrobeniusIsog W))
        (addPullback_y W (negFrobeniusIsog W))
        (addPullback_x_negFrobenius_eq_curve_addX W ▸
          addPullback_y_negFrobenius_eq_curve_addY W ▸
          (Affine.nonsingular_add
            (generic_nonsingular W)
            ((WeierstrassCurve.Affine.nonsingular_neg _ _).mpr
              ((WeierstrassCurve.Affine.baseChange_nonsingular _
                (RingHom.injective
                  (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom)
                (x_gen W) (y_gen W)).mpr
                (generic_nonsingular W)))
            (fun h ↦ x_gen_ne_frob_x_gen W h.1))) := by
  change genericPoint W + (-frobeniusW_KE W (genericPoint W)) = _
  unfold genericPoint
  rw [frobeniusW_KE_some]
  change Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W) +
      Affine.Point.some
        ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (x_gen W))
        ((W_KE W).toAffine.negY
          ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (x_gen W))
          ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (y_gen W)))
        ((WeierstrassCurve.Affine.nonsingular_neg _ _).mpr
          ((WeierstrassCurve.Affine.baseChange_nonsingular _
            (RingHom.injective
              (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom)
            (x_gen W) (y_gen W)).mpr
            (generic_nonsingular W))) = _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (x_gen_ne_frob_x_gen W)]
  congr 1
  · exact (addPullback_x_negFrobenius_eq_curve_addX W).symm
  · exact (addPullback_y_negFrobenius_eq_curve_addY W).symm

/-- **xy-family Lemma 2 (xCoord identity, both sides via curve identity)**:
for any `k : W.toAffine.Point`,
`(generic + lift k) - frobeniusW_KE(generic + lift k) =
  some(addPullback_x, addPullback_y, h)`. -/
theorem genericPoint_lift_sub_frobeniusW_KE_apply (k : W.toAffine.Point) :
    (genericPoint W + liftPointToKE W k) -
        frobeniusW_KE W (genericPoint W + liftPointToKE W k) =
      Affine.Point.some
        (addPullback_x W (negFrobeniusIsog W))
        (addPullback_y W (negFrobeniusIsog W))
        (addPullback_x_negFrobenius_eq_curve_addX W ▸
          addPullback_y_negFrobenius_eq_curve_addY W ▸
          (Affine.nonsingular_add
            (generic_nonsingular W)
            ((WeierstrassCurve.Affine.nonsingular_neg _ _).mpr
              ((WeierstrassCurve.Affine.baseChange_nonsingular _
                (RingHom.injective
                  (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom)
                (x_gen W) (y_gen W)).mpr
                (generic_nonsingular W)))
            (fun h ↦ x_gen_ne_frob_x_gen W h.1))) := by
  rw [id_sub_frobeniusW_KE_add_lift_eq W (genericPoint W) k]
  exact genericPoint_sub_frobeniusW_KE_apply W

omit [Fintype K] in
/-- **Uniform `τ_k`-identification on x_gen for `some` points**: for any
non-zero `k = some xk yk h_ns`, `translateAlgEquivOfPoint W (some xk yk h_ns) (x_gen W) =
translateX_xy W xk yk`. -/
theorem translateAlgEquivOfPoint_some_apply_x_gen (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) :
    translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (x_gen W) =
      translateX_xy W xk yk := by
  by_cases h_2_tor : yk = W.toAffine.negY xk yk
  · rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h_2_tor]
    exact translateAlgHom_of_2tor_apply_x_gen W xk yk h_ns h_2_tor
  · rw [translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h_2_tor]
    exact translateAlgHom_apply_x_gen W xk yk h_ns h_2_tor

omit [Fintype K] in
/-- **Uniform `τ_k`-identification on y_gen for `some` points**: for any
non-zero `k = some xk yk h_ns`, `translateAlgEquivOfPoint W (some xk yk h_ns) (y_gen W) =
translateY_xy W xk yk`. -/
theorem translateAlgEquivOfPoint_some_apply_y_gen (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) :
    translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (y_gen W) =
      translateY_xy W xk yk := by
  by_cases h_2_tor : yk = W.toAffine.negY xk yk
  · rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h_2_tor]
    exact translateAlgHom_of_2tor_apply_y_gen W xk yk h_ns h_2_tor
  · rw [translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h_2_tor]
    exact translateAlgHom_apply_y_gen W xk yk h_ns h_2_tor

omit [DecidableEq K] [W.toAffine.IsElliptic] in
/-- **Generalized curve-sum lemma**: for any W_KE-point `some x y h` with
`x ≠ frob x`, the curve sum `some(x, y, h) - frob_KE(some(x, y, h))` evaluates
as `some(addX(x, frob x, slope), addY(...), h_sum)` where the slope is
`(W_KE).slope(x, frob x, y, negY (frob x) (frob y))`. -/
theorem some_sub_frobeniusW_KE_some_apply
    (x y : W.toAffine.FunctionField) (h : (W_KE W).toAffine.Nonsingular x y)
    (h_x_ne : x ≠ FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x) :
    Affine.Point.some x y h - frobeniusW_KE W (Affine.Point.some x y h) =
      Affine.Point.some
        ((W_KE W).toAffine.addX x
          (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x)
          ((W_KE W).toAffine.slope x
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x) y
            ((W_KE W).toAffine.negY
              (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x)
              (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField y))))
        ((W_KE W).toAffine.addY x
          (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x) y
          ((W_KE W).toAffine.slope x
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x) y
            ((W_KE W).toAffine.negY
              (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x)
              (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField y))))
        (Affine.nonsingular_add h
          ((WeierstrassCurve.Affine.nonsingular_neg _ _).mpr
            ((WeierstrassCurve.Affine.baseChange_nonsingular _
              (RingHom.injective
                (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom) x y).mpr h))
          (fun hxy ↦ h_x_ne hxy.1)) := by
  change Affine.Point.some x y h + (-frobeniusW_KE W (Affine.Point.some x y h)) = _
  rw [frobeniusW_KE_some]
  change Affine.Point.some x y h +
      Affine.Point.some
        (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x)
        ((W_KE W).toAffine.negY
          (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField x)
          (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField y))
        ((WeierstrassCurve.Affine.nonsingular_neg _ _).mpr
          ((WeierstrassCurve.Affine.baseChange_nonsingular _
            (RingHom.injective
              (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom) x y).mpr h)) = _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne h_x_ne]

/-- **`τ_k x_gen ≠ frob (τ_k x_gen)`**: the τ_k-translated transcendence
condition. -/
theorem τ_k_x_gen_ne_frob_τ_k_x_gen (k : W.toAffine.Point) :
    translateAlgEquivOfPoint W k (x_gen W) ≠
      FiniteField.frobeniusAlgHom K W.toAffine.FunctionField
        (translateAlgEquivOfPoint W k (x_gen W)) := by
  intro h_eq
  apply x_gen_ne_frob_x_gen W
  apply (translateAlgEquivOfPoint W k).injective
  simpa only [FiniteField.coe_frobeniusAlgHom, map_pow] using h_eq

omit [Fintype K] in
/-- **Uniform identification of `generic + lift k`**: for any K-rational point
k, `genericPoint W + liftPointToKE W k` evaluates to a `some` form with
coordinates `(τ_k x_gen, τ_k y_gen)`. -/
theorem genericPoint_add_lift_eq_some (k : W.toAffine.Point) :
    ∃ h : (W_KE W).toAffine.Nonsingular
        (translateAlgEquivOfPoint W k (x_gen W))
        (translateAlgEquivOfPoint W k (y_gen W)),
      genericPoint W + liftPointToKE W k =
        Affine.Point.some
          (translateAlgEquivOfPoint W k (x_gen W))
          (translateAlgEquivOfPoint W k (y_gen W)) h := by
  rcases k with _ | ⟨xk, yk, h_ns⟩
  · refine ⟨?_, ?_⟩
    · change (W_KE W).toAffine.Nonsingular (x_gen W) (y_gen W)
      exact generic_nonsingular W
    · change genericPoint W + (0 : (W_KE W).toAffine.Point) = _
      rw [add_zero]
      rfl
  · refine ⟨?_, ?_⟩
    · rw [translateAlgEquivOfPoint_some_apply_x_gen W xk yk h_ns,
          translateAlgEquivOfPoint_some_apply_y_gen W xk yk h_ns]
      exact (Affine.nonsingular_add (generic_nonsingular W)
        ((WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine)
          (RingHom.injective (algebraMap K W.toAffine.FunctionField)) xk yk).mpr h_ns)
        (fun hxy ↦ x_gen_sub_const_ne_zero W xk
          (sub_eq_zero.mpr hxy.left)))
    · change genericPoint W + liftPointToKE W (Affine.Point.some xk yk h_ns) = _
      rw [liftPointToKE_some W xk yk h_ns, genericPoint_add_liftSomePoint W xk yk h_ns]
      congr 1
      · exact (translateAlgEquivOfPoint_some_apply_x_gen W xk yk h_ns).symm
      · exact (translateAlgEquivOfPoint_some_apply_y_gen W xk yk h_ns).symm

/-- **xy-family addX identity**: for any K-rational k,
`(W_KE).addX(τ_k x_gen, (τ_k x_gen)^q, τ_k addSlope) = addPullback_x W negFrob`. -/
theorem xy_family_addX_unconditional (hq : 2 ≤ Fintype.card K)
    (k : (isogOneSub_negFrobenius W hq).kernel) :
    (W_KE W).toAffine.addX
        (translateAlgEquivOfPoint W k.val (x_gen W))
        ((translateAlgEquivOfPoint W k.val (x_gen W)) ^ Fintype.card K)
        (translateAlgEquivOfPoint W k.val (addSlope W (negFrobeniusIsog W))) =
      addPullback_x W (negFrobeniusIsog W) := by
  rw [translateAlgEquivOfPoint_addSlope_negFrobeniusIsog W k.val]
  obtain ⟨h_T, h_gen_lift_eq⟩ := genericPoint_add_lift_eq_some W k.val
  have h_curve_some := some_sub_frobeniusW_KE_some_apply W
    (translateAlgEquivOfPoint W k.val (x_gen W))
    (translateAlgEquivOfPoint W k.val (y_gen W))
    h_T (τ_k_x_gen_ne_frob_τ_k_x_gen W k.val)
  rw [← h_gen_lift_eq] at h_curve_some
  rw [genericPoint_lift_sub_frobeniusW_KE_apply W k.val] at h_curve_some
  exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp h_curve_some).1.symm

/-- **xy-family addY identity**: companion to the addX identity. -/
theorem xy_family_addY_unconditional (hq : 2 ≤ Fintype.card K)
    (k : (isogOneSub_negFrobenius W hq).kernel) :
    (W_KE W).toAffine.addY
        (translateAlgEquivOfPoint W k.val (x_gen W))
        ((translateAlgEquivOfPoint W k.val (x_gen W)) ^ Fintype.card K)
        (translateAlgEquivOfPoint W k.val (y_gen W))
        (translateAlgEquivOfPoint W k.val (addSlope W (negFrobeniusIsog W))) =
      addPullback_y W (negFrobeniusIsog W) := by
  rw [translateAlgEquivOfPoint_addSlope_negFrobeniusIsog W k.val]
  obtain ⟨h_T, h_gen_lift_eq⟩ := genericPoint_add_lift_eq_some W k.val
  have h_curve_some := some_sub_frobeniusW_KE_some_apply W
    (translateAlgEquivOfPoint W k.val (x_gen W))
    (translateAlgEquivOfPoint W k.val (y_gen W))
    h_T (τ_k_x_gen_ne_frob_τ_k_x_gen W k.val)
  rw [← h_gen_lift_eq] at h_curve_some
  rw [genericPoint_lift_sub_frobeniusW_KE_apply W k.val] at h_curve_some
  exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp h_curve_some).2.symm

/-- **xy-family Lemma 2 UNCONDITIONAL**: the abstract τ_k-invariance of
`(isogOneSub_negFrobenius W hq).pullback (x_gen W)` and `... (y_gen W)`,
discharged via the curve-level addX/addY identities. -/
theorem xy_family_isogOneSub_negFrobenius (hq : 2 ≤ Fintype.card K) :
    ∀ k : (isogOneSub_negFrobenius W hq).kernel,
      (translateAlgEquivOfPoint W k.val
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
        (isogOneSub_negFrobenius W hq).pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val
          ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) =
        (isogOneSub_negFrobenius W hq).pullback (y_gen W)) :=
  xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance W hq
    (xy_family_addX_unconditional W hq) (xy_family_addY_unconditional W hq)

end HasseWeil
