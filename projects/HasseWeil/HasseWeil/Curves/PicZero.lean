import HasseWeil.Curves.ProjectiveDivisor
import HasseWeil.Curves.PointFunctor

/-!
# Pic⁰(E) ≅ E for elliptic curves: σ and κ maps

Following Silverman III.3.4, this file builds the σ "sum-of-points" map
on degree-zero projective divisors of an elliptic Weierstrass curve, plus
the inverse `κ : E → Pic⁰(E)`, `P ↦ class of (P) − (O)`, and the basic
API.

The full bijection `σ̄ : Pic⁰(E) ≅ E` is gated on `T-III-3-003` (worker-K)
which provides the "(P) ~ (Q) ⇒ P = Q" half. This file delivers
everything that does NOT depend on `T-III-3-003`. See
`.mathlib-quality/tickets/picard/` for the Pic⁰-route ticket roadmap.

## Main definitions

* `Curves.ProjectiveSmoothPoint.toAffinePoint` — bridge from a projective
  smooth point to mathlib's `Affine.Point` (`infinity ↦ 0`).
* `Curves.projectiveDivisorSum` — the σ map: `Σ nᵢ (Pᵢ) ↦ Σ nᵢ • Pᵢ`
  using the elliptic-curve group law.
* `Curves.projectiveDivisorSumHom` — the σ map bundled as an
  `AddMonoidHom`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.3.4
-/

namespace HasseWeil.Curves

variable {F : Type*} [Field F]

/-! ### Bridge: projective smooth point → `Affine.Point` -/

namespace ProjectiveSmoothPoint

variable {W : WeierstrassCurve.Affine F}

/-- A projective smooth point promotes to an `Affine.Point`: the point at
infinity becomes the basepoint `0`, an affine smooth point becomes
`Point.some` via `SmoothPlaneCurve.SmoothPoint.toAffinePoint`. -/
noncomputable def toAffinePoint
    (P : ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) :
    W.Point :=
  match P with
  | .infinity => 0
  | .affine Q => Q.toAffinePoint

@[simp] theorem toAffinePoint_infinity :
    (ProjectiveSmoothPoint.infinity :
      ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)).toAffinePoint =
      (0 : W.Point) := rfl

@[simp] theorem toAffinePoint_affine
    (Q : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (ProjectiveSmoothPoint.affine Q).toAffinePoint = Q.toAffinePoint := rfl

end ProjectiveSmoothPoint

/-! ### The sum-of-points map σ -/

variable [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The "sum-of-points" map `σ : ProjectiveDivisor → W.Point` sending
`Σ nᵢ (Pᵢ)` to `Σ nᵢ • Pᵢ` using the elliptic-curve group law. The
point at infinity contributes `0 : W.Point` (its `toAffinePoint`).

Restricted to `Div⁰` (and descended to `Pic⁰`), this is Silverman
III.3.4's σ map. Reference: Silverman III.3.4. -/
noncomputable def projectiveDivisorSum
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) : W.Point :=
  D.sum fun P n ↦ n • P.toAffinePoint

@[simp] theorem projectiveDivisorSum_zero :
    projectiveDivisorSum W 0 = 0 := by
  simp [projectiveDivisorSum]

@[simp] theorem projectiveDivisorSum_single
    (P : ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (n : ℤ) :
    projectiveDivisorSum W (Finsupp.single P n) = n • P.toAffinePoint := by
  unfold projectiveDivisorSum
  rw [Finsupp.sum_single_index]
  exact zero_zsmul _

@[simp] theorem projectiveDivisorSum_add
    (D₁ D₂ : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    projectiveDivisorSum W (D₁ + D₂) =
      projectiveDivisorSum W D₁ + projectiveDivisorSum W D₂ := by
  unfold projectiveDivisorSum
  rw [Finsupp.sum_add_index']
  · intro P; exact zero_zsmul _
  · intro P m n; exact add_zsmul P.toAffinePoint m n

/-- The σ map as a bundled additive group homomorphism
`ProjectiveDivisor → W.Point`. Use this to inherit `map_neg`, `map_sub`,
`map_zsmul` for free. -/
noncomputable def projectiveDivisorSumHom :
    ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) →+ W.Point where
  toFun := projectiveDivisorSum W
  map_zero' := projectiveDivisorSum_zero W
  map_add' := projectiveDivisorSum_add W

@[simp] theorem projectiveDivisorSumHom_apply
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    projectiveDivisorSumHom W D = projectiveDivisorSum W D := rfl

@[simp] theorem projectiveDivisorSum_neg
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    projectiveDivisorSum W (-D) = -(projectiveDivisorSum W D) :=
  (projectiveDivisorSumHom W).map_neg D

@[simp] theorem projectiveDivisorSum_sub
    (D₁ D₂ : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    projectiveDivisorSum W (D₁ - D₂) =
      projectiveDivisorSum W D₁ - projectiveDivisorSum W D₂ :=
  (projectiveDivisorSumHom W).map_sub D₁ D₂

theorem projectiveDivisorSum_zsmul
    (n : ℤ) (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    projectiveDivisorSum W (n • D) = n • projectiveDivisorSum W D :=
  (projectiveDivisorSumHom W).map_zsmul n D

end HasseWeil.Curves

/-! ### Bridge: `Affine.Point` → `ProjectiveSmoothPoint` (for the κ map) -/

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

/-- Send a mathlib `Affine.Point` to its `ProjectiveSmoothPoint` representative:
the basepoint `0 ↦ infinity`, an affine point `some x y h ↦ affine ⟨x, y, h⟩`.
This is the inverse-direction bridge to `ProjectiveSmoothPoint.toAffinePoint`. -/
noncomputable def toProjectiveSmoothPoint (P : W.Point) :
    HasseWeil.Curves.ProjectiveSmoothPoint
      (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F) :=
  match P with
  | .zero => .infinity
  | .some x y h => .affine ⟨x, y, h⟩

@[simp] theorem toProjectiveSmoothPoint_zero :
    (0 : W.Point).toProjectiveSmoothPoint =
      HasseWeil.Curves.ProjectiveSmoothPoint.infinity := rfl

@[simp] theorem toProjectiveSmoothPoint_some {x y : F} (h : W.Nonsingular x y) :
    (Point.some x y h).toProjectiveSmoothPoint =
      .affine ⟨x, y, h⟩ := rfl

/-- Round-trip: pushing an `Affine.Point` to a `ProjectiveSmoothPoint` and
back recovers the original. -/
@[simp] theorem toProjectiveSmoothPoint_toAffinePoint (P : W.Point) :
    P.toProjectiveSmoothPoint.toAffinePoint = P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

/-- Round-trip in the other direction: pushing a `ProjectiveSmoothPoint`
to an `Affine.Point` and back recovers the original. -/
@[simp] theorem toAffinePoint_toProjectiveSmoothPoint
    (P : HasseWeil.Curves.ProjectiveSmoothPoint
      (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F)) :
    P.toAffinePoint.toProjectiveSmoothPoint = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

/-- **T-FINTYPE-PROJECTIVE-SMOOTH-POINT bijection**: `Affine.Point ≃ ProjectiveSmoothPoint`.
Sends `0 ↦ infinity` and `some x y h ↦ affine ⟨x, y, h⟩`. -/
noncomputable def equivProjectiveSmoothPoint :
    W.Point ≃
      HasseWeil.Curves.ProjectiveSmoothPoint
        (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F) where
  toFun := toProjectiveSmoothPoint
  invFun := HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint
  left_inv := toProjectiveSmoothPoint_toAffinePoint
  right_inv := toAffinePoint_toProjectiveSmoothPoint

end WeierstrassCurve.Affine.Point

/-! ### Fintype instance and cardinality identity for `ProjectiveSmoothPoint`

`T-FINTYPE-PROJECTIVE-SMOOTH-POINT`: derive a `Fintype` instance for
`ProjectiveSmoothPoint W.toAffine` from the existing `Fintype W.toAffine.Point`
(elliptic-curve point count) via the bijection
`Affine.Point ≃ ProjectiveSmoothPoint` (above). The cardinality equals
`pointCount W.toAffine = Fintype.card W.toAffine.Point`. -/

namespace HasseWeil.Curves.ProjectiveSmoothPoint

variable {F : Type*} [Field F]

/-- **Fintype instance for `ProjectiveSmoothPoint`** derived from the
shipped bijection `Affine.Point ≃ ProjectiveSmoothPoint`. Requires a
`Fintype` instance on the affine point type (the elliptic-curve point
set). -/
noncomputable instance fintype {W : WeierstrassCurve.Affine F}
    [Fintype W.Point] :
    Fintype (ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) :=
  Fintype.ofEquiv W.Point (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint)

/-- **T-FINTYPE-PROJECTIVE-SMOOTH-POINT card identity**: the cardinality
of `ProjectiveSmoothPoint W` equals `pointCount W.toAffine = Fintype.card
W.toAffine.Point`. The `+ 1` convention for the `infinity` place is
absorbed because mathlib's `Affine.Point` already includes the basepoint
`0` (= infinity); the bijection above is one-to-one onto the projective
type. -/
theorem card_eq_card_affine_point {W : WeierstrassCurve.Affine F}
    [Fintype W.Point] :
    Fintype.card (ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) =
      Fintype.card W.Point := by
  exact (Fintype.card_congr
    (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint).symm)

end HasseWeil.Curves.ProjectiveSmoothPoint

/-! ### The canonical map κ : W.Point → Pic⁰ -/

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The divisor `(P) − (O)` as an element of `ProjectiveDivisor`. The κ
map factors as `picZeroOfPoint W P = QuotientAddGroup.mk ⟨kappaDivisor W P, _⟩`. -/
noncomputable def kappaDivisor
    (P : W.Point) : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) :=
  Finsupp.single P.toProjectiveSmoothPoint 1
    - Finsupp.single ProjectiveSmoothPoint.infinity 1

theorem kappaDivisor_degree (P : W.Point) :
    ProjectiveDivisor.degree (kappaDivisor W P) = 0 := by
  unfold kappaDivisor
  rw [ProjectiveDivisor.degree_sub]
  -- Both single-divisors have degree 1, so the difference is 0.
  show ProjectiveDivisor.degree
      (Finsupp.single P.toProjectiveSmoothPoint (1 : ℤ)) -
    ProjectiveDivisor.degree
      (Finsupp.single (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)) = 0
  unfold ProjectiveDivisor.degree
  rw [Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  ring

/-- The canonical map `κ : W.Point → Pic⁰(E)` of Silverman III.3.4(d):
sends `P ↦ class of (P) − (O)`. The basepoint `0 : W.Point` (≡ `O` of
the elliptic curve) maps to the zero class. -/
noncomputable def picZeroOfPoint (P : W.Point) :
    SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) :=
  QuotientAddGroup.mk ⟨kappaDivisor W P,
    ProjectiveDivisor.mem_degZero.mpr (kappaDivisor_degree W P)⟩

/-- `κ` sends the basepoint to the zero class: `(O) − (O) = 0`. -/
@[simp] theorem picZeroOfPoint_zero :
    picZeroOfPoint W (0 : W.Point) = 0 := by
  unfold picZeroOfPoint
  -- The underlying divisor is 0.
  have h_zero : kappaDivisor W (0 : W.Point) = 0 := by
    unfold kappaDivisor
    show Finsupp.single ProjectiveSmoothPoint.infinity (1 : ℤ) -
        Finsupp.single ProjectiveSmoothPoint.infinity (1 : ℤ) = 0
    exact sub_self _
  -- A QuotientAddGroup.mk of (0 : ↥degZero) is 0.
  have h_subtype :
      (⟨kappaDivisor W (0 : W.Point), ProjectiveDivisor.mem_degZero.mpr
        (kappaDivisor_degree W (0 : W.Point))⟩ :
        ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F)) = 0 :=
    Subtype.ext h_zero
  rw [h_subtype]
  exact QuotientAddGroup.mk_zero _

/-! ### `σ̄ ∘ κ = id` (the easy direction of the bijection) -/

/-- `σ` sends `(P) − (O)` to `P`: the σ map composed with κ is the identity
at the divisor level. This is one direction of Silverman III.3.4's
bijection; the reverse direction `κ ∘ σ̄ = id` is gated on T-III-3-003
(see `T-PIC-F-001`). -/
@[simp] theorem projectiveDivisorSum_kappaDivisor (P : W.Point) :
    projectiveDivisorSum W (kappaDivisor W P) = P := by
  unfold kappaDivisor
  rw [projectiveDivisorSum_sub, projectiveDivisorSum_single,
    projectiveDivisorSum_single, one_zsmul, one_zsmul]
  show P.toProjectiveSmoothPoint.toAffinePoint -
    (ProjectiveSmoothPoint.infinity :
      ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)).toAffinePoint = P
  rw [ProjectiveSmoothPoint.toAffinePoint_infinity, sub_zero]
  -- Now: P.toProjectiveSmoothPoint.toAffinePoint = P
  cases P with
  | zero => rfl
  | some x y h => rfl

/-! ### Building blocks toward T-PIC-A-002

The full theorem `projectiveDivisorSum (projectiveDivisorOf f) = 0` for
nonzero `f` (Silverman III.3.5) is open. The lemmas below capture the
**multiplicative structure** of `σ ∘ projectiveDivisorOf`: it is a group
homomorphism `K(E)* → W.Point`. Hence to prove vanishing for all `f` it
suffices to prove vanishing on a multiplicative generating set. -/

/-- The σ map vanishes on the trivial principal divisor (`f = 1`). -/
@[simp] theorem projectiveDivisorSum_projectiveDivisorOf_one :
    projectiveDivisorSum W
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf 1) = 0 := by
  rw [SmoothPlaneCurve.projectiveDivisorOf_one]
  exact projectiveDivisorSum_zero W

/-- σ ∘ projectiveDivisorOf is multiplicative-to-additive: vanishing on
two factors gives vanishing on their product. -/
theorem projectiveDivisorSum_projectiveDivisorOf_mul
    {f g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    projectiveDivisorSum W
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf (f * g)) =
    projectiveDivisorSum W
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) +
    projectiveDivisorSum W
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf g) := by
  rw [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hf hg,
    projectiveDivisorSum_add]

/-- σ ∘ projectiveDivisorOf vanishes on inverses iff it vanishes on the
original element. -/
theorem projectiveDivisorSum_projectiveDivisorOf_inv
    {f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField} (hf : f ≠ 0) :
    projectiveDivisorSum W
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f⁻¹) =
    -(projectiveDivisorSum W
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f)) := by
  rw [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_inv hf,
    projectiveDivisorSum_neg]

/-! #### `(P) + (−P) − 2·(O)` family

The divisor `(P) + (−P) − 2·(∞)` is principal on `E` (it is the divisor
of `x − x(P)`, the vertical line through `P`). Without identifying which
function it is the divisor of, we can directly verify that σ vanishes on
this family — `P + (−P) − 2·O = 0` in `W.Point` by the abelian-group
identity `P + (−P) = 0`.

This is the simplest non-trivial family of principal divisors with
verifiable σ-vanishing, and it provides a concrete "sanity check"
demonstration that σ does annihilate at least some non-trivial principal
divisors. Per Silverman III.3.4 + III.3.5, every divisor of a vertical
line `x − x_0` for an `F`-rational `x_0` lies in this family. -/

/-- σ vanishes on the divisor `(P) + (−P) − 2·(∞)` for any `P`. This is
a specific family of principal divisors (the divisors of `x − x(P)`-type
vertical lines), verifiable directly from the abelian-group identity
`P + (−P) = 0`. -/
theorem projectiveDivisorSum_vertical_line (P : W.Point) :
    projectiveDivisorSum W
      (Finsupp.single P.toProjectiveSmoothPoint 1
        + Finsupp.single (-P).toProjectiveSmoothPoint 1
        - (2 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1) = 0 := by
  simp only [projectiveDivisorSum_sub, projectiveDivisorSum_add,
    projectiveDivisorSum_single, projectiveDivisorSum_zsmul,
    one_zsmul, ProjectiveSmoothPoint.toAffinePoint_infinity, smul_zero,
    sub_zero, P.toProjectiveSmoothPoint_toAffinePoint,
    (-P).toProjectiveSmoothPoint_toAffinePoint]
  exact add_neg_cancel P

end HasseWeil.Curves

