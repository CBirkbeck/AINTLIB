import HasseWeil.Curves.Infinity
import HasseWeil.Curves.PicZero

/-!
# Pole-order parity at infinity

For a Weierstrass curve `E : y² = x³ + ...`, the basis `{1, y}` of the
coordinate ring over `F[x]` gives a parity decomposition of orders at
infinity:
- `ord_∞(p(x))` = `-2 · natDeg p` (even, for nonzero `p ∈ F[x]`).
- `ord_∞(q(x) · y)` = `-2 · natDeg q − 3` (odd ≤ -3, for nonzero `q ∈ F[x]`).
- `ord_∞(p(x) + q(x) · y)` = the more negative of the two.

The crucial consequence: **`ord_∞` of a nonzero coordinate-ring element
is never equal to `-1`**. This is the parity obstruction used in
Silverman III.3.3 (the "no nonconstant function with single pole at O"
fact, weakened to the special case `(P) − (O)` is principal ⇒ P = O).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.5 (algebraic
  Liouville-type results), III.3.3 (no degree-1 morphism to ℙ¹).
-/

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic]

/-- **Parity obstruction**: for any nonzero coordinate-ring element
`u ∈ F[E]`, the order at infinity of its image in `F(E)` is never
exactly `-1`. The decomposition `u = p · 1 + q · y` gives
`ord_∞ = -max(2·natDeg p, 2·natDeg q + 3)` (when both nonzero),
or one of `{0, -2, -4, ...}` (q = 0) or `{-3, -5, -7, ...}` (p = 0).
None of these can equal `-1`.

This is the load-bearing parity lemma for the unified A-002/F-001
package: ruling out `(P) − (O)` as a principal divisor for `P ≠ O`. -/
theorem coordRingImage_ordAtInfty_ne_neg_one
    (u : C.CoordinateRing) (hu : u ≠ 0) :
    C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField u) ≠
      ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨p, q, hpq⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  -- u = p • 1 + q • Y. Reduce to cases on (p, q).
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · -- Both zero ⟹ u = 0, contradiction.
      exfalso; apply hu
      rw [← hpq, hp, hq, zero_smul, zero_smul, zero_add]
    · -- p = 0, q ≠ 0: u = q • Y. ord = -2·natDeg q - 3 (odd ≥ 3).
      rw [← hpq, hp]
      -- Use algebraMap_smul_basis_eq to convert:
      -- algMap (0 • 1 + q • Y) = algMap 0 + algMap q · coordY = algMap q · coordY
      rw [C.algebraMap_smul_basis_eq 0 q]
      simp only [map_zero, zero_add]
      -- Goal: ord(algMap q · coordY) ≠ -1
      have hq_alg_ne :
          (algebraMap (Polynomial F) C.FunctionField q) ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap (Polynomial F) C.FunctionField)]
        exact fun h ↦ hq
          (FaithfulSMul.algebraMap_injective (Polynomial F) C.FunctionField h)
      rw [C.ordAtInfty_mul hq_alg_ne C.coordYInFunctionField_ne_zero,
        ordAtInfty_coordYInFunctionField,
        C.ordAtInfty_algebraMap_polynomial_of_ne_zero hq]
      -- LHS = ((-natDeg q) * 2 : ℤ) + ((-3 : ℤ)) : WithTop ℤ
      -- = ((-2·natDeg q - 3 : ℤ) : WithTop ℤ). Odd ≥ 3 in absolute value, never -1.
      intro h_eq
      have : ((-2 * (q.natDegree : ℤ) + (-3) : ℤ) : WithTop ℤ) =
          ((-1 : ℤ) : WithTop ℤ) := by
        rw [← h_eq]; push_cast; ring
      have h_int : (-2 * (q.natDegree : ℤ) + (-3) : ℤ) = -1 :=
        WithTop.coe_injective this
      omega
  · by_cases hq : q = 0
    · -- p ≠ 0, q = 0: u = p • 1. ord = -2·natDeg p (even).
      rw [← hpq, hq]
      rw [C.algebraMap_smul_basis_eq p 0]
      simp only [map_zero, zero_mul, add_zero]
      rw [C.ordAtInfty_algebraMap_polynomial_of_ne_zero hp]
      intro h_eq
      have h_int : (-2 * (p.natDegree : ℤ) : ℤ) = -1 :=
        WithTop.coe_injective h_eq
      omega
    · -- Both nonzero: use the basis lemma.
      rw [← hpq,
        C.ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero hp hq]
      intro h_eq
      have h_int : (-(max (2 * p.natDegree) (2 * q.natDegree + 3) : ℕ) : ℤ) =
          (-1 : ℤ) :=
        WithTop.coe_injective h_eq
      have h3 : 3 ≤ max (2 * p.natDegree) (2 * q.natDegree + 3) := by
        apply le_max_of_le_right; omega
      omega

/-- Function-field version: for any `f ∈ K(E)*` lying in the image of
the coordinate ring, `ord_∞(f) ≠ -1`. Directly from the parity lemma. -/
theorem funcField_image_ordAtInfty_ne_neg_one
    (f : C.FunctionField) (hf : f ≠ 0)
    (h_coord : ∃ u : C.CoordinateRing,
      algebraMap C.CoordinateRing C.FunctionField u = f) :
    C.ordAtInfty f ≠ ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨u, hu_eq⟩ := h_coord
  have hu_ne : u ≠ 0 := fun h ↦ hf (by rw [← hu_eq, h, map_zero])
  rw [← hu_eq]
  exact C.coordRingImage_ordAtInfty_ne_neg_one u hu_ne

end HasseWeil.Curves.SmoothPlaneCurve

/-! ### Special weak uniqueness: `(P) − (O) ∈ Prin ⟹ P = O`

This is Silverman III.3.3 specialized to `(Q) = (O)`: a function with
divisor `(P) − (O)` would be regular on the affine part (no finite
poles) hence in the coordinate-ring image, but its order at infinity
must be `−1` from the divisor while parity forbids that. The full
Silverman III.3.3 (`(P) ∼ (Q) ⟹ P = Q`) requires more (worker-K's
T-III-3-003), but this special case is sufficient for the unified
A-002/F-001 package per reviewer guidance (Q3).

The version below takes the "f lies in coordinate-ring image" as an
explicit hypothesis. The unconditional version requires the
no-finite-poles bridge `mem_coordinateRing_of_valuation_le_one` from
`Curves/IntegralClosure.lean` plus the project's `ord_P` ↔
`HeightOneSpectrum.valuation` bridge from `Curves/NormValuation.lean`.
That composition is its own ~80-150 LOC ticket. -/

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Specialized Silverman III.3.3** (the version we need for the
unified A-002/F-001 package, per reviewer Q3): if `(P) − (O)` is a
principal divisor witnessed by `f` AND `f` lies in the coordinate-ring
image, then `P = 0`.

The CR-image hypothesis is the only bridge to the unconditional version
(removing `h_coord` requires the no-finite-poles ⟹ CR-image bridge,
which is its own ticket). -/
theorem point_minus_O_principal_eq_zero_of_coord
    (P : W.Point) (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0)
    (h_div : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f =
      kappaDivisor W P)
    (h_coord : ∃ u : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing,
      algebraMap _ (⟨W⟩ : SmoothPlaneCurve F).FunctionField u = f) :
    P = 0 := by
  by_contra hP
  -- From h_div: (projectiveDivisorOf f) ∞ = (kappaDivisor W P) ∞ = -1.
  have h_inf : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f
      ProjectiveSmoothPoint.infinity = -1 := by
    rw [h_div]
    -- kappaDivisor W P at ∞ = (single P.toProj 1 - single ∞ 1) at ∞ = 0 - 1 = -1
    -- (since P.toProj ≠ ∞ for P ≠ 0)
    unfold kappaDivisor
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
    have h_ne : P.toProjectiveSmoothPoint ≠
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) := by
      intro h
      apply hP
      have := congr_arg ProjectiveSmoothPoint.toAffinePoint h
      rwa [P.toProjectiveSmoothPoint_toAffinePoint,
        ProjectiveSmoothPoint.toAffinePoint_infinity] at this
    rw [if_neg h_ne, if_pos rfl]
    decide
  -- Use projectiveDivisorOf_apply_infinity to convert: -1 = (ordAtInfty f).untopD 0
  rw [SmoothPlaneCurve.projectiveDivisorOf_apply_infinity] at h_inf
  -- Conclude ordAtInfty f = -1 (the only WithTop ℤ value with untopD 0 = -1).
  have h_ord_eq : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f =
      ((-1 : ℤ) : WithTop ℤ) := by
    cases h_top : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f with
    | top =>
      -- ordAtInfty f = ⊤ ⟹ f = 0, contradicts hf.
      exact absurd
        (((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_eq_top_iff f).mp h_top) hf
    | coe n =>
      rw [h_top, WithTop.untopD_coe] at h_inf
      rw [h_inf]
  -- Apply parity lemma: ordAtInfty f ≠ -1.
  exact (⟨W⟩ : SmoothPlaneCurve F).funcField_image_ordAtInfty_ne_neg_one
    f hf h_coord h_ord_eq

end HasseWeil.Curves
