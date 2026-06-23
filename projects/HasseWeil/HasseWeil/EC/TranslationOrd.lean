/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.Translation
import HasseWeil.Curves.AlgebraicNonNegOrd
import HasseWeil.EC.GenericPoint
import HasseWeil.Curves.SmoothPointTranslate
import HasseWeil.OrdAtInftyBridge

/-!
# Order of `x_gen − xk` at the smooth point `(xk, −y_T)`

For an elliptic curve `W/F` and a base-field point `T = (xk, yk) ∈ E(F)`,
the x-coordinate function `x_gen − xk ∈ K(E)` vanishes at *both* `T` and
`−T = (xk, negY xk yk)`. We package this here as the foundational
ord-positivity lemma needed for the translation transcendence chain:

```
ord_P (x_gen − xk) ≥ 1   at  P = −T.
```

This is one half of Step 1 of the reviewer's redirect: combined with
`ord_P (y_gen − yk) = 0` at `−T` (for non-2-torsion `T`), it gives
`ord_P (translateSlope_xy) < 0`, hence `ord_P (translateX_xy) < 0`,
which by `transcendental_of_neg_ord_P` yields transcendence of
`translateX_xy` over `F`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.1, II.2.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-! ### The smooth point `−T` -/

/-- The smooth point `−T = (xk, negY xk yk)` of `W_smooth W` arising from a
base-field point `T = (xk, yk) ∈ E(F)`. -/
noncomputable def negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_smooth W).SmoothPoint where
  x := xk
  y := W.toAffine.negY xk yk
  nonsingular := (Affine.nonsingular_neg xk yk).mpr h_ns

@[simp] theorem negSmoothPoint_x (xk yk : F)
    (h_ns : W.toAffine.Nonsingular xk yk) :
    (negSmoothPoint W xk yk h_ns).x = xk := rfl

@[simp] theorem negSmoothPoint_y (xk yk : F)
    (h_ns : W.toAffine.Nonsingular xk yk) :
    (negSmoothPoint W xk yk h_ns).y = W.toAffine.negY xk yk := rfl

/-! ### `x_gen − xk` as image of `XClass` -/

/-- The function `x_gen W − algebraMap F KE xk` is the image under
`algebraMap CoordinateRing FunctionField` of `XClass W.toAffine xk`,
the class of `X − xk` in the coordinate ring. -/
theorem x_gen_sub_const_eq_algebraMap_XClass (xk : F) :
    x_gen W - algebraMap F KE xk =
      algebraMap W.toAffine.CoordinateRing KE
        (Affine.CoordinateRing.XClass W.toAffine xk) := by
  unfold x_gen
  rw [show (algebraMap F KE xk : KE) =
    algebraMap W.toAffine.CoordinateRing KE
      (algebraMap F W.toAffine.CoordinateRing xk)
    from IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing KE xk]
  rw [← _root_.map_sub]
  congr 1
  rw [show (algebraMap F W.toAffine.CoordinateRing xk
      : W.toAffine.CoordinateRing) =
    algebraMap (Polynomial F) W.toAffine.CoordinateRing (Polynomial.C xk)
    from IsScalarTower.algebraMap_apply F (Polynomial F)
      W.toAffine.CoordinateRing xk]
  rw [← _root_.map_sub]
  rfl

/-! ### `XClass W xk` is in the maximal ideal at any point with `x = xk` -/

/-- For any smooth point `P` of `W_smooth W` whose x-coordinate is `xk`,
the class of `X − xk` lies in the maximal ideal at `P`. Direct from the
definition of `maximalIdealAt = XYIdeal` as a span containing `XClass`. -/
theorem XClass_mem_maximalIdealAt
    (P : (W_smooth W).SmoothPoint) (xk : F) (h_x : P.x = xk) :
    Affine.CoordinateRing.XClass W.toAffine xk ∈
      (W_smooth W).maximalIdealAt P := by
  rw [← h_x]
  change Affine.CoordinateRing.XClass W.toAffine P.x ∈
    Affine.CoordinateRing.XYIdeal W.toAffine P.x (Polynomial.C P.y)
  unfold Affine.CoordinateRing.XYIdeal
  exact Ideal.subset_span (Set.mem_insert _ _)

/-! ### Order at `−T` of `x_gen − xk` is positive -/

/-- **Foundational ord-positivity at `−T`**: at the smooth point
`−T = (xk, negY xk yk)`, the function `x_gen − xk` has order at least 1.

Proof: `x_gen − xk` corresponds to `XClass W xk ∈ CoordinateRing`, an
element of the maximal ideal at `−T`. Hence `ord_P ≠ 0` (membership
bridge). Combined with `pointValuation ≤ 1` (so `ord_P ≥ 0`) and
`algebraMap (XClass) ≠ 0` (so `ord_P ≠ ⊤`), we conclude `ord_P ≥ 1`. -/
theorem one_le_ord_P_x_gen_sub_const
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap F KE xk) := by
  set P := negSmoothPoint W xk yk h_ns
  set u := Affine.CoordinateRing.XClass W.toAffine xk
  rw [x_gen_sub_const_eq_algebraMap_XClass W xk]
  have hu_ne : u ≠ 0 :=
    Affine.CoordinateRing.XClass_ne_zero (W' := W.toAffine) xk
  have hu_mem : u ∈ (W_smooth W).maximalIdealAt P :=
    XClass_mem_maximalIdealAt W P xk rfl
  have h_ord_ne_zero : (W_smooth W).ord_P P
      (algebraMap W.toAffine.CoordinateRing KE u) ≠ 0 :=
    ((W_smooth W).ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt hu_ne P).mpr hu_mem
  have h_au_ne : algebraMap W.toAffine.CoordinateRing KE u ≠ 0 :=
    (map_ne_zero_iff _
      (IsFractionRing.injective W.toAffine.CoordinateRing KE)).mpr hu_ne
  have h_ord_nonneg : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (algebraMap W.toAffine.CoordinateRing KE u) := by
    have hv : (W_smooth W).pointValuation P
        (algebraMap W.toAffine.CoordinateRing KE u) ≠ 0 :=
      ((W_smooth W).pointValuation P).ne_zero_iff.mpr h_au_ne
    unfold SmoothPlaneCurve.ord_P
    rw [dif_neg hv]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
        WithTop.coe_le_coe]
    have h_unz_le : WithZero.unzero hv ≤ 1 := by
      rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]
      exact (W_smooth W).pointValuation_algebraMap_le_one u P
    have h_toAdd : (WithZero.unzero hv).toAdd ≤ 0 := by
      have h2 : Multiplicative.toAdd (WithZero.unzero hv) ≤
          Multiplicative.toAdd (1 : Multiplicative ℤ) := h_unz_le
      rwa [show ((1 : Multiplicative ℤ)).toAdd = (0 : ℤ) from rfl] at h2
    omega
  have h_ne_top : (W_smooth W).ord_P P
      (algebraMap W.toAffine.CoordinateRing KE u) ≠ ⊤ :=
    (SmoothPlaneCurve.ord_P_eq_top_iff _).not.mpr h_au_ne
  cases h : (W_smooth W).ord_P P
      (algebraMap W.toAffine.CoordinateRing KE u) with
  | top => exact absurd h h_ne_top
  | coe n =>
      rw [h] at h_ord_nonneg h_ord_ne_zero
      have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast h_ord_nonneg
      have hn_ne : n ≠ 0 := by
        intro hn
        apply h_ord_ne_zero
        rw [hn]; rfl
      exact_mod_cast (show (1 : ℤ) ≤ n by omega)

/-! ### `ord_P (x_gen − xk) ≤ 1` at `−T` for non-2-torsion `T`

The substantive upper bound complementing `one_le_ord_P_x_gen_sub_const`.
At a smooth point `P = (xk, negY xk yk)` with non-2-torsion structure
(`yk ≠ negY xk yk`), the maximal ideal of the local ring is generated
by `algMap XClass`, making `algMap XClass` a uniformizer in the DVR
sense. Hence `ord_P (algMap XClass) = 1`, equivalently
`ord_P (x_gen - xk) = 1`.

The proof leverages Mathlib's `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton`:
when the prime ideal equals `span{r}` for a generator `r`, `intValuation
r = exp(-1)`. -/

/-- **`ord_P P f ≤ 1` from `pointValuation P f = exp(-1)`**: generic
valuation-to-order computation on any smooth plane curve. Since
`ord_P P f = -(unzero hv).toAdd` for nonzero valuation, a valuation of
`exp(-1) = ofAdd(-1)` gives `ord_P P f = 1`. (Forward companion of
`pointValuation_eq_exp_neg_of_ord_P_eq`.) -/
private theorem ord_P_le_one_of_pointValuation_eq_exp_neg_one
    {C : SmoothPlaneCurve F} {P : C.SmoothPoint} {f : C.FunctionField}
    (hf : C.pointValuation P f = WithZero.exp (-1 : ℤ)) :
    C.ord_P P f ≤ ((1 : ℤ) : WithTop ℤ) := by
  have h_val_ne : C.pointValuation P f ≠ 0 := by
    rw [hf]; exact WithZero.exp_ne_zero
  unfold SmoothPlaneCurve.ord_P
  rw [dif_neg h_val_ne]
  have h_unz : WithZero.unzero h_val_ne = Multiplicative.ofAdd (-1 : ℤ) := by
    rwa [← WithZero.coe_inj, WithZero.coe_unzero]
  rw [h_unz]
  rfl

/-- **`algMap XClass ≠ 0` in the local ring at `P`**: the image of the
nonzero coordinate-ring element `XClass W xk` under the localisation map
`CoordinateRing → localRingAt P` is nonzero, since the localisation is
injective (the prime complement avoids zero divisors). -/
private theorem algMap_XClass_localRingAt_ne_zero
    (xk : F) (P : (W_smooth W).SmoothPoint) :
    algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt P)
        (Affine.CoordinateRing.XClass W.toAffine xk) ≠ 0 := by
  have h_xc_ne : Affine.CoordinateRing.XClass W.toAffine xk ≠ 0 :=
    Affine.CoordinateRing.XClass_ne_zero (W' := W.toAffine) (x := xk)
  rw [show algebraMap (W_smooth W).CoordinateRing
      ((W_smooth W).localRingAt P) = (algebraMap _ _) from rfl]
  exact (map_ne_zero_iff _
    (IsLocalization.injective (M := ((W_smooth W).maximalIdealAt P).primeCompl)
      ((W_smooth W).localRingAt P)
      ((W_smooth W).maximalIdealAt P).primeCompl_le_nonZeroDivisors)).mpr h_xc_ne

/-- **`pointValuation P (algMap XClass) = exp(-1)` from the maxIdeal-span
hypothesis**: when the maximal ideal of the local ring at `P` equals
`span{algMap XClass}`, the generator has integer valuation `exp(-1)`
(`intValuation_singleton`), which lifts to the function field via
`valuation_of_algebraMap`. -/
private theorem pointValuation_algMap_XClass_eq_exp_neg_one_of_maxIdeal_span
    (xk : F) (P : (W_smooth W).SmoothPoint)
    (h_max_eq : IsLocalRing.maximalIdeal ((W_smooth W).localRingAt P) =
      Ideal.span ({algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt P)
        (Affine.CoordinateRing.XClass W.toAffine xk)} : Set _)) :
    (W_smooth W).pointValuation P
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
          (Affine.CoordinateRing.XClass W.toAffine xk)) =
      WithZero.exp (-1 : ℤ) := by
  set v := IsDiscreteValuationRing.maximalIdeal ((W_smooth W).localRingAt P)
    with hv_def
  have h_int_val : v.intValuation
      (algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt P)
        (Affine.CoordinateRing.XClass W.toAffine xk)) =
      WithZero.exp (-1 : ℤ) :=
    v.intValuation_singleton (algMap_XClass_localRingAt_ne_zero W xk P) h_max_eq
  change v.valuation _ _ = _
  rw [IsScalarTower.algebraMap_apply (W_smooth W).CoordinateRing
    ((W_smooth W).localRingAt P) (W_smooth W).FunctionField]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact h_int_val

/-- **`ord_P (x_gen − xk) ≤ 1` at `−T`, witness-parametric on the
maxIdeal-span hypothesis**: given that the maximal ideal of the local
ring at `−T = (xk, negY xk yk)` equals `span{algMap XClass}`, we have
`ord_P (x_gen − xk) ≤ 1`. The hypothesis is dischargeable for non-
2-torsion case from `localRing_isDVR`'s second case. -/
theorem ord_P_x_gen_sub_const_le_one_of_maxIdeal_span
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_max_eq : IsLocalRing.maximalIdeal
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns)) =
      Ideal.span ({algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns))
        (Affine.CoordinateRing.XClass W.toAffine xk)} : Set _)) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap F KE xk) ≤ ((1 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns
  rw [x_gen_sub_const_eq_algebraMap_XClass W xk]
  exact ord_P_le_one_of_pointValuation_eq_exp_neg_one
    (pointValuation_algMap_XClass_eq_exp_neg_one_of_maxIdeal_span W xk P h_max_eq)

/-- **`ord_P (x_gen − xk) = 1` at `−T`, witness-parametric on the
maxIdeal-span hypothesis**: combines the `≥ 1` form
(`one_le_ord_P_x_gen_sub_const`) with the `≤ 1` form
(`ord_P_x_gen_sub_const_le_one_of_maxIdeal_span`). -/
theorem ord_P_x_gen_sub_const_eq_one_of_maxIdeal_span
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_max_eq : IsLocalRing.maximalIdeal
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns)) =
      Ideal.span ({algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns))
        (Affine.CoordinateRing.XClass W.toAffine xk)} : Set _)) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap F KE xk) = ((1 : ℤ) : WithTop ℤ) :=
  le_antisymm
    (ord_P_x_gen_sub_const_le_one_of_maxIdeal_span W xk yk h_ns h_max_eq)
    (one_le_ord_P_x_gen_sub_const W xk yk h_ns)

/-! ### Discharging the maxIdeal-span hypothesis for non-2-torsion case

For non-2-torsion `T = (xk, yk)` (i.e., `yk ≠ negY xk yk`), the maximal
ideal of localRingAt(negSmoothPoint W xk yk h_ns) is generated by
`algMap (XClass)`. This follows from the same algebraic structure used
in `localRing_isDVR`'s second case (where `polynomialY ≠ 0` at the
smooth point).

The non-2-torsion condition is equivalent to `polynomialY.evalEval xk
(negY xk yk) ≠ 0`: since `polynomialY = 2Y + a₁X + a₃` evaluates to
`-(2yk + a₁xk + a₃)` at `(xk, negY xk yk)`, and the 2-torsion condition
(`yk = negY xk yk`) is equivalent to `2yk + a₁xk + a₃ = 0`. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`polynomialY` non-vanishes at `negSmoothPoint` for non-2-torsion**:
at the smooth point `(xk, negY xk yk)` arising from non-2-torsion
`(xk, yk)`, `polynomialY.evalEval` is nonzero. -/
theorem polynomialY_evalEval_ne_zero_at_negSmoothPoint
    (xk yk : F) (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    W.toAffine.polynomialY.evalEval xk (W.toAffine.negY xk yk) ≠ 0 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  have hneg : W.toAffine.negY xk yk = -yk - W.a₁ * xk - W.a₃ := rfl
  rw [hneg]
  intro h_eq
  apply h_not_2_tor
  rw [hneg]
  linear_combination -h_eq

/-! ### Unconditional maxIdeal-span discharge for non-2-torsion case

Reproduces the relevant content from `localRing_isDVR`'s second case
(where `polynomialY ≠ 0`), exposed publicly. The proof reproduces
`hmap_eq` from the second case using the public helpers
`yclass_mul_quot_in_xclass_span` and `mk_quot_not_mem` from
`HasseWeil/Valuation.lean`.

**Wall-break techniques applied** (per PROTOCOL.md):
- `set` abstraction on Polynomial.Bivariate subterms BEFORE rw.
- `open scoped Polynomial.Bivariate` for notation.
- Direct mul-of-unit-implies-mem reasoning (avoiding the private
  `mem_of_mul_unit` helper). -/

open scoped Polynomial.Bivariate in
/-- **Unconditional**: at the smooth point `(xk, negY xk yk)` arising from
non-2-torsion `(xk, yk)`, the maximal ideal of the local ring is
generated by `algMap (XClass)`. -/
theorem maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    IsLocalRing.maximalIdeal
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns)) =
      Ideal.span ({algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns))
        (Affine.CoordinateRing.XClass W.toAffine xk)} : Set _) := by
  set P_smooth := negSmoothPoint W xk yk h_ns
  set P_ideal : Ideal (W_smooth W).CoordinateRing :=
    (W_smooth W).maximalIdealAt P_smooth with hPIdef
  have h_eq_at : W.toAffine.Equation xk (W.toAffine.negY xk yk) :=
    ((Affine.nonsingular_neg xk yk).mpr h_ns).1
  have hY : W.toAffine.polynomialY.evalEval xk (W.toAffine.negY xk yk) ≠ 0 :=
    polynomialY_evalEval_ne_zero_at_negSmoothPoint W xk yk h_not_2_tor
  set yk' : F := W.toAffine.negY xk yk with hyk'
  set Q : (W_smooth W).CoordinateRing :=
    Affine.CoordinateRing.mk W.toAffine
      (W.toAffine.polynomial /ₘ (Y - Polynomial.C (Polynomial.C yk')))
    with hQ
  set XC : (W_smooth W).CoordinateRing :=
    Affine.CoordinateRing.XClass W.toAffine xk with hXC
  set YC : (W_smooth W).CoordinateRing :=
    Affine.CoordinateRing.YClass W.toAffine (Polynomial.C yk') with hYC
  set f := algebraMap (W_smooth W).CoordinateRing
    ((W_smooth W).localRingAt P_smooth) with hf
  have h_yc_mul : YC * Q ∈ Ideal.span ({XC} : Set _) :=
    yclass_mul_quot_in_xclass_span W.toAffine h_eq_at
  have h_Q_notmem : Q ∉ P_ideal := mk_quot_not_mem W.toAffine h_eq_at hY
  have h_f_yc_mul : f YC * f Q ∈ Ideal.span ({f XC} : Set _) := by
    rw [← map_mul]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h_yc_mul
    exact Ideal.mem_span_singleton'.mpr ⟨f c, by rw [← hc, map_mul]⟩
  have h_f_Q_unit : IsUnit (f Q) :=
    IsLocalization.map_units ((W_smooth W).localRingAt P_smooth)
      (⟨Q, h_Q_notmem⟩ : P_ideal.primeCompl)
  have h_f_yc_mem : f YC ∈ Ideal.span ({f XC} : Set _) := by
    obtain ⟨u, hu⟩ := h_f_Q_unit
    have h1 : f YC * (↑u : _) ∈ Ideal.span ({f XC} : Set _) := by
      rwa [hu]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    refine Ideal.mem_span_singleton'.mpr ⟨c * (↑u⁻¹ : _), ?_⟩
    have h_cancel : f YC = f YC * (↑u : _) * (↑u⁻¹ : _) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [h_cancel, ← hc]
    ring
  have h_pideal_eq : P_ideal = Ideal.span ({XC, YC} : Set _) := rfl
  have h_map_eq : Ideal.map f P_ideal = Ideal.span ({f XC} : Set _) := by
    rw [h_pideal_eq, Ideal.map_span, Set.image_pair]
    exact le_antisymm
      (Ideal.span_le.mpr (fun z hz ↦ by
        rcases (Set.mem_insert_iff.mp hz) with rfl | hz'
        · exact Ideal.subset_span rfl
        · simp only [Set.mem_singleton_iff] at hz'
          rw [hz']; exact h_f_yc_mem))
      (Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
  have h_loc_eq : IsLocalRing.maximalIdeal
      ((W_smooth W).localRingAt P_smooth) = Ideal.map f P_ideal := by
    change IsLocalRing.maximalIdeal
        (Localization.AtPrime P_ideal) = Ideal.map f P_ideal
    exact (Localization.AtPrime.map_eq_maximalIdeal).symm
  rw [h_loc_eq, h_map_eq]

/-- **`ord_P (x_gen − xk) = 1` at `−T` for non-2-torsion (UNCONDITIONAL)**:
combines the witness-parametric `ord_P_x_gen_sub_const_eq_one_of_maxIdeal_span`
with the unconditional `maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor`. -/
theorem ord_P_x_gen_sub_const_eq_one_of_non_2_tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap F KE xk) = ((1 : ℤ) : WithTop ℤ) :=
  ord_P_x_gen_sub_const_eq_one_of_maxIdeal_span W xk yk h_ns
    (maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor W xk yk h_ns h_not_2_tor)

/-- **Valuation form of `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`**:
`pointValuation` at `−T` of `x_gen − xk` is < 1 (i.e., the function
vanishes at the smooth point `−T`). Direct via
`one_le_ord_P_iff_pointValuation_lt_one`. -/
theorem pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
      (x_gen W - algebraMap F KE xk) < 1 := by
  have h_ord_eq : (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
      (x_gen W - algebraMap F KE xk) = ((1 : ℤ) : WithTop ℤ) :=
    ord_P_x_gen_sub_const_eq_one_of_non_2_tor W xk yk h_ns h_not_2_tor
  have h_ne : x_gen W - algebraMap F KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have h_le : (1 : WithTop ℤ) ≤ (W_smooth W).ord_P
      (negSmoothPoint W xk yk h_ns) (x_gen W - algebraMap F KE xk) := by
    rw [h_ord_eq]; rfl
  exact (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one h_ne).mp h_le

/-- **Weakened ≤ 1 form**: at `−T` for non-2-torsion `T`, the function
`x_gen − xk` has `pointValuation ≤ 1`. Direct weakening of
`pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint` via `le_of_lt`.
Useful for downstream consumers needing the integer-ring containment form
(rather than strict vanishing). -/
theorem pointValuation_x_gen_sub_const_le_one_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap F KE xk) ≤ 1 :=
  le_of_lt (pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint
    W xk yk h_ns h_not_2_tor)

/-- **`x_gen W` has pointValuation ≤ 1 at any smooth point**: x_gen is in the
algMap-image of the CoordinateRing (specifically, the image of `algebraMap
(Polynomial F) CoordinateRing X`), so its pointValuation at any P is ≤ 1.
Direct via `pointValuation_algebraMap_le_one`. -/
theorem pointValuation_x_gen_le_one (P : (W_smooth W).SmoothPoint) :
    (W_smooth W).pointValuation P (x_gen W) ≤ 1 := by
  change (W_smooth W).pointValuation P
    (algebraMap W.toAffine.CoordinateRing KE
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)) ≤ 1
  exact (W_smooth W).pointValuation_algebraMap_le_one _ P

/-- **`y_gen W` has pointValuation ≤ 1 at any smooth point**: y_gen is in the
algMap-image of the CoordinateRing (specifically, the image of
`AdjoinRoot.root W.toAffine.polynomial`), so its pointValuation at any P
is ≤ 1. Direct via `pointValuation_algebraMap_le_one`. -/
theorem pointValuation_y_gen_le_one (P : (W_smooth W).SmoothPoint) :
    (W_smooth W).pointValuation P (y_gen W) ≤ 1 := by
  change (W_smooth W).pointValuation P
    (algebraMap W.toAffine.CoordinateRing KE
      (AdjoinRoot.root W.toAffine.polynomial)) ≤ 1
  exact (W_smooth W).pointValuation_algebraMap_le_one _ P

/-- **Conjunction: x_gen and y_gen both have pointValuation ≤ 1 at any
smooth point.** Useful one-shot package for downstream consumers needing
both witnesses. -/
theorem pointValuation_xy_gen_le_one (P : (W_smooth W).SmoothPoint) :
    (W_smooth W).pointValuation P (x_gen W) ≤ 1 ∧
    (W_smooth W).pointValuation P (y_gen W) ≤ 1 :=
  ⟨pointValuation_x_gen_le_one W P, pointValuation_y_gen_le_one W P⟩

/-- **`x_gen W` lifts to `localRingAt P`**: by the biconditional integer
characterisation (commit a1aa4d7), x_gen comes from an element of
`(W_smooth W).localRingAt P`. -/
theorem x_gen_mem_localRingAt_image (P : (W_smooth W).SmoothPoint) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        x_gen W :=
  Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
    (x_gen W) (pointValuation_x_gen_le_one W P)

/-- **`y_gen W` lifts to `localRingAt P`**: companion to
`x_gen_mem_localRingAt_image`. -/
theorem y_gen_mem_localRingAt_image (P : (W_smooth W).SmoothPoint) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        y_gen W :=
  Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
    (y_gen W) (pointValuation_y_gen_le_one W P)

/-- **`algMap F→KE c` lifts to `localRingAt P` at any smooth point**: F-constants
are integer-ring elements at every P. -/
theorem algebraMap_F_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        algebraMap F (W_smooth W).FunctionField c :=
  Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
    (algebraMap F _ c)
    ((W_smooth W).pointValuation_algebraMap_F_le_one P c)

/-- **algMap F→KE c is in the localRingAt-image: ≤ 1 form**: simple `≤ 1`
restatement of `pointValuation_algebraMap_F_le_one`. -/
theorem pointValuation_algebraMap_F_le_one_apply
    (P : (W_smooth W).SmoothPoint) (c : F) :
    (W_smooth W).pointValuation P (algebraMap F KE c) ≤ 1 :=
  (W_smooth W).pointValuation_algebraMap_F_le_one P c

/-! ### `y_gen − yk'` at a smooth point with y-coord `yk'` -/

/-- The function `y_gen W − algebraMap F KE yk'` is the image under
`algebraMap CoordinateRing FunctionField` of `YClass W.toAffine (C yk')`,
the class of `Y − yk'` in the coordinate ring. -/
theorem y_gen_sub_const_eq_algebraMap_YClass (yk' : F) :
    y_gen W - algebraMap F KE yk' =
      algebraMap W.toAffine.CoordinateRing KE
        (Affine.CoordinateRing.YClass W.toAffine (Polynomial.C yk')) := by
  unfold y_gen
  rw [show (algebraMap F KE yk' : KE) =
    algebraMap W.toAffine.CoordinateRing KE
      (algebraMap F W.toAffine.CoordinateRing yk')
    from IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing KE yk']
  rw [← _root_.map_sub]
  congr 1

/-- For any smooth point `P` of `W_smooth W` whose y-coordinate is `yk'`,
the class of `Y − yk'` lies in the maximal ideal at `P`. -/
theorem YClass_mem_maximalIdealAt
    (P : (W_smooth W).SmoothPoint) (yk' : F) (h_y : P.y = yk') :
    Affine.CoordinateRing.YClass W.toAffine (Polynomial.C yk') ∈
      (W_smooth W).maximalIdealAt P := by
  rw [← h_y]
  change Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y) ∈
    Affine.CoordinateRing.XYIdeal W.toAffine P.x (Polynomial.C P.y)
  unfold Affine.CoordinateRing.XYIdeal
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- **Foundational ord-positivity for the y-side**: at any smooth point
`P` of `W_smooth W` with `P.y = yk'`, the function `y_gen − yk'` has order
at least 1.

Proof: parallel to `one_le_ord_P_x_gen_sub_const`, using `YClass` and the
membership of `YClass` in the maximal ideal. -/
theorem one_le_ord_P_y_gen_sub_const_at_smoothPoint
    (P : (W_smooth W).SmoothPoint) (yk' : F) (h_y : P.y = yk') :
    ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (y_gen W - algebraMap F KE yk') := by
  set u := Affine.CoordinateRing.YClass W.toAffine (Polynomial.C yk')
    with hu_def
  rw [y_gen_sub_const_eq_algebraMap_YClass W yk']
  have hu_ne : u ≠ 0 :=
    Affine.CoordinateRing.YClass_ne_zero (W' := W.toAffine) (Polynomial.C yk')
  have hu_mem : u ∈ (W_smooth W).maximalIdealAt P :=
    YClass_mem_maximalIdealAt W P yk' h_y
  have h_ord_ne_zero : (W_smooth W).ord_P P
      (algebraMap W.toAffine.CoordinateRing KE u) ≠ 0 :=
    ((W_smooth W).ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt hu_ne P).mpr hu_mem
  have h_v_le : (W_smooth W).pointValuation P
      (algebraMap W.toAffine.CoordinateRing KE u) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_le_one u P
  have h_au_ne : algebraMap W.toAffine.CoordinateRing KE u ≠ 0 :=
    (map_ne_zero_iff _
      (IsFractionRing.injective W.toAffine.CoordinateRing KE)).mpr hu_ne
  have h_ord_nonneg : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (algebraMap W.toAffine.CoordinateRing KE u) := by
    have hv : (W_smooth W).pointValuation P
        (algebraMap W.toAffine.CoordinateRing KE u) ≠ 0 :=
      ((W_smooth W).pointValuation P).ne_zero_iff.mpr h_au_ne
    unfold SmoothPlaneCurve.ord_P
    rw [dif_neg hv]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
        WithTop.coe_le_coe]
    have h_unz_le : WithZero.unzero hv ≤ 1 := by
      rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]
      exact h_v_le
    have h_toAdd : (WithZero.unzero hv).toAdd ≤ 0 := by
      have h1 : ((1 : Multiplicative ℤ)).toAdd = (0 : ℤ) := rfl
      have h2 : Multiplicative.toAdd (WithZero.unzero hv) ≤
          Multiplicative.toAdd (1 : Multiplicative ℤ) := h_unz_le
      rw [h1] at h2
      exact h2
    omega
  have h_ne_top : (W_smooth W).ord_P P
      (algebraMap W.toAffine.CoordinateRing KE u) ≠ ⊤ :=
    (SmoothPlaneCurve.ord_P_eq_top_iff _).not.mpr h_au_ne
  cases h : (W_smooth W).ord_P P
      (algebraMap W.toAffine.CoordinateRing KE u) with
  | top => exact absurd h h_ne_top
  | coe n =>
      rw [h] at h_ord_nonneg h_ord_ne_zero
      have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast h_ord_nonneg
      have hn_ne : n ≠ 0 := by
        intro hn
        apply h_ord_ne_zero
        rw [hn]; rfl
      exact_mod_cast (show (1 : ℤ) ≤ n by omega)

/-- **Specialisation to `−T`**: at the smooth point `−T = (xk, negY xk yk)`,
the function `y_gen − negY xk yk` has order at least 1. -/
theorem one_le_ord_P_y_gen_sub_negY_const
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) :=
  one_le_ord_P_y_gen_sub_const_at_smoothPoint W _
    (W.toAffine.negY xk yk) rfl

/-! ### Unconditional maxIdeal-span and ord_P y-side for 2-torsion case

Companion to the x-side ord_P upper bound at non-2-torsion smooth points
(`maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor` +
`ord_P_x_gen_sub_const_eq_one_of_non_2_tor`).

For 2-torsion smooth point P (where `yk = negY xk yk`, equivalently
`polynomialY = 0` at the point), the maxIdeal of `localRingAt P` is
generated by `algMap (YClass)` (NOT `algMap (XClass)`). The y-side
companion gives `ord_P (y_gen - negY xk yk) = 1` exact for 2-torsion. -/

open scoped Polynomial.Bivariate in
/-- **Unconditional**: at the 2-torsion smooth point `(xk, negY xk yk = yk)`,
the maximal ideal of the local ring is generated by `algMap (YClass)`.

Reproduces the relevant content from `localRing_isDVR`'s first case
(where `polynomialX ≠ 0`), exposed publicly using:
- `xclass_mul_C_g_in_yclass_span` (public helper from Valuation.lean).
- `mk_C_g_not_mem` (public helper from Valuation.lean).
- `polynomialX_evalEval_ne_zero_at_2tor` (existing). -/
theorem maximalIdeal_localRingAt_eq_span_YClass_of_2_tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    IsLocalRing.maximalIdeal
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns)) =
      Ideal.span ({algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns))
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk)))} : Set _) := by
  set P_smooth := negSmoothPoint W xk yk h_ns
  set P_ideal : Ideal (W_smooth W).CoordinateRing :=
    (W_smooth W).maximalIdealAt P_smooth with hPIdef
  have h_eq_at : W.toAffine.Equation xk (W.toAffine.negY xk yk) :=
    ((Affine.nonsingular_neg xk yk).mpr h_ns).1
  have h_negY_eq : W.toAffine.negY xk yk = yk := h_2_tor.symm
  have hX : W.toAffine.polynomialX.evalEval xk
      (W.toAffine.negY xk yk) ≠ 0 := by
    rw [h_negY_eq]
    have h_polY : W.toAffine.polynomialY.evalEval xk yk = 0 := by
      rw [WeierstrassCurve.Affine.evalEval_polynomialY]
      have hneg : W.toAffine.negY xk yk = -yk - W.a₁ * xk - W.a₃ := rfl
      rw [hneg] at h_2_tor
      linear_combination h_2_tor
    rcases h_ns.2 with hX' | hY'
    · exact hX'
    · exact absurd h_polY hY'
  set yk' : F := W.toAffine.negY xk yk with hyk'
  set CG : (W_smooth W).CoordinateRing :=
    Affine.CoordinateRing.mk W.toAffine
      (Polynomial.C (W.toAffine.polynomial.eval (Polynomial.C yk') /ₘ
        (Polynomial.X - Polynomial.C xk))) with hCG
  set XC : (W_smooth W).CoordinateRing :=
    Affine.CoordinateRing.XClass W.toAffine xk with hXC
  set YC : (W_smooth W).CoordinateRing :=
    Affine.CoordinateRing.YClass W.toAffine (Polynomial.C yk') with hYC
  set f := algebraMap (W_smooth W).CoordinateRing
    ((W_smooth W).localRingAt P_smooth) with hf
  have h_xc_mul : XC * CG ∈ Ideal.span ({YC} : Set _) :=
    xclass_mul_C_g_in_yclass_span W.toAffine h_eq_at
  have h_CG_notmem : CG ∉ P_ideal := mk_C_g_not_mem W.toAffine h_eq_at hX
  have h_f_xc_mul : f XC * f CG ∈ Ideal.span ({f YC} : Set _) := by
    rw [← map_mul]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h_xc_mul
    exact Ideal.mem_span_singleton'.mpr ⟨f c, by rw [← hc, map_mul]⟩
  have h_f_CG_unit : IsUnit (f CG) :=
    IsLocalization.map_units ((W_smooth W).localRingAt P_smooth)
      (⟨CG, h_CG_notmem⟩ : P_ideal.primeCompl)
  have h_f_xc_mem : f XC ∈ Ideal.span ({f YC} : Set _) := by
    obtain ⟨u, hu⟩ := h_f_CG_unit
    have h1 : f XC * (↑u : _) ∈ Ideal.span ({f YC} : Set _) := by
      rwa [hu]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    refine Ideal.mem_span_singleton'.mpr ⟨c * (↑u⁻¹ : _), ?_⟩
    have h_cancel : f XC = f XC * (↑u : _) * (↑u⁻¹ : _) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [h_cancel, ← hc]
    ring
  have h_pideal_eq : P_ideal = Ideal.span ({XC, YC} : Set _) := rfl
  have h_map_eq : Ideal.map f P_ideal = Ideal.span ({f YC} : Set _) := by
    rw [h_pideal_eq, Ideal.map_span, Set.image_pair]
    exact le_antisymm
      (Ideal.span_le.mpr (fun z hz ↦ by
        rcases (Set.mem_insert_iff.mp hz) with rfl | hz'
        · exact h_f_xc_mem
        · simp only [Set.mem_singleton_iff] at hz'
          rw [hz']; exact Ideal.subset_span rfl))
      (Ideal.span_mono (Set.singleton_subset_iff.mpr
        (Set.mem_insert_of_mem _ rfl)))
  have h_loc_eq : IsLocalRing.maximalIdeal
      ((W_smooth W).localRingAt P_smooth) = Ideal.map f P_ideal := by
    change IsLocalRing.maximalIdeal
        (Localization.AtPrime P_ideal) = Ideal.map f P_ideal
    exact (Localization.AtPrime.map_eq_maximalIdeal).symm
  rw [h_loc_eq, h_map_eq]

/-- **`ord_P (y_gen - yk') ≤ 1` at `−T`, witness-parametric on the
maxIdeal-span hypothesis (YClass form)**: y-side mirror of
`ord_P_x_gen_sub_const_le_one_of_maxIdeal_span`. -/
theorem ord_P_y_gen_sub_negY_const_le_one_of_maxIdeal_span
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_max_eq : IsLocalRing.maximalIdeal
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns)) =
      Ideal.span ({algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt (negSmoothPoint W xk yk h_ns))
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk)))} : Set _)) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) ≤
      ((1 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns
  rw [y_gen_sub_const_eq_algebraMap_YClass W (W.toAffine.negY xk yk)]
  set v := IsDiscreteValuationRing.maximalIdeal ((W_smooth W).localRingAt P)
    with hv_def
  have h_yc_ne : Affine.CoordinateRing.YClass W.toAffine
      (Polynomial.C (W.toAffine.negY xk yk)) ≠ 0 :=
    Affine.CoordinateRing.YClass_ne_zero (W' := W.toAffine)
      (y := Polynomial.C (W.toAffine.negY xk yk))
  have h_yc_loc_ne : algebraMap (W_smooth W).CoordinateRing
      ((W_smooth W).localRingAt P)
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk))) ≠ 0 := by
    exact (map_ne_zero_iff _
      (IsLocalization.injective (M := ((W_smooth W).maximalIdealAt P).primeCompl)
        ((W_smooth W).localRingAt P)
        ((W_smooth W).maximalIdealAt P).primeCompl_le_nonZeroDivisors)).mpr h_yc_ne
  have h_int_val : v.intValuation
      (algebraMap (W_smooth W).CoordinateRing
        ((W_smooth W).localRingAt P)
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk)))) =
      WithZero.exp (-1 : ℤ) :=
    v.intValuation_singleton h_yc_loc_ne h_max_eq
  have h_val_KE : (W_smooth W).pointValuation P
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk)))) =
      WithZero.exp (-1 : ℤ) := by
    change v.valuation _ _ = _
    rw [IsScalarTower.algebraMap_apply (W_smooth W).CoordinateRing
      ((W_smooth W).localRingAt P) (W_smooth W).FunctionField]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact h_int_val
  change (W_smooth W).pointValuation P
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk)))) =
      WithZero.exp (-1 : ℤ) at h_val_KE
  have h_val_ne : (W_smooth W).pointValuation P
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk)))) ≠ 0 := by
    rw [h_val_KE]; exact WithZero.exp_ne_zero
  change (W_smooth W).ord_P P
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
        (Affine.CoordinateRing.YClass W.toAffine
          (Polynomial.C (W.toAffine.negY xk yk)))) ≤ ((1 : ℤ) : WithTop ℤ)
  unfold SmoothPlaneCurve.ord_P
  rw [dif_neg h_val_ne]
  have h_unz : WithZero.unzero h_val_ne = Multiplicative.ofAdd (-1 : ℤ) := by
    rwa [← WithZero.coe_inj, WithZero.coe_unzero]
  rw [h_unz]
  change ((-(Multiplicative.ofAdd (-1 : ℤ)).toAdd : ℤ) : WithTop ℤ) ≤
    ((1 : ℤ) : WithTop ℤ)
  rfl

/-- **`ord_P (y_gen - negY xk yk) = 1` at `−T` for 2-torsion (UNCONDITIONAL)**:
y-side companion to `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`.
Combines the witness-parametric upper bound with the unconditional
`maximalIdeal_localRingAt_eq_span_YClass_of_2_tor`. -/
theorem ord_P_y_gen_sub_negY_const_eq_one_of_2_tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) =
      ((1 : ℤ) : WithTop ℤ) :=
  le_antisymm
    (ord_P_y_gen_sub_negY_const_le_one_of_maxIdeal_span W xk yk h_ns
      (maximalIdeal_localRingAt_eq_span_YClass_of_2_tor W xk yk h_ns h_2_tor))
    (one_le_ord_P_y_gen_sub_negY_const W xk yk h_ns)

/-- **Valuation form of `one_le_ord_P_y_gen_sub_const_at_smoothPoint`**:
at any smooth point P with `P.y = yk'`, `pointValuation P (y_gen − yk')`
is < 1. The y-side companion to
`pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint`, generalising
to arbitrary smooth points (not just `−T`). -/
theorem pointValuation_y_gen_sub_const_lt_one_at_smoothPoint
    (P : (W_smooth W).SmoothPoint) (yk' : F) (h_y : P.y = yk') :
    (W_smooth W).pointValuation P (y_gen W - algebraMap F KE yk') < 1 := by
  have h_le : (1 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (y_gen W - algebraMap F KE yk') :=
    one_le_ord_P_y_gen_sub_const_at_smoothPoint W P yk' h_y
  have h_ne : y_gen W - algebraMap F KE yk' ≠ 0 := by
    rw [y_gen_sub_const_eq_algebraMap_YClass]
    exact (map_ne_zero_iff _
      (IsFractionRing.injective W.toAffine.CoordinateRing KE)).mpr
      (Affine.CoordinateRing.YClass_ne_zero (Polynomial.C yk'))
  exact (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one h_ne).mp h_le

/-- **Valuation form of `one_le_ord_P_y_gen_sub_negY_const`**: at the
smooth point `−T = (xk, negY xk yk)`, the function `y_gen − negY xk yk`
has pointValuation < 1. Specialisation of
`pointValuation_y_gen_sub_const_lt_one_at_smoothPoint` to `−T`. -/
theorem pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) < 1 :=
  pointValuation_y_gen_sub_const_lt_one_at_smoothPoint W _
    (W.toAffine.negY xk yk) rfl

/-- **Weakened ≤ 1 form**: at any smooth point P with `P.y = yk'`,
the function `y_gen − yk'` has `pointValuation ≤ 1`. Direct weakening of
`pointValuation_y_gen_sub_const_lt_one_at_smoothPoint` via `le_of_lt`. -/
theorem pointValuation_y_gen_sub_const_le_one_at_smoothPoint
    (P : (W_smooth W).SmoothPoint) (yk' : F) (h_y : P.y = yk') :
    (W_smooth W).pointValuation P (y_gen W - algebraMap F KE yk') ≤ 1 :=
  le_of_lt (pointValuation_y_gen_sub_const_lt_one_at_smoothPoint W P yk' h_y)

/-- **Weakened ≤ 1 form at `−T`**: at the smooth point `−T`, the function
`y_gen − negY xk yk` has `pointValuation ≤ 1`. Direct weakening of
`pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint` via
`le_of_lt`. -/
theorem pointValuation_y_gen_sub_negY_const_le_one_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) ≤ 1 :=
  le_of_lt (pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint
    W xk yk h_ns)

/-- **Combined per-coordinate vanishing at `−T` for non-2-torsion `T`**:
both the x-side and y-side vanishing witnesses bundled together.
Conjunction of `pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint`
(commit a1db85b) and `pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint`
(commit be85fb4). Useful for downstream Helper 2 chord-slope combination
where both x-coord and y-coord vanishing at `−T` are needed simultaneously. -/
theorem pointValuation_xy_sub_const_lt_one_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    ((W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap F KE xk) < 1) ∧
    ((W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) < 1) :=
  ⟨pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint W xk yk h_ns h_not_2_tor,
   pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint W xk yk h_ns⟩

/-! ### `ord_P (y_gen − yk) = 0` at `−T` for non-2-torsion `T`

For non-2-torsion `T = (xk, yk)` (i.e. `yk ≠ negY xk yk`), the function
`y_gen − yk` has *zero* ord at `−T`, since at `−T` the value of `y_gen` is
`negY xk yk ≠ yk`.

Decomposition: `y_gen − yk = (y_gen − negY xk yk) + (negY xk yk − yk)`,
where the first term has ord ≥ 1 (vanishes at `−T`) and the second is a
nonzero base-field constant (ord = 0). By strict non-arch, the constant
dominates, giving ord = 0. -/

/-- **`ord_P (y_gen − yk) = 0` at `−T` for non-2-torsion `T`** (key
ord-vanishing for the slope computation). -/
theorem ord_P_y_gen_sub_const_eq_zero
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE yk) = 0 := by
  set P := negSmoothPoint W xk yk h_ns
  have h_decomp : y_gen W - algebraMap F KE yk =
      (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) +
        algebraMap F KE (W.toAffine.negY xk yk - yk) := by
    rw [_root_.map_sub]; ring
  rw [h_decomp]
  have h1 : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) :=
    one_le_ord_P_y_gen_sub_negY_const W xk yk h_ns
  have h_const_ne : W.toAffine.negY xk yk - yk ≠ 0 := by
    intro h
    exact h_not_2_tor (sub_eq_zero.mp h).symm
  have h2 : (W_smooth W).ord_P P
      (algebraMap F KE (W.toAffine.negY xk yk - yk)) = 0 :=
    (W_smooth W).ord_P_algebraMap_F_of_ne_zero h_const_ne P
  have h_lt : (W_smooth W).ord_P P
      (algebraMap F KE (W.toAffine.negY xk yk - yk)) <
    (W_smooth W).ord_P P
      (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) := by
    rw [h2]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1)) h1
  have h_swap : ((y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) +
      algebraMap F KE (W.toAffine.negY xk yk - yk) : KE) =
    algebraMap F KE (W.toAffine.negY xk yk - yk) +
      (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) := add_comm _ _
  rw [h_swap]
  exact (SmoothPlaneCurve.ord_P_add_eq_of_lt h_lt).trans h2

/-! ### `ord_P (translateSlope_xy) ≤ -1` at `−T` for non-2-torsion `T` -/

/-- **Valuation form of `ord_P_y_gen_sub_const_eq_zero`**: at `−T` for
non-2-torsion `T`, `pointValuation` of `y_gen − yk` equals 1 (i.e., the
function is a unit at `−T`, since at `−T` the value of `y_gen` is
`negY xk yk ≠ yk`). Direct via `ord_P_eq_zero_iff_pointValuation_eq_one`. -/
theorem pointValuation_y_gen_sub_const_eq_one_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE yk) = 1 := by
  have h_ord_eq : (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
      (y_gen W - algebraMap F KE yk) = 0 :=
    ord_P_y_gen_sub_const_eq_zero W xk yk h_ns h_not_2_tor
  have h_ne : y_gen W - algebraMap F KE yk ≠ 0 := by
    rw [y_gen_sub_const_eq_algebraMap_YClass]
    exact (map_ne_zero_iff _
      (IsFractionRing.injective W.toAffine.CoordinateRing KE)).mpr
      (Affine.CoordinateRing.YClass_ne_zero (Polynomial.C yk))
  have h_pv_ne : (W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
      (y_gen W - algebraMap F KE yk) ≠ 0 :=
    ((W_smooth W).pointValuation _).ne_zero_iff.mpr h_ne
  unfold SmoothPlaneCurve.ord_P at h_ord_eq
  rw [dif_neg h_pv_ne] at h_ord_eq
  have h_toAdd : (WithZero.unzero h_pv_ne).toAdd = 0 := by
    have h_neg : -((WithZero.unzero h_pv_ne).toAdd : ℤ) = 0 := by
      exact_mod_cast h_ord_eq
    omega
  have : WithZero.unzero h_pv_ne = (1 : Multiplicative ℤ) := by
    ext; exact h_toAdd
  rw [← WithZero.coe_unzero h_pv_ne, this]; rfl

/-- **`pointValuation` of `y_gen − yk` is ≤ 1** at `−T` for non-2-torsion `T`.
Direct `le_of_eq` weakening of
`pointValuation_y_gen_sub_const_eq_one_at_negSmoothPoint`. -/
theorem pointValuation_y_gen_sub_const_le_one_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE yk) ≤ 1 :=
  le_of_eq (pointValuation_y_gen_sub_const_eq_one_at_negSmoothPoint
    W xk yk h_ns h_not_2_tor)

/-- **Triple per-coordinate valuation witnesses at `−T` for non-2-torsion `T`**:
bundles the three crucial valuation properties at `−T` into a single
conjunctive theorem:
1. `pointValuation P (x_gen − xk) < 1` (x-coord vanishes at `−T`).
2. `pointValuation P (y_gen − negY xk yk) < 1` (y-coord at `−T`
   evaluates to `negY xk yk`, vanishing of `y_gen − negY xk yk`).
3. `pointValuation P (y_gen − yk) = 1` (y-coord at `−T` ≠ `yk`,
   so `y_gen − yk` is a unit).

Useful for downstream consumers needing the full per-coordinate behaviour
at `−T` for the chord-slope construction. Conjunction of three already-
shipped bridges. -/
theorem pointValuation_triple_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    ((W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap F KE xk) < 1) ∧
    ((W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE (W.toAffine.negY xk yk)) < 1) ∧
    ((W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)
        (y_gen W - algebraMap F KE yk) = 1) :=
  ⟨pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint W xk yk h_ns h_not_2_tor,
   pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint W xk yk h_ns,
   pointValuation_y_gen_sub_const_eq_one_at_negSmoothPoint W xk yk h_ns h_not_2_tor⟩

/-- **`ord_P (translateSlope_xy) ≤ -1` at `−T` for non-2-torsion `T`**:
combining the y-side ord = 0 with the x-side ord ≥ 1 via the secant
formula. -/
theorem ord_P_translateSlope_xy_le_neg_one
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateSlope_xy W xk yk) ≤ ((-1 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns
  rw [translateSlope_xy_eq]
  have hx_ne : x_gen W - algebraMap F KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have h_div : (y_gen W - algebraMap F KE yk) /
      (x_gen W - algebraMap F KE xk) =
      (y_gen W - algebraMap F KE yk) *
        (x_gen W - algebraMap F KE xk)⁻¹ := div_eq_mul_inv _ _
  rw [h_div]
  have h_mul : (W_smooth W).ord_P P
      ((y_gen W - algebraMap F KE yk) *
        (x_gen W - algebraMap F KE xk)⁻¹) =
      (W_smooth W).ord_P P (y_gen W - algebraMap F KE yk) +
        (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk)⁻¹ :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  rw [h_mul]
  have h_inv : (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk)⁻¹ =
      -(W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) :=
    SmoothPlaneCurve.ord_P_inv (P := P) _ hx_ne
  rw [h_inv]
  have h_y0 : (W_smooth W).ord_P P (y_gen W - algebraMap F KE yk) = 0 :=
    ord_P_y_gen_sub_const_eq_zero W xk yk h_ns h_not_2_tor
  rw [h_y0, zero_add]
  have h_x : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) :=
    one_le_ord_P_x_gen_sub_const W xk yk h_ns
  have h_ne_top : (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) ≠ ⊤ :=
    (SmoothPlaneCurve.ord_P_eq_top_iff _).not.mpr hx_ne
  cases h : (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) with
  | top => exact absurd h h_ne_top
  | coe n =>
      rw [h] at h_x
      have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast h_x
      change -((n : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)
      rw [show -((n : ℤ) : WithTop ℤ) = ((-n : ℤ) : WithTop ℤ) from rfl]
      exact_mod_cast (show -n ≤ -1 by omega)

/-- **`ord_P (translateSlope_xy) ≠ ⊤` at `−T` for non-2-torsion `T`**:
the slope is nonzero at `−T`. Direct from `ord_P_translateSlope_xy_le_neg_one`
+ `(-1 : WithTop ℤ) ≠ ⊤`. -/
theorem ord_P_translateSlope_xy_ne_top
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateSlope_xy W xk yk) ≠ ⊤ := by
  intro h_top
  have h_le : (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
      (translateSlope_xy W xk yk) ≤ ((-1 : ℤ) : WithTop ℤ) :=
    ord_P_translateSlope_xy_le_neg_one W xk yk h_ns h_not_2_tor
  rw [h_top] at h_le
  exact absurd h_le (by decide)

/-- **translateSlope_xy ≠ 0 at `−T` for non-2-torsion `T`**: corollary of
the ord_P_ne_top form above. -/
theorem translateSlope_xy_ne_zero_at_negSmoothPoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateSlope_xy W xk yk ≠ 0 := by
  intro h_zero
  have h_top : (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
      (translateSlope_xy W xk yk) = ⊤ := by
    rw [h_zero]; exact SmoothPlaneCurve.ord_P_zero
  exact ord_P_translateSlope_xy_ne_top W xk yk h_ns h_not_2_tor h_top

/-! ### `ord_P (translateX_xy) ≤ -2` at `−T` for non-2-torsion `T`

Key algebraic identity: `translateX_xy · (x_gen − xk)² = N` where

```
N := (y_gen − yk)² + a₁ (y_gen − yk)(x_gen − xk)
        − (a₂ + x_gen + xk)(x_gen − xk)²
```

`N` is a polynomial in `x_gen`, `y_gen` (so its image in `K(E)` lies in
the coordinate ring's image), and at `−T = (xk, negY xk yk)` it
evaluates to `(negY xk yk − yk)² ≠ 0` for non-2-torsion `T`. Hence
`ord_P N = 0` at `−T`.

Combined with `ord_P (x_gen − xk) ≥ 1`, we get
`ord_P (translateX_xy) = ord_P N − 2·ord_P (x_gen − xk) ≤ −2 < 0`. -/

/-- The algebraic identity `translateX_xy · (x_gen − xk)² = N`. -/
private theorem translateX_xy_mul_sq_eq
    (xk yk : F) :
    translateX_xy W xk yk *
        (x_gen W - algebraMap F KE xk) ^ 2 =
      (y_gen W - algebraMap F KE yk) ^ 2 +
        algebraMap F KE W.a₁ * (y_gen W - algebraMap F KE yk) *
          (x_gen W - algebraMap F KE xk) -
        (algebraMap F KE W.a₂ + x_gen W + algebraMap F KE xk) *
          (x_gen W - algebraMap F KE xk) ^ 2 := by
  unfold translateX_xy
  rw [WeierstrassCurve.Affine.addX]
  rw [show translateSlope_xy W xk yk =
    (y_gen W - algebraMap F KE yk) / (x_gen W - algebraMap F KE xk)
    from translateSlope_xy_eq W xk yk]
  have h_x_ne : x_gen W - algebraMap F KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have ha1 : (W_KE W).a₁ = algebraMap F KE W.a₁ := rfl
  have ha2 : (W_KE W).a₂ = algebraMap F KE W.a₂ := rfl
  rw [ha1, ha2]
  field_simp
  ring

/-- The algebraic identity `translateY_xy · (x_gen − xk)³ = M_y` where `M_y`
is a polynomial in `yd, xd, x_gen, y_gen, a₁, a₂, a₃, xk'`.  Companion to
`translateX_xy_mul_sq_eq`.  Using `addY = negY (addX) (negAddY) =
−(slope·(addX − x₁) + y₁) − a₁·addX − a₃` and substituting the slope and
addX expansions, then multiplying through by `xd³`, yields the
polynomial RHS below. -/
theorem translateY_xy_mul_cube_eq
    (xk yk : F) :
    translateY_xy W xk yk *
        (x_gen W - algebraMap F KE xk) ^ 3 =
      -((y_gen W - algebraMap F KE yk) ^ 3) -
        2 * algebraMap F KE W.a₁ * (y_gen W - algebraMap F KE yk) ^ 2 *
          (x_gen W - algebraMap F KE xk) +
        ((y_gen W - algebraMap F KE yk) *
          (algebraMap F KE W.a₂ + 2 * x_gen W + algebraMap F KE xk) -
          (algebraMap F KE W.a₁) ^ 2 *
            (y_gen W - algebraMap F KE yk)) *
          (x_gen W - algebraMap F KE xk) ^ 2 +
        (-y_gen W +
          algebraMap F KE W.a₁ *
            (algebraMap F KE W.a₂ + x_gen W + algebraMap F KE xk) -
          algebraMap F KE W.a₃) *
          (x_gen W - algebraMap F KE xk) ^ 3 := by
  unfold translateY_xy
  rw [WeierstrassCurve.Affine.addY]
  rw [WeierstrassCurve.Affine.negY]
  rw [WeierstrassCurve.Affine.negAddY]
  rw [WeierstrassCurve.Affine.addX]
  rw [show translateSlope_xy W xk yk =
    (y_gen W - algebraMap F KE yk) / (x_gen W - algebraMap F KE xk)
    from translateSlope_xy_eq W xk yk]
  have h_x_ne : x_gen W - algebraMap F KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have ha1 : (W_KE W).a₁ = algebraMap F KE W.a₁ := rfl
  have ha2 : (W_KE W).a₂ = algebraMap F KE W.a₂ := rfl
  have ha3 : (W_KE W).a₃ = algebraMap F KE W.a₃ := rfl
  rw [ha1, ha2, ha3]
  field_simp
  ring

/-- Helper: any element of `algebraMap R KE` image has nonneg ord at any
smooth point. -/
private theorem ord_P_algebraMap_R_nonneg (P : (W_smooth W).SmoothPoint)
    (u : W.toAffine.CoordinateRing) :
    (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (algebraMap W.toAffine.CoordinateRing KE u) := by
  have h_v_le : (W_smooth W).pointValuation P
      (algebraMap W.toAffine.CoordinateRing KE u) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_le_one u P
  by_cases hf : algebraMap W.toAffine.CoordinateRing KE u = 0
  · rw [hf]
    rw [show ((W_smooth W).ord_P P (0 : KE)) = ⊤ from
      SmoothPlaneCurve.ord_P_zero]
    exact le_top
  · have hv : (W_smooth W).pointValuation P
        (algebraMap W.toAffine.CoordinateRing KE u) ≠ 0 :=
      ((W_smooth W).pointValuation P).ne_zero_iff.mpr hf
    unfold SmoothPlaneCurve.ord_P
    rw [dif_neg hv]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
        WithTop.coe_le_coe]
    have h_unz_le : WithZero.unzero hv ≤ 1 := by
      rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]
      exact h_v_le
    have h_toAdd : (WithZero.unzero hv).toAdd ≤ 0 := by
      have h1 : ((1 : Multiplicative ℤ)).toAdd = (0 : ℤ) := rfl
      have h2 : Multiplicative.toAdd (WithZero.unzero hv) ≤
          Multiplicative.toAdd (1 : Multiplicative ℤ) := h_unz_le
      rwa [h1] at h2
    omega

/-- `x_gen` has nonneg ord at any smooth point (it's in the image of the
coordinate ring). Public to support consumers in Worker B's
`PoleDivisorFallback` stream (Action 3 γ-form: poles of `γ*x_gen` lie
above the X-prime). -/
theorem ord_P_x_gen_nonneg (P : (W_smooth W).SmoothPoint) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W) := by
  change (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P
    (algebraMap W.toAffine.CoordinateRing KE
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X))
  exact ord_P_algebraMap_R_nonneg W P _

/-- Helper: `algebraMap F KE c` has nonneg ord at any smooth point. -/
theorem ord_P_algebraMap_F_nonneg (P : (W_smooth W).SmoothPoint)
    (c : F) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (algebraMap F KE c) := by
  by_cases hc : c = 0
  · rw [hc, map_zero]
    rw [show ((W_smooth W).ord_P P (0 : KE)) = ⊤ from
      SmoothPlaneCurve.ord_P_zero]
    exact le_top
  · exact le_of_eq ((W_smooth W).ord_P_algebraMap_F_of_ne_zero hc P).symm

/-- **The `yd²` term has order `0`** when `ord_P yd = 0`. In the quadratic
combination matching `translateX_xy_mul_sq_eq`, this is the dominant
(smallest-order) summand against which all `xd`-bearing terms are compared.
X-side companion to `ord_P_neg_yd_cube_eq_zero`. -/
private theorem ord_P_x_yd_sq_eq_zero {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {yd : C.FunctionField} (hyd : C.ord_P P yd = 0) :
    C.ord_P P (yd ^ 2) = 0 := by
  rw [SmoothPlaneCurve.ord_P_pow (P := P) yd 2, hyd]; simp

/-- **The `xd`-linear term `a₁·yd·xd` has order `≥ 1`.** Its order is
`ord_P a₁ + ord_P yd + ord_P xd = (≥0) + 0 + (≥1)`, using `ord_P yd = 0` and
`1 ≤ ord_P xd`. The first of the two `xd`-bearing bounds in the quadratic
combination. -/
private theorem one_le_ord_P_x_linear_term {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {xd yd a1 : C.FunctionField}
    (hxd : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P xd) (hyd : C.ord_P P yd = 0)
    (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1) :
    ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P (a1 * yd * xd) := by
  rw [SmoothPlaneCurve.ord_P_mul (P := P) (a1 * yd) xd,
    SmoothPlaneCurve.ord_P_mul (P := P) a1 yd, hyd, add_zero]
  calc ((1 : ℤ) : WithTop ℤ) = 0 + ((1 : ℤ) : WithTop ℤ) := by rw [zero_add]
    _ ≤ C.ord_P P a1 + C.ord_P P xd := add_le_add ha1 hxd

/-- **The `xd²` coefficient `a₂ + xg + xk'` has order `≥ 0`.** A sum of three
nonneg-order pieces, combined by the non-archimedean inequality. -/
private theorem ord_P_x_quadratic_coef_nonneg {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a2 xk' xg : C.FunctionField}
    (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2) (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg)
    (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk') :
    (0 : WithTop ℤ) ≤ C.ord_P P (a2 + xg + xk') := by
  have h12 : (0 : WithTop ℤ) ≤ C.ord_P P (a2 + xg) :=
    (le_min ha2 hxg).trans (SmoothPlaneCurve.ord_P_add_le (P := P) a2 xg)
  exact (le_min h12 hxk').trans
    (SmoothPlaneCurve.ord_P_add_le (P := P) (a2 + xg) xk')

/-- **The `xd²` term `(a₂ + xg + xk')·xd²` has order `≥ 2`.** Combines the
nonneg coefficient (`ord_P_x_quadratic_coef_nonneg`) with `2 ≤ ord_P (xd²)`
(itself `2 • ord_P xd ≥ 2 • 1`). The second of the two `xd`-bearing bounds. -/
private theorem two_le_ord_P_x_quadratic_term {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {xd a2 xk' xg : C.FunctionField}
    (hxd : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P xd) (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2)
    (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg) (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk') :
    ((2 : ℤ) : WithTop ℤ) ≤ C.ord_P P ((a2 + xg + xk') * xd ^ 2) := by
  have h_xd_sq : ((2 : ℤ) : WithTop ℤ) ≤ C.ord_P P (xd ^ 2) := by
    rw [SmoothPlaneCurve.ord_P_pow (P := P) xd 2]
    refine le_trans ?_ (nsmul_le_nsmul_right hxd 2); rfl
  rw [SmoothPlaneCurve.ord_P_mul (P := P) (a2 + xg + xk') (xd ^ 2)]
  calc ((2 : ℤ) : WithTop ℤ) = 0 + ((2 : ℤ) : WithTop ℤ) := by rw [zero_add]
    _ ≤ _ := add_le_add
      (ord_P_x_quadratic_coef_nonneg ha2 hxg hxk') h_xd_sq

/-- **The non-`yd²` remainder `a₁·yd·xd − (a₂+xg+xk')·xd²` has order `≥ 1`.**
Both summands are `xd`-bearing: the linear term has order `≥ 1`
(`one_le_ord_P_x_linear_term`) and the quadratic term order `≥ 2 ≥ 1`
(`two_le_ord_P_x_quadratic_term`), so their difference has order `≥ 1` by the
non-archimedean inequality. -/
private theorem one_le_ord_P_x_rest {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {xd yd a1 a2 xk' xg : C.FunctionField}
    (hxd : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P xd) (hyd : C.ord_P P yd = 0)
    (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1) (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2)
    (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg) (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk') :
    ((1 : ℤ) : WithTop ℤ) ≤
      C.ord_P P (a1 * yd * xd + -((a2 + xg + xk') * xd ^ 2)) := by
  have h_B : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P (a1 * yd * xd) :=
    one_le_ord_P_x_linear_term hxd hyd ha1
  have h_C : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P ((a2 + xg + xk') * xd ^ 2) :=
    le_trans (by exact_mod_cast (show (1 : ℤ) ≤ 2 by norm_num))
      (two_le_ord_P_x_quadratic_term hxd ha2 hxg hxk')
  have h_add := SmoothPlaneCurve.ord_P_add_le (P := P)
    (a1 * yd * xd) (-((a2 + xg + xk') * xd ^ 2))
  rw [SmoothPlaneCurve.ord_P_neg (P := P) ((a2 + xg + xk') * xd ^ 2)] at h_add
  exact (le_min h_B h_C).trans h_add

/-- **Abstract `ord_P`-engine for the `translateX_xy` quadratic identity.**
Given a smooth point `P`, an `xd` with `1 ≤ ord_P xd`, a `yd` with
`ord_P yd = 0`, and nonneg-order `a1 a2 xk' xg`, the quadratic combination
matching the right side of `translateX_xy_mul_sq_eq` has `ord_P = 0`: the
dominant `yd²` term (order `0`) strictly beats the `xd`-bearing remainder
(order `≥ 1`), so `ord_P_add_eq_of_lt` pins the sum to `0`. X-side analogue of
`ord_P_translateY_cube_combination_eq_zero`. -/
private theorem ord_P_translateX_quadratic_combination_eq_zero
    {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint}
    {xd yd a1 a2 xk' xg : C.FunctionField}
    (hxd : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P xd) (hyd : C.ord_P P yd = 0)
    (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1) (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2)
    (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg) (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk') :
    C.ord_P P (yd ^ 2 + (a1 * yd * xd + -((a2 + xg + xk') * xd ^ 2))) = 0 := by
  have h_yd_sq : C.ord_P P (yd ^ 2) = 0 := ord_P_x_yd_sq_eq_zero hyd
  have h_rest : ((1 : ℤ) : WithTop ℤ) ≤
      C.ord_P P (a1 * yd * xd + -((a2 + xg + xk') * xd ^ 2)) :=
    one_le_ord_P_x_rest hxd hyd ha1 ha2 hxg hxk'
  have h_strict : C.ord_P P (yd ^ 2) <
      C.ord_P P (a1 * yd * xd + -((a2 + xg + xk') * xd ^ 2)) := by
    rw [h_yd_sq]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (0 : ℤ) < 1 by norm_num)) h_rest
  exact (SmoothPlaneCurve.ord_P_add_eq_of_lt h_strict).trans h_yd_sq

/-- **A factor of a square-multiple of order `0` has strictly negative order.**
If `ord_P (f · g²) = 0` while `1 ≤ ord_P g` (so `g ≠ 0`), then writing
`ord_P g = ↑n` with `n ≥ 1` forces `ord_P f = ↑k` finite with
`k + (n + n) = 0`, hence `k < 0`. Isolates the final integer-cancellation
step of `ord_P_translateX_xy_lt_zero`. -/
private theorem ord_P_lt_zero_of_ord_P_mul_sq_eq_zero
    {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint} {f g : C.FunctionField}
    (hfg : C.ord_P P (f * g ^ 2) = 0) (hg : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P g) :
    C.ord_P P f < 0 := by
  rw [SmoothPlaneCurve.ord_P_mul (P := P) f (g ^ 2),
    SmoothPlaneCurve.ord_P_pow (P := P) g 2] at hfg
  cases hg_case : C.ord_P P g with
  | top =>
      -- `ord_P g = ⊤` makes `ord_P f + 2 • ⊤ = ⊤ ≠ 0`, contradicting `hfg`.
      rw [hg_case, two_nsmul, top_add, add_top] at hfg
      exact absurd hfg (by simp)
  | coe n =>
      rw [hg_case] at hg hfg
      have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hg
      cases hf_case : C.ord_P P f with
      | top =>
          rw [hf_case] at hfg
          exact absurd hfg (by simp)
      | coe k =>
          rw [hf_case] at hfg
          have h_smul : ((2 : ℕ) • ((n : ℤ) : WithTop ℤ)) =
              (((n + n) : ℤ) : WithTop ℤ) := by
            change (1 + 1) • ((n : ℤ) : WithTop ℤ) = (((n + n) : ℤ) : WithTop ℤ)
            rw [add_smul, one_smul]; push_cast; ring
          rw [h_smul, show ((k : ℤ) : WithTop ℤ) + (((n + n) : ℤ) : WithTop ℤ) =
            ((k + (n + n) : ℤ) : WithTop ℤ) from by push_cast; ring] at hfg
          have h_eq : k + (n + n) = 0 := by exact_mod_cast hfg
          exact_mod_cast (show k < 0 by omega)

/-- **`ord_P (translateX_xy) < 0` at `−T` for non-2-torsion `T`**: the key
substantive step toward `translateX_xy_transcendental`.

Strategy: use the algebraic identity `translateX_xy · (x_gen − xk)² = N`
where the RHS has `ord_P = 0` (the dominant term is `(y_gen − yk)²` with
ord 0, others have ord ≥ 1). With `ord_P (x_gen − xk) ≥ 1`, this yields
`ord_P (translateX_xy) ≤ −2 · 1 = −2 < 0`. -/
theorem ord_P_translateX_xy_lt_zero
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateX_xy W xk yk) < 0 := by
  set P := negSmoothPoint W xk yk h_ns
  set yd := y_gen W - algebraMap F KE yk with hyd_def
  set xd := x_gen W - algebraMap F KE xk with hxd_def
  set a1 := algebraMap F KE W.a₁ with ha1_def
  set a2 := algebraMap F KE W.a₂ with ha2_def
  set xk' := algebraMap F KE xk with hxk'_def
  -- Order facts for the building blocks of the quadratic identity.
  have h_xd_ord : ((1 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P P xd :=
    one_le_ord_P_x_gen_sub_const W xk yk h_ns
  have h_yd_ord : (W_smooth W).ord_P P yd = 0 :=
    ord_P_y_gen_sub_const_eq_zero W xk yk h_ns h_not_2_tor
  have h_xg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W) :=
    ord_P_x_gen_nonneg W P
  have h_a1_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a1 :=
    ord_P_algebraMap_F_nonneg W P W.a₁
  have h_a2_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a2 :=
    ord_P_algebraMap_F_nonneg W P W.a₂
  have h_xk_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P xk' :=
    ord_P_algebraMap_F_nonneg W P xk
  -- The quadratic combination matching `translateX_xy_mul_sq_eq` has `ord_P = 0`
  -- (dominant `yd²` term beats the `xd`-bearing remainder), via the engine.
  have h_RHS' : (W_smooth W).ord_P P
      (yd ^ 2 + (a1 * yd * xd + -((a2 + x_gen W + xk') * xd ^ 2))) = 0 :=
    ord_P_translateX_quadratic_combination_eq_zero
      h_xd_ord h_yd_ord h_a1_nn h_a2_nn h_xg_nn h_xk_nn
  -- Transport along the algebraic identity to `ord_P (translateX_xy · xd²) = 0`.
  have h_id : translateX_xy W xk yk * xd ^ 2 =
      yd ^ 2 + (a1 * yd * xd + -((a2 + x_gen W + xk') * xd ^ 2)) := by
    rw [hyd_def, hxd_def, ha1_def, ha2_def, hxk'_def,
        translateX_xy_mul_sq_eq W xk yk]
    ring
  have h_LHS_ord : (W_smooth W).ord_P P (translateX_xy W xk yk * xd ^ 2) = 0 :=
    h_id ▸ h_RHS'
  -- `ord_P (translateX_xy · xd²) = 0` with `ord_P xd ≥ 1` forces a pole.
  exact ord_P_lt_zero_of_ord_P_mul_sq_eq_zero h_LHS_ord h_xd_ord

/-! ### Exact equality `ord_P (translateX_xy) = -2` for non-2-torsion `T`

Strengthens `ord_P_translateX_xy_lt_zero` to the EXACT equality `= -2`
using the now-unconditional `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`
(commit 06adc8e). The algebraic identity gives `ord_P (translateX_xy) +
2·ord_P (x_gen − xk) = 0`. With `ord_P (x_gen − xk) = 1` exact, the
result is `ord_P (translateX_xy) = −2`. -/

/-- **`ord_P (f ^ 2) = 2` from `ord_P f = 1`.** Specialises `ord_P_pow` to a
square and the value `1`, turning the natural-number scalar `2 • (1 : WithTop ℤ)`
into the integer `2`. The X-side analogue of `ord_P_cube_eq_three_of_ord_P_eq_one`,
used for `xd ^ 2` once `ord_P xd = 1` is known. -/
private theorem ord_P_sq_eq_two_of_ord_P_eq_one
    {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint} {f : C.FunctionField}
    (hf : C.ord_P P f = ((1 : ℤ) : WithTop ℤ)) :
    C.ord_P P (f ^ 2) = ((2 : ℤ) : WithTop ℤ) := by
  rw [SmoothPlaneCurve.ord_P_pow (P := P) f 2, hf]; rfl

/-- **A function whose ord is a finite integer `n` away from `0` has ord `-n`.**
If `ord_P f + n = 0` in `WithTop ℤ`, then `ord_P f = -n`. This isolates the
final integer-cancellation step shared by the exact pole-order computations
(`ord_P (translateX_xy) = -2`, `ord_P (translateY_xy) = -3`): the hypothesis
forces `ord_P f` to be finite (the `⊤` branch gives `⊤ = 0`), after which
casting back through `WithTop.coe` solves the remaining integer equation. -/
private theorem ord_P_eq_neg_of_add_coe_eq_zero
    {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint} {f : C.FunctionField}
    {n : ℤ} (h : C.ord_P P f + ((n : ℤ) : WithTop ℤ) = 0) :
    C.ord_P P f = ((-n : ℤ) : WithTop ℤ) := by
  cases ht_case : C.ord_P P f with
  | top => rw [ht_case, top_add] at h; exact absurd h (by simp)
  | coe k =>
      rw [ht_case] at h
      have h_int_eq : k + n = 0 := by
        have h_sum : ((k + n : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by
          rw [show ((k + n : ℤ) : WithTop ℤ) =
            ((k : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) from by
              push_cast; ring]
          exact h
        exact_mod_cast h_sum
      have h_k_eq : k = -n := by omega
      exact_mod_cast h_k_eq

/-- **`ord_P (translateX_xy) = -2` exact at `−T` for non-2-torsion `T`**:
combines the algebraic identity with the now-unconditional
`ord_P (x_gen − xk) = 1` to derive the exact pole order `-2`. This
matches `ordAtInfty x_gen = -2` (Lemma 1 of the pole-divisor route). -/
theorem ord_P_translateX_xy_eq_neg_two_of_non_2_tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateX_xy W xk yk) = ((-2 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns
  set yd := y_gen W - algebraMap F KE yk with hyd_def
  set xd := x_gen W - algebraMap F KE xk with hxd_def
  set a1 := algebraMap F KE W.a₁ with ha1_def
  set a2 := algebraMap F KE W.a₂ with ha2_def
  set xk' := algebraMap F KE xk with hxk'_def
  -- Order facts for the building blocks, with `ord_P xd = 1` *exact*.
  have h_xd_ord_eq : (W_smooth W).ord_P P xd = ((1 : ℤ) : WithTop ℤ) :=
    ord_P_x_gen_sub_const_eq_one_of_non_2_tor W xk yk h_ns h_not_2_tor
  have h_yd_ord : (W_smooth W).ord_P P yd = 0 :=
    ord_P_y_gen_sub_const_eq_zero W xk yk h_ns h_not_2_tor
  have h_xg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W) :=
    ord_P_x_gen_nonneg W P
  have h_a1_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a1 :=
    ord_P_algebraMap_F_nonneg W P W.a₁
  have h_a2_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a2 :=
    ord_P_algebraMap_F_nonneg W P W.a₂
  have h_xk_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P xk' :=
    ord_P_algebraMap_F_nonneg W P xk
  -- `ord_P (xd²) = 2` exact (the X-side `ord_P_pow` specialisation).
  have h_xd_sq_eq : (W_smooth W).ord_P P (xd ^ 2) = ((2 : ℤ) : WithTop ℤ) :=
    ord_P_sq_eq_two_of_ord_P_eq_one h_xd_ord_eq
  -- The quadratic combination matching `translateX_xy_mul_sq_eq` has `ord_P = 0`
  -- (dominant `yd²` term beats the `xd`-bearing remainder), via the engine.
  have h_RHS' : (W_smooth W).ord_P P
      (yd ^ 2 + (a1 * yd * xd + -((a2 + x_gen W + xk') * xd ^ 2))) = 0 :=
    ord_P_translateX_quadratic_combination_eq_zero
      h_xd_ord_eq.ge h_yd_ord h_a1_nn h_a2_nn h_xg_nn h_xk_nn
  -- Transport along the algebraic identity to `ord_P (translateX_xy · xd²) = 0`.
  have h_id : translateX_xy W xk yk * xd ^ 2 =
      yd ^ 2 + (a1 * yd * xd + -((a2 + x_gen W + xk') * xd ^ 2)) := by
    rw [hyd_def, hxd_def, ha1_def, ha2_def, hxk'_def,
        translateX_xy_mul_sq_eq W xk yk]
    ring
  have h_LHS_ord : (W_smooth W).ord_P P (translateX_xy W xk yk * xd ^ 2) = 0 :=
    h_id ▸ h_RHS'
  -- Split off the `xd²` factor (order `2`) and cancel to pin `ord_P = -2`.
  have h_split₁ : (W_smooth W).ord_P P (translateX_xy W xk yk * xd ^ 2) =
      (W_smooth W).ord_P P (translateX_xy W xk yk) +
      (W_smooth W).ord_P P (xd ^ 2) :=
    SmoothPlaneCurve.ord_P_mul (P := P) (translateX_xy W xk yk) (xd ^ 2)
  rw [h_split₁, h_xd_sq_eq] at h_LHS_ord
  exact ord_P_eq_neg_of_add_coe_eq_zero (n := 2) h_LHS_ord

/-! ### `ord_P (translateY_xy) = -3` exact at `−T` for non-2-torsion `T`

Using the algebraic identity `translateY_xy · (x_gen − xk)³ = M_y` (where
`M_y` is the explicit polynomial from `translateY_xy_mul_cube_eq`) and
the strict-non-archimedean comparison `ord_P (-yd³) = 0 < 1 ≤ ord_P
(other terms)`, we derive `ord_P (translateY_xy · xd³) = 0`, hence
`ord_P (translateY_xy) = −3`. This matches `ordAtInfty (y_gen) = -3`,
the y-side analogue of Lemma 1's pole at infinity.

Proof structure parallels `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`. -/

/-- **`ord_P (2) ≥ 0`.** The constant `2 = 1 + 1` has nonnegative order at any
smooth point, since `ord_P 1 = 0` and `ord_P` is non-archimedean. Generic
building block for bounding the orders of integer-scaled function-field
elements. -/
private theorem ord_P_two_nonneg {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} : (0 : WithTop ℤ) ≤ C.ord_P P (2 : C.FunctionField) := by
  rw [show (2 : C.FunctionField) = (1 : C.FunctionField) + 1 by ring]
  calc (0 : WithTop ℤ) = min (C.ord_P P 1) (C.ord_P P 1) := by simp
    _ ≤ _ := SmoothPlaneCurve.ord_P_add_le (P := P) _ _

/-- **A common lower bound on the orders of `a` and `b` bounds `ord_P (a + b)`.**
From `n ≤ ord_P a` and `n ≤ ord_P b`, the non-archimedean inequality gives
`n ≤ min (ord_P a) (ord_P b) ≤ ord_P (a + b)`. Generic building block for
combining order lower bounds across a sum. -/
private theorem ord_P_le_add_of_le_of_le {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a b : C.FunctionField} {n : WithTop ℤ}
    (ha : n ≤ C.ord_P P a) (hb : n ≤ C.ord_P P b) :
    n ≤ C.ord_P P (a + b) :=
  (le_min ha hb).trans (SmoothPlaneCurve.ord_P_add_le (P := P) a b)

/-- **`ord_P` of a sum of nonneg-order terms is nonneg.** The `n = 0` case of
`ord_P_le_add_of_le_of_le`. Generic building block reused throughout the
cube-combination order bounds. -/
private theorem ord_P_add_nonneg {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a b : C.FunctionField}
    (ha : (0 : WithTop ℤ) ≤ C.ord_P P a) (hb : (0 : WithTop ℤ) ≤ C.ord_P P b) :
    (0 : WithTop ℤ) ≤ C.ord_P P (a + b) :=
  ord_P_le_add_of_le_of_le ha hb

/-- **`ord_P` of a product of nonneg-order terms is nonneg.** Immediate from
additivity `ord_P (a * b) = ord_P a + ord_P b`. Generic building block. -/
private theorem ord_P_mul_nonneg {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a b : C.FunctionField}
    (ha : (0 : WithTop ℤ) ≤ C.ord_P P a) (hb : (0 : WithTop ℤ) ≤ C.ord_P P b) :
    (0 : WithTop ℤ) ≤ C.ord_P P (a * b) := by
  rw [SmoothPlaneCurve.ord_P_mul (P := P)]; simpa using add_le_add ha hb

/-- **`ord_P (2 * a) ≥ 0` when `ord_P a ≥ 0`.** Combines `ord_P_two_nonneg`
with `ord_P_mul_nonneg`; used for the `2 * a₁` and `2 * xg` factors. -/
private theorem ord_P_two_mul_nonneg {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a : C.FunctionField}
    (ha : (0 : WithTop ℤ) ≤ C.ord_P P a) :
    (0 : WithTop ℤ) ≤ C.ord_P P ((2 : C.FunctionField) * a) :=
  ord_P_mul_nonneg ord_P_two_nonneg ha

/-- **The `-(yd³)` term has order `0`.** When `ord_P yd = 0`, the leading term
`-(yd ^ 3)` of the cube combination has order exactly `0`; this is the dominant
(smallest-order) term against which all `xd`-power terms are compared. -/
private theorem ord_P_neg_yd_cube_eq_zero {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {yd : C.FunctionField} (hyd : C.ord_P P yd = 0) :
    C.ord_P P (-(yd ^ 3)) = 0 := by
  rw [SmoothPlaneCurve.ord_P_neg, SmoothPlaneCurve.ord_P_pow (P := P), hyd]; simp

/-- **The `xd`-linear term `-(2·a₁·yd²·xd)` has order `≥ 1`.** Its order is
`ord_P (2 * a₁) + ord_P (yd²) + ord_P xd = (≥0) + 0 + 1`, using `ord_P yd = 0`
and `ord_P xd = 1`. The first of the three `xd`-power bounds. -/
private theorem one_le_ord_P_xd_linear_term {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {xd yd a1 : C.FunctionField}
    (hxd : C.ord_P P xd = ((1 : ℤ) : WithTop ℤ)) (hyd : C.ord_P P yd = 0)
    (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1) :
    ((1 : ℤ) : WithTop ℤ) ≤
      C.ord_P P (-((2 : C.FunctionField) * a1 * yd ^ 2 * xd)) := by
  have h_yd_sq : C.ord_P P (yd ^ 2) = 0 := by
    rw [SmoothPlaneCurve.ord_P_pow (P := P) yd 2, hyd]; simp
  rw [SmoothPlaneCurve.ord_P_neg, SmoothPlaneCurve.ord_P_mul (P := P) _ xd,
    SmoothPlaneCurve.ord_P_mul (P := P) _ (yd ^ 2), h_yd_sq, add_zero, hxd]
  simpa using add_le_add (ord_P_two_mul_nonneg ha1) (le_refl ((1 : ℤ) : WithTop ℤ))

/-- **The `xd²` coefficient `yd·(a₂+2·xg+xk') - a₁²·yd` has order `≥ 0`.**
A sum/product of nonneg-order pieces (using `ord_P yd = 0`): the factor
`a₂ + 2·xg + xk'` is nonneg, `yd` times it is nonneg, and `a₁²·yd` is nonneg. -/
private theorem ord_P_xd_quadratic_coef_nonneg {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {yd a1 a2 xk' xg : C.FunctionField}
    (hyd : C.ord_P P yd = 0) (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1)
    (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2) (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk')
    (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg) :
    (0 : WithTop ℤ) ≤
      C.ord_P P (yd * (a2 + (2 : C.FunctionField) * xg + xk') - a1 ^ 2 * yd) := by
  have h_sum_nn : (0 : WithTop ℤ) ≤
      C.ord_P P (a2 + (2 : C.FunctionField) * xg + xk') :=
    ord_P_add_nonneg (ord_P_add_nonneg ha2 (ord_P_two_mul_nonneg hxg)) hxk'
  have h_mul1' : (0 : WithTop ℤ) ≤
      C.ord_P P (yd * (a2 + (2 : C.FunctionField) * xg + xk')) := by
    rw [SmoothPlaneCurve.ord_P_mul (P := P), hyd, zero_add]; exact h_sum_nn
  have h_a1sq_yd_nn : (0 : WithTop ℤ) ≤ C.ord_P P (-(a1 ^ 2 * yd)) := by
    rw [SmoothPlaneCurve.ord_P_neg, SmoothPlaneCurve.ord_P_mul (P := P), hyd,
      add_zero, SmoothPlaneCurve.ord_P_pow (P := P)]
    simpa using nsmul_le_nsmul_right ha1 2
  rw [show yd * (a2 + (2 : C.FunctionField) * xg + xk') - a1 ^ 2 * yd =
      yd * (a2 + (2 : C.FunctionField) * xg + xk') + -(a1 ^ 2 * yd) by ring]
  exact ord_P_add_nonneg h_mul1' h_a1sq_yd_nn

/-- **The `xd²` term `(yd·(a₂+2·xg+xk') - a₁²·yd)·xd²` has order `≥ 2`.**
Combines the nonneg coefficient (`ord_P_xd_quadratic_coef_nonneg`) with
`ord_P (xd²) = 2`. The second of the three `xd`-power bounds. -/
private theorem two_le_ord_P_xd_quadratic_term {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {xd yd a1 a2 xk' xg : C.FunctionField}
    (hxd : C.ord_P P xd = ((1 : ℤ) : WithTop ℤ)) (hyd : C.ord_P P yd = 0)
    (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1) (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2)
    (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk') (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg) :
    ((2 : ℤ) : WithTop ℤ) ≤
      C.ord_P P
        ((yd * (a2 + (2 : C.FunctionField) * xg + xk') - a1 ^ 2 * yd) * xd ^ 2) := by
  have h_xd_sq_eq : C.ord_P P (xd ^ 2) = ((2 : ℤ) : WithTop ℤ) := by
    rw [SmoothPlaneCurve.ord_P_pow (P := P) xd 2, hxd]; rfl
  rw [SmoothPlaneCurve.ord_P_mul (P := P), h_xd_sq_eq]
  calc ((2 : ℤ) : WithTop ℤ) = 0 + ((2 : ℤ) : WithTop ℤ) := by rw [zero_add]
    _ ≤ _ := add_le_add
      (ord_P_xd_quadratic_coef_nonneg hyd ha1 ha2 hxk' hxg) (le_refl _)

/-- **The `xd³` coefficient `-yg + a₁·(a₂+xg+xk') - a₃` has order `≥ 0`.**
A sum of nonneg-order pieces: `-yg`, the product `a₁·(a₂+xg+xk')`, and `-a₃`. -/
private theorem ord_P_xd_cubic_coef_nonneg {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a1 a2 a3 xk' xg yg : C.FunctionField}
    (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1) (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2)
    (ha3 : (0 : WithTop ℤ) ≤ C.ord_P P a3) (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk')
    (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg) (hyg : (0 : WithTop ℤ) ≤ C.ord_P P yg) :
    (0 : WithTop ℤ) ≤ C.ord_P P (-yg + a1 * (a2 + xg + xk') - a3) := by
  have h_a2xxk_nn : (0 : WithTop ℤ) ≤ C.ord_P P (a2 + xg + xk') :=
    ord_P_add_nonneg (ord_P_add_nonneg ha2 hxg) hxk'
  have h_a1mul_nn : (0 : WithTop ℤ) ≤ C.ord_P P (a1 * (a2 + xg + xk')) :=
    ord_P_mul_nonneg ha1 h_a2xxk_nn
  rw [show -yg + a1 * (a2 + xg + xk') - a3 =
      -yg + a1 * (a2 + xg + xk') + -a3 by ring]
  exact ord_P_add_nonneg
    (ord_P_add_nonneg (by rwa [SmoothPlaneCurve.ord_P_neg]) h_a1mul_nn)
    (by rwa [SmoothPlaneCurve.ord_P_neg])

/-- **The `xd³` term `(-yg + a₁·(a₂+xg+xk') - a₃)·xd³` has order `≥ 3`.**
Combines the nonneg coefficient (`ord_P_xd_cubic_coef_nonneg`) with
`ord_P (xd³) = 3`. The third of the three `xd`-power bounds. -/
private theorem three_le_ord_P_xd_cubic_term {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {xd a1 a2 a3 xk' xg yg : C.FunctionField}
    (hxd : C.ord_P P xd = ((1 : ℤ) : WithTop ℤ)) (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1)
    (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2) (ha3 : (0 : WithTop ℤ) ≤ C.ord_P P a3)
    (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk') (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg)
    (hyg : (0 : WithTop ℤ) ≤ C.ord_P P yg) :
    ((3 : ℤ) : WithTop ℤ) ≤
      C.ord_P P ((-yg + a1 * (a2 + xg + xk') - a3) * xd ^ 3) := by
  have h_xd_cube_eq : C.ord_P P (xd ^ 3) = ((3 : ℤ) : WithTop ℤ) := by
    rw [SmoothPlaneCurve.ord_P_pow (P := P) xd 3, hxd]; rfl
  rw [SmoothPlaneCurve.ord_P_mul (P := P), h_xd_cube_eq]
  calc ((3 : ℤ) : WithTop ℤ) = 0 + ((3 : ℤ) : WithTop ℤ) := by rw [zero_add]
    _ ≤ _ := add_le_add
      (ord_P_xd_cubic_coef_nonneg ha1 ha2 ha3 hxk' hxg hyg) (le_refl _)

/-- **Abstract `ord_P`-engine for the `translateY_xy` cube identity.**
Given a smooth point `P` of a smooth plane curve `C` and function-field
elements `xd` (with `ord_P xd = 1`), `yd` (with `ord_P yd = 0`) and
nonneg-order elements `a1 a2 a3 xk' xg yg`, the explicit cubic combination
matching the right side of `translateY_xy_mul_cube_eq` has `ord_P = 0`.
This isolates the purely valuation-theoretic arithmetic of
`ord_P_translateY_xy_eq_neg_three_of_non_2_tor` from the curve-specific
algebraic identity, keeping each declaration within the default heartbeat
budget. -/
private theorem ord_P_translateY_cube_combination_eq_zero
    (C : Curves.SmoothPlaneCurve F) (P : C.SmoothPoint)
    (xd yd a1 a2 a3 xk' xg yg : C.FunctionField)
    (hxd : C.ord_P P xd = ((1 : ℤ) : WithTop ℤ))
    (hyd : C.ord_P P yd = 0)
    (ha1 : (0 : WithTop ℤ) ≤ C.ord_P P a1)
    (ha2 : (0 : WithTop ℤ) ≤ C.ord_P P a2)
    (ha3 : (0 : WithTop ℤ) ≤ C.ord_P P a3)
    (hxk' : (0 : WithTop ℤ) ≤ C.ord_P P xk')
    (hxg : (0 : WithTop ℤ) ≤ C.ord_P P xg)
    (hyg : (0 : WithTop ℤ) ≤ C.ord_P P yg) :
    C.ord_P P
      (-(yd ^ 3) +
        (-((2 : C.FunctionField) * a1 * yd ^ 2 * xd) +
          ((yd * (a2 + (2 : C.FunctionField) * xg + xk') - a1 ^ 2 * yd) * xd ^ 2 +
            (-yg + a1 * (a2 + xg + xk') - a3) * xd ^ 3))) = 0 := by
  -- Order facts for the four monomials, via the per-term helpers above.
  have h_neg_yd_cube : C.ord_P P (-(yd ^ 3)) = 0 := ord_P_neg_yd_cube_eq_zero hyd
  have h_T2 : ((1 : ℤ) : WithTop ℤ) ≤
      C.ord_P P (-((2 : C.FunctionField) * a1 * yd ^ 2 * xd)) :=
    one_le_ord_P_xd_linear_term hxd hyd ha1
  have h_T3 : ((2 : ℤ) : WithTop ℤ) ≤
      C.ord_P P
        ((yd * (a2 + (2 : C.FunctionField) * xg + xk') - a1 ^ 2 * yd) * xd ^ 2) :=
    two_le_ord_P_xd_quadratic_term hxd hyd ha1 ha2 hxk' hxg
  have h_T4 : ((3 : ℤ) : WithTop ℤ) ≤
      C.ord_P P ((-yg + a1 * (a2 + xg + xk') - a3) * xd ^ 3) :=
    three_le_ord_P_xd_cubic_term hxd ha1 ha2 ha3 hxk' hxg hyg
  -- Name the three xd-power terms and bound their sum below by `1`.
  set B : C.FunctionField := -((2 : C.FunctionField) * a1 * yd ^ 2 * xd) with hB
  set T3 : C.FunctionField :=
    (yd * (a2 + (2 : C.FunctionField) * xg + xk') - a1 ^ 2 * yd) * xd ^ 2 with hT3
  set T4 : C.FunctionField :=
    (-yg + a1 * (a2 + xg + xk') - a3) * xd ^ 3 with hT4
  have h_T234 : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P (B + (T3 + T4)) := by
    have h_T3' : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P T3 :=
      le_trans (by exact_mod_cast (show (1 : ℤ) ≤ 2 by norm_num)) h_T3
    have h_T4' : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P T4 :=
      le_trans (by exact_mod_cast (show (1 : ℤ) ≤ 3 by norm_num)) h_T4
    have h_T34 : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P (T3 + T4) :=
      ord_P_le_add_of_le_of_le h_T3' h_T4'
    exact ord_P_le_add_of_le_of_le h_T2 h_T34
  -- The `-(yd³)` term dominates: it has strictly smaller order than the rest.
  have h_strict : C.ord_P P (-(yd ^ 3)) < C.ord_P P (B + (T3 + T4)) := by
    rw [h_neg_yd_cube]
    exact lt_of_lt_of_le (by exact_mod_cast (show (0 : ℤ) < 1 by norm_num)) h_T234
  exact (SmoothPlaneCurve.ord_P_add_eq_of_lt h_strict).trans h_neg_yd_cube

/-- **`y_gen W` has nonneg ord at any smooth point** (it is in the image of the
coordinate ring, being `algebraMap R KE (AdjoinRoot.root …)`). The y-side
companion to `ord_P_x_gen_nonneg`, used wherever `ord_P (y_gen) ≥ 0` is needed
(e.g. as the `hyg` hypothesis of `ord_P_translateY_cube_combination_eq_zero`). -/
private theorem ord_P_y_gen_nonneg (P : (W_smooth W).SmoothPoint) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (y_gen W) :=
  ord_P_algebraMap_R_nonneg W P _

/-- **`ord_P (f ^ 3) = 3` from `ord_P f = 1`.** Specialises `ord_P_pow` to a
cube and the value `1`, turning the natural-number scalar `3 • (1 : WithTop ℤ)`
into the integer `3`. Used for `xd ^ 3` once `ord_P xd = 1` is known. -/
private theorem ord_P_cube_eq_three_of_ord_P_eq_one
    {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint} {f : C.FunctionField}
    (hf : C.ord_P P f = ((1 : ℤ) : WithTop ℤ)) :
    C.ord_P P (f ^ 3) = ((3 : ℤ) : WithTop ℤ) := by
  rw [SmoothPlaneCurve.ord_P_pow (P := P) f 3, hf]; rfl

/-- **`ord_P (translateY_xy) = -3` exact at `−T` for non-2-torsion `T`**:
combines the algebraic identity `translateY_xy_mul_cube_eq` with the
ord-vanishing facts `ord_P (yd) = 0` and `ord_P (xd) = 1` to derive the
exact pole order `-3`. The y-side analogue of
`ord_P_translateX_xy_eq_neg_two_of_non_2_tor`. -/
theorem ord_P_translateY_xy_eq_neg_three_of_non_2_tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateY_xy W xk yk) = ((-3 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns
  set yd := y_gen W - algebraMap F KE yk with hyd_def
  set xd := x_gen W - algebraMap F KE xk with hxd_def
  set a1 := algebraMap F KE W.a₁ with ha1_def
  set a2 := algebraMap F KE W.a₂ with ha2_def
  set a3 := algebraMap F KE W.a₃ with ha3_def
  set xk' := algebraMap F KE xk with hxk'_def
  have h_xd_ord_eq : (W_smooth W).ord_P P xd = ((1 : ℤ) : WithTop ℤ) :=
    ord_P_x_gen_sub_const_eq_one_of_non_2_tor W xk yk h_ns h_not_2_tor
  have h_yd_ord : (W_smooth W).ord_P P yd = 0 :=
    ord_P_y_gen_sub_const_eq_zero W xk yk h_ns h_not_2_tor
  have h_xg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W) :=
    ord_P_x_gen_nonneg W P
  have h_a1_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a1 :=
    ord_P_algebraMap_F_nonneg W P W.a₁
  have h_a2_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a2 :=
    ord_P_algebraMap_F_nonneg W P W.a₂
  have h_a3_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a3 :=
    ord_P_algebraMap_F_nonneg W P W.a₃
  have h_xk_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P xk' :=
    ord_P_algebraMap_F_nonneg W P xk
  have h_yg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (y_gen W) :=
    ord_P_y_gen_nonneg W P
  have h_xd_cube_eq : (W_smooth W).ord_P P (xd^3) = ((3 : ℤ) : WithTop ℤ) :=
    ord_P_cube_eq_three_of_ord_P_eq_one h_xd_ord_eq
  have h_RHS' : (W_smooth W).ord_P P
      (-(yd^3) +
        (-((2 : KE) * a1 * yd^2 * xd) +
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
            (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3))) = 0 :=
    ord_P_translateY_cube_combination_eq_zero (W_smooth W) P xd yd a1 a2 a3 xk'
      (x_gen W) (y_gen W) h_xd_ord_eq h_yd_ord h_a1_nn h_a2_nn h_a3_nn h_xk_nn
      h_xg_nn h_yg_nn
  have h_id : translateY_xy W xk yk * xd^3 =
      -(yd^3) +
        (-((2 : KE) * a1 * yd^2 * xd) +
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
            (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3)) := by
    rw [hyd_def, hxd_def, ha1_def, ha2_def, ha3_def, hxk'_def,
        translateY_xy_mul_cube_eq W xk yk]
    ring
  have h_LHS_ord : (W_smooth W).ord_P P (translateY_xy W xk yk * xd^3) = 0 :=
    h_id ▸ h_RHS'
  have h_split₁ : (W_smooth W).ord_P P (translateY_xy W xk yk * xd^3) =
      (W_smooth W).ord_P P (translateY_xy W xk yk) +
      (W_smooth W).ord_P P (xd^3) :=
    SmoothPlaneCurve.ord_P_mul (P := P) (translateY_xy W xk yk) (xd^3)
  rw [h_split₁, h_xd_cube_eq] at h_LHS_ord
  exact ord_P_eq_neg_of_add_coe_eq_zero (n := 3) h_LHS_ord

/-! ### `translateX_xy_transcendental` (axiom-clean for non-2-torsion `T`)

Combines `ord_P_translateX_xy_lt_zero` with `transcendental_of_neg_ord_P`
to give the substantive transcendence statement for the translation x-coord
over `F`. -/

/-- **`translateX_xy` is transcendental over `F`** for non-2-torsion
`T = (xk, yk)`. Direct from the negative ord at `−T` (substantive content
in `ord_P_translateX_xy_lt_zero`) via the algebraic-Liouville
contrapositive (`transcendental_of_neg_ord_P`). -/
theorem translateX_xy_transcendental
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    Transcendental F (translateX_xy W xk yk) :=
  SmoothPlaneCurve.transcendental_of_neg_ord_P
    (ord_P_translateX_xy_lt_zero W xk yk h_ns h_not_2_tor)

/-! ### Unconditional `translateAlgHom` for non-2-torsion `T`

The existing `translateAlgHom` in `EC/Translation.lean` takes the
base-hom injectivity as an explicit hypothesis. For non-2-torsion
`T = (xk, yk)`, this is dischargeable unconditionally:
* Equation: from `h_ns.1`.
* TranslateNonInverse: from `x_gen` transcendence (rules out `x_gen = xk`).
* Base-hom injectivity: from `translateX_xy_transcendental`. -/

/-- **Unconditional `translateAlgHom`** for non-2-torsion `T = (xk, yk)`:
all witnesses discharged. -/
noncomputable def translateAlgHom_of_nonTorsion
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    KE →ₐ[F] KE :=
  translateAlgHom W xk yk h_ns.1
    (fun h ↦ x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h.1))
    (translateBaseHom_injective_of_transcendental W xk yk
      (translateX_xy_transcendental W xk yk h_ns h_not_2_tor))

/-! ### Inverse via translation by `−T`

For non-2-torsion `T`, the inverse of `translateAlgHom_of_nonTorsion W T`
is `translateAlgHom_of_nonTorsion W (−T)`. The hypotheses for `−T`:
* Nonsingular at `(xk, negY xk yk)`: from `Affine.nonsingular_neg`.
* `−T` non-2-torsion (i.e., `negY xk yk ≠ negY xk (negY xk yk)`):
  reduces to `negY xk yk ≠ yk` since `negY ∘ negY = id`. -/

/-- Helper: `negY xk (negY xk yk) = yk` (the negation involution). -/
private theorem negY_negY_eq (xk yk : F) :
    W.toAffine.negY xk (W.toAffine.negY xk yk) = yk := by
  unfold WeierstrassCurve.Affine.negY
  ring

/-- The unconditional translation algebra hom for `−T = (xk, negY xk yk)`,
when `T = (xk, yk)` is non-2-torsion. -/
noncomputable def translateAlgHom_of_nonTorsion_neg
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    KE →ₐ[F] KE :=
  translateAlgHom_of_nonTorsion W xk (W.toAffine.negY xk yk)
    ((Affine.nonsingular_neg xk yk).mpr h_ns)
    (by rw [negY_negY_eq W xk yk]; exact h_not_2_tor.symm)

/-! ### Action evaluation on generators

Compute `translateAlgHom_of_nonTorsion T (x_gen W)` and on `y_gen W`. -/

/-- `translateAlgHom_of_nonTorsion T x_gen = translateX_xy T` (definitional).
The lift via `IsFractionRing.liftAlgHom` of `translateCoordAlgHom`, which
on `algebraMap (Polynomial F) R Polynomial.X` gives `translateBaseHom X =
translateX_xy`. -/
theorem translateAlgHom_apply_x_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor (x_gen W) =
      translateX_xy W xk yk := by
  let hxy : TranslateNonInverse W xk yk :=
    fun h ↦ x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h.1)
  unfold translateAlgHom_of_nonTorsion translateAlgHom
  unfold x_gen
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change (translateCoordAlgHom W xk yk h_ns.1 hxy).toRingHom
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) =
    translateX_xy W xk yk
  change translateCoordRingHom W xk yk h_ns.1 hxy
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) =
    translateX_xy W xk yk
  unfold translateCoordRingHom
  change AdjoinRoot.lift (translateBaseHom W xk yk) (translateY_xy W xk yk)
      (translate_poly_eval₂_zero W xk yk h_ns.1 hxy)
      (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) =
    translateX_xy W xk yk
  rw [AdjoinRoot.lift_of]
  simp [translateBaseHom, Polynomial.eval₂_X]

/-! ### The lifted point `T_lift` on `W_KE`

Bridges `T = (xk, yk) ∈ E(F)` to `T_lift = (algebraMap xk, algebraMap yk) ∈ E(K(E))`
as a `(W_KE W).toAffine.Point`. Used to invoke Mathlib's `Affine.Point`
group law on the generic point. -/

/-- `T = (xk, yk) ∈ E(F)` lifted to a point on `W_KE` over `K(E)`. -/
noncomputable def liftSomePoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_KE W).toAffine.Point :=
  Affine.Point.some (algebraMap F KE xk) (algebraMap F KE yk)
    ((WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine)
      (RingHom.injective (algebraMap F KE)) xk yk).mpr h_ns)

/-- `−T` lifted as `Affine.Point.some` (rather than via `Neg`). The
explicit form makes pattern-matching with `add_some` cleaner. -/
noncomputable def liftSomePoint_neg
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_KE W).toAffine.Point :=
  liftSomePoint W xk (W.toAffine.negY xk yk)
    ((Affine.nonsingular_neg xk yk).mpr h_ns)

/-! ### `T_lift + (−T_lift) = 0` (Silverman III.5: translation is a group action)

Direct computation via `Affine.Point.add_of_Y_eq`: when `x_T = x_{-T}` and
`y_T = negY x_{-T} y_{-T}` (which holds since `negY ∘ negY = id` on the
y-coordinate), the sum is the zero point. -/

/-- `negY` commutes with `algebraMap` for the `W_KE` base change. -/
private theorem WKE_negY_algebraMap (xk yk' : F) :
    (W_KE W).toAffine.negY (algebraMap F KE xk) (algebraMap F KE yk') =
      algebraMap F KE (W.toAffine.negY xk yk') := by
  unfold WeierstrassCurve.Affine.negY
  change -(algebraMap F KE yk') - (W_KE W).a₁ * (algebraMap F KE xk) -
    (W_KE W).a₃ = _
  change -(algebraMap F KE yk') - algebraMap F KE W.a₁ * (algebraMap F KE xk) -
    algebraMap F KE W.a₃ = _
  rw [← map_mul, ← map_neg, ← _root_.map_sub, ← _root_.map_sub]

theorem liftSomePoint_add_neg_eq_zero
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    liftSomePoint W xk yk h_ns +
        liftSomePoint_neg W xk yk h_ns = 0 := by
  unfold liftSomePoint liftSomePoint_neg liftSomePoint
  apply Affine.Point.add_of_Y_eq
  · rfl
  · rw [WKE_negY_algebraMap, negY_negY_eq]

/-- **Round-trip at the `Affine.Point` level**:
`P_gen + T_lift + (−T_lift) = P_gen`. Direct application of Mathlib's
group law via `add_assoc` + `liftSomePoint_add_neg_eq_zero` + `add_zero`. -/
theorem genericPoint_round_trip
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (genericPoint W + liftSomePoint W xk yk h_ns) +
        liftSomePoint_neg W xk yk h_ns = genericPoint W := by
  rw [add_assoc, liftSomePoint_add_neg_eq_zero, add_zero]

/-- `genericPoint + liftSomePoint T = some translateX_xy_T translateY_xy_T h`.
Direct via `add_of_X_ne` (the x-coords differ since `x_gen` is transcendental). -/
theorem genericPoint_add_liftSomePoint
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    genericPoint W + liftSomePoint W xk yk h_ns =
      Affine.Point.some (translateX_xy W xk yk) (translateY_xy W xk yk)
        (Affine.nonsingular_add (generic_nonsingular W)
          ((WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine)
            (RingHom.injective (algebraMap F KE)) xk yk).mpr h_ns)
          (fun hxy ↦ x_gen_sub_const_ne_zero W xk
            (sub_eq_zero.mpr hxy.left))) := by
  unfold genericPoint liftSomePoint
  exact Affine.Point.add_of_X_ne (fun h_eq ↦
    x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h_eq))

/-- `genericPoint + liftSomePoint_neg T` = `some translateX_xy_neg translateY_xy_neg h`,
where `translateX_xy_neg` is `translateX_xy` with `(xk, yk) ↦ (xk, negY xk yk)`. -/
theorem genericPoint_add_liftSomePoint_neg
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    genericPoint W + liftSomePoint_neg W xk yk h_ns =
      Affine.Point.some
        (translateX_xy W xk (W.toAffine.negY xk yk))
        (translateY_xy W xk (W.toAffine.negY xk yk))
        (Affine.nonsingular_add (generic_nonsingular W)
          ((WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine)
            (RingHom.injective (algebraMap F KE))
            xk (W.toAffine.negY xk yk)).mpr
              ((Affine.nonsingular_neg xk yk).mpr h_ns))
          (fun hxy ↦ x_gen_sub_const_ne_zero W xk
            (sub_eq_zero.mpr hxy.left))) :=
  genericPoint_add_liftSomePoint W xk (W.toAffine.negY xk yk)
    ((Affine.nonsingular_neg xk yk).mpr h_ns)

/-! ### `translateX_xy(-T) ≠ algebraMap xk` for non-2-torsion T

Required for the second addition (translation by T applied to `(translateX_xy(-T),
translateY_xy(-T))`) to use `add_of_X_ne` rather than degenerate to zero. -/

/-- For non-2-torsion `T = (xk, yk)`, `translateX_xy W xk (negY xk yk)` is
transcendental over `F`. (`-T = (xk, negY xk yk)` is also non-2-torsion since
`negY xk (negY xk yk) = yk ≠ negY xk yk`.) -/
theorem translateX_xy_neg_transcendental
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    Transcendental F (translateX_xy W xk (W.toAffine.negY xk yk)) :=
  translateX_xy_transcendental W xk (W.toAffine.negY xk yk)
    ((Affine.nonsingular_neg xk yk).mpr h_ns)
    (by rw [negY_negY_eq W xk yk]; exact h_not_2_tor.symm)

/-- `translateX_xy(-T) ≠ algebraMap F KE xk` for non-2-torsion `T`.
Direct from transcendence. -/
theorem translateX_xy_neg_ne_algebraMap
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateX_xy W xk (W.toAffine.negY xk yk) ≠ algebraMap F KE xk := by
  intro h_eq
  apply translateX_xy_neg_transcendental W xk yk h_ns h_not_2_tor
  refine ⟨Polynomial.X - Polynomial.C xk, Polynomial.X_sub_C_ne_zero xk, ?_⟩
  rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]

/-! ### `translateAlgHom_neg` evaluation on x_gen

`σ(x_gen) = translateX_xy W xk (negY xk yk)` — used to identify σ-images
with translation by −T at the K(E) level. -/

/-- Evaluation of `translateAlgHom_of_nonTorsion_neg` on `x_gen`. -/
theorem translateAlgHom_neg_apply_x_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor (x_gen W) =
      translateX_xy W xk (W.toAffine.negY xk yk) := by
  unfold translateAlgHom_of_nonTorsion_neg
  exact translateAlgHom_apply_x_gen W xk (W.toAffine.negY xk yk) _ _

/-- Evaluation of `translateAlgHom_of_nonTorsion` on `y_gen`. The image is
`translateY_xy W xk yk`. -/
theorem translateAlgHom_apply_y_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor (y_gen W) =
      translateY_xy W xk yk := by
  let hxy : TranslateNonInverse W xk yk :=
    fun h ↦ x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h.1)
  unfold translateAlgHom_of_nonTorsion translateAlgHom
  unfold y_gen
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change (translateCoordAlgHom W xk yk h_ns.1 hxy).toRingHom
      (AdjoinRoot.root W.toAffine.polynomial) =
    translateY_xy W xk yk
  change translateCoordRingHom W xk yk h_ns.1 hxy
      (AdjoinRoot.root W.toAffine.polynomial) =
    translateY_xy W xk yk
  unfold translateCoordRingHom
  exact AdjoinRoot.lift_root _

/-- Evaluation of `translateAlgHom_of_nonTorsion_neg` on `y_gen`. -/
theorem translateAlgHom_neg_apply_y_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor (y_gen W) =
      translateY_xy W xk (W.toAffine.negY xk yk) := by
  unfold translateAlgHom_of_nonTorsion_neg
  exact translateAlgHom_apply_y_gen W xk (W.toAffine.negY xk yk) _ _

/-! ### Round-trip on `x_gen` — Silverman III.4.10(a) substantive content

`σ(τ(x_gen)) = x_gen` where `τ = translateAlgHom_of_nonTorsion T`,
`σ = translateAlgHom_of_nonTorsion_neg T`. This is the curve group-law
identity `(P + T) − T = P` lifted to the function-field algebra-hom level.

Proof structure: σ acts as a ring hom on K(E). Apply σ to `translateX_xy T =
addX(x_gen, xk', slope_T)`. By ring-hom commutation with `addX` (which is
just a polynomial in the operands), this gives
`addX(σ x_gen, σ xk', σ slope_T) = addX(translateX_xy(-T), xk', σ slope_T)`.

For the slope: `σ slope_T = (σ y_gen − σ yk')/(σ x_gen − σ xk') =
(translateY_xy(-T) − yk')/(translateX_xy(-T) − xk')`. This is *exactly*
the slope of the line from `(translateX_xy(-T), translateY_xy(-T))` to
`(xk, yk)` — the slope used in the Affine.Point computation `(P_neg +
T_lift)`, where `P_neg = some translateX_xy(-T) translateY_xy(-T) ?h`.

So `σ(translateX_xy T) = (P_neg + T_lift).x`. By Mathlib's group law
`(gen + neg_T_lift) + T_lift = gen` (i.e., `P_neg + T_lift = gen`),
extracting the x-coord gives `(P_neg + T_lift).x = x_gen`. -/

/-- σ commutes with `(W_KE).addX` after F-constant fixing. -/
private theorem σ_commutes_addX
    {σ : KE →ₐ[F] KE} (a b ℓ : KE) :
    σ ((W_KE W).toAffine.addX a b ℓ) =
      (W_KE W).toAffine.addX (σ a) (σ b) (σ ℓ) := by
  unfold WeierstrassCurve.Affine.addX
  have h_a1 : σ ((W_KE W).a₁) = (W_KE W).a₁ := by
    change σ (algebraMap F KE W.a₁) = algebraMap F KE W.a₁
    exact σ.commutes _
  have h_a2 : σ ((W_KE W).a₂) = (W_KE W).a₂ := by
    change σ (algebraMap F KE W.a₂) = algebraMap F KE W.a₂
    exact σ.commutes _
  rw [_root_.map_sub, _root_.map_sub, _root_.map_sub, _root_.map_add,
      map_pow, map_mul, h_a1, h_a2]

/-- σ commutes with `(W_KE).negY` after F-constant fixing. -/
private theorem σ_commutes_negY
    {σ : KE →ₐ[F] KE} (x y : KE) :
    σ ((W_KE W).toAffine.negY x y) =
      (W_KE W).toAffine.negY (σ x) (σ y) := by
  unfold WeierstrassCurve.Affine.negY
  have h_a1 : σ ((W_KE W).a₁) = (W_KE W).a₁ := by
    change σ (algebraMap F KE W.a₁) = algebraMap F KE W.a₁
    exact σ.commutes _
  have h_a3 : σ ((W_KE W).a₃) = (W_KE W).a₃ := by
    change σ (algebraMap F KE W.a₃) = algebraMap F KE W.a₃
    exact σ.commutes _
  rw [_root_.map_sub, _root_.map_sub, _root_.map_neg, map_mul, h_a1, h_a3]

/-- σ commutes with `(W_KE).negAddY` after F-constant fixing. -/
private theorem σ_commutes_negAddY
    {σ : KE →ₐ[F] KE} (a b y₁ ℓ : KE) :
    σ ((W_KE W).toAffine.negAddY a b y₁ ℓ) =
      (W_KE W).toAffine.negAddY (σ a) (σ b) (σ y₁) (σ ℓ) := by
  unfold WeierstrassCurve.Affine.negAddY
  rw [_root_.map_add, _root_.map_mul, _root_.map_sub, σ_commutes_addX]

/-- σ commutes with `(W_KE).addY` after F-constant fixing. -/
private theorem σ_commutes_addY
    {σ : KE →ₐ[F] KE} (a b y₁ ℓ : KE) :
    σ ((W_KE W).toAffine.addY a b y₁ ℓ) =
      (W_KE W).toAffine.addY (σ a) (σ b) (σ y₁) (σ ℓ) := by
  unfold WeierstrassCurve.Affine.addY
  rw [σ_commutes_negY, σ_commutes_addX, σ_commutes_negAddY]

/-- σ commutes with `(W_KE).slope` when `x₁ ≠ x₂` (the secant case). -/
private theorem σ_commutes_slope_of_X_ne
    {σ : KE →ₐ[F] KE} {a b y₁ y₂ : KE} (hx : a ≠ b) (hx_σ : σ a ≠ σ b) :
    σ ((W_KE W).toAffine.slope a b y₁ y₂) =
      (W_KE W).toAffine.slope (σ a) (σ b) (σ y₁) (σ y₂) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx,
      WeierstrassCurve.Affine.slope_of_X_ne hx_σ,
      _root_.map_div₀, _root_.map_sub, _root_.map_sub]

/-- **Round-trip on `x_gen`** — Silverman III.4.10(a) at the algebra-hom level.
`σ(τ(x_gen)) = x_gen` where τ = translation by T, σ = translation by −T.

Proof: τ(x_gen) = translateX_xy T. Apply σ; by ring-hom and slope identities,
σ(translateX_xy T) = (W_KE).addX (translateX_xy(-T)) xk' slope where slope is
the secant slope from (translateX_xy(-T), translateY_xy(-T)) to (xk, yk).

This equals (P_neg + T_lift).x where P_neg = some translateX_xy(-T)
translateY_xy(-T). By Mathlib's group law, P_neg + T_lift = (gen + neg_T) +
T_lift = gen + (neg_T + T) = gen. Extracting the x-coord: P_neg + T_lift = gen
gives addX' = x_gen. -/
theorem translateAlgHom_round_trip_x_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor
        (translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor (x_gen W)) =
      x_gen W := by
  rw [translateAlgHom_apply_x_gen W xk yk h_ns h_not_2_tor]
  set σ := translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor
  have hσx : σ (x_gen W) = translateX_xy W xk (W.toAffine.negY xk yk) :=
    translateAlgHom_neg_apply_x_gen W xk yk h_ns h_not_2_tor
  have hσy : σ (y_gen W) = translateY_xy W xk (W.toAffine.negY xk yk) :=
    translateAlgHom_neg_apply_y_gen W xk yk h_ns h_not_2_tor
  unfold translateX_xy
  rw [σ_commutes_addX W (x_gen W) (algebraMap F KE xk)
        (translateSlope_xy W xk yk)]
  rw [σ.commutes xk, hσx]
  have hx_ne : x_gen W ≠ algebraMap F KE xk := fun h ↦
    x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h)
  have hx_σ_ne : σ (x_gen W) ≠ algebraMap F KE xk := by
    rw [hσx]
    exact translateX_xy_neg_ne_algebraMap W xk yk h_ns h_not_2_tor
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk) := by
    rwa [σ.commutes]
  have h_slope_eq : σ (translateSlope_xy W xk yk) =
      (W_KE W).toAffine.slope (translateX_xy W xk (W.toAffine.negY xk yk))
        (algebraMap F KE xk)
        (translateY_xy W xk (W.toAffine.negY xk yk)) (algebraMap F KE yk) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk)
        (y_gen W) (algebraMap F KE yk)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk, σ.commutes yk, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint_neg W xk yk h_ns) +
      liftSomePoint W xk yk h_ns = genericPoint W := by
    rw [add_assoc]
    rw [add_comm (liftSomePoint_neg W xk yk h_ns)
        (liftSomePoint W xk yk h_ns)]
    rw [liftSomePoint_add_neg_eq_zero, add_zero]
  have h_ne_2 : translateX_xy W xk (W.toAffine.negY xk yk) ≠ algebraMap F KE xk :=
    translateX_xy_neg_ne_algebraMap W xk yk h_ns h_not_2_tor
  rw [genericPoint_add_liftSomePoint_neg W xk yk h_ns] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_ne_2)] at h_gen_eq
  unfold genericPoint at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.1

/-- **Round-trip on `y_gen`** — Silverman III.4.10(a) at the algebra-hom level.
`σ(τ(y_gen)) = y_gen` where τ = translation by T, σ = translation by −T.

Same group-law identity as `_x_gen`, extracting the y-coordinate of the
sum `(P_neg + T_lift)` via `Point.some.injEq.2.1` rather than `.1`. -/
theorem translateAlgHom_round_trip_y_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor
        (translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor (y_gen W)) =
      y_gen W := by
  rw [translateAlgHom_apply_y_gen W xk yk h_ns h_not_2_tor]
  set σ := translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor
  have hσx : σ (x_gen W) = translateX_xy W xk (W.toAffine.negY xk yk) :=
    translateAlgHom_neg_apply_x_gen W xk yk h_ns h_not_2_tor
  have hσy : σ (y_gen W) = translateY_xy W xk (W.toAffine.negY xk yk) :=
    translateAlgHom_neg_apply_y_gen W xk yk h_ns h_not_2_tor
  unfold translateY_xy
  rw [σ_commutes_addY W (x_gen W) (algebraMap F KE xk) (y_gen W)
        (translateSlope_xy W xk yk)]
  rw [σ.commutes xk, hσx, hσy]
  have hx_ne : x_gen W ≠ algebraMap F KE xk := fun h ↦
    x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h)
  have hx_σ_ne : σ (x_gen W) ≠ algebraMap F KE xk := by
    rw [hσx]
    exact translateX_xy_neg_ne_algebraMap W xk yk h_ns h_not_2_tor
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk) := by
    rwa [σ.commutes]
  have h_slope_eq : σ (translateSlope_xy W xk yk) =
      (W_KE W).toAffine.slope (translateX_xy W xk (W.toAffine.negY xk yk))
        (algebraMap F KE xk)
        (translateY_xy W xk (W.toAffine.negY xk yk)) (algebraMap F KE yk) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk)
        (y_gen W) (algebraMap F KE yk)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk, σ.commutes yk, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint_neg W xk yk h_ns) +
      liftSomePoint W xk yk h_ns = genericPoint W := by
    rw [add_assoc]
    rw [add_comm (liftSomePoint_neg W xk yk h_ns)
        (liftSomePoint W xk yk h_ns)]
    rw [liftSomePoint_add_neg_eq_zero, add_zero]
  have h_ne_2 : translateX_xy W xk (W.toAffine.negY xk yk) ≠ algebraMap F KE xk :=
    translateX_xy_neg_ne_algebraMap W xk yk h_ns h_not_2_tor
  rw [genericPoint_add_liftSomePoint_neg W xk yk h_ns] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_ne_2)] at h_gen_eq
  unfold genericPoint at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.2

/-! ### `AlgHom` extensionality from agreement on `x_gen, y_gen`.

`K(E) = Frac(R)` where `R = AdjoinRoot W.polynomial` and `W.polynomial : F[X][Y]`.
Two `F`-`AlgHom`s `K(E) →ₐ[F] K(E)` are equal iff they agree on the generators
`x_gen` (image of `Polynomial.X`) and `y_gen` (image of `AdjoinRoot.root`). -/

/-- Two `F`-AlgHoms `KE →ₐ[F] KE` are equal iff they agree on `x_gen` and
`y_gen`. Reduction chain: `IsLocalization.algHom_ext` (peeling `Frac`),
`AdjoinRoot.algHom_ext'` (peeling AdjoinRoot), `Polynomial.algHom_ext`
(peeling `F[X]`). -/
theorem algHom_ext_x_y_gen {ψ₁ ψ₂ : KE →ₐ[F] KE}
    (hx : ψ₁ (x_gen W) = ψ₂ (x_gen W))
    (hy : ψ₁ (y_gen W) = ψ₂ (y_gen W)) :
    ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext
    (nonZeroDivisors W.toAffine.CoordinateRing)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ψ₁ (algebraMap _ KE (algebraMap _ _ Polynomial.X)) =
      ψ₂ (algebraMap _ KE (algebraMap _ _ Polynomial.X))
    exact hx
  · change ψ₁ (algebraMap _ KE (AdjoinRoot.root W.toAffine.polynomial)) =
      ψ₂ (algebraMap _ KE (AdjoinRoot.root W.toAffine.polynomial))
    exact hy

/-- **AlgEquiv version of `algHom_ext_x_y_gen`**: two `F`-`AlgEquiv`s `KE ≃ₐ[F] KE` agreeing on
`x_gen` and `y_gen` are equal. Reduces any `translateAlgEquivOfPoint` identity (composition,
inverse, group action) to the proven action-on-generators lemmas. -/
theorem algEquiv_ext_x_y_gen {ψ₁ ψ₂ : KE ≃ₐ[F] KE}
    (hx : ψ₁ (x_gen W) = ψ₂ (x_gen W))
    (hy : ψ₁ (y_gen W) = ψ₂ (y_gen W)) :
    ψ₁ = ψ₂ := by
  refine AlgEquiv.ext fun z ↦ ?_
  have h := algHom_ext_x_y_gen (W := W) (ψ₁ := ψ₁.toAlgHom) (ψ₂ := ψ₂.toAlgHom)
    (by simpa using hx) (by simpa using hy)
  have hz := DFunLike.congr_fun h z
  simpa using hz

/-! ### Inverse round-trip: `τ(σ(x_gen)) = x_gen` and `τ(σ(y_gen)) = y_gen`.

Group-law identity: `(gen + T_lift) + (−T_lift) = gen`. The proof structure
mirrors the forward round-trip, with `T_lift` and `−T_lift` swapped. -/

/-- **Inverse round-trip on `x_gen`**: `τ(σ(x_gen)) = x_gen`. -/
theorem translateAlgHom_inv_round_trip_x_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor
        (translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor (x_gen W)) =
      x_gen W := by
  rw [translateAlgHom_neg_apply_x_gen W xk yk h_ns h_not_2_tor]
  set τ := translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor
  have hτx : τ (x_gen W) = translateX_xy W xk yk :=
    translateAlgHom_apply_x_gen W xk yk h_ns h_not_2_tor
  have hτy : τ (y_gen W) = translateY_xy W xk yk :=
    translateAlgHom_apply_y_gen W xk yk h_ns h_not_2_tor
  unfold translateX_xy
  rw [σ_commutes_addX W (x_gen W) (algebraMap F KE xk)
        (translateSlope_xy W xk (W.toAffine.negY xk yk))]
  rw [τ.commutes xk, hτx]
  have hx_ne : x_gen W ≠ algebraMap F KE xk := fun h ↦
    x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h)
  have hx_τ_ne : τ (x_gen W) ≠ algebraMap F KE xk := by
    rw [hτx]
    intro h_eq
    apply translateX_xy_transcendental W xk yk h_ns h_not_2_tor
    refine ⟨Polynomial.X - Polynomial.C xk,
      Polynomial.X_sub_C_ne_zero _, ?_⟩
    rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]
  have hx_τ_ne_full : τ (x_gen W) ≠ τ (algebraMap F KE xk) := by
    rwa [τ.commutes]
  have h_slope_eq : τ (translateSlope_xy W xk (W.toAffine.negY xk yk)) =
      (W_KE W).toAffine.slope (translateX_xy W xk yk)
        (algebraMap F KE xk)
        (translateY_xy W xk yk) (algebraMap F KE (W.toAffine.negY xk yk)) := by
    change τ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk)
        (y_gen W) (algebraMap F KE (W.toAffine.negY xk yk))) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_τ_ne_full]
    rw [τ.commutes xk, τ.commutes (W.toAffine.negY xk yk), hτx, hτy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk yk h_ns) +
      liftSomePoint_neg W xk yk h_ns = genericPoint W :=
    genericPoint_round_trip W xk yk h_ns
  have h_ne_2 : translateX_xy W xk yk ≠ algebraMap F KE xk := by
    intro h_eq
    apply translateX_xy_transcendental W xk yk h_ns h_not_2_tor
    refine ⟨Polynomial.X - Polynomial.C xk,
      Polynomial.X_sub_C_ne_zero _, ?_⟩
    rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]
  rw [genericPoint_add_liftSomePoint W xk yk h_ns] at h_gen_eq
  unfold liftSomePoint_neg liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_ne_2)] at h_gen_eq
  unfold genericPoint at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.1

/-- **Inverse round-trip on `y_gen`**: `τ(σ(y_gen)) = y_gen`. -/
theorem translateAlgHom_inv_round_trip_y_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor
        (translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor (y_gen W)) =
      y_gen W := by
  rw [translateAlgHom_neg_apply_y_gen W xk yk h_ns h_not_2_tor]
  set τ := translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor
  have hτx : τ (x_gen W) = translateX_xy W xk yk :=
    translateAlgHom_apply_x_gen W xk yk h_ns h_not_2_tor
  have hτy : τ (y_gen W) = translateY_xy W xk yk :=
    translateAlgHom_apply_y_gen W xk yk h_ns h_not_2_tor
  unfold translateY_xy
  rw [σ_commutes_addY W (x_gen W) (algebraMap F KE xk)
        (y_gen W) (translateSlope_xy W xk (W.toAffine.negY xk yk))]
  rw [τ.commutes xk, hτx, hτy]
  have hx_ne : x_gen W ≠ algebraMap F KE xk := fun h ↦
    x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h)
  have hx_τ_ne : τ (x_gen W) ≠ algebraMap F KE xk := by
    rw [hτx]
    intro h_eq
    apply translateX_xy_transcendental W xk yk h_ns h_not_2_tor
    refine ⟨Polynomial.X - Polynomial.C xk,
      Polynomial.X_sub_C_ne_zero _, ?_⟩
    rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]
  have hx_τ_ne_full : τ (x_gen W) ≠ τ (algebraMap F KE xk) := by
    rwa [τ.commutes]
  have h_slope_eq : τ (translateSlope_xy W xk (W.toAffine.negY xk yk)) =
      (W_KE W).toAffine.slope (translateX_xy W xk yk)
        (algebraMap F KE xk)
        (translateY_xy W xk yk) (algebraMap F KE (W.toAffine.negY xk yk)) := by
    change τ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk)
        (y_gen W) (algebraMap F KE (W.toAffine.negY xk yk))) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_τ_ne_full]
    rw [τ.commutes xk, τ.commutes (W.toAffine.negY xk yk), hτx, hτy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk yk h_ns) +
      liftSomePoint_neg W xk yk h_ns = genericPoint W :=
    genericPoint_round_trip W xk yk h_ns
  have h_ne_2 : translateX_xy W xk yk ≠ algebraMap F KE xk := by
    intro h_eq
    apply translateX_xy_transcendental W xk yk h_ns h_not_2_tor
    refine ⟨Polynomial.X - Polynomial.C xk,
      Polynomial.X_sub_C_ne_zero _, ?_⟩
    rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]
  rw [genericPoint_add_liftSomePoint W xk yk h_ns] at h_gen_eq
  unfold liftSomePoint_neg liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_ne_2)] at h_gen_eq
  unfold genericPoint at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.2

/-! ### 2-torsion case — algebraic foundations

The non-2-torsion infrastructure above evaluates at the smooth point `−T`,
which is *distinct* from `T`. For a 2-torsion `T = (xk, yk)` (i.e.,
`yk = negY xk yk`, equivalently `2yk + a₁ xk + a₃ = 0`), we have `−T = T`,
and the order analysis at the *single* smooth point uses a different
algebraic structure. The shared substantive tool is the **curve identity**

```
(y_gen − yk) · A = (x_gen − xk) · (B − a₁ yk)
```

where
```
A := y_gen + yk + a₁ x_gen + a₃,
B := x_gen² + x_gen·xk + xk² + a₂ (x_gen + xk) + a₄.
```

It follows from subtracting the Weierstrass equation at `(x_gen, y_gen)`
from the Weierstrass equation at `(xk, yk)`. At smooth `T`, `B − a₁ yk`
evaluates to `∂F/∂x|_T`, which is nonzero whenever `∂F/∂y|_T = 0` (the
2-torsion side of the smoothness alternative). At 2-torsion `T`, `A`
vanishes (the 2-torsion condition `2yk + a₁ xk + a₃ = 0`), giving
`ord_T A ≥ 1`.

Combining: `ord_T (slope) = ord_T (B − a₁ yk) − ord_T A ≤ −1`, hence
`ord_T (translateX_xy) ≤ −2`, hence `translateX_xy` is transcendental.
This avoids the `h_not_2_tor` hypothesis required by the existing chain. -/

omit [DecidableEq F] in
/-- **Curve identity in `K(E)`** (foundational for both 2-torsion and
non-2-torsion analysis): for any `(xk, yk)` satisfying the Weierstrass
equation in `F`,

```
(y_gen − yk) · (y_gen + yk + a₁ x_gen + a₃) =
  (x_gen − xk) · (x_gen² + x_gen·xk + xk² + a₂ (x_gen + xk) + a₄ − a₁ yk).
```

Proof: subtract the Weierstrass relation at the constant point from the
generic-point relation; the difference factors as `(y − yk)·A − (x − xk)·B'`
modulo `ring`. -/
theorem curve_identity_translate
    (xk yk : F) (h_eq : W.toAffine.Equation xk yk) :
    (y_gen W - algebraMap F KE yk) *
        (y_gen W + algebraMap F KE yk +
          algebraMap F KE W.a₁ * x_gen W + algebraMap F KE W.a₃) =
      (x_gen W - algebraMap F KE xk) *
        (x_gen W ^ 2 + x_gen W * algebraMap F KE xk +
          algebraMap F KE xk ^ 2 +
          algebraMap F KE W.a₂ * (x_gen W + algebraMap F KE xk) +
          algebraMap F KE W.a₄ -
          algebraMap F KE W.a₁ * algebraMap F KE yk) := by
  classical
  have h_gen :
      y_gen W ^ 2 + algebraMap F KE W.a₁ * x_gen W * y_gen W +
        algebraMap F KE W.a₃ * y_gen W =
      x_gen W ^ 3 + algebraMap F KE W.a₂ * x_gen W ^ 2 +
        algebraMap F KE W.a₄ * x_gen W + algebraMap F KE W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp (generic_equation W)
  have h_lift : (W_KE W).toAffine.Equation
      (algebraMap F KE xk) (algebraMap F KE yk) :=
    translate_constant_equation W xk yk h_eq
  have h_const :
      algebraMap F KE yk ^ 2 +
        algebraMap F KE W.a₁ * algebraMap F KE xk * algebraMap F KE yk +
        algebraMap F KE W.a₃ * algebraMap F KE yk =
      algebraMap F KE xk ^ 3 +
        algebraMap F KE W.a₂ * algebraMap F KE xk ^ 2 +
        algebraMap F KE W.a₄ * algebraMap F KE xk +
        algebraMap F KE W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h_lift
  linear_combination h_gen - h_const

/-! ### 2-torsion factorisation of `A`

For 2-torsion `T = (xk, yk)` (i.e., `yk = negY xk yk`), the curve-identity
factor `A = y_gen + yk + a₁ x_gen + a₃` simplifies because
`2yk + a₁ xk + a₃ = 0` (the 2-torsion condition rewritten). Concretely,

```
A = (y_gen − yk) + a₁ (x_gen − xk).
```

Both summands have order ≥ 1 at the smooth point `−T = T`, giving
`ord_T A ≥ 1`. This is the substantive 2-torsion-specific fact used to
bound `ord_T (slope) ≤ −1`. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **A-factorisation at 2-torsion**: `A = (y_gen − yk) + a₁ (x_gen − xk)`
when `T = (xk, yk)` is 2-torsion. Algebraic identity in `K(E)` derived from
`2yk + a₁ xk + a₃ = 0` (which is `yk = negY xk yk` rewritten). -/
theorem A_factorization_at_2tor
    (xk yk : F) (h_2_tor : yk = W.toAffine.negY xk yk) :
    y_gen W + algebraMap F KE yk +
        algebraMap F KE W.a₁ * x_gen W + algebraMap F KE W.a₃ =
      (y_gen W - algebraMap F KE yk) +
        algebraMap F KE W.a₁ * (x_gen W - algebraMap F KE xk) := by
  classical
  have h_2yk : (2 : F) * yk + W.a₁ * xk + W.a₃ = 0 := by
    have h := h_2_tor
    have hneg : W.toAffine.negY xk yk = -yk - W.a₁ * xk - W.a₃ := rfl
    rw [hneg] at h
    linear_combination h
  have h_lift : algebraMap F KE ((2 : F) * yk + W.a₁ * xk + W.a₃) = 0 := by
    rw [h_2yk, map_zero]
  rw [map_add, map_add, map_mul, map_mul, map_ofNat] at h_lift
  linear_combination h_lift

/-! ### Order at smooth 2-torsion `T` of `A` -/

set_option linter.unusedDecidableInType false in
/-- **`ord_T A ≥ 1` at smooth 2-torsion `T`**: combine the
A-factorisation with the existing order bounds for `y_gen − yk` and
`x_gen − xk` at the smooth point `−T = T`. -/
theorem one_le_ord_P_A_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (y_gen W + algebraMap F KE yk +
          algebraMap F KE W.a₁ * x_gen W + algebraMap F KE W.a₃) := by
  set P := negSmoothPoint W xk yk h_ns
  rw [A_factorization_at_2tor W xk yk h_2_tor]
  have h_y_ord : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (y_gen W - algebraMap F KE yk) := by
    have h_y_eq_neg : yk = W.toAffine.negY xk yk := h_2_tor
    rw [h_y_eq_neg]
    exact one_le_ord_P_y_gen_sub_negY_const W xk yk h_ns
  have h_x_ord : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) :=
    one_le_ord_P_x_gen_sub_const W xk yk h_ns
  have h_a1_ord : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (algebraMap F KE W.a₁) :=
    ord_P_algebraMap_F_nonneg W P W.a₁
  have h_mul_eq : (W_smooth W).ord_P P
      (algebraMap F KE W.a₁ * (x_gen W - algebraMap F KE xk)) =
      (W_smooth W).ord_P P (algebraMap F KE W.a₁) +
        (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  have h_prod_ord : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (algebraMap F KE W.a₁ * (x_gen W - algebraMap F KE xk)) := by
    rw [h_mul_eq]
    have h_sum : (0 : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) ≤
        (W_smooth W).ord_P P (algebraMap F KE W.a₁) +
          (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) :=
      add_le_add h_a1_ord h_x_ord
    rwa [zero_add] at h_sum
  have h_add := SmoothPlaneCurve.ord_P_add_le (P := P)
      (y_gen W - algebraMap F KE yk)
      (algebraMap F KE W.a₁ * (x_gen W - algebraMap F KE xk))
  exact le_trans (le_min h_y_ord h_prod_ord) h_add

/-! ### `polynomialX` non-vanishing at smooth 2-torsion `T`

The Weierstrass `polynomialX = a₁ y − 3x² − 2 a₂ x − a₄` (Mathlib's
notation). At a 2-torsion point, `polynomialY.evalEval` vanishes (the
2-torsion condition is exactly `polynomialY.evalEval xk yk = 0`). The
nonsingularity hypothesis then forces `polynomialX.evalEval xk yk ≠ 0`. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`polynomialX` non-vanishes at smooth 2-torsion**: for smooth
2-torsion `T = (xk, yk)`, `W.polynomialX.evalEval xk yk ≠ 0`. Direct from
`Nonsingular` + the 2-torsion-side `polynomialY.evalEval xk yk = 0`. -/
theorem polynomialX_evalEval_ne_zero_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    W.toAffine.polynomialX.evalEval xk yk ≠ 0 := by
  have h_polY : W.toAffine.polynomialY.evalEval xk yk = 0 := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialY]
    have hneg : W.toAffine.negY xk yk = -yk - W.a₁ * xk - W.a₃ := rfl
    rw [hneg] at h_2_tor
    linear_combination h_2_tor
  rcases h_ns.2 with hX | hY
  · exact hX
  · exact absurd h_polY hY

/-! ### `ord_T (B − a₁ yk) = 0` at smooth 2-torsion `T`

The RHS factor of the curve identity. Decompose
`B − a₁ yk = (x_gen − xk) · R + C` with `R = x_gen + 2 xk + a₂ ∈ K(E)` and
`C = 3 xk² + 2 a₂ xk + a₄ − a₁ yk = −polynomialX.evalEval xk yk ∈ F`.
At smooth 2-torsion `T`, `C ≠ 0` (by `polynomialX_evalEval_ne_zero_at_2tor`),
so `ord_T C = 0`. The other summand has `ord_T ≥ 1`. Strict inequality
gives `ord_T (B − a₁ yk) = ord_T C = 0`. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **B-decomposition**: `B − a₁ yk = (x_gen − xk) · (x_gen + 2 xk + a₂)
+ (3 xk² + 2 a₂ xk + a₄ − a₁ yk)`. -/
private theorem B_minus_a1_yk_decomposition (xk yk : F) :
    x_gen W ^ 2 + x_gen W * algebraMap F KE xk +
        algebraMap F KE xk ^ 2 +
        algebraMap F KE W.a₂ * (x_gen W + algebraMap F KE xk) +
        algebraMap F KE W.a₄ -
        algebraMap F KE W.a₁ * algebraMap F KE yk =
      (x_gen W - algebraMap F KE xk) *
          (x_gen W + algebraMap F KE (2 * xk + W.a₂)) +
        algebraMap F KE
          (3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk) := by
  classical
  push_cast [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- **`ord_P (a + b) = 0` from `ord_P b = 0` and `1 ≤ ord_P a`.** The summand
`b` has the strictly smaller order (`0 < 1 ≤ ord_P a`), so by strict
non-archimedeanity (`ord_P_add_eq_of_lt`) it dominates the sum:
`ord_P (a + b) = ord_P b = 0`. Generic building block for the recurring
"low-order constant + high-order remainder pins the sum to the constant's
order" pole-order arguments. -/
private theorem ord_P_add_eq_zero_of_eq_zero_of_one_le
    {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint} {a b : C.FunctionField}
    (hb : C.ord_P P b = 0) (ha : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P a) :
    C.ord_P P (a + b) = 0 := by
  have h_lt : C.ord_P P b < C.ord_P P a :=
    lt_of_lt_of_le (by rw [hb]; exact_mod_cast (show (0 : ℤ) < 1 by norm_num)) ha
  rw [add_comm, SmoothPlaneCurve.ord_P_add_eq_of_lt h_lt, hb]

/-- **The constant `C = 3 xk² + 2 a₂ xk + a₄ − a₁ yk` is nonzero at smooth
2-torsion.** This constant equals `−polynomialX.evalEval xk yk`, which is
nonzero at a smooth 2-torsion point (`polynomialX_evalEval_ne_zero_at_2tor`);
unfolding `evalEval_polynomialX` and clearing signs transfers the nonvanishing
to `C`. -/
private theorem C_const_ne_zero_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk : F) ≠ 0 := by
  have h_polX : W.toAffine.polynomialX.evalEval xk yk ≠ 0 :=
    polynomialX_evalEval_ne_zero_at_2tor W xk yk h_ns h_2_tor
  rw [WeierstrassCurve.Affine.evalEval_polynomialX] at h_polX
  intro h
  apply h_polX
  linear_combination -h

/-- **`ord_T ((x_gen − xk) · (x_gen + 2 xk + a₂)) ≥ 1` at smooth 2-torsion.**
The first factor `x_gen − xk` vanishes at `T` to order `≥ 1`
(`one_le_ord_P_x_gen_sub_const`); the second factor `x_gen + (2 xk + a₂)` is a
sum of a nonneg-order generator and a constant, hence has order `≥ 0`. By
additivity `ord_T (·) = ord_T (x_gen − xk) + ord_T (x_gen + …)`, the product
order is `≥ 1 + 0 = 1`. (Additivity is applied in term mode on the abstract
factors, since `ord_P_mul` does not rewrite under a forced `KE` type.) -/
private theorem one_le_ord_P_x_gen_sub_mul_factor_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    ((1 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        ((x_gen W - algebraMap F KE xk) *
          (x_gen W + algebraMap F KE (2 * xk + W.a₂))) := by
  set P := negSmoothPoint W xk yk h_ns
  have h_x_nonneg : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W) :=
    ord_P_x_gen_nonneg W P
  have h_const_nonneg : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (algebraMap F KE (2 * xk + W.a₂)) :=
    ord_P_algebraMap_F_nonneg W P _
  have h_R_nonneg : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P
      (x_gen W + algebraMap F KE (2 * xk + W.a₂)) :=
    ord_P_add_nonneg h_x_nonneg h_const_nonneg
  have h_x_sub : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) :=
    one_le_ord_P_x_gen_sub_const W xk yk h_ns
  have h_prod_eq : (W_smooth W).ord_P P
      ((x_gen W - algebraMap F KE xk) *
        (x_gen W + algebraMap F KE (2 * xk + W.a₂))) =
      (W_smooth W).ord_P P (x_gen W - algebraMap F KE xk) +
        (W_smooth W).ord_P P
          (x_gen W + algebraMap F KE (2 * xk + W.a₂)) :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  rw [h_prod_eq]
  have h := add_le_add h_x_sub h_R_nonneg
  rwa [add_zero] at h

set_option linter.unusedDecidableInType false in
/-- **`ord_T (B − a₁ yk) = 0` at smooth 2-torsion `T`**: stated in
decomposed form `(x_gen − xk) · (x_gen + 2 xk + a₂) + C` where
`C = 3 xk² + 2 a₂ xk + a₄ − a₁ yk = −polynomialX.evalEval xk yk`.
At smooth 2-torsion `T`, `C ≠ 0` (by
`polynomialX_evalEval_ne_zero_at_2tor`), so `ord_T C = 0`. The other
summand has `ord_T ≥ 1`. Strict inequality gives the result. -/
theorem ord_P_B_minus_a1_yk_decomposed_eq_zero_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        ((x_gen W - algebraMap F KE xk) *
            (x_gen W + algebraMap F KE (2 * xk + W.a₂)) +
          algebraMap F KE
            (3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk)) = 0 := by
  set P := negSmoothPoint W xk yk h_ns
  -- The constant summand `C` is nonzero, so it has order `0`.
  have h_C_ord : (W_smooth W).ord_P P
      (algebraMap F KE
        (3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk)) = 0 :=
    (W_smooth W).ord_P_algebraMap_F_of_ne_zero
      (C_const_ne_zero_at_2tor W xk yk h_ns h_2_tor) P
  -- The product summand has order `≥ 1`, strictly above `ord_P C = 0`,
  -- so the constant dominates the sum and pins its order to `0`.
  exact ord_P_add_eq_zero_of_eq_zero_of_one_le h_C_ord
    (one_le_ord_P_x_gen_sub_mul_factor_at_2tor W xk yk h_ns)

set_option linter.unusedDecidableInType false in
/-- **`ord_T (B − a₁ yk) = 0` at smooth 2-torsion `T`**: bridge from the
decomposed form to the original `B − a₁ yk` form via the algebraic
identity `B_minus_a1_yk_decomposition`. -/
theorem ord_P_B_minus_a1_yk_eq_zero_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (x_gen W ^ 2 + x_gen W * algebraMap F KE xk +
          algebraMap F KE xk ^ 2 +
          algebraMap F KE W.a₂ * (x_gen W + algebraMap F KE xk) +
          algebraMap F KE W.a₄ -
          algebraMap F KE W.a₁ * algebraMap F KE yk) = 0 := by
  have h_eq := B_minus_a1_yk_decomposition W xk yk
  have h_decomposed :=
    ord_P_B_minus_a1_yk_decomposed_eq_zero_at_2tor W xk yk h_ns h_2_tor
  exact h_eq ▸ h_decomposed

/-- **A function whose order is `0` is nonzero.** If `ord_P P f = 0` then `f ≠ 0`,
since the zero function has order `⊤ ≠ 0`. Generic building block (companion to
`ne_zero_of_ord_P_le_neg_one`): an *exact* order value supplies the nonvanishing
hypothesis needed before a `cases` on a related order can land in a finite branch
or before `ord_P_inv` (which needs `f ≠ 0`) can fire. -/
private theorem ne_zero_of_ord_P_eq_zero {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {f : C.FunctionField}
    (hf : C.ord_P P f = 0) : f ≠ 0 := fun h_zero ↦ by
  rw [h_zero, C.ord_P_zero] at hf
  exact absurd hf (by simp)

/-- **`ord_P P (b · a⁻¹) ≤ −1`** when `b` has order `0` and `a` has order `≥ 1`.
The quotient `b / a` of an order-`0` numerator by an order-`≥ 1` denominator has
strictly negative order: additivity and `ord_P_inv` give
`ord_P (b · a⁻¹) = ord_P b − ord_P a = −ord_P a`, and destructuring the finite
order `ord_P a = ↑n` (finite since `a ≠ 0`) reduces the bound `−n ≤ −1` to the
integer fact `1 ≤ n`, dispatched by `omega`. Generic building block for the
"slope = (order-`0`) / (order-`≥ 1`)" pole-order arguments at 2-torsion. -/
private theorem ord_P_mul_inv_le_neg_one {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a b : C.FunctionField} (ha_ne : a ≠ 0)
    (ha : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P a) (hb : C.ord_P P b = 0) :
    C.ord_P P (b * a⁻¹) ≤ ((-1 : ℤ) : WithTop ℤ) := by
  rw [SmoothPlaneCurve.ord_P_mul (P := P) _ _,
    SmoothPlaneCurve.ord_P_inv (P := P) _ ha_ne, hb, zero_add]
  cases h_a : C.ord_P P a with
  | top => exact absurd ((SmoothPlaneCurve.ord_P_eq_top_iff _).mp h_a) ha_ne
  | coe n =>
      rw [h_a] at ha
      have h_n : (1 : ℤ) ≤ n := by exact_mod_cast ha
      change -((n : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)
      rw [show -((n : ℤ) : WithTop ℤ) = ((-n : ℤ) : WithTop ℤ) from rfl]
      exact_mod_cast (show -n ≤ -1 by omega)

/-! ### `ord_T (translateSlope_xy) ≤ −1` at smooth 2-torsion `T`

Cleaner approach (per user directive): express `slope = (B − a₁ yk) / A`
directly via the curve identity, with `A ≠ 0` deduced from `RHS ≠ 0`
(non-zero since `ord_T(B − a₁ yk) = 0`). Then
`ord_T(slope) = ord_T(B − a₁ yk) − ord_T(A) = 0 − (≥1) = ≤ −1`. -/

set_option linter.unusedDecidableInType false in
/-- **`ord_T (translateSlope_xy) ≤ −1` at smooth 2-torsion `T`** via
slope = (B − a₁ yk) / A. -/
theorem ord_P_translateSlope_xy_le_neg_one_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateSlope_xy W xk yk) ≤ ((-1 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns
  set Bma : KE := x_gen W ^ 2 + x_gen W * algebraMap F KE xk +
      algebraMap F KE xk ^ 2 +
      algebraMap F KE W.a₂ * (x_gen W + algebraMap F KE xk) +
      algebraMap F KE W.a₄ -
      algebraMap F KE W.a₁ * algebraMap F KE yk with hBma_def
  set A : KE := y_gen W + algebraMap F KE yk +
      algebraMap F KE W.a₁ * x_gen W + algebraMap F KE W.a₃ with hA_def
  have h_id : (y_gen W - algebraMap F KE yk) * A =
      (x_gen W - algebraMap F KE xk) * Bma := by
    rw [hA_def, hBma_def]
    exact curve_identity_translate W xk yk h_ns.1
  -- Order facts for numerator `Bma` (= `0`) and denominator `A` (≥ `1`).
  have h_A_ord : ((1 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P P A := by
    rw [hA_def]
    exact one_le_ord_P_A_at_2tor W xk yk h_ns h_2_tor
  have h_Bma_ord : (W_smooth W).ord_P P Bma = 0 := by
    rw [hBma_def]
    exact ord_P_B_minus_a1_yk_eq_zero_at_2tor W xk yk h_ns h_2_tor
  -- `A ≠ 0`: the RHS `(x_gen − xk) · Bma` of the curve identity is nonzero.
  have h_x_ne : x_gen W - algebraMap F KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have h_Bma_ne : Bma ≠ 0 := ne_zero_of_ord_P_eq_zero h_Bma_ord
  have h_A_ne : A ≠ 0 :=
    right_ne_zero_of_mul (a := y_gen W - algebraMap F KE yk)
      (h_id ▸ mul_ne_zero h_x_ne h_Bma_ne)
  -- `slope = Bma / A`, so `ord_P slope = ord_P Bma − ord_P A ≤ 0 − 1 = −1`.
  have h_slope_eq : translateSlope_xy W xk yk = Bma / A := by
    rw [translateSlope_xy_eq, div_eq_div_iff h_x_ne h_A_ne]
    linear_combination h_id
  rw [h_slope_eq, div_eq_mul_inv]
  exact ord_P_mul_inv_le_neg_one h_A_ne h_A_ord h_Bma_ord

/-! ### `ord_T (translateX_xy) < 0` at smooth 2-torsion `T`

`translateX_xy = slope² + rest` where `rest = a₁·slope − a₂ − x_gen − xk`.
With `ord_T(slope) = n ≤ −1` (the slope bound, finite since `slope ≠ 0`):

* `ord_T(slope²) = 2n`.
* `ord_T(rest) ≥ n` — coming from the cases:
  * `ord_T(a₁·slope) = ord(a₁) + ord(slope) = 0 + n = n` (or `⊤` when `a₁ = 0`).
  * `ord_T(−a₂ − x_gen − xk) ≥ 0 ≥ n` (since `n < 0`).
  * Min is `≥ n`; `ord_P_add_le` lifts to the sum.
* `2n < n` (since `n < 0`), hence `ord_T(slope²) < ord_T(rest)`.
* `ord_P_add_eq_of_lt` ⟹ `ord_T(translateX_xy) = ord_T(slope²) = 2n ≤ −2 < 0`.

The `cases h_n : ord_T(s)` destructure to a finite `n` is the wall-break:
all `WithTop ℤ` arithmetic happens via `ℤ` and `omega`. -/

/-- **A function whose order is `≤ −1` is nonzero.** If `ord_P P f ≤ −1` then
`f ≠ 0`, since the zero function has order `⊤`. Generic building block: lets a
strict order bound supply the nonvanishing hypothesis needed for `cases` on
`ord_P P f` to land in the finite branch. -/
private theorem ne_zero_of_ord_P_le_neg_one {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {f : C.FunctionField}
    (hf : C.ord_P P f ≤ ((-1 : ℤ) : WithTop ℤ)) : f ≠ 0 := fun h_zero ↦ by
  rw [h_zero, C.ord_P_zero] at hf
  exact absurd hf (by simp)

/-- **`addX` decomposition of `translateX_xy` into slope² plus a remainder.**
Unfolding `translateX_xy` and `WeierstrassCurve.Affine.addX` writes the
translated x-coordinate as `s² + (a₁·s + (−a₂ − x_gen − xk))`, where
`s = translateSlope_xy`. The `s²` term carries the (doubled, strictly negative)
slope order; the remainder collects the lower-order pieces. -/
private theorem translateX_xy_eq_slope_sq_add_rest (xk yk : F) :
    translateX_xy W xk yk =
      translateSlope_xy W xk yk * translateSlope_xy W xk yk +
        ((W_KE W).a₁ * translateSlope_xy W xk yk +
          (-(W_KE W).a₂ + -x_gen W + -algebraMap F KE xk)) := by
  unfold translateX_xy
  rw [WeierstrassCurve.Affine.addX]
  ring

set_option linter.unusedDecidableInType false in
/-- **`ord_P P s ≤ ord_P P (a₁·s)`.** The slope order is a lower bound for the
order of the linear term `a₁·s`: when `a₁ = 0` the term is `0` (order `⊤`),
otherwise `ord_P (a₁·s) = ord_P a₁ + ord_P s = 0 + ord_P s` since the constant
`a₁ = algebraMap F KE W.a₁` has order `0`. -/
private theorem ord_P_slope_le_ord_P_a1_mul_slope (xk yk : F)
    (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateSlope_xy W xk yk) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        ((W_KE W).a₁ * translateSlope_xy W xk yk) := by
  set P := negSmoothPoint W xk yk h_ns
  set s : KE := translateSlope_xy W xk yk
  by_cases ha1 : (W_KE W).a₁ = 0
  · have h_zero : (W_KE W).a₁ * s = 0 := by rw [ha1, zero_mul]
    have h_top : (W_smooth W).ord_P P ((W_KE W).a₁ * s) = ⊤ := by
      rw [h_zero]; exact (W_smooth W).ord_P_zero
    rw [h_top]; exact le_top
  · have h_a1_F : W.a₁ ≠ 0 := fun h ↦ ha1 (by
      change algebraMap F KE W.a₁ = 0
      rw [h, map_zero])
    have h_a1_ord : (W_smooth W).ord_P P ((W_KE W).a₁) = 0 := by
      change (W_smooth W).ord_P P (algebraMap F KE W.a₁) = 0
      exact (W_smooth W).ord_P_algebraMap_F_of_ne_zero h_a1_F P
    have h_mul_ord : (W_smooth W).ord_P P ((W_KE W).a₁ * s) =
        (W_smooth W).ord_P P ((W_KE W).a₁) + (W_smooth W).ord_P P s :=
      SmoothPlaneCurve.ord_P_mul (P := P) _ _
    rw [h_mul_ord, h_a1_ord, zero_add]

/-- **The remainder's constant part `−a₂ − x_gen − xk` has nonnegative order.**
Each summand is (the negative of) either a constant `algebraMap F KE _` or the
generic x-coordinate `x_gen`, all of nonnegative order at any smooth point;
`ord_P_neg` strips the signs and `ord_P_le_add_of_le_of_le` combines the sum. -/
private theorem ord_P_translate_const_part_nonneg (xk : F)
    (P : (W_smooth W).SmoothPoint) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P
      (-(W_KE W).a₂ + -x_gen W + -algebraMap F KE xk) := by
  have h_a2_neg : (W_smooth W).ord_P P (-(W_KE W).a₂) =
      (W_smooth W).ord_P P ((W_KE W).a₂) := SmoothPlaneCurve.ord_P_neg (P := P) _
  have h_xgen_neg : (W_smooth W).ord_P P (-x_gen W) =
      (W_smooth W).ord_P P (x_gen W) := SmoothPlaneCurve.ord_P_neg (P := P) _
  have h_xk_neg : (W_smooth W).ord_P P (-algebraMap F KE xk) =
      (W_smooth W).ord_P P (algebraMap F KE xk) := SmoothPlaneCurve.ord_P_neg (P := P) _
  have h_a2 : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (-(W_KE W).a₂) := by
    rw [h_a2_neg]; exact ord_P_algebraMap_F_nonneg W P W.a₂
  have h_xgen : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (-x_gen W) := by
    rw [h_xgen_neg]; exact ord_P_x_gen_nonneg W P
  have h_xk : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (-algebraMap F KE xk) := by
    rw [h_xk_neg]; exact ord_P_algebraMap_F_nonneg W P xk
  exact ord_P_le_add_of_le_of_le (ord_P_le_add_of_le_of_le h_a2 h_xgen) h_xk

set_option linter.unusedDecidableInType false in
/-- **`ord_P P s ≤ ord_P P rest`** for `rest = a₁·s + (−a₂ − x_gen − xk)`, when
`ord_P P s ≤ 0`. The linear term `a₁·s` has order `≥ ord_P s`
(`ord_P_slope_le_ord_P_a1_mul_slope`); the constant part has order `≥ 0 ≥ ord_P s`
(`ord_P_translate_const_part_nonneg`); `ord_P_le_add_of_le_of_le` lifts the common
lower bound to the sum. -/
private theorem ord_P_slope_le_ord_P_translate_rest (xk yk : F)
    (h_ns : W.toAffine.Nonsingular xk yk)
    (h_le : (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
      (translateSlope_xy W xk yk) ≤ 0) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateSlope_xy W xk yk) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        ((W_KE W).a₁ * translateSlope_xy W xk yk +
          (-(W_KE W).a₂ + -x_gen W + -algebraMap F KE xk)) :=
  ord_P_le_add_of_le_of_le (ord_P_slope_le_ord_P_a1_mul_slope W xk yk h_ns)
    (le_trans h_le (ord_P_translate_const_part_nonneg W xk _))

/-- **A doubled strictly-negative order dominates a sum.** If `ord_P P a = n + n`
with `n < 0`, and `n ≤ ord_P P b`, then `n + n < n ≤ ord_P P b`, so the `a`-term
is the unique smallest-order summand: `ord_P_add_eq_of_lt` gives
`ord_P P (a + b) = n + n < 0`. Generic building block for "leading slope² term
wins" pole-order arguments. -/
private theorem ord_P_add_double_lt_zero {C : Curves.SmoothPlaneCurve F}
    {P : C.SmoothPoint} {a b : C.FunctionField} {n : ℤ}
    (ha : C.ord_P P a = ((n : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ))
    (hb : ((n : ℤ) : WithTop ℤ) ≤ C.ord_P P b) (hn : n < 0) :
    C.ord_P P (a + b) < 0 := by
  have h_lt : C.ord_P P a < C.ord_P P b := by
    rw [ha]
    refine lt_of_lt_of_le ?_ hb
    rw [show ((n : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) =
        (((n + n : ℤ) : ℤ) : WithTop ℤ) from rfl]
    exact_mod_cast (show n + n < n by omega)
  rw [SmoothPlaneCurve.ord_P_add_eq_of_lt h_lt, ha,
    show ((n : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) =
      (((n + n : ℤ) : ℤ) : WithTop ℤ) from rfl]
  exact_mod_cast (show n + n < 0 by omega)

set_option linter.unusedDecidableInType false in
/-- **`ord_T (translateX_xy) < 0` at smooth 2-torsion `T`**: from the
slope bound + `addX` decomposition, with all WithTop arithmetic reduced to
finite `ℤ` after destructuring `ord_T(slope) = ↑n`. -/
theorem ord_P_translateX_xy_lt_zero_at_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateX_xy W xk yk) < 0 := by
  set P := negSmoothPoint W xk yk h_ns
  set s : KE := translateSlope_xy W xk yk
  -- Slope bound: `ord_P P s ≤ −1`, hence `s ≠ 0`.
  have h_slope_ord : (W_smooth W).ord_P P s ≤ ((-1 : ℤ) : WithTop ℤ) :=
    ord_P_translateSlope_xy_le_neg_one_at_2tor W xk yk h_ns h_2_tor
  have h_s_ne : s ≠ 0 := ne_zero_of_ord_P_le_neg_one h_slope_ord
  -- `addX`: `translateX_xy = s² + rest`, then destructure `ord_P P s = ↑n`.
  rw [translateX_xy_eq_slope_sq_add_rest]
  cases h_n : (W_smooth W).ord_P P s with
  | top => exact absurd ((SmoothPlaneCurve.ord_P_eq_top_iff _).mp h_n) h_s_ne
  | coe n =>
      rw [h_n] at h_slope_ord
      have h_n_le : n ≤ -1 := by exact_mod_cast h_slope_ord
      -- `ord_P P (s²) = ↑n + ↑n`.
      have h_sq_mul : (W_smooth W).ord_P P (s * s) =
          (W_smooth W).ord_P P s + (W_smooth W).ord_P P s :=
        SmoothPlaneCurve.ord_P_mul (P := P) s s
      have h_sq_ord : (W_smooth W).ord_P P (s * s) =
          ((n : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) := by
        rw [h_sq_mul, h_n]
      -- `ord_P P rest ≥ ↑n` (linear term `≥ ord_P s`, constant part `≥ 0 ≥ ↑n`).
      have h_s_le_zero : (W_smooth W).ord_P P s ≤ (0 : WithTop ℤ) := by
        rw [h_n]; exact_mod_cast (show n ≤ 0 by omega)
      have h_rest_ord : ((n : ℤ) : WithTop ℤ) ≤
          (W_smooth W).ord_P P ((W_KE W).a₁ * s +
            (-(W_KE W).a₂ + -x_gen W + -algebraMap F KE xk)) := by
        rw [← h_n]
        exact ord_P_slope_le_ord_P_translate_rest W xk yk h_ns h_s_le_zero
      -- `s²` is the unique smallest-order term: `ord_P P (s² + rest) = 2n < 0`.
      exact ord_P_add_double_lt_zero h_sq_ord h_rest_ord (by omega)

/-! ### `translateX_xy_transcendental` extended to 2-torsion `T` -/

set_option linter.unusedDecidableInType false in
/-- **`translateX_xy_transcendental_2tor`**: at 2-torsion `T = (xk, yk)`,
`translateX_xy T` is transcendental over `F`. -/
theorem translateX_xy_transcendental_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    Transcendental F (translateX_xy W xk yk) :=
  SmoothPlaneCurve.transcendental_of_neg_ord_P
    (ord_P_translateX_xy_lt_zero_at_2tor W xk yk h_ns h_2_tor)

/-! ### `translateAlgHom` for 2-torsion `T`

Mechanical lift: same `translateAlgHom` constructor as non-2-torsion,
with `translateBaseHom_injective_of_transcendental` consuming the
2-torsion transcendence proof. -/

/-- **Unconditional `translateAlgHom`** for 2-torsion `T = (xk, yk)`:
all witnesses discharged. -/
noncomputable def translateAlgHom_of_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    KE →ₐ[F] KE :=
  translateAlgHom W xk yk h_ns.1
    (fun h ↦ x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h.1))
    (translateBaseHom_injective_of_transcendental W xk yk
      (translateX_xy_transcendental_2tor W xk yk h_ns h_2_tor))

/-! ### Action of `translateAlgHom_of_2tor` on `x_gen`, `y_gen`

Mechanical specialisation of `translateAlgHom_apply_x_gen` and
`translateAlgHom_apply_y_gen` (proven generically in this file for the
generic `translateAlgHom_of_nonTorsion`; the proofs work for any
`translateAlgHom W xk yk h_eq hxy hinj` regardless of 2-torsion). -/

/-- `translateAlgHom_of_2tor T x_gen = translateX_xy T`. -/
theorem translateAlgHom_of_2tor_apply_x_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    translateAlgHom_of_2tor W xk yk h_ns h_2_tor (x_gen W) =
      translateX_xy W xk yk := by
  let hxy : TranslateNonInverse W xk yk :=
    fun h ↦ x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h.1)
  unfold translateAlgHom_of_2tor translateAlgHom
  unfold x_gen
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change (translateCoordAlgHom W xk yk h_ns.1 hxy).toRingHom
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) =
    translateX_xy W xk yk
  change translateCoordRingHom W xk yk h_ns.1 hxy
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) =
    translateX_xy W xk yk
  unfold translateCoordRingHom
  change AdjoinRoot.lift (translateBaseHom W xk yk) (translateY_xy W xk yk)
      (translate_poly_eval₂_zero W xk yk h_ns.1 hxy)
      (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) =
    translateX_xy W xk yk
  rw [AdjoinRoot.lift_of]
  simp [translateBaseHom, Polynomial.eval₂_X]

/-- `translateX_xy T ≠ algebraMap F KE xk` for 2-torsion `T`. Direct
from transcendence of `translateX_xy`. -/
theorem translateX_xy_ne_algebraMap_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    translateX_xy W xk yk ≠ algebraMap F KE xk := by
  intro h_eq
  apply translateX_xy_transcendental_2tor W xk yk h_ns h_2_tor
  refine ⟨Polynomial.X - Polynomial.C xk, Polynomial.X_sub_C_ne_zero xk, ?_⟩
  rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]

/-- `translateX_xy T ≠ algebraMap F KE c` for ANY `c ∈ F` and 2-torsion `T`.
Generalisation of `translateX_xy_ne_algebraMap_2tor` from the specific `xk`
to an arbitrary base-field constant. -/
theorem translateX_xy_2tor_ne_algebraMap_any
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) (c : F) :
    translateX_xy W xk yk ≠ algebraMap F KE c := by
  intro h_eq
  apply translateX_xy_transcendental_2tor W xk yk h_ns h_2_tor
  refine ⟨Polynomial.X - Polynomial.C c, Polynomial.X_sub_C_ne_zero c, ?_⟩
  rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]

/-- `translateX_xy T ≠ algebraMap F KE c` for ANY `c ∈ F` and non-2-torsion `T`.
Generalisation of `translateX_xy_neg_ne_algebraMap` to arbitrary `c`. -/
theorem translateX_xy_nonTor_ne_algebraMap_any
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) (c : F) :
    translateX_xy W xk yk ≠ algebraMap F KE c := by
  intro h_eq
  apply translateX_xy_transcendental W xk yk h_ns h_not_2_tor
  refine ⟨Polynomial.X - Polynomial.C c, Polynomial.X_sub_C_ne_zero c, ?_⟩
  rw [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h_eq, sub_self]

/-- **Unified `translateX_xy ≠ algebraMap F KE c`** for any base-field constant
`c` and any non-zero point `T = (xk, yk)` (regardless of 2-torsion). -/
theorem translateX_xy_ne_algebraMap_any
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) (c : F) :
    translateX_xy W xk yk ≠ algebraMap F KE c := by
  by_cases h : yk = W.toAffine.negY xk yk
  · exact translateX_xy_2tor_ne_algebraMap_any W xk yk h_ns h c
  · exact translateX_xy_nonTor_ne_algebraMap_any W xk yk h_ns h c

/-! ### Curve group law at 2-torsion: `liftSomePoint + liftSomePoint = 0`

For 2-torsion `T = (xk, yk)` (i.e., `yk = negY xk yk`), the lifted point
`liftSomePoint W xk yk h_ns ∈ (W_KE).toAffine.Point` is also 2-torsion
(the 2-torsion condition is preserved by `algebraMap F → KE` via
`Affine.map_negY`). Hence `T_lift + T_lift = 0` via Mathlib's
`Affine.Point.add_self_of_Y_eq`. -/

/-- For 2-torsion `T`, the lifted point is its own negation:
`liftSomePoint W xk yk + liftSomePoint W xk yk = 0`. -/
theorem liftSomePoint_add_self_eq_zero_of_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    liftSomePoint W xk yk h_ns + liftSomePoint W xk yk h_ns = 0 := by
  unfold liftSomePoint
  apply Affine.Point.add_self_of_Y_eq
  change algebraMap F KE yk =
    (W.map (algebraMap F KE)).toAffine.negY
      (algebraMap F KE xk) (algebraMap F KE yk)
  rw [WeierstrassCurve.Affine.map_negY (W' := W) (f := algebraMap F KE),
      ← h_2_tor]

/-- `translateAlgHom_of_2tor T y_gen = translateY_xy T`. -/
theorem translateAlgHom_of_2tor_apply_y_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    translateAlgHom_of_2tor W xk yk h_ns h_2_tor (y_gen W) =
      translateY_xy W xk yk := by
  let hxy : TranslateNonInverse W xk yk :=
    fun h ↦ x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h.1)
  unfold translateAlgHom_of_2tor translateAlgHom
  unfold y_gen
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change (translateCoordAlgHom W xk yk h_ns.1 hxy).toRingHom
      (AdjoinRoot.root W.toAffine.polynomial) =
    translateY_xy W xk yk
  change translateCoordRingHom W xk yk h_ns.1 hxy
      (AdjoinRoot.root W.toAffine.polynomial) =
    translateY_xy W xk yk
  unfold translateCoordRingHom
  exact AdjoinRoot.lift_root _

/-! ### Round-trip on `x_gen` for 2-torsion `T`: `τ²(x_gen) = x_gen`

Mirrors `translateAlgHom_round_trip_x_gen` but with σ = τ (since
−T = T for 2-torsion). The curve group law fact
`gen + T_lift + T_lift = gen` (via `liftSomePoint_add_self_eq_zero_of_2tor`)
replaces the `gen + T_lift + (−T)_lift = gen` used in the non-2-torsion
version. -/

/-- **Round-trip on `x_gen` for 2-torsion `T`**: applying
`translateAlgHom_of_2tor T` twice returns `x_gen`. -/
theorem translateAlgHom_of_2tor_round_trip_x_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    translateAlgHom_of_2tor W xk yk h_ns h_2_tor
        (translateAlgHom_of_2tor W xk yk h_ns h_2_tor (x_gen W)) =
      x_gen W := by
  rw [translateAlgHom_of_2tor_apply_x_gen W xk yk h_ns h_2_tor]
  set σ := translateAlgHom_of_2tor W xk yk h_ns h_2_tor
  have hσx : σ (x_gen W) = translateX_xy W xk yk :=
    translateAlgHom_of_2tor_apply_x_gen W xk yk h_ns h_2_tor
  have hσy : σ (y_gen W) = translateY_xy W xk yk :=
    translateAlgHom_of_2tor_apply_y_gen W xk yk h_ns h_2_tor
  unfold translateX_xy
  rw [σ_commutes_addX W (x_gen W) (algebraMap F KE xk)
        (translateSlope_xy W xk yk)]
  rw [σ.commutes xk, hσx]
  have hx_ne : x_gen W ≠ algebraMap F KE xk := fun h ↦
    x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h)
  have hx_σ_ne : σ (x_gen W) ≠ algebraMap F KE xk := by
    rw [hσx]
    exact translateX_xy_ne_algebraMap_2tor W xk yk h_ns h_2_tor
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk) := by
    rwa [σ.commutes]
  have h_slope_eq : σ (translateSlope_xy W xk yk) =
      (W_KE W).toAffine.slope (translateX_xy W xk yk)
        (algebraMap F KE xk)
        (translateY_xy W xk yk) (algebraMap F KE yk) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk)
        (y_gen W) (algebraMap F KE yk)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk, σ.commutes yk, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk yk h_ns) +
      liftSomePoint W xk yk h_ns = genericPoint W := by
    rw [add_assoc, liftSomePoint_add_self_eq_zero_of_2tor W xk yk h_ns h_2_tor,
        add_zero]
  have h_ne_2 : translateX_xy W xk yk ≠ algebraMap F KE xk :=
    translateX_xy_ne_algebraMap_2tor W xk yk h_ns h_2_tor
  rw [genericPoint_add_liftSomePoint W xk yk h_ns] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_ne_2)] at h_gen_eq
  unfold genericPoint at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.1

/-- **Round-trip on `y_gen` for 2-torsion `T`**: applying
`translateAlgHom_of_2tor T` twice returns `y_gen`. -/
theorem translateAlgHom_of_2tor_round_trip_y_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    translateAlgHom_of_2tor W xk yk h_ns h_2_tor
        (translateAlgHom_of_2tor W xk yk h_ns h_2_tor (y_gen W)) =
      y_gen W := by
  rw [translateAlgHom_of_2tor_apply_y_gen W xk yk h_ns h_2_tor]
  set σ := translateAlgHom_of_2tor W xk yk h_ns h_2_tor
  have hσx : σ (x_gen W) = translateX_xy W xk yk :=
    translateAlgHom_of_2tor_apply_x_gen W xk yk h_ns h_2_tor
  have hσy : σ (y_gen W) = translateY_xy W xk yk :=
    translateAlgHom_of_2tor_apply_y_gen W xk yk h_ns h_2_tor
  unfold translateY_xy
  rw [σ_commutes_addY W (x_gen W) (algebraMap F KE xk) (y_gen W)
        (translateSlope_xy W xk yk)]
  rw [σ.commutes xk, hσx, hσy]
  have hx_ne : x_gen W ≠ algebraMap F KE xk := fun h ↦
    x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h)
  have hx_σ_ne : σ (x_gen W) ≠ algebraMap F KE xk := by
    rw [hσx]
    exact translateX_xy_ne_algebraMap_2tor W xk yk h_ns h_2_tor
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk) := by
    rwa [σ.commutes]
  have h_slope_eq : σ (translateSlope_xy W xk yk) =
      (W_KE W).toAffine.slope (translateX_xy W xk yk)
        (algebraMap F KE xk)
        (translateY_xy W xk yk) (algebraMap F KE yk) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk)
        (y_gen W) (algebraMap F KE yk)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk, σ.commutes yk, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk yk h_ns) +
      liftSomePoint W xk yk h_ns = genericPoint W := by
    rw [add_assoc, liftSomePoint_add_self_eq_zero_of_2tor W xk yk h_ns h_2_tor,
        add_zero]
  have h_ne_2 : translateX_xy W xk yk ≠ algebraMap F KE xk :=
    translateX_xy_ne_algebraMap_2tor W xk yk h_ns h_2_tor
  rw [genericPoint_add_liftSomePoint W xk yk h_ns] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_ne_2)] at h_gen_eq
  unfold genericPoint at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.2

/-! ### `translateAlgEquiv_of_2tor` — translation by 2-torsion as a self-inverse AlgEquiv

For 2-torsion `T`, translation by `T` is its own inverse (since `2T = 0`).
The two round-trips combine via `algHom_ext_x_y_gen` to give the AlgEquiv. -/

/-- **Translation as an algebra equivalence** for 2-torsion `T`:
`τ_T : K(E) ≃ₐ[F] K(E)` whose action on the generic-point coordinates is
translation by `T`, with itself as inverse (since `2T = 0`). -/
noncomputable def translateAlgEquiv_of_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    KE ≃ₐ[F] KE :=
  AlgEquiv.ofAlgHom
    (translateAlgHom_of_2tor W xk yk h_ns h_2_tor)
    (translateAlgHom_of_2tor W xk yk h_ns h_2_tor)
    (algHom_ext_x_y_gen W
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_of_2tor_round_trip_x_gen W xk yk h_ns h_2_tor)
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_of_2tor_round_trip_y_gen W xk yk h_ns h_2_tor))
    (algHom_ext_x_y_gen W
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_of_2tor_round_trip_x_gen W xk yk h_ns h_2_tor)
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_of_2tor_round_trip_y_gen W xk yk h_ns h_2_tor))

/-! ### Translation as an `AlgEquiv` of `K(E)` over `F`

The four round-trips combined with `algHom_ext_x_y_gen` give the AlgEquiv
`τ_T : K(E) ≃ₐ[F] K(E)` whose action on the generic point coordinates is
translation by `T`. This is the function-field-level lift of the
group-translation `Affine.Point → Affine.Point` of Silverman §III.5. -/

/-- **Translation as an algebra equivalence** of `K(E)` over `F`.
For non-2-torsion `T = (xk, yk)`, the `F`-algebra automorphism of `K(E)`
sending `x_gen ↦ translateX_xy T`, `y_gen ↦ translateY_xy T`, with inverse
given by translation by `−T`. -/
noncomputable def translateAlgEquiv
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    KE ≃ₐ[F] KE :=
  AlgEquiv.ofAlgHom
    (translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor)
    (translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor)
    (algHom_ext_x_y_gen W
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_inv_round_trip_x_gen W xk yk h_ns h_not_2_tor)
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_inv_round_trip_y_gen W xk yk h_ns h_not_2_tor))
    (algHom_ext_x_y_gen W
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_round_trip_x_gen W xk yk h_ns h_not_2_tor)
      (by simp only [AlgHom.comp_apply, AlgHom.coe_id, id]
          exact translateAlgHom_round_trip_y_gen W xk yk h_ns h_not_2_tor))

/-! ### Unified `translateAlgEquivOfPoint` — case-dispatch over `Affine.Point`

Single F-algebra equivalence per point of `E(F)`, handling all three cases:
* `T = 0` (the identity point): `AlgEquiv.refl`.
* `T = (xk, yk)` with `yk = negY xk yk` (2-torsion non-zero):
  `translateAlgEquiv_of_2tor`.
* `T = (xk, yk)` with `yk ≠ negY xk yk` (non-2-torsion non-zero):
  `translateAlgEquiv`.

This is the unified action map needed for the `MulSemiringAction (ker β) K(E)`
instance (Layer 1 of the III.4.10(a) Galois route). The group-hom property
(translateAlgEquivOfPoint (T₁ + T₂) = trans of components) follows from the
curve group law lifted via `liftSomePoint_add_*` lemmas; ship in a separate
commit. -/

/-- **Unified translation AlgEquiv** by any point `T ∈ E(F)`. Identity at
`T = 0`, the 2-torsion AlgEquiv when `yk = negY xk yk`, and the non-2-torsion
AlgEquiv otherwise. -/
noncomputable def translateAlgEquivOfPoint :
    W.toAffine.Point → (KE ≃ₐ[F] KE)
  | .zero => AlgEquiv.refl
  | .some xk yk h_ns =>
      if h : yk = W.toAffine.negY xk yk then
        translateAlgEquiv_of_2tor W xk yk h_ns h
      else
        translateAlgEquiv W xk yk h_ns h

@[simp] theorem translateAlgEquivOfPoint_zero :
    translateAlgEquivOfPoint W .zero = AlgEquiv.refl := rfl

theorem translateAlgEquivOfPoint_some_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    translateAlgEquivOfPoint W (.some xk yk h_ns) =
      translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor := by
  unfold translateAlgEquivOfPoint
  exact dif_pos h_2_tor

theorem translateAlgEquivOfPoint_some_nonTor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateAlgEquivOfPoint W (.some xk yk h_ns) =
      translateAlgEquiv W xk yk h_ns h_not_2_tor := by
  unfold translateAlgEquivOfPoint
  exact dif_neg h_not_2_tor

/-! ### Identity action: the zero point acts as `AlgEquiv.refl` -/

/-- The translation AlgEquiv at `T = 0` is the identity on K(E). -/
@[simp] theorem translateAlgEquivOfPoint_zero_apply (f : KE) :
    translateAlgEquivOfPoint W .zero f = f := rfl

/-- The translation AlgEquiv at `T = 0` evaluated as an `AlgHom` is the
identity: `(translateAlgEquivOfPoint W .zero).toAlgHom = AlgHom.id F KE`. -/
theorem translateAlgEquivOfPoint_zero_toAlgHom :
    (translateAlgEquivOfPoint W .zero).toAlgHom = AlgHom.id F KE := by
  rw [translateAlgEquivOfPoint_zero]
  rfl

/-! ### Group-hom property — trivial cases

`translateAlgEquivOfPoint` respects addition on `Affine.Point`:
`translateAlgEquivOfPoint (T₁ + T₂) = (translateAlgEquivOfPoint T₁).trans
(translateAlgEquivOfPoint T₂)`.

Trivial cases: when either operand is `.zero`. The substantive cases
(both non-zero) require the curve group law lifted via `Point.map`
+ `genericPoint_add_liftSomePoint`; ship in follow-up commits. -/

/-- Group-hom property at `T₁ = 0`: `translateAlgEquivOfPoint (0 + T) =
(refl).trans (translateAlgEquivOfPoint T)`. -/
theorem translateAlgEquivOfPoint_zero_add (T : W.toAffine.Point) :
    translateAlgEquivOfPoint W (0 + T) =
      (translateAlgEquivOfPoint W 0).trans (translateAlgEquivOfPoint W T) := by
  rw [zero_add]
  apply AlgEquiv.ext
  intro f
  change translateAlgEquivOfPoint W T f =
    translateAlgEquivOfPoint W T (translateAlgEquivOfPoint W 0 f)
  rfl

/-- Group-hom property at `T₂ = 0`: `translateAlgEquivOfPoint (T + 0) =
(translateAlgEquivOfPoint T).trans (refl)`. -/
theorem translateAlgEquivOfPoint_add_zero (T : W.toAffine.Point) :
    translateAlgEquivOfPoint W (T + 0) =
      (translateAlgEquivOfPoint W T).trans (translateAlgEquivOfPoint W 0) := by
  rw [add_zero]
  apply AlgEquiv.ext
  intro f
  change translateAlgEquivOfPoint W T f =
    translateAlgEquivOfPoint W 0 (translateAlgEquivOfPoint W T f)
  rfl

/-! ### Lift function: `Affine.Point F → Affine.Point KE`

The lift `Point.map (Algebra.ofId F KE)` from F-points to KE-points. This is
a group hom by Mathlib's `Affine.Point.map` (Affine/Point.lean:793), giving
`lift (T₁ + T₂) = lift T₁ + lift T₂` via `map_add`. The lift connects
`liftSomePoint` to the abstract Mathlib machinery. -/

/-- The lift from `W.toAffine.Point` to `(W_KE W).toAffine.Point` via the
canonical `F →ₐ[F] KE`. -/
noncomputable def liftPointToKE :
    W.toAffine.Point →+ (W_KE W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId F KE)

/-- The lift sends `.zero` to `0`. -/
@[simp] theorem liftPointToKE_zero : liftPointToKE W 0 = 0 :=
  AddMonoidHom.map_zero _

/-- The lift is a group hom: `lift (T₁ + T₂) = lift T₁ + lift T₂`. -/
theorem liftPointToKE_add (T₁ T₂ : W.toAffine.Point) :
    liftPointToKE W (T₁ + T₂) = liftPointToKE W T₁ + liftPointToKE W T₂ :=
  AddMonoidHom.map_add _ _ _

/-- Identification of the abstract `liftPointToKE` with the explicit
`liftSomePoint` for `.some xk yk h_ns`. Both produce the lift of
`(xk, yk)` via `algebraMap`; the nonsingular witnesses are equal by
propositional irrelevance. -/
theorem liftPointToKE_some
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    liftPointToKE W (Affine.Point.some xk yk h_ns) =
      liftSomePoint W xk yk h_ns := rfl

/-- For non-zero T = `.some xk yk h_ns`, `(- T).some` decomposition:
`-T = .some xk (negY xk yk) ((nonsingular_neg).mpr h_ns)`. -/
theorem neg_some_eq_some
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    -(Affine.Point.some xk yk h_ns : W.toAffine.Point) =
      Affine.Point.some xk (W.toAffine.negY xk yk)
        ((Affine.nonsingular_neg xk yk).mpr h_ns) := rfl

/-- **2-tor + 2-tor sum is 2-tor**: if T₁, T₂ are 2-torsion and T₁+T₂ = some
xk₃ yk₃ h_ns₃ is non-zero, then yk₃ = negY xk₃ yk₃. -/
theorem sum_2tor_of_2tor_2tor
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃) :
    yk₃ = W.toAffine.negY xk₃ yk₃ := by
  have h₁ : Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₁ yk₁ h_ns₁ =
      (0 : W.toAffine.Point) :=
    Affine.Point.add_self_of_Y_eq (h₁ := h_ns₁) h_2_tor₁
  have h₂ : Affine.Point.some xk₂ yk₂ h_ns₂ + Affine.Point.some xk₂ yk₂ h_ns₂ =
      (0 : W.toAffine.Point) :=
    Affine.Point.add_self_of_Y_eq (h₁ := h_ns₂) h_2_tor₂
  have h_T₃_self_eq_zero :
      Affine.Point.some xk₃ yk₃ h_ns₃ +
        Affine.Point.some xk₃ yk₃ h_ns₃ = (0 : W.toAffine.Point) := by
    rw [← h_sum]
    have : (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂) +
        (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂) =
      (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₁ yk₁ h_ns₁) +
        (Affine.Point.some xk₂ yk₂ h_ns₂ + Affine.Point.some xk₂ yk₂ h_ns₂) := by
      abel
    rw [this, h₁, h₂, add_zero]
  rw [add_eq_zero_iff_eq_neg, neg_some_eq_some] at h_T₃_self_eq_zero
  exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp
    h_T₃_self_eq_zero).2

/-- **Mixed 2-tor / non-2-tor sum is non-2-tor**. -/
theorem sum_nonTor_of_2tor_nonTor
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃) :
    yk₃ ≠ W.toAffine.negY xk₃ yk₃ := by
  intro h_T₃_2tor
  have h₁ : Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₁ yk₁ h_ns₁ =
      (0 : W.toAffine.Point) :=
    Affine.Point.add_self_of_Y_eq (h₁ := h_ns₁) h_2_tor₁
  have h₃ : Affine.Point.some xk₃ yk₃ h_ns₃ + Affine.Point.some xk₃ yk₃ h_ns₃ =
      (0 : W.toAffine.Point) :=
    Affine.Point.add_self_of_Y_eq (h₁ := h_ns₃) h_T₃_2tor
  apply h_not_2_tor₂
  have h_T₂_self_zero : Affine.Point.some xk₂ yk₂ h_ns₂ +
      Affine.Point.some xk₂ yk₂ h_ns₂ = (0 : W.toAffine.Point) := by
    have h_T₃_eq := h₃
    rw [← h_sum] at h_T₃_eq
    have h_swap : (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂) +
        (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂) =
      (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₁ yk₁ h_ns₁) +
        (Affine.Point.some xk₂ yk₂ h_ns₂ + Affine.Point.some xk₂ yk₂ h_ns₂) := by
      abel
    rw [h_swap, h₁, zero_add] at h_T₃_eq
    exact h_T₃_eq
  rw [add_eq_zero_iff_eq_neg, neg_some_eq_some] at h_T₂_self_zero
  exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp h_T₂_self_zero).2

/-- **Mixed non-2-tor / 2-tor sum is non-2-tor**. -/
theorem sum_nonTor_of_nonTor_2tor
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃) :
    yk₃ ≠ W.toAffine.negY xk₃ yk₃ := by
  intro h_T₃_2tor
  have h₂ : Affine.Point.some xk₂ yk₂ h_ns₂ + Affine.Point.some xk₂ yk₂ h_ns₂ =
      (0 : W.toAffine.Point) :=
    Affine.Point.add_self_of_Y_eq (h₁ := h_ns₂) h_2_tor₂
  have h₃ : Affine.Point.some xk₃ yk₃ h_ns₃ + Affine.Point.some xk₃ yk₃ h_ns₃ =
      (0 : W.toAffine.Point) :=
    Affine.Point.add_self_of_Y_eq (h₁ := h_ns₃) h_T₃_2tor
  apply h_not_2_tor₁
  have h_T₁_self_zero : Affine.Point.some xk₁ yk₁ h_ns₁ +
      Affine.Point.some xk₁ yk₁ h_ns₁ = (0 : W.toAffine.Point) := by
    have h_T₃_eq := h₃
    rw [← h_sum] at h_T₃_eq
    have h_swap : (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂) +
        (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂) =
      (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₁ yk₁ h_ns₁) +
        (Affine.Point.some xk₂ yk₂ h_ns₂ + Affine.Point.some xk₂ yk₂ h_ns₂) := by
      abel
    rw [h_swap, h₂, add_zero] at h_T₃_eq
    exact h_T₃_eq
  rw [add_eq_zero_iff_eq_neg, neg_some_eq_some] at h_T₁_self_zero
  exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp h_T₁_self_zero).2

/-! ### Group-hom branch: 2-torsion self-composition

For 2-torsion `T` (non-zero), `T + T = 2T = 0`, and the corresponding
group-hom statement reduces to
`(translateAlgEquiv_of_2tor T).trans (translateAlgEquiv_of_2tor T) = refl`.

Proof: `translateAlgEquiv_of_2tor T` has equal `toFun` and `invFun`
(both `translateAlgHom_of_2tor T`), so `.symm = id`. Then
`AlgEquiv.self_trans_symm` finishes. -/

/-- The 2-torsion AlgEquiv is its own inverse: `(τ_T).symm = τ_T`. -/
theorem translateAlgEquiv_of_2tor_symm
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor).symm =
      translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor := by
  apply AlgEquiv.ext
  intro f
  rfl

/-- 2-torsion self-composition equals the identity: this is the group-hom
property for the case `T₁ = T₂ = T` with `T` 2-torsion (so `T₁ + T₂ = 0`). -/
theorem translateAlgEquiv_of_2tor_self_trans
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    (translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor).trans
        (translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor) =
      AlgEquiv.refl := by
  conv_lhs => rw [← translateAlgEquiv_of_2tor_symm W xk yk h_ns h_2_tor]
  exact AlgEquiv.self_trans_symm _

/-- **Group-hom for `T + T = 0` at 2-torsion `T`** (first non-trivial branch):
`translateAlgEquivOfPoint W (T + T) = (τ_T).trans (τ_T)` for 2-torsion `T`,
since both sides equal `AlgEquiv.refl`. -/
theorem translateAlgEquivOfPoint_2tor_add_self
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    let T := Affine.Point.some xk yk h_ns
    translateAlgEquivOfPoint W (T + T) =
      (translateAlgEquivOfPoint W T).trans (translateAlgEquivOfPoint W T) := by
  simp only
  have h_add : Affine.Point.some xk yk h_ns +
      Affine.Point.some xk yk h_ns = (0 : W.toAffine.Point) :=
    Affine.Point.add_self_of_Y_eq h_2_tor
  rw [h_add]
  change translateAlgEquivOfPoint W .zero =
    (translateAlgEquivOfPoint W (.some xk yk h_ns)).trans
      (translateAlgEquivOfPoint W (.some xk yk h_ns))
  rw [translateAlgEquivOfPoint_zero]
  rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h_2_tor]
  exact (translateAlgEquiv_of_2tor_self_trans W xk yk h_ns h_2_tor).symm

/-! ### Group-hom branch: non-2-torsion `T + (-T) = 0`

For non-2-torsion `T`, `T + (-T) = 0`, and the group-hom statement at this
case is `(τ_T).trans (τ_(-T)) = refl`. We show `(τ_T).symm = τ_(-T)` and
finish via `AlgEquiv.self_trans_symm`. -/

/-- For non-2-torsion `T`, `(translateAlgEquiv T).symm = translateAlgEquivOfPoint (-T)`.
Both are `AlgEquiv.ofAlgHom (translateAlgHom_of_nonTorsion_neg) (translateAlgHom_of_nonTorsion) ...`
modulo Prop irrelevance on the witnesses. -/
theorem translateAlgEquiv_symm_eq_neg_point
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (translateAlgEquiv W xk yk h_ns h_not_2_tor).symm =
      translateAlgEquivOfPoint W (-(Affine.Point.some xk yk h_ns)) := by
  apply AlgEquiv.ext
  intro f
  change translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor f =
    translateAlgEquivOfPoint W (.some xk (W.toAffine.negY xk yk)
      ((Affine.nonsingular_neg xk yk).mpr h_ns)) f
  have h_not_2_tor_neg :
      W.toAffine.negY xk yk ≠ W.toAffine.negY xk (W.toAffine.negY xk yk) := by
    rw [negY_negY_eq W xk yk]
    exact (Ne.symm h_not_2_tor)
  rw [translateAlgEquivOfPoint_some_nonTor W xk (W.toAffine.negY xk yk)
        ((Affine.nonsingular_neg xk yk).mpr h_ns) h_not_2_tor_neg]
  rfl

/-- **Group-hom for `T + (-T) = 0` at non-2-torsion `T`**: both sides equal
`AlgEquiv.refl` (via `(τ_T).symm = τ_(-T)` + `self_trans_symm`). -/
theorem translateAlgEquivOfPoint_nonTor_add_neg
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    let T := Affine.Point.some xk yk h_ns
    translateAlgEquivOfPoint W (T + (-T)) =
      (translateAlgEquivOfPoint W T).trans (translateAlgEquivOfPoint W (-T)) := by
  simp only
  have h_add : Affine.Point.some xk yk h_ns +
      -(Affine.Point.some xk yk h_ns) = (0 : W.toAffine.Point) :=
    add_neg_cancel _
  rw [h_add]
  change translateAlgEquivOfPoint W .zero =
    (translateAlgEquivOfPoint W (.some xk yk h_ns)).trans
      (translateAlgEquivOfPoint W (-(.some xk yk h_ns)))
  rw [translateAlgEquivOfPoint_zero,
      translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h_not_2_tor]
  rw [← translateAlgEquiv_symm_eq_neg_point W xk yk h_ns h_not_2_tor]
  exact (AlgEquiv.self_trans_symm _).symm

/-! ### Group-hom branch: substantive non-zero/non-zero/sum-non-zero (x_gen)

For non-2-torsion `T₁`, `T₂` with `T₁ + T₂ = .some xk₃ yk₃ h_ns₃` non-2-torsion,
the proof on `x_gen` mirrors `translateAlgHom_round_trip_x_gen` with the
key change: the curve group law fact becomes
`(gen + lift T₂) + lift T₁ = gen + lift(T₁+T₂)` (via commutativity +
`liftPointToKE_add` + `liftPointToKE_some`), replacing the round-trip's
`gen + lift T₁ + lift(-T₁) = gen`. -/

/-- **Substantive group-hom on x_gen** for non-2-torsion T₁, T₂ with non-2-torsion
non-zero sum `T₁ + T₂ = some xk₃ yk₃ h_ns₃`. -/
theorem translateAlgEquivOfPoint_add_nonTor_x_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (x_gen W)) =
      translateX_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_apply_x_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_apply_y_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  rw [translateAlgHom_apply_x_gen W xk₁ yk₁ h_ns₁ h_not_2_tor₁]
  unfold translateX_xy
  rw [σ_commutes_addX W (x_gen W) (algebraMap F KE xk₁)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.1

/-- **Substantive group-hom on y_gen** for non-2-torsion T₁, T₂ with non-2-torsion
non-zero sum `T₁ + T₂ = some xk₃ yk₃ h_ns₃`. Parallel of the x_gen case
with translateY_xy / addY in place of translateX_xy / addX. -/
theorem translateAlgEquivOfPoint_add_nonTor_y_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (y_gen W)) =
      translateY_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_apply_x_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_apply_y_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  rw [translateAlgHom_apply_y_gen W xk₁ yk₁ h_ns₁ h_not_2_tor₁]
  unfold translateY_xy
  rw [σ_commutes_addY W (x_gen W) (algebraMap F KE xk₁) (y_gen W)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx, hσy]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.2

/-! ### Group-hom branch: 2-torsion + 2-torsion with non-zero sum

For 2-torsion T₁, T₂ with T₁ + T₂ = some xk₃ yk₃ (non-zero), the sum T₃
is also 2-torsion (since 2T₃ = 2T₁ + 2T₂ = 0). Proof mirrors the non-2-tor
substantive case with translateAlgHom_of_2tor in place of
translateAlgHom_of_nonTorsion. -/

/-- **Substantive group-hom on x_gen for 2-tor T₁, T₂, sum non-zero**: parallel
of the non-2-tor case using translateAlgHom_of_2tor. -/
theorem translateAlgEquivOfPoint_add_2tor_x_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (x_gen W)) =
      translateX_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_x_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_y_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  rw [translateAlgHom_of_2tor_apply_x_gen W xk₁ yk₁ h_ns₁ h_2_tor₁]
  unfold translateX_xy
  rw [σ_commutes_addX W (x_gen W) (algebraMap F KE xk₁)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.1

/-- **Substantive group-hom on y_gen for 2-tor T₁, T₂, sum non-zero**. -/
theorem translateAlgEquivOfPoint_add_2tor_y_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (y_gen W)) =
      translateY_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_x_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_y_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  rw [translateAlgHom_of_2tor_apply_y_gen W xk₁ yk₁ h_ns₁ h_2_tor₁]
  unfold translateY_xy
  rw [σ_commutes_addY W (x_gen W) (algebraMap F KE xk₁) (y_gen W)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx, hσy]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.2

/-! ### Group-hom branch: mixed (2-tor T₁ + non-2-tor T₂)

The mixed case `T₁ 2-tor + T₂ non-2-tor + T₁+T₂ non-zero` (and the
symmetric `T₁ non-2-tor + T₂ 2-tor`). The sum `T₁ + T₂` is non-2-torsion
(since 2(T₁+T₂) = 0 + 2T₂ = 2T₂ ≠ 0 for non-2-tor T₂). The proof
template is the same as the pure-non-2-tor case but with translateAlgHom_of_2tor
applied for T₁ in the σ-commutation chain. -/

/-- **Mixed: 2-tor T₁ + non-2-tor T₂, sum non-2-tor non-zero, x_gen**. -/
theorem translateAlgEquivOfPoint_add_2tor_nonTor_x_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (x_gen W)) =
      translateX_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_apply_x_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_apply_y_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  rw [translateAlgHom_of_2tor_apply_x_gen W xk₁ yk₁ h_ns₁ h_2_tor₁]
  unfold translateX_xy
  rw [σ_commutes_addX W (x_gen W) (algebraMap F KE xk₁)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.1

/-- **Mixed: 2-tor T₁ + non-2-tor T₂, sum non-2-tor non-zero, y_gen**. -/
theorem translateAlgEquivOfPoint_add_2tor_nonTor_y_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (y_gen W)) =
      translateY_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_apply_x_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_apply_y_gen W xk₂ yk₂ h_ns₂ h_not_2_tor₂
  rw [translateAlgHom_of_2tor_apply_y_gen W xk₁ yk₁ h_ns₁ h_2_tor₁]
  unfold translateY_xy
  rw [σ_commutes_addY W (x_gen W) (algebraMap F KE xk₁) (y_gen W)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx, hσy]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.2

/-- **Mixed: non-2-tor T₁ + 2-tor T₂, sum non-2-tor non-zero, x_gen**. -/
theorem translateAlgEquivOfPoint_add_nonTor_2tor_x_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (x_gen W)) =
      translateX_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_x_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_y_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  rw [translateAlgHom_apply_x_gen W xk₁ yk₁ h_ns₁ h_not_2_tor₁]
  unfold translateX_xy
  rw [σ_commutes_addX W (x_gen W) (algebraMap F KE xk₁)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.1

/-- **Mixed: non-2-tor T₁ + 2-tor T₂, sum non-2-tor non-zero, y_gen**. -/
theorem translateAlgEquivOfPoint_add_nonTor_2tor_y_gen
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (y_gen W)) =
      translateY_xy W xk₃ yk₃ := by
  set σ := translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσx : σ (x_gen W) = translateX_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_x_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  have hσy : σ (y_gen W) = translateY_xy W xk₂ yk₂ :=
    translateAlgHom_of_2tor_apply_y_gen W xk₂ yk₂ h_ns₂ h_2_tor₂
  rw [translateAlgHom_apply_y_gen W xk₁ yk₁ h_ns₁ h_not_2_tor₁]
  unfold translateY_xy
  rw [σ_commutes_addY W (x_gen W) (algebraMap F KE xk₁) (y_gen W)
        (translateSlope_xy W xk₁ yk₁)]
  rw [σ.commutes xk₁, hσx, hσy]
  have hx_ne : x_gen W ≠ algebraMap F KE xk₁ := fun h ↦
    x_gen_sub_const_ne_zero W xk₁ (sub_eq_zero.mpr h)
  have hx_σ_ne_full : σ (x_gen W) ≠ σ (algebraMap F KE xk₁) := by
    rwa [σ.commutes, hσx]
  have h_slope_eq : σ (translateSlope_xy W xk₁ yk₁) =
      (W_KE W).toAffine.slope (translateX_xy W xk₂ yk₂)
        (algebraMap F KE xk₁)
        (translateY_xy W xk₂ yk₂) (algebraMap F KE yk₁) := by
    change σ ((W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk₁)
        (y_gen W) (algebraMap F KE yk₁)) = _
    rw [σ_commutes_slope_of_X_ne W hx_ne hx_σ_ne_full]
    rw [σ.commutes xk₁, σ.commutes yk₁, hσx, hσy]
  rw [h_slope_eq]
  have h_gen_eq : (genericPoint W + liftSomePoint W xk₂ yk₂ h_ns₂) +
      liftSomePoint W xk₁ yk₁ h_ns₁ = genericPoint W +
        liftSomePoint W xk₃ yk₃ h_ns₃ := by
    rw [add_assoc, add_comm (liftSomePoint W xk₂ yk₂ h_ns₂)
      (liftSomePoint W xk₁ yk₁ h_ns₁)]
    congr 1
    have h₁ := (liftPointToKE_some W xk₁ yk₁ h_ns₁).symm
    have h₂ := (liftPointToKE_some W xk₂ yk₂ h_ns₂).symm
    have h₃ := (liftPointToKE_some W xk₃ yk₃ h_ns₃).symm
    rw [h₁, h₂, h₃]
    rw [← liftPointToKE_add]
    rw [show (Affine.Point.some xk₁ yk₁ h_ns₁ + Affine.Point.some xk₂ yk₂ h_ns₂
        : W.toAffine.Point) = Affine.Point.some xk₃ yk₃ h_ns₃ from h_sum]
  rw [genericPoint_add_liftSomePoint W xk₂ yk₂ h_ns₂] at h_gen_eq
  rw [genericPoint_add_liftSomePoint W xk₃ yk₃ h_ns₃] at h_gen_eq
  unfold liftSomePoint at h_gen_eq
  rw [Affine.Point.add_of_X_ne (h_x₂_ne)] at h_gen_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_gen_eq |>.2

/-- **Master mixed (non-2-tor T₁ + 2-tor T₂) case** at AlgEquiv level. -/
theorem translateAlgEquivOfPoint_add_nonTor_2tor_main
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_not_2_tor₃ : yk₃ ≠ W.toAffine.negY xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgEquivOfPoint W (Affine.Point.some xk₃ yk₃ h_ns₃) =
      (translateAlgEquivOfPoint W (Affine.Point.some xk₁ yk₁ h_ns₁)).trans
        (translateAlgEquivOfPoint W (Affine.Point.some xk₂ yk₂ h_ns₂)) := by
  rw [translateAlgEquivOfPoint_some_nonTor W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
  rw [translateAlgEquivOfPoint_some_nonTor W xk₁ yk₁ h_ns₁ h_not_2_tor₁]
  rw [translateAlgEquivOfPoint_some_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂]
  apply AlgEquiv.coe_algHom_injective
  apply algHom_ext_x_y_gen W
  · change translateAlgHom_of_nonTorsion W xk₃ yk₃ h_ns₃ h_not_2_tor₃ (x_gen W) =
      translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (x_gen W))
    rw [translateAlgHom_apply_x_gen W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
    exact (translateAlgEquivOfPoint_add_nonTor_2tor_x_gen W xk₁ yk₁ h_ns₁
      h_not_2_tor₁ xk₂ yk₂ h_ns₂ h_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm
  · change translateAlgHom_of_nonTorsion W xk₃ yk₃ h_ns₃ h_not_2_tor₃ (y_gen W) =
      translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (y_gen W))
    rw [translateAlgHom_apply_y_gen W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
    exact (translateAlgEquivOfPoint_add_nonTor_2tor_y_gen W xk₁ yk₁ h_ns₁
      h_not_2_tor₁ xk₂ yk₂ h_ns₂ h_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm

/-- **Master mixed (2-tor T₁ + non-2-tor T₂) case** at AlgEquiv level. -/
theorem translateAlgEquivOfPoint_add_2tor_nonTor_main
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_not_2_tor₃ : yk₃ ≠ W.toAffine.negY xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgEquivOfPoint W (Affine.Point.some xk₃ yk₃ h_ns₃) =
      (translateAlgEquivOfPoint W (Affine.Point.some xk₁ yk₁ h_ns₁)).trans
        (translateAlgEquivOfPoint W (Affine.Point.some xk₂ yk₂ h_ns₂)) := by
  rw [translateAlgEquivOfPoint_some_nonTor W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
  rw [translateAlgEquivOfPoint_some_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁]
  rw [translateAlgEquivOfPoint_some_nonTor W xk₂ yk₂ h_ns₂ h_not_2_tor₂]
  apply AlgEquiv.coe_algHom_injective
  apply algHom_ext_x_y_gen W
  · change translateAlgHom_of_nonTorsion W xk₃ yk₃ h_ns₃ h_not_2_tor₃ (x_gen W) =
      translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (x_gen W))
    rw [translateAlgHom_apply_x_gen W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
    exact (translateAlgEquivOfPoint_add_2tor_nonTor_x_gen W xk₁ yk₁ h_ns₁
      h_2_tor₁ xk₂ yk₂ h_ns₂ h_not_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm
  · change translateAlgHom_of_nonTorsion W xk₃ yk₃ h_ns₃ h_not_2_tor₃ (y_gen W) =
      translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (y_gen W))
    rw [translateAlgHom_apply_y_gen W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
    exact (translateAlgEquivOfPoint_add_2tor_nonTor_y_gen W xk₁ yk₁ h_ns₁
      h_2_tor₁ xk₂ yk₂ h_ns₂ h_not_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm

/-- **Master 2-tor + 2-tor + sum non-zero case** at the AlgEquiv level. -/
theorem translateAlgEquivOfPoint_add_2tor_main
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_2_tor₁ : yk₁ = W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_2_tor₂ : yk₂ = W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_2_tor₃ : yk₃ = W.toAffine.negY xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgEquivOfPoint W (Affine.Point.some xk₃ yk₃ h_ns₃) =
      (translateAlgEquivOfPoint W (Affine.Point.some xk₁ yk₁ h_ns₁)).trans
        (translateAlgEquivOfPoint W (Affine.Point.some xk₂ yk₂ h_ns₂)) := by
  rw [translateAlgEquivOfPoint_some_2tor W xk₃ yk₃ h_ns₃ h_2_tor₃]
  rw [translateAlgEquivOfPoint_some_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁]
  rw [translateAlgEquivOfPoint_some_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂]
  apply AlgEquiv.coe_algHom_injective
  apply algHom_ext_x_y_gen W
  · change translateAlgHom_of_2tor W xk₃ yk₃ h_ns₃ h_2_tor₃ (x_gen W) =
      translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (x_gen W))
    rw [translateAlgHom_of_2tor_apply_x_gen W xk₃ yk₃ h_ns₃ h_2_tor₃]
    exact (translateAlgEquivOfPoint_add_2tor_x_gen W xk₁ yk₁ h_ns₁
      h_2_tor₁ xk₂ yk₂ h_ns₂ h_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm
  · change translateAlgHom_of_2tor W xk₃ yk₃ h_ns₃ h_2_tor₃ (y_gen W) =
      translateAlgHom_of_2tor W xk₂ yk₂ h_ns₂ h_2_tor₂
        (translateAlgHom_of_2tor W xk₁ yk₁ h_ns₁ h_2_tor₁ (y_gen W))
    rw [translateAlgHom_of_2tor_apply_y_gen W xk₃ yk₃ h_ns₃ h_2_tor₃]
    exact (translateAlgEquivOfPoint_add_2tor_y_gen W xk₁ yk₁ h_ns₁
      h_2_tor₁ xk₂ yk₂ h_ns₂ h_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm

/-- **Master non-2-tor T₁ + non-2-tor T₂ with 2-tor sum**: the variant of
the non-2-tor master theorem when T₁+T₂ happens to be 2-torsion. The
per-component lemmas don't depend on T₃'s 2-tor status, so we reuse them. -/
theorem translateAlgEquivOfPoint_add_nonTor_main_2torSum
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_2_tor₃ : yk₃ = W.toAffine.negY xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgEquivOfPoint W (Affine.Point.some xk₃ yk₃ h_ns₃) =
      (translateAlgEquivOfPoint W (Affine.Point.some xk₁ yk₁ h_ns₁)).trans
        (translateAlgEquivOfPoint W (Affine.Point.some xk₂ yk₂ h_ns₂)) := by
  rw [translateAlgEquivOfPoint_some_2tor W xk₃ yk₃ h_ns₃ h_2_tor₃]
  rw [translateAlgEquivOfPoint_some_nonTor W xk₁ yk₁ h_ns₁ h_not_2_tor₁]
  rw [translateAlgEquivOfPoint_some_nonTor W xk₂ yk₂ h_ns₂ h_not_2_tor₂]
  apply AlgEquiv.coe_algHom_injective
  apply algHom_ext_x_y_gen W
  · change translateAlgHom_of_2tor W xk₃ yk₃ h_ns₃ h_2_tor₃ (x_gen W) =
      translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (x_gen W))
    rw [translateAlgHom_of_2tor_apply_x_gen W xk₃ yk₃ h_ns₃ h_2_tor₃]
    exact (translateAlgEquivOfPoint_add_nonTor_x_gen W xk₁ yk₁ h_ns₁
      h_not_2_tor₁ xk₂ yk₂ h_ns₂ h_not_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm
  · change translateAlgHom_of_2tor W xk₃ yk₃ h_ns₃ h_2_tor₃ (y_gen W) =
      translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (y_gen W))
    rw [translateAlgHom_of_2tor_apply_y_gen W xk₃ yk₃ h_ns₃ h_2_tor₃]
    exact (translateAlgEquivOfPoint_add_nonTor_y_gen W xk₁ yk₁ h_ns₁
      h_not_2_tor₁ xk₂ yk₂ h_ns₂ h_not_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm

/-- **Master substantive case (non-2-tor / non-2-tor / non-2-tor sum)** of the
group-hom property at the AlgEquiv level. Combines the per-component
x_gen and y_gen results via algHom_ext_x_y_gen. -/
theorem translateAlgEquivOfPoint_add_nonTor_main
    (xk₁ yk₁ : F) (h_ns₁ : W.toAffine.Nonsingular xk₁ yk₁)
    (h_not_2_tor₁ : yk₁ ≠ W.toAffine.negY xk₁ yk₁)
    (xk₂ yk₂ : F) (h_ns₂ : W.toAffine.Nonsingular xk₂ yk₂)
    (h_not_2_tor₂ : yk₂ ≠ W.toAffine.negY xk₂ yk₂)
    (xk₃ yk₃ : F) (h_ns₃ : W.toAffine.Nonsingular xk₃ yk₃)
    (h_not_2_tor₃ : yk₃ ≠ W.toAffine.negY xk₃ yk₃)
    (h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
        Affine.Point.some xk₂ yk₂ h_ns₂ =
      Affine.Point.some xk₃ yk₃ h_ns₃)
    (h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁) :
    translateAlgEquivOfPoint W (Affine.Point.some xk₃ yk₃ h_ns₃) =
      (translateAlgEquivOfPoint W (Affine.Point.some xk₁ yk₁ h_ns₁)).trans
        (translateAlgEquivOfPoint W (Affine.Point.some xk₂ yk₂ h_ns₂)) := by
  rw [translateAlgEquivOfPoint_some_nonTor W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
  rw [translateAlgEquivOfPoint_some_nonTor W xk₁ yk₁ h_ns₁ h_not_2_tor₁]
  rw [translateAlgEquivOfPoint_some_nonTor W xk₂ yk₂ h_ns₂ h_not_2_tor₂]
  apply AlgEquiv.coe_algHom_injective
  apply algHom_ext_x_y_gen W
  · change translateAlgHom_of_nonTorsion W xk₃ yk₃ h_ns₃ h_not_2_tor₃ (x_gen W) =
      translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (x_gen W))
    rw [translateAlgHom_apply_x_gen W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
    exact (translateAlgEquivOfPoint_add_nonTor_x_gen W xk₁ yk₁ h_ns₁
      h_not_2_tor₁ xk₂ yk₂ h_ns₂ h_not_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm
  · change translateAlgHom_of_nonTorsion W xk₃ yk₃ h_ns₃ h_not_2_tor₃ (y_gen W) =
      translateAlgHom_of_nonTorsion W xk₂ yk₂ h_ns₂ h_not_2_tor₂
        (translateAlgHom_of_nonTorsion W xk₁ yk₁ h_ns₁ h_not_2_tor₁ (y_gen W))
    rw [translateAlgHom_apply_y_gen W xk₃ yk₃ h_ns₃ h_not_2_tor₃]
    exact (translateAlgEquivOfPoint_add_nonTor_y_gen W xk₁ yk₁ h_ns₁
      h_not_2_tor₁ xk₂ yk₂ h_ns₂ h_not_2_tor₂ xk₃ yk₃ h_ns₃ h_sum h_x₂_ne).symm

/-! ### Master group-hom theorem `translateAlgEquivOfPoint_add`

Assembles all 6 case-master sub-theorems into the unconditional group-hom
property. Case dispatch:
* T₁ = 0: `translateAlgEquivOfPoint_zero_add`.
* T₂ = 0: `translateAlgEquivOfPoint_add_zero`.
* T₁, T₂ both `.some`, T₁+T₂ = 0:
  - T₁ 2-tor: `translateAlgEquivOfPoint_2tor_add_self` (T₂ = -T₁ = T₁).
  - T₁ non-2-tor: `translateAlgEquivOfPoint_nonTor_add_neg` (T₂ = -T₁).
* T₁, T₂ both `.some`, T₁+T₂ = `.some xk₃ yk₃ h_ns₃`:
  - (2-tor T₁, 2-tor T₂): sum 2-tor (`sum_2tor_of_2tor_2tor`) →
    `translateAlgEquivOfPoint_add_2tor_main`.
  - (2-tor T₁, non-2-tor T₂): sum non-2-tor (`sum_nonTor_of_2tor_nonTor`)
    → `translateAlgEquivOfPoint_add_2tor_nonTor_main`.
  - (non-2-tor T₁, 2-tor T₂): sum non-2-tor (`sum_nonTor_of_nonTor_2tor`)
    → `translateAlgEquivOfPoint_add_nonTor_2tor_main`.
  - (non-2-tor T₁, non-2-tor T₂): sum can be either; case-split.

The `h_x₂_ne : translateX_xy ≠ algebraMap` hypothesis is auto-discharged
via `translateX_xy_ne_algebraMap_any`. -/

/-- **Master group-hom theorem** for `translateAlgEquivOfPoint`. -/
theorem translateAlgEquivOfPoint_add (T₁ T₂ : W.toAffine.Point) :
    translateAlgEquivOfPoint W (T₁ + T₂) =
      (translateAlgEquivOfPoint W T₁).trans (translateAlgEquivOfPoint W T₂) := by
  rcases T₁ with _ | ⟨xk₁, yk₁, h_ns₁⟩
  · exact translateAlgEquivOfPoint_zero_add W T₂
  rcases T₂ with _ | ⟨xk₂, yk₂, h_ns₂⟩
  · exact translateAlgEquivOfPoint_add_zero W _
  cases h_sum : Affine.Point.some xk₁ yk₁ h_ns₁ +
      Affine.Point.some xk₂ yk₂ h_ns₂ with
  | zero =>
    have h_T₂_neg_T₁ : Affine.Point.some xk₂ yk₂ h_ns₂ =
        -(Affine.Point.some xk₁ yk₁ h_ns₁ : W.toAffine.Point) :=
      (neg_eq_of_add_eq_zero_right h_sum).symm
    rw [translateAlgEquivOfPoint_zero, h_T₂_neg_T₁]
    by_cases h_T₁_2tor : yk₁ = W.toAffine.negY xk₁ yk₁
    · have h_neg_eq : -(Affine.Point.some xk₁ yk₁ h_ns₁ : W.toAffine.Point) =
          Affine.Point.some xk₁ yk₁ h_ns₁ := by
        rw [neg_some_eq_some]
        congr 1
        exact h_T₁_2tor.symm
      rw [h_neg_eq, translateAlgEquivOfPoint_some_2tor W xk₁ yk₁ h_ns₁ h_T₁_2tor]
      exact (translateAlgEquiv_of_2tor_self_trans W xk₁ yk₁ h_ns₁ h_T₁_2tor).symm
    · rw [translateAlgEquivOfPoint_some_nonTor W xk₁ yk₁ h_ns₁ h_T₁_2tor]
      rw [← translateAlgEquiv_symm_eq_neg_point W xk₁ yk₁ h_ns₁ h_T₁_2tor]
      exact (AlgEquiv.self_trans_symm _).symm
  | some xk₃ yk₃ h_ns₃ =>
    have h_x₂_ne : translateX_xy W xk₂ yk₂ ≠ algebraMap F KE xk₁ :=
      translateX_xy_ne_algebraMap_any W xk₂ yk₂ h_ns₂ xk₁
    by_cases h_T₁_2tor : yk₁ = W.toAffine.negY xk₁ yk₁
    · by_cases h_T₂_2tor : yk₂ = W.toAffine.negY xk₂ yk₂
      · have h_T₃_2tor := sum_2tor_of_2tor_2tor W xk₁ yk₁ h_ns₁ h_T₁_2tor
          xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_sum
        exact translateAlgEquivOfPoint_add_2tor_main W xk₁ yk₁ h_ns₁ h_T₁_2tor
          xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_T₃_2tor h_sum h_x₂_ne
      · have h_T₃_not_2tor := sum_nonTor_of_2tor_nonTor W xk₁ yk₁ h_ns₁ h_T₁_2tor
          xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_sum
        exact translateAlgEquivOfPoint_add_2tor_nonTor_main W xk₁ yk₁ h_ns₁ h_T₁_2tor
          xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_T₃_not_2tor h_sum h_x₂_ne
    · by_cases h_T₂_2tor : yk₂ = W.toAffine.negY xk₂ yk₂
      · have h_T₃_not_2tor := sum_nonTor_of_nonTor_2tor W xk₁ yk₁ h_ns₁ h_T₁_2tor
          xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_sum
        exact translateAlgEquivOfPoint_add_nonTor_2tor_main W xk₁ yk₁ h_ns₁ h_T₁_2tor
          xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_T₃_not_2tor h_sum h_x₂_ne
      · by_cases h_T₃_2tor : yk₃ = W.toAffine.negY xk₃ yk₃
        · exact translateAlgEquivOfPoint_add_nonTor_main_2torSum W xk₁ yk₁ h_ns₁
            h_T₁_2tor xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_T₃_2tor h_sum h_x₂_ne
        · exact translateAlgEquivOfPoint_add_nonTor_main W xk₁ yk₁ h_ns₁ h_T₁_2tor
            xk₂ yk₂ h_ns₂ h_T₂_2tor xk₃ yk₃ h_ns₃ h_T₃_2tor h_sum h_x₂_ne

/-- **Pointwise translation composition**: `τ_{S₁+S₂}(x) = τ_{S₂}(τ_{S₁}(x))`. -/
theorem translateAlgEquivOfPoint_add_apply (S₁ S₂ : W.toAffine.Point) (x : KE) :
    translateAlgEquivOfPoint W (S₁ + S₂) x =
      translateAlgEquivOfPoint W S₂ (translateAlgEquivOfPoint W S₁ x) := by
  rw [translateAlgEquivOfPoint_add, AlgEquiv.trans_apply]

/-! ### `MulSemiringAction` packaging

Bundle the kernel-translation action `translateAlgEquivOfPoint` into
Mathlib's `MulSemiringAction (Multiplicative W.toAffine.Point) K(E)`
typeclass. The acting group is the multiplicative version of the
additive `Affine.Point` — the conversion is via `Multiplicative.toAdd`. -/

/-- **`MulSemiringAction` instance** for the kernel-translation action.
The `mul_smul` axiom is the master group-hom theorem
`translateAlgEquivOfPoint_add` (modulo `add_comm` to align the
composition direction); the ring-hom axioms (`smul_zero`, `smul_add`,
`smul_one`, `smul_mul`) follow from `AlgEquiv` being a ring hom. -/
noncomputable instance translateMulSemiringAction :
    MulSemiringAction (Multiplicative W.toAffine.Point) KE where
  smul g f := translateAlgEquivOfPoint W (Multiplicative.toAdd g) f
  one_smul f := by
    change translateAlgEquivOfPoint W (0 : W.toAffine.Point) f = f
    rfl
  mul_smul g₁ g₂ f := by
    change translateAlgEquivOfPoint W
        (Multiplicative.toAdd g₁ + Multiplicative.toAdd g₂) f =
      translateAlgEquivOfPoint W (Multiplicative.toAdd g₁)
        (translateAlgEquivOfPoint W (Multiplicative.toAdd g₂) f)
    rw [add_comm]
    have h := translateAlgEquivOfPoint_add W (Multiplicative.toAdd g₂)
      (Multiplicative.toAdd g₁)
    exact congrFun (congrArg DFunLike.coe h) f
  smul_zero g :=
    map_zero (translateAlgEquivOfPoint W (Multiplicative.toAdd g))
  smul_add g f₁ f₂ :=
    map_add (translateAlgEquivOfPoint W (Multiplicative.toAdd g)) f₁ f₂
  smul_one g :=
    map_one (translateAlgEquivOfPoint W (Multiplicative.toAdd g))
  smul_mul g f₁ f₂ :=
    map_mul (translateAlgEquivOfPoint W (Multiplicative.toAdd g)) f₁ f₂

/-! ### Injectivity of `translateAlgEquivOfPoint`

The map `W.toAffine.Point → (KE ≃ₐ[F] KE)` is injective: distinct points give
distinct translation AlgEquivs. The substantive content reduces to
`translateAlgEquivOfPoint W T = AlgEquiv.refl ⇒ T = 0`, since the map is a
group hom (`translateAlgEquivOfPoint_add`).

For non-zero `T = (xk, yk)`: `translateAlgEquivOfPoint` acts on `x_gen` as
`translateX_xy W xk yk`, which has negative ord at the smooth point `−T`
(`ord_P_translateX_xy_lt_zero`). Meanwhile `x_gen` has nonneg ord everywhere
(`ord_P_x_gen_nonneg`). Hence the action is non-trivial, contradicting
`= AlgEquiv.refl`. -/

/-- For non-2-torsion `T = (xk, yk)`, `translateX_xy ≠ x_gen` via ord-comparison
at `−T`: ord_{-T}(translateX_xy) < 0 vs ord_{-T}(x_gen) ≥ 0. -/
theorem translateX_xy_ne_x_gen_nonTor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    translateX_xy W xk yk ≠ x_gen W := by
  intro h_eq
  have h_neg : (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
      (translateX_xy W xk yk) < 0 :=
    ord_P_translateX_xy_lt_zero W xk yk h_ns h_not_2_tor
  have h_nonneg : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (x_gen W) :=
    ord_P_x_gen_nonneg W _
  rw [h_eq] at h_neg
  exact absurd h_nonneg (not_le.mpr h_neg)

/-- For 2-torsion `T = (xk, yk)`, `translateX_xy ≠ x_gen` via the same
ord-comparison argument using `ord_P_translateX_xy_lt_zero_at_2tor`. -/
theorem translateX_xy_ne_x_gen_2tor
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_2_tor : yk = W.toAffine.negY xk yk) :
    translateX_xy W xk yk ≠ x_gen W := by
  intro h_eq
  have h_neg : (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
      (translateX_xy W xk yk) < 0 :=
    ord_P_translateX_xy_lt_zero_at_2tor W xk yk h_ns h_2_tor
  have h_nonneg : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (x_gen W) :=
    ord_P_x_gen_nonneg W _
  rw [h_eq] at h_neg
  exact absurd h_nonneg (not_le.mpr h_neg)

/-- `translateAlgEquivOfPoint W (some xk yk h_ns) ≠ AlgEquiv.refl`:
the action on `x_gen` is non-trivial since `translateX_xy ≠ x_gen`
(both 2-tor and non-2-tor cases). -/
theorem translateAlgEquivOfPoint_some_ne_refl
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    translateAlgEquivOfPoint W (.some xk yk h_ns) ≠ AlgEquiv.refl := by
  intro h_eq
  have h_apply : translateAlgEquivOfPoint W (.some xk yk h_ns) (x_gen W) =
      x_gen W := by rw [h_eq]; rfl
  by_cases h_2_tor : yk = W.toAffine.negY xk yk
  · rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h_2_tor] at h_apply
    have h_x : (translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor) (x_gen W) =
        translateX_xy W xk yk := by
      change (translateAlgHom_of_2tor W xk yk h_ns h_2_tor).toFun (x_gen W) =
        translateX_xy W xk yk
      exact translateAlgHom_of_2tor_apply_x_gen W xk yk h_ns h_2_tor
    rw [h_x] at h_apply
    exact translateX_xy_ne_x_gen_2tor W xk yk h_ns h_2_tor h_apply
  · rw [translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h_2_tor] at h_apply
    have h_x : (translateAlgEquiv W xk yk h_ns h_2_tor) (x_gen W) =
        translateX_xy W xk yk := by
      change (translateAlgHom_of_nonTorsion W xk yk h_ns h_2_tor).toFun (x_gen W) =
        translateX_xy W xk yk
      exact translateAlgHom_apply_x_gen W xk yk h_ns h_2_tor
    rw [h_x] at h_apply
    exact translateX_xy_ne_x_gen_nonTor W xk yk h_ns h_2_tor h_apply

/-- **`translateAlgEquivOfPoint W T = AlgEquiv.refl` iff `T = 0`**: the kernel
of the translation action on `K(E)` is trivial. Direct from
`translateAlgEquivOfPoint_some_ne_refl` (non-zero `T` is non-refl) and
`translateAlgEquivOfPoint_zero` (zero `T` is refl). -/
theorem translateAlgEquivOfPoint_eq_refl_iff_zero (T : W.toAffine.Point) :
    translateAlgEquivOfPoint W T = AlgEquiv.refl ↔ T = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases T with _ | ⟨xk, yk, h_ns⟩
    · rfl
    · exact absurd h (translateAlgEquivOfPoint_some_ne_refl W xk yk h_ns)
  · rintro rfl
    exact translateAlgEquivOfPoint_zero W

/-- **Injectivity of `translateAlgEquivOfPoint`**: the map
`W.toAffine.Point → (KE ≃ₐ[F] KE)` is injective. Distinct rational points
give distinct translation AlgEquivs of `K(E)`. Direct from the trivial
kernel (`translateAlgEquivOfPoint_eq_refl_iff_zero`) plus the group hom
property (`translateAlgEquivOfPoint_add`). -/
theorem translateAlgEquivOfPoint_injective :
    Function.Injective (translateAlgEquivOfPoint W) := by
  intro T₁ T₂ h_eq
  have h_neg : translateAlgEquivOfPoint W (T₁ + (-T₂)) =
      (translateAlgEquivOfPoint W T₁).trans (translateAlgEquivOfPoint W (-T₂)) :=
    translateAlgEquivOfPoint_add W T₁ (-T₂)
  rw [h_eq] at h_neg
  have h_inv : (translateAlgEquivOfPoint W T₂).trans
      (translateAlgEquivOfPoint W (-T₂)) = AlgEquiv.refl := by
    have h_sum : translateAlgEquivOfPoint W (T₂ + (-T₂)) =
        (translateAlgEquivOfPoint W T₂).trans (translateAlgEquivOfPoint W (-T₂)) :=
      translateAlgEquivOfPoint_add W T₂ (-T₂)
    rw [add_neg_cancel] at h_sum
    have h_refl : translateAlgEquivOfPoint W (0 : W.toAffine.Point) = AlgEquiv.refl :=
      translateAlgEquivOfPoint_zero W
    rw [h_refl] at h_sum
    exact h_sum.symm
  rw [h_inv] at h_neg
  have h_zero : T₁ + (-T₂) = 0 :=
    (translateAlgEquivOfPoint_eq_refl_iff_zero W (T₁ + (-T₂))).mp h_neg
  exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h_zero)

/-! ### Ord-transport Step (B) base case: k = 0

The substantive ord-transport identity
`pointValuation P (translateAlgEquivOfPoint W k f) = pointValuation (P + k) f`
specialized to `k = 0`. Trivial: both sides reduce to `pointValuation P f`
since `translateAlgEquivOfPoint W .zero = AlgEquiv.refl` and
`P.translate_of_finite .zero h = P`.

This is the base case of Step (B) of the ord-transport arc. The general
case (any non-zero `k`) is the substantive content. -/

/-- **Step (B) at k = 0**: ord-transport identity for the trivial translation. -/
theorem translateAlgEquivOfPoint_zero_smul_pointValuation
    (P : (W_smooth W).SmoothPoint)
    (h : (P.toAffinePoint +
        (Affine.Point.zero : (W_smooth W).toAffine.Point)).IsSome)
    (f : W.toAffine.FunctionField) :
    (W_smooth W).pointValuation P
        (translateAlgEquivOfPoint W (Affine.Point.zero : W.toAffine.Point) f) =
      (W_smooth W).pointValuation
        (P.translate_of_finite (Affine.Point.zero : (W_smooth W).toAffine.Point) h) f := by
  haveI : (W_smooth W).toAffine.IsElliptic := inferInstanceAs W.toAffine.IsElliptic
  rw [translateAlgEquivOfPoint_zero_apply]
  change _ = (W_smooth W).pointValuation
    (P.translate_of_finite (0 : (W_smooth W).toAffine.Point) h) f
  rw [Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_zero]

/-! ### Step (B) Conditional: AlgEquiv form

A refinement of `pointValuation_translate_of_smul_eq_of_transport_witness`
(SmoothPointTranslate.lean:Conditional) using an `AlgEquiv` hypothesis form.
Takes a comap-equality witness on `translateAlgEquivOfPoint W k` directly
(rather than an arbitrary RingEquiv), keeping the connection to Worker A's
shipped infrastructure explicit. -/

/-- **Step (B) Conditional, AlgEquiv form**: discharge the pointValuation
transport identity from a comap-equality hypothesis on
`translateAlgEquivOfPoint W k` directly. The hypothesis expresses that
`τ_k` transports `pointValuation (P+k)` to `pointValuation P` under
`Valuation.comap`. -/
theorem translateAlgEquivOfPoint_smul_pointValuation_of_comap
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_comap : ((W_smooth W).pointValuation P).comap
        (translateAlgEquivOfPoint W k).toAlgHom.toRingHom =
      (W_smooth W).pointValuation (P.translate_of_finite k h))
    (f : W.toAffine.FunctionField) :
    (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).pointValuation (P.translate_of_finite k h) f := by
  have := congr_arg (fun v ↦ v f) h_comap
  exact this

/-- **Pointwise → comap-equality bridge**: for `translateAlgEquivOfPoint W k`,
the comap-equality form follows from the pointwise transport identity for
all `f`. Direct application of `Valuation.ext`. This is the converse to
`translateAlgEquivOfPoint_smul_pointValuation_of_comap` and closes the
equivalence between the two formulations of Step (B). -/
theorem comap_pointValuation_eq_of_pointwise_smul
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_pointwise : ∀ f : W.toAffine.FunctionField,
      (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k f) =
        (W_smooth W).pointValuation (P.translate_of_finite k h) f) :
    ((W_smooth W).pointValuation P).comap
        (translateAlgEquivOfPoint W k).toAlgHom.toRingHom =
      (W_smooth W).pointValuation (P.translate_of_finite k h) := by
  apply Valuation.ext
  intro f
  exact h_pointwise f

/-! ### Step (B') base case at k = 0 — Valuation form

The Valuation-level analogue of `translateAlgEquivOfPoint_zero_smul_pointValuation`:
at the trivial translation `k = 0`, the comap of `pointValuation P` along
`(translateAlgEquivOfPoint W 0).toRingHom = RingHom.id` equals `pointValuation P`,
and this matches `pointValuation (P.translate_of_finite 0 h)` by Step (A)'s
`translate_of_finite_zero`. -/

/-- **Step (B') at k = 0** (Valuation form): the comap-equality form of the
ord-transport identity holds trivially at `k = 0`, since
`translateAlgEquivOfPoint W .zero` is the identity ring homomorphism. -/
theorem translateAlgEquivOfPoint_zero_pointValuation_comap
    (P : (W_smooth W).SmoothPoint)
    (h : (P.toAffinePoint +
        (Affine.Point.zero : (W_smooth W).toAffine.Point)).IsSome) :
    ((W_smooth W).pointValuation P).comap
        (translateAlgEquivOfPoint W
          (Affine.Point.zero : W.toAffine.Point)).toAlgHom.toRingHom =
      (W_smooth W).pointValuation
        (P.translate_of_finite
          (Affine.Point.zero : (W_smooth W).toAffine.Point) h) := by
  apply Valuation.ext
  intro f
  exact translateAlgEquivOfPoint_zero_smul_pointValuation W P h f

/-! ### Step (B'') — named substantive obligation

The remaining substantive content of the ord-transport arc: the **Valuation
equality** for the specific `τ_k = translateAlgEquivOfPoint W k`. Formally
state this as a Prop-valued definition `IsTranslateValuationCompatible`.
The base case (`k = 0`) is shipped above; the general case (any non-zero
k whose translate of `P.toAffinePoint` is `IsSome`) is the genuine
geometric obligation, connecting the function-field-level translation to
the smooth-point maximal-ideal structure.

Workers targeting Step (B'') discharge `IsTranslateValuationCompatible`
as a single named obligation; downstream consumers chain through the
already-shipped Conditional consumers
(`translateAlgEquivOfPoint_smul_pointValuation_of_comap`) to produce the
pointwise transport identity. -/

/-- **Step (B'') obligation** (Valuation equality): the substantive
geometric content of the ord-transport arc, namely that
`translateAlgEquivOfPoint W k` transports `pointValuation (P+k)` to
`pointValuation P` under `Valuation.comap`.

Discharging this for our specific `translateAlgEquivOfPoint` (using
Worker A's x_gen/y_gen action lemmas and the smooth-point maximal-ideal
structure) is the remaining geometric obligation in the multi-session
ord-transport arc. -/
def IsTranslateValuationCompatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) : Prop :=
  ((W_smooth W).pointValuation P).comap
      (translateAlgEquivOfPoint W k).toAlgHom.toRingHom =
    (W_smooth W).pointValuation (P.translate_of_finite k h)

/-- **Step (B'') at k = 0**: discharged via the trivial translation case. -/
theorem isTranslateValuationCompatible_zero
    (P : (W_smooth W).SmoothPoint)
    (h : (P.toAffinePoint +
        (Affine.Point.zero : (W_smooth W).toAffine.Point)).IsSome) :
    IsTranslateValuationCompatible W P
      (Affine.Point.zero : (W_smooth W).toAffine.Point) h :=
  translateAlgEquivOfPoint_zero_pointValuation_comap W P h

/-- **Conditional consumer (Valuation form)**: the pointwise transport
identity follows from `IsTranslateValuationCompatible` by congr. This is
the canonical bridge from the named obligation to the pointwise form
needed by downstream consumers (Lemma 3 of the pole-divisor route). -/
theorem translateAlgEquivOfPoint_smul_pointValuation_of_compatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_compat : IsTranslateValuationCompatible W P k h)
    (f : W.toAffine.FunctionField) :
    (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).pointValuation (P.translate_of_finite k h) f :=
  translateAlgEquivOfPoint_smul_pointValuation_of_comap W P k h h_compat f

/-- **Step (B'') iff form**: `IsTranslateValuationCompatible` is equivalent to
the pointwise transport identity for all `f`. Closes the bidirectional
equivalence between the obligation form and the per-element transport form. -/
theorem isTranslateValuationCompatible_iff_pointwise
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    IsTranslateValuationCompatible W P k h ↔
      ∀ f : W.toAffine.FunctionField,
        (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k f) =
          (W_smooth W).pointValuation (P.translate_of_finite k h) f := by
  refine ⟨fun h_compat f ↦ ?_, fun h_pointwise ↦ ?_⟩
  · exact translateAlgEquivOfPoint_smul_pointValuation_of_compatible W P k h h_compat f
  · exact comap_pointValuation_eq_of_pointwise_smul W P k h h_pointwise

/-! ### Step (B'') case-split: zero vs non-zero `k`

The general Step (B'') obligation `IsTranslateValuationCompatible W P k h`
splits into the trivial `k = 0` case (already discharged via
`isTranslateValuationCompatible_zero`) and the substantive `k = some xk
yk h_ns` case. Ship the case-dispatch reducer below: given the non-zero
case as a witness, derive the general case. -/

/-- **Step (B'') case-split reducer**: the general obligation reduces to
the substantive non-zero case. Given a witness for every non-zero
`k = some xk yk h_ns`, the general `IsTranslateValuationCompatible`
holds for all `k`.

This isolates the substantive geometric content to the **`some` case
only** — the `zero` case is discharged unconditionally via
`isTranslateValuationCompatible_zero`. Future workers targeting Step
(B'') need only handle `k = some xk yk h_ns`. -/
theorem isTranslateValuationCompatible_of_some_witness
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_some : ∀ (k' : (W_smooth W).toAffine.Point) (_ : k' ≠ Affine.Point.zero)
      (h' : (P.toAffinePoint + k').IsSome),
      IsTranslateValuationCompatible W P k' h') :
    IsTranslateValuationCompatible W P k h := by
  by_cases hk : k = Affine.Point.zero
  · subst hk
    exact isTranslateValuationCompatible_zero W P h
  · exact h_some k hk h

/-! ### Modular Step (B'') discharge — Piece 1: localRingAt-level transport

The substantive Step (B'') obligation `IsTranslateValuationCompatible` is
the Valuation equality `(pointValuation P).comap τ_k = pointValuation
(P+k)`. By `Valuation.isEquiv_iff_val_le_one`, IsEquiv between these
valuations is equivalent to `val_le_one_iff` pointwise. The local-ring-
level content of the transport says that `τ_k` carries the **valuation
subring** of `pointValuation (P+k)` (i.e., `localRingAt (P+k)` viewed
as a subring of K(E)) onto the valuation subring of `pointValuation P`.

This is the **integrality-handling at the localised level**: for each
`x ∈ K(E)`, `pointValuation P (τ_k x) ≤ 1` iff `pointValuation (P+k) x ≤ 1`.

Define this as `IsTranslateLocalRingCompatible`. Ship the structural
identification with `Valuation.IsEquiv` via `isEquiv_iff_val_le_one`. -/

/-- **Piece 1 (localRingAt-level transport hypothesis)**: the local-ring-
level transport of the valuation subring under `translateAlgEquivOfPoint
W k`. Pointwise statement that `τ_k` preserves the unit ball at the
smooth-point level: an element of `K(E)` has non-negative valuation at
`P+k` iff its `τ_k`-image has non-negative valuation at `P`.

This is the cleanest **algebraic** form of the Step (B'') obligation
at the local-ring level, and is equivalent to `Valuation.IsEquiv`
between the comap and the target pointValuation. -/
def IsTranslateLocalRingCompatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) : Prop :=
  ∀ x : W.toAffine.FunctionField,
    (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k x) ≤ 1 ↔
      (W_smooth W).pointValuation (P.translate_of_finite k h) x ≤ 1

/-- **Piece 1 reduction**: `IsTranslateLocalRingCompatible` is equivalent
to `Valuation.IsEquiv` between the comap and the target pointValuation.
Direct via Mathlib's `isEquiv_iff_val_le_one`. -/
theorem isTranslateLocalRingCompatible_iff_isEquiv
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    IsTranslateLocalRingCompatible W P k h ↔
      Valuation.IsEquiv
        (((W_smooth W).pointValuation P).comap
          (translateAlgEquivOfPoint W k).toAlgHom.toRingHom)
        ((W_smooth W).pointValuation (P.translate_of_finite k h)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  rfl

/-! ### Modular Step (B'') discharge — Piece 2: maxIdeal preservation

The maxIdeal-preservation hypothesis is the dual form of `IsTranslate
LocalRingCompatible`: instead of `≤ 1` agreement (= valuation subring),
it asks for `< 1` agreement (= maximal ideal of the valuation subring).

By Mathlib's TFAE chain (`isEquiv_iff_val_le_one`, `isEquiv_iff_val_lt_one`,
etc.), the two forms are equivalent. Ship both:
- `IsTranslateMaxIdealCompatible` — definition.
- `isTranslateMaxIdealCompatible_iff_isEquiv` — equivalence with IsEquiv.
- `isTranslateLocalRingCompatible_iff_maxIdealCompatible` — equivalence
  between Pieces 1 and 2.

Either form is sufficient as the "input hypothesis" for the substantive
geometric content; the choice determines which algebraic invariant
Worker A's localRingAt-transport lift exposes. -/

/-- **Piece 2 (maxIdeal-preservation transport hypothesis)**: the
maxIdeal-level transport of the valuation under `translateAlgEquivOfPoint
W k`. Pointwise statement that `τ_k` preserves the maxIdeal: an element
of `K(E)` lies strictly inside the maxIdeal at `P+k` iff its `τ_k`-image
lies strictly inside the maxIdeal at `P`.

Equivalent to `IsTranslateLocalRingCompatible` (via Mathlib's TFAE);
chosen as a complementary form when the maxIdeal-side description is
more natural for the substantive proof. -/
def IsTranslateMaxIdealCompatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) : Prop :=
  ∀ x : W.toAffine.FunctionField,
    (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k x) < 1 ↔
      (W_smooth W).pointValuation (P.translate_of_finite k h) x < 1

/-- **Piece 2 reduction**: `IsTranslateMaxIdealCompatible` is equivalent
to `Valuation.IsEquiv`. Direct via Mathlib's `isEquiv_iff_val_lt_one`. -/
theorem isTranslateMaxIdealCompatible_iff_isEquiv
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    IsTranslateMaxIdealCompatible W P k h ↔
      Valuation.IsEquiv
        (((W_smooth W).pointValuation P).comap
          (translateAlgEquivOfPoint W k).toAlgHom.toRingHom)
        ((W_smooth W).pointValuation (P.translate_of_finite k h)) := by
  rw [Valuation.isEquiv_iff_val_lt_one]
  rfl

/-- **Piece 1 ⟺ localRingAt-image transport**: `IsTranslateLocalRingCompatible`
is equivalent to the localRingAt-image preservation form: for every `f`,
`τ_k f` is in the algMap-image of `localRingAt P` iff `f` is in the
algMap-image of `localRingAt (P+k)`.

Connects the abstract Valuation-≤-1 form to the concrete localRing
transport via the biconditional integer characterisation
`mem_localRingAt_image_iff_pointValuation_le_one`. Downstream consumers
proving the substantive content can choose either form — the abstract
valuation form for clean reductions, or the concrete localRing-image
form for direct construction via Worker A's localRing transport. -/
theorem isTranslateLocalRingCompatible_iff_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    IsTranslateLocalRingCompatible W P k h ↔
      (∀ f : W.toAffine.FunctionField,
        (∃ x : (W_smooth W).localRingAt P,
          algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField x =
            translateAlgEquivOfPoint W k f) ↔
        (∃ y : (W_smooth W).localRingAt (P.translate_of_finite k h),
          algebraMap ((W_smooth W).localRingAt (P.translate_of_finite k h))
              (W_smooth W).FunctionField y = f)) := by
  unfold IsTranslateLocalRingCompatible
  refine ⟨fun h_le f ↦ ?_, fun h_image f ↦ ?_⟩
  · rw [Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one,
        Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one]
    exact h_le f
  · rw [← Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one,
        ← Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one]
    exact h_image f

/-- **Piece 1 ⟺ Piece 2**: the local-ring transport (≤ 1) hypothesis is
equivalent to the maxIdeal-preservation (< 1) hypothesis. Direct
composition via the IsEquiv equivalence. -/
theorem isTranslateLocalRingCompatible_iff_maxIdealCompatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    IsTranslateLocalRingCompatible W P k h ↔
      IsTranslateMaxIdealCompatible W P k h := by
  rw [isTranslateLocalRingCompatible_iff_isEquiv,
      isTranslateMaxIdealCompatible_iff_isEquiv]

/-- **CoordinateRing-restricted maxIdeal-transport hypothesis**: the
substantive content of `IsTranslateMaxIdealCompatible` restricted to
elements coming from `(W_smooth W).CoordinateRing` (via `algebraMap`).

This is the **single substantive geometric content** for the Step (B'')
discharge: given a CoordinateRing element `r` vanishing at `P + k` (i.e.,
in `maxIdealAt (P+k)`), `τ_k(algMap r)` has valuation < 1 at `P` (i.e.,
"vanishes at P" at the function-field level). Equivalently, `τ_k`
respects the maxIdeal at the CoordinateRing-image level.

The proof of this from the explicit `translateAlgEquivOfPoint` action on
`x_gen`, `y_gen` (via `translateX_xy`, `translateY_xy`) plus
`pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt` is the
remaining substantive step. The localisation extension (CoordinateRing →
localRingAt) is a separate sub-piece. -/
def IsTranslateMaxIdealCompatible_on_CoordinateRing
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) : Prop :=
  ∀ r : (W_smooth W).CoordinateRing,
    r ∈ (W_smooth W).maximalIdealAt (P.translate_of_finite k h) →
      (W_smooth W).pointValuation P
          (translateAlgEquivOfPoint W k
            (algebraMap (W_smooth W).CoordinateRing
              (W_smooth W).FunctionField r)) < 1

/-- **Full → CoordinateRing-restricted**: the full
`IsTranslateMaxIdealCompatible` implies its CoordinateRing-restriction.
Direct restriction of the universal hypothesis to the algebraMap-image,
combined with `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`. -/
theorem isTranslateMaxIdealCompatible_on_CoordinateRing_of_full
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_full : IsTranslateMaxIdealCompatible W P k h) :
    IsTranslateMaxIdealCompatible_on_CoordinateRing W P k h := by
  intro r h_mem
  have h_lt : (W_smooth W).pointValuation (P.translate_of_finite k h)
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r) < 1 :=
    (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) (u := r) (P := P.translate_of_finite k h)).mpr h_mem
  exact (h_full _).mpr h_lt

/-- **Step (B'') CoordinateRing k=0 base case**: the CoordinateRing-restricted
maxIdeal-preservation holds trivially at `k = 0`. Direct via
`translateAlgEquivOfPoint_zero_apply` (τ_0 = identity) +
`translate_of_finite_zero` + `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`. -/
theorem isTranslateMaxIdealCompatible_on_CoordinateRing_zero
    (P : (W_smooth W).SmoothPoint)
    (h : (P.toAffinePoint +
        (Affine.Point.zero : (W_smooth W).toAffine.Point)).IsSome) :
    IsTranslateMaxIdealCompatible_on_CoordinateRing W P
      (Affine.Point.zero : (W_smooth W).toAffine.Point) h := by
  haveI : (W_smooth W).toAffine.IsElliptic := inferInstanceAs W.toAffine.IsElliptic
  intro r h_mem
  have h_eq_P : P.translate_of_finite (Affine.Point.zero : (W_smooth W).toAffine.Point) h = P :=
    Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_zero P h
  rw [h_eq_P] at h_mem
  change (W_smooth W).pointValuation P
      (translateAlgEquivOfPoint W (.zero : W.toAffine.Point)
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r)) < 1
  rw [translateAlgEquivOfPoint_zero_apply]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := W_smooth W) (u := r) (P := P)).mpr h_mem

/-- **Step (B'') CoordinateRing case-dispatch reducer**: the CoordinateRing-
restricted maxIdeal-preservation reduces to the substantive non-zero case.
Given a witness for every non-zero `k`, the general
`IsTranslateMaxIdealCompatible_on_CoordinateRing` holds for all `k`.

This isolates the substantive geometric content to the **`some` case
only** — the `zero` case is discharged unconditionally via
`isTranslateMaxIdealCompatible_on_CoordinateRing_zero`. Future workers
targeting Step (B'') need only handle `k = some xk yk h_ns`. -/
theorem isTranslateMaxIdealCompatible_on_CoordinateRing_of_some_witness
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_some : ∀ (k' : (W_smooth W).toAffine.Point) (_ : k' ≠ Affine.Point.zero)
      (h' : (P.toAffinePoint + k').IsSome),
      IsTranslateMaxIdealCompatible_on_CoordinateRing W P k' h') :
    IsTranslateMaxIdealCompatible_on_CoordinateRing W P k h := by
  by_cases hk : k = Affine.Point.zero
  · subst hk
    exact isTranslateMaxIdealCompatible_on_CoordinateRing_zero W P h
  · exact h_some k hk h

/-! ### Step (B'') sub-piece: x_gen and y_gen evaluation transport hypotheses

The substantive geometric content of `IsTranslateMaxIdealCompatible_on_CoordinateRing`
for non-zero `k` reduces (by polynomial induction extending to all
CoordinateRing elements) to two **specific witness conditions** on the
generators `x_gen W` and `y_gen W`:

  - `pointValuation P (τ_k(x_gen) - algMap (P+k).x) < 1`
  - `pointValuation P (τ_k(y_gen) - algMap (P+k).y) < 1`

Geometrically: `τ_k(x_gen)` evaluated at `P` equals `(P+k).x`, since `τ_k`
is the function-field-level translation by `k`. The substantive proof of
these witnesses uses the explicit `translateX_xy` / `translateY_xy` formulas
combined with the smooth-point evaluation theory.

We name this hypothesis as a single Prop for downstream use. -/

/-- **x_gen / y_gen evaluation transport hypothesis**: the substantive
geometric content for non-zero `k` Step (B'') discharge.

`τ_k` applied to `x_gen W` and `y_gen W` gives elements that, after
subtracting the `(P+k)`-coordinate, vanish at `P` (i.e., have valuation
< 1 at `P`). The two witnesses encode `τ_k(x_gen)(P) = (P+k).x` and
`τ_k(y_gen)(P) = (P+k).y` at the valuation level. -/
def IsTranslateXY_evaluatesAt
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) : Prop :=
  ((W_smooth W).pointValuation P
      ((translateAlgEquivOfPoint W k (x_gen W) : W.toAffine.FunctionField) -
        algebraMap F W.toAffine.FunctionField
          (P.translate_of_finite k h).x) < 1) ∧
  ((W_smooth W).pointValuation P
      ((translateAlgEquivOfPoint W k (y_gen W) : W.toAffine.FunctionField) -
        algebraMap F W.toAffine.FunctionField
          (P.translate_of_finite k h).y) < 1)

/-! ### Modular Step (B'') discharge — Piece 3: from IsEquiv + value-agreement

The substantive structural step from Pieces 1/2 to the full `IsTranslate
ValuationCompatible`: given `Valuation.IsEquiv` between the two
pointValuations PLUS pointwise value agreement on a witness element
(typically a uniformizer at `P+k`), conclude pointwise value agreement
on every element.

This uses Mathlib's `Valuation.IsEquiv.le_one_iff_le_one` etc. plus the
`IsRankOneDiscrete` structure of pointValuation (both valuations have
value group `WithZero (Multiplicative ℤ)` with generator
`Multiplicative.ofAdd (-1)`).

The simplest sufficient hypothesis is **direct pointwise value
agreement on every element** (`Valuation.ext` form). This bypasses the
substantive IsEquiv → Eq promotion entirely and stays compatible with
Worker A's localRingAt-transport approach: once Worker A's lift gives
pointwise agreement on every f, `IsTranslateValuationCompatible`
discharges. -/

/-- **Piece 3 (DVR uniqueness via direct pointwise hypothesis)**: from a
pointwise value-equality hypothesis on every element, conclude
`IsTranslateValuationCompatible`. Direct via `Valuation.ext` applied at
the comap level.

This is the **canonical bridge** from a pointwise-equality witness
(which Worker A's localRingAt-transport ultimately produces, applied at
each element) to the named obligation `IsTranslateValuationCompatible`.
The DVR uniqueness aspect lives in establishing the pointwise hypothesis
itself — given it, the bridge is structural. -/
theorem isTranslateValuationCompatible_of_pointwise_eq
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_eq : ∀ x : W.toAffine.FunctionField,
      (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k x) =
        (W_smooth W).pointValuation (P.translate_of_finite k h) x) :
    IsTranslateValuationCompatible W P k h :=
  comap_pointValuation_eq_of_pointwise_smul W P k h h_eq

/-- **Piece 3 (alternative form)**: same, but parameterised on the
**comap** form (`((pointValuation P).comap τ_k) x = ...`) rather than
the τ_k-applied form. Functionally identical via the definitional
equality `(comap τ_k v) x = v (τ_k x)`. -/
theorem isTranslateValuationCompatible_of_comap_pointwise_eq
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_eq : ∀ x : W.toAffine.FunctionField,
      ((W_smooth W).pointValuation P).comap
          (translateAlgEquivOfPoint W k).toAlgHom.toRingHom x =
        (W_smooth W).pointValuation (P.translate_of_finite k h) x) :
    IsTranslateValuationCompatible W P k h := by
  apply Valuation.ext
  exact h_eq

/-! ### Modular discharge framework — usage chain

The complete chain from Worker A's localRingAt-transport lift to the
Step (B'') named obligation `IsTranslateValuationCompatible`:

1. **Worker A's substantive piece** (in progress): construct a ring iso
   `localRingAt(P+k) ≃+* localRingAt(P)` compatible with `τ_k` at the
   K(E) level + maxIdeal preservation.

2. **Pointwise agreement extraction**: from the localRingAt iso +
   maxIdeal correspondence, derive
   `∀ f, pointValuation P (τ_k f) = pointValuation (P+k) f`. The
   substantive step uses that for FractionRing valuations from
   HeightOneSpectrum primes, the value at any element is determined by
   the prime-multiplicity in the integral closure, and the ring iso
   transports these multiplicities.

3. **Obligation discharge** (this piece): apply
   `isTranslateValuationCompatible_of_pointwise_eq` to upgrade the
   pointwise agreement to `IsTranslateValuationCompatible`.

Steps 1 and 2 form Worker A's substantive territory. Step 3 is the
clean structural bridge shipped here. -/

/-! ### Modular Step (B'') discharge — Piece 4: ord-form bridge

The additive `ord_P` version of the pointwise transport hypothesis
provides a complementary entry point. Useful when the substantive proof
naturally produces an integer multiplicity (via the prime-power
decomposition of an element in a DVR) rather than a multiplicative
value group element.

The bridge: given `ord_P P (τ_k f) = ord_{P+k} f` for all `f ≠ 0`,
conclude pointwise pointValuation equality, hence
`IsTranslateValuationCompatible`. -/

/-- **Piece 4 (ord-form bridge)**: from `ord_P` agreement on every nonzero
element, derive `IsTranslateValuationCompatible`. Uses the structural
relationship between `ord_P` and `pointValuation` (additive log of the
multiplicative valuation).

The hypothesis is the additive form of the pointwise valuation transport
identity, useful when the substantive proof naturally produces integer
multiplicities. -/
theorem isTranslateValuationCompatible_of_ord_P_eq
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_ord : ∀ f : W.toAffine.FunctionField, f ≠ 0 →
      (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
        (W_smooth W).ord_P (P.translate_of_finite k h) f) :
    IsTranslateValuationCompatible W P k h := by
  apply isTranslateValuationCompatible_of_pointwise_eq
  intro f
  by_cases hf : f = 0
  · subst hf
    rw [map_zero]
    change (W_smooth W).pointValuation P 0 =
      (W_smooth W).pointValuation (P.translate_of_finite k h) 0
    rw [map_zero, map_zero]
  · have hτf_ne : translateAlgEquivOfPoint W k f ≠ 0 := by
      intro h_eq
      apply hf
      have := (translateAlgEquivOfPoint W k).injective
      apply this
      rw [h_eq, map_zero]
    have h_ord_eq : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
        (W_smooth W).ord_P (P.translate_of_finite k h) f := h_ord f hf
    have hv1 : (W_smooth W).pointValuation P
        (translateAlgEquivOfPoint W k f) ≠ 0 :=
      ((W_smooth W).pointValuation P).ne_zero_iff.mpr hτf_ne
    have hv2 : (W_smooth W).pointValuation (P.translate_of_finite k h) f ≠ 0 :=
      ((W_smooth W).pointValuation _).ne_zero_iff.mpr hf
    have h_def1 : (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k f) =
        ((-(WithZero.unzero hv1).toAdd : ℤ) : WithTop ℤ) := by
      unfold Curves.SmoothPlaneCurve.ord_P
      exact dif_neg hv1
    have h_def2 : (W_smooth W).ord_P (P.translate_of_finite k h) f =
        ((-(WithZero.unzero hv2).toAdd : ℤ) : WithTop ℤ) := by
      unfold Curves.SmoothPlaneCurve.ord_P
      exact dif_neg hv2
    rw [h_def1, h_def2] at h_ord_eq
    have h_int_eq : (-(WithZero.unzero hv1).toAdd : ℤ) =
        (-(WithZero.unzero hv2).toAdd : ℤ) := by
      exact_mod_cast h_ord_eq
    have h_unzero_eq : WithZero.unzero hv1 = WithZero.unzero hv2 := by
      apply Multiplicative.toAdd.injective
      omega
    rw [← WithZero.coe_unzero hv1, ← WithZero.coe_unzero hv2, h_unzero_eq]

/-! ### Modular Step (B'') discharge — Piece 5: clean interface for Worker A

The clean interface for Worker A's substantive localRingAt-transport
content. Once Worker A ships:
1. `mem_localRingAt_image_of_pointValuation_le_one` (≤ 1 ↔ in localRingAt
   image at P).
2. A ring iso `φ : localRingAt(P+k) ≃+* localRingAt(P)` compatible with
   `τ_k` at the K(E) level + maxIdeal preservation.

The chain to `IsTranslateValuationCompatible` reduces to:
- IsTranslateLocalRingCompatible (≤ 1-iff): pointwise consequence of
  the localRingAt iso.
- Pointwise valuation equality: derived from the iso + maxIdeal
  preservation via multiplicity-tracking in the DVR maxIdeal.
- Apply `isTranslateValuationCompatible_of_pointwise_eq` (Piece 3).

Below: a single-Conditional consumer taking the **pointwise valuation
equality** form (which is the eventual output of the localRingAt-iso
chain) and producing `IsTranslateValuationCompatible`. This is
essentially the same as Piece 3 but stated in terms of value equality
on every nonzero element (the natural form for the substantive proof). -/

/-- **Piece 5 (clean interface)**: take the pointwise nonzero-element
valuation equality and discharge `IsTranslateValuationCompatible`.

Hypothesis matches the natural output of Worker A's localRingAt-iso
chain: at each nonzero `f ∈ K(E)`, the τ_k-transport agrees on
pointValuation. The zero case is handled automatically. -/
theorem isTranslateValuationCompatible_of_nonzero_pointwise_eq
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_eq : ∀ f : W.toAffine.FunctionField, f ≠ 0 →
      (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k f) =
        (W_smooth W).pointValuation (P.translate_of_finite k h) f) :
    IsTranslateValuationCompatible W P k h := by
  apply isTranslateValuationCompatible_of_pointwise_eq
  intro f
  by_cases hf : f = 0
  · subst hf
    rw [map_zero]
    change (W_smooth W).pointValuation P 0 =
      (W_smooth W).pointValuation (P.translate_of_finite k h) 0
    rw [map_zero, map_zero]
  · exact h_eq f hf

/-! ### Step (C) — ordAtInfty ↔ ord_P bridge for Lemma 3

Step (B'') framework (Pieces 1–5) handles the **finite-to-finite**
ord-transport: `ord_P (τ_k f) = ord_{P+k} f` when `P + k` is a finite
SmoothPoint (i.e., `(P.toAffinePoint + k).IsSome`).

For Lemma 3 (finite kernel points T ∈ ker γ for `γ = isogOneSub_negFrobenius`),
the chain to closure requires the **complementary** infinity case:
when `P + k` reaches the identity `Affine.Point.zero` (= the point at
infinity in the projective view), the right-hand side becomes
`ordAtInfty f` rather than `ord_{P+k} f`.

For γ = 1 − π and T ∈ ker γ \ {O}:
* Worker A's xy_family: `τ_{-T} (γ.pullback x_gen) = γ.pullback x_gen`
  (since -T ∈ ker γ).
* Step (C) bridge: `ord_T (τ_{-T} f) = ordAtInfty f` when `T + (-T) = 0`
  (i.e., when the translation lands exactly at the identity).
* Lemma 1: `ordAtInfty (γ.pullback x_gen) = -2`.

Composing the three: `ord_T (γ.pullback x_gen) = ord_T (τ_{-T} (γ.pullback
x_gen)) = ordAtInfty (γ.pullback x_gen) = -2`. This closes Lemma 3 at
finite kernel points.

Step (C) ships:
* `IsTranslateOrdAtInftyCompatible` — the named obligation.
* Conditional consumer composing the obligation with invariance to
  derive the explicit value `-2` at finite kernel points.

The substantive geometric content (proving the obligation for our
specific `translateAlgEquivOfPoint`) is shipped or in flight via
Worker A's localRingAt-transport infrastructure extended to handle the
infinity case. -/

/-- **Step (C) named obligation**: the substantive content bridging
finite-point `ord_P` to `ordAtInfty` under translation. For a finite
SmoothPoint `P` and group element `k` such that `P + k = 0` (the
identity), the function-field-level translation `τ_k` carries the
order-at-`P` to the order-at-infinity:

```
  ord_P (τ_k f) = ordAtInfty f          -- when P + k = 0
```

This is the **infinity-side analogue** of Step (B'')'s
`IsTranslateValuationCompatible`. The framework parallel mirrors that
structure. -/
def IsTranslateOrdAtInftyCompatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (_h_zero : P.toAffinePoint + k = Affine.Point.zero) : Prop :=
  ∀ f : W.toAffine.FunctionField,
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f

/-- **Step (C) Conditional consumer**: combine the named obligation
`IsTranslateOrdAtInftyCompatible` with a τ-invariance hypothesis on `f`
(matching Worker A's xy_family form) to derive the constant-on-orbit
identity for `f` between finite ord_P and ordAtInfty.

For invariant `f` (= `τ_k f = f`) and a translate-to-zero hypothesis,
the chain `ord_P f = ord_P (τ_k f) = ordAtInfty f` closes via Step (C). -/
theorem ord_P_eq_ordAtInfty_of_invariant_and_compatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h_zero : P.toAffinePoint + k = Affine.Point.zero)
    (h_compat : IsTranslateOrdAtInftyCompatible W P k h_zero)
    (f : W.toAffine.FunctionField)
    (h_inv : translateAlgEquivOfPoint W k f = f) :
    (W_smooth W).ord_P P f = (W_smooth W).ordAtInfty f := by
  have h_transport : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f := h_compat f
  rw [h_inv] at h_transport
  exact h_transport

/-- **Step (C) iff form**: `IsTranslateOrdAtInftyCompatible` is equivalent
to the pointwise transport identity for all `f`. Direct unfolding of
the definition. -/
theorem isTranslateOrdAtInftyCompatible_iff_pointwise
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h_zero : P.toAffinePoint + k = Affine.Point.zero) :
    IsTranslateOrdAtInftyCompatible W P k h_zero ↔
      ∀ f : W.toAffine.FunctionField,
        (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
          (W_smooth W).ordAtInfty f :=
  Iff.rfl

/-! ### Step (C) modular pieces — analog of Step (B'') Pieces 3-5

For symmetry with Step (B'') framework, ship analogous reductions for
Step (C). The substantive content (proving `IsTranslateOrdAtInfty
Compatible` for our specific `translateAlgEquivOfPoint`) is the next
geometric step; the framework here makes the obligation interface
clean for downstream consumers. -/

/-- **Step (C) Piece 3** (pointwise → obligation): direct construction
of `IsTranslateOrdAtInftyCompatible` from a pointwise nonzero
hypothesis.

Hypothesis: for nonzero `f`, `ord_P (τ_k f) = ordAtInfty f`. The zero
case is automatic (both sides are `⊤`).

This is the **clean interface** matching the natural output of the
substantive geometric proof (which produces ord-agreement on every
nonzero element). -/
theorem isTranslateOrdAtInftyCompatible_of_nonzero_pointwise_eq
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h_zero : P.toAffinePoint + k = Affine.Point.zero)
    (h_eq : ∀ f : W.toAffine.FunctionField, f ≠ 0 →
      (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
        (W_smooth W).ordAtInfty f) :
    IsTranslateOrdAtInftyCompatible W P k h_zero := by
  intro f
  by_cases hf : f = 0
  · subst hf
    rw [map_zero]
    change (W_smooth W).ord_P P 0 = (W_smooth W).ordAtInfty 0
    rw [Curves.SmoothPlaneCurve.ord_P_zero,
        Curves.SmoothPlaneCurve.ordAtInfty_zero]
  · exact h_eq f hf

/-- **Step (C) Piece 4** (compose with finite-k Step (B'') and
ordAtInfty-as-ord_zero identification): provide a "pseudo-Step (B'')"
form where the destination is the infinity place rather than a finite
SmoothPoint. -/
theorem ord_P_translateAlgEquivOfPoint_eq_ordAtInfty_of_compatible
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h_zero : P.toAffinePoint + k = Affine.Point.zero)
    (h_compat : IsTranslateOrdAtInftyCompatible W P k h_zero)
    (f : W.toAffine.FunctionField) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f :=
  h_compat f

/-! ### Step (C) substantive partial discharge — constant case

The simplest substantive case of `IsTranslateOrdAtInftyCompatible` that
discharges directly: for `f = algebraMap F K(E) c` (a constant from F),
both sides reduce to 0 (for nonzero c) or ⊤ (for c = 0). The K-AlgEquiv
property of `translateAlgEquivOfPoint` means it FIXES K-rationals
(`τ_k.commutes`), so the LHS reduces immediately.

This is the partial-but-unconditional cover of Step (C) for constants.
The remaining substantive content (non-constant `f`) requires the deep
geometric content (local-ring-at-infinity infrastructure or equivalent
algebra-norm transport). -/

/-- **Step (C) discharge for constants**: for `f = algebraMap F K(E) c`
(a constant from F), the bridge `ord_P (τ_k f) = ordAtInfty f` holds
unconditionally (independent of any geometric obligation).

For nonzero c: both sides are 0.
For c = 0: both sides are ⊤.

Proof: `τ_k` is a K-AlgEquiv on K(E), so it fixes the image of K (via
`AlgEquiv.commutes`). The LHS reduces to `ord_P (algebraMap c)` =
`ordAtInfty (algebraMap c)` = 0 (for nonzero c). -/
theorem ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (c : F) :
    (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k
          (algebraMap F W.toAffine.FunctionField c)) =
      (W_smooth W).ordAtInfty
        (algebraMap F W.toAffine.FunctionField c) := by
  rw [(translateAlgEquivOfPoint W k).commutes]
  by_cases hc : c = 0
  · subst hc
    rw [map_zero]
    rw [show ((W_smooth W).ord_P P (0 : W.toAffine.FunctionField)) = ⊤ from
        Curves.SmoothPlaneCurve.ord_P_zero]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤ from
        (W_smooth W).ordAtInfty_zero]
  · have h_lhs : (W_smooth W).ord_P P
        (algebraMap F W.toAffine.FunctionField c) = 0 :=
      Curves.SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero
        (W_smooth W) hc P
    have h_rhs : (W_smooth W).ordAtInfty
        (algebraMap F W.toAffine.FunctionField c) = 0 :=
      (W_smooth W).ordAtInfty_algebraMap_F_nonzero hc
    rw [h_lhs, h_rhs]

/-! ### Step (C) bridge — multiplicativity preservation

The Step (C) bridge `ord_P (τ_k f) = ordAtInfty f` is preserved under
multiplication: if it holds for `f` and `g` (both nonzero), it holds for
`f · g`. Direct from multiplicativity of both `ord_P` (`ord_P_mul`) and
`ordAtInfty` (`ordAtInfty_mul`), combined with `map_mul` for `τ_k`. -/

/-- **Step (C) bridge — multiplicativity**: if the Step (C) identity
`ord_P (τ_k f) = ordAtInfty f` holds for nonzero `f` and `g`, it holds
for `f · g`. Direct from `ord_P_mul`, `ordAtInfty_mul`, and `map_mul`. -/
theorem ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (f g : W.toAffine.FunctionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f)
    (h_g : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) =
      (W_smooth W).ordAtInfty g) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k (f * g)) =
      (W_smooth W).ordAtInfty (f * g) := by
  rw [map_mul]
  have h_mul : (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k f * translateAlgEquivOfPoint W k g) =
      (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) +
        (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) :=
    Curves.SmoothPlaneCurve.ord_P_mul _ _
  have h_inf_mul : (W_smooth W).ordAtInfty (f * g) =
      (W_smooth W).ordAtInfty f + (W_smooth W).ordAtInfty g :=
    (W_smooth W).ordAtInfty_mul hf hg
  rw [h_mul, h_inf_mul, h_f, h_g]

/-- **Step (C) bridge — power multiplicativity (nonzero base)**: if the
Step (C) identity holds for nonzero `f`, it holds for `f^n` (any
`n : ℕ`). Direct via `pow_ne_zero` and induction. -/
theorem ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (f : W.toAffine.FunctionField) (hf : f ≠ 0)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f)
    (n : ℕ) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k (f ^ n)) =
      (W_smooth W).ordAtInfty (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, map_one]
    rw [show ((W_smooth W).ord_P P (1 : W.toAffine.FunctionField)) = 0 from
        Curves.SmoothPlaneCurve.ord_P_one]
    rw [show ((W_smooth W).ordAtInfty (1 : W.toAffine.FunctionField)) = 0 from
        (W_smooth W).ordAtInfty_one]
  | succ m ih =>
    rw [pow_succ, map_mul]
    have h_mul : (W_smooth W).ord_P P
          (translateAlgEquivOfPoint W k (f ^ m) *
            translateAlgEquivOfPoint W k f) =
        (W_smooth W).ord_P P (translateAlgEquivOfPoint W k (f ^ m)) +
          (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) :=
      Curves.SmoothPlaneCurve.ord_P_mul _ _
    have h_inf_mul : (W_smooth W).ordAtInfty (f ^ m * f) =
        (W_smooth W).ordAtInfty (f ^ m) + (W_smooth W).ordAtInfty f :=
      (W_smooth W).ordAtInfty_mul (pow_ne_zero m hf) hf
    rw [h_mul, ih, h_f, h_inf_mul]

/-- **Step (C) bridge — inverse**: bridge for `f⁻¹` from bridge for nonzero `f`. -/
theorem ord_P_translateAlgEquivOfPoint_inv_eq_ordAtInfty_of_base
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (f : W.toAffine.FunctionField) (hf : f ≠ 0)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f⁻¹) =
      (W_smooth W).ordAtInfty f⁻¹ := by
  have h_τ_inv : translateAlgEquivOfPoint W k f⁻¹ =
      (translateAlgEquivOfPoint W k f)⁻¹ := map_inv₀ _ f
  have h_τkf_ne : translateAlgEquivOfPoint W k f ≠ 0 := by
    intro h
    apply hf
    have := (translateAlgEquivOfPoint W k).injective
    apply this
    rw [h, map_zero]
  have h_lhs : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f⁻¹) =
      -((W_smooth W).ord_P P (translateAlgEquivOfPoint W k f)) := by
    rw [h_τ_inv]
    exact Curves.SmoothPlaneCurve.ord_P_inv _ h_τkf_ne
  have h_rhs : (W_smooth W).ordAtInfty f⁻¹ =
      -((W_smooth W).ordAtInfty f) := (W_smooth W).ordAtInfty_inv f
  rw [h_lhs, h_rhs, h_f]

/-- **Step (C) bridge — division**: composition of mul + inv. -/
theorem ord_P_translateAlgEquivOfPoint_div_eq_ordAtInfty_of_each
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (f g : W.toAffine.FunctionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f)
    (h_g : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) =
      (W_smooth W).ordAtInfty g) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k (f / g)) =
      (W_smooth W).ordAtInfty (f / g) := by
  rw [div_eq_mul_inv]
  apply ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W P k f g⁻¹ hf (inv_ne_zero hg) h_f
  exact ord_P_translateAlgEquivOfPoint_inv_eq_ordAtInfty_of_base
    W P k g hg h_g

/-- **Step (C) bridge — strict non-archimedean addition**. -/
theorem ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (f g : W.toAffine.FunctionField)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f)
    (h_g : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) =
      (W_smooth W).ordAtInfty g)
    (h_lt : (W_smooth W).ordAtInfty f < (W_smooth W).ordAtInfty g) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k (f + g)) =
      (W_smooth W).ordAtInfty (f + g) := by
  rw [map_add]
  have h_lt_τ : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) <
      (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) := by
    rwa [h_f, h_g]
  have h_lhs : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k f + translateAlgEquivOfPoint W k g) =
      (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) :=
    Curves.SmoothPlaneCurve.ord_P_add_eq_of_lt (P := P) h_lt_τ
  have h_rhs : (W_smooth W).ordAtInfty (f + g) =
      (W_smooth W).ordAtInfty f :=
    (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
  rw [h_lhs, h_rhs, h_f]

/-- **Step (C) bridge — strict non-archimedean subtraction**: via add + neg. -/
theorem ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (f g : W.toAffine.FunctionField)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f)
    (h_g : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) =
      (W_smooth W).ordAtInfty g)
    (h_lt : (W_smooth W).ordAtInfty f < (W_smooth W).ordAtInfty g) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k (f - g)) =
      (W_smooth W).ordAtInfty (f - g) := by
  rw [sub_eq_add_neg]
  apply ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W P k f (-g) h_f
  · rw [map_neg]
    have h_neg_lhs : (W_smooth W).ord_P P (-(translateAlgEquivOfPoint W k g)) =
        (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) :=
      Curves.SmoothPlaneCurve.ord_P_neg (P := P) (translateAlgEquivOfPoint W k g)
    have h_neg_rhs : (W_smooth W).ordAtInfty (-g) =
        (W_smooth W).ordAtInfty g := (W_smooth W).ordAtInfty_neg g
    rw [h_neg_lhs, h_neg_rhs]
    exact h_g
  · have h_neg_rhs : (W_smooth W).ordAtInfty (-g) =
        (W_smooth W).ordAtInfty g := (W_smooth W).ordAtInfty_neg g
    rwa [h_neg_rhs]

/-- **Step (C) bridge — negation**: ord is invariant under negation in both
the local and pole-at-infinity valuations, so the bridge transports
across `f ↦ -f`. -/
theorem ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (f : W.toAffine.FunctionField)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W k (-f)) =
      (W_smooth W).ordAtInfty (-f) := by
  rw [map_neg]
  have h_lhs : (W_smooth W).ord_P P (-(translateAlgEquivOfPoint W k f)) =
      (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) :=
    Curves.SmoothPlaneCurve.ord_P_neg (P := P) (translateAlgEquivOfPoint W k f)
  have h_rhs : (W_smooth W).ordAtInfty (-f) = (W_smooth W).ordAtInfty f :=
    (W_smooth W).ordAtInfty_neg f
  rwa [h_lhs, h_rhs]

/-- **Step (C) bridge combinator — strict-add chain over a list with
dominant element**.

Given:
* `dom : F(E)` with bridge `ord_T(τ_k dom) = ordAtInfty dom`.
* `rest : List F(E)` with bridges for each element.
* For each `f ∈ rest`, `ordAtInfty dom < ordAtInfty f` (dominant strictly
  smaller).

Conclude: `ord_T(τ_k (dom + rest.sum)) = ordAtInfty (dom + rest.sum)`.

Proof by induction on `rest`: each cons step uses the binary strict-add
bridge to extend the running sum, preserving the dominant property
because `ordAtInfty (dom + f) = ordAtInfty dom` for `f` strictly larger
in ord.

This combinator turns the tedious eight-strict-add chain for
`addPullbackNumerator_reduced_negFrobenius` into a single application
listing the eight term bridges + the dominance hypotheses. -/
theorem ord_P_translateAlgEquivOfPoint_sum_dominant
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (dom : W.toAffine.FunctionField) (rest : List W.toAffine.FunctionField)
    (h_dom_bridge : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k dom) =
      (W_smooth W).ordAtInfty dom)
    (h_rest_bridges : ∀ f ∈ rest,
      (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
        (W_smooth W).ordAtInfty f)
    (h_dom_lt : ∀ f ∈ rest,
      (W_smooth W).ordAtInfty dom < (W_smooth W).ordAtInfty f) :
    (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k (dom + rest.sum)) =
      (W_smooth W).ordAtInfty (dom + rest.sum) := by
  induction rest generalizing dom with
  | nil =>
    simp only [List.sum_nil, add_zero]
    exact h_dom_bridge
  | cons f rest' ih =>
    rw [List.sum_cons,
        show dom + (f + rest'.sum) = (dom + f) + rest'.sum from by ring]
    have h_f_bridge : (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k f) =
        (W_smooth W).ordAtInfty f :=
      h_rest_bridges f List.mem_cons_self
    have h_dom_lt_f : (W_smooth W).ordAtInfty dom <
        (W_smooth W).ordAtInfty f :=
      h_dom_lt f List.mem_cons_self
    have h_dom_f_bridge : (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k (dom + f)) =
        (W_smooth W).ordAtInfty (dom + f) :=
      ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
        W P k dom f h_dom_bridge h_f_bridge h_dom_lt_f
    have h_dom_f_ord : (W_smooth W).ordAtInfty (dom + f) =
        (W_smooth W).ordAtInfty dom :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_dom_lt_f
    have h_dom_f_lt : ∀ g ∈ rest',
        (W_smooth W).ordAtInfty (dom + f) <
        (W_smooth W).ordAtInfty g := by
      intro g hg
      rw [h_dom_f_ord]
      exact h_dom_lt g (List.mem_cons_of_mem f hg)
    have h_rest_bridges' : ∀ g ∈ rest',
        (W_smooth W).ord_P P (translateAlgEquivOfPoint W k g) =
          (W_smooth W).ordAtInfty g := fun g hg ↦
      h_rest_bridges g (List.mem_cons_of_mem f hg)
    exact ih (dom + f) h_dom_f_bridge h_rest_bridges' h_dom_f_lt

/-- **Step (C) bridge — constant scalar multiplication**: if the bridge
holds for nonzero `f`, it holds for `algebraMap F K(E) c · f` (c ∈ F
arbitrary, including 0).  For nonzero c: combines the algebraMap bridge
with the mul bridge.  For c = 0: both sides are ⊤. -/
theorem ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (c : F) (f : W.toAffine.FunctionField) (hf : f ≠ 0)
    (h_f : (W_smooth W).ord_P P (translateAlgEquivOfPoint W k f) =
      (W_smooth W).ordAtInfty f) :
    (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k
          (algebraMap F W.toAffine.FunctionField c * f)) =
      (W_smooth W).ordAtInfty
        (algebraMap F W.toAffine.FunctionField c * f) := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, zero_mul, map_zero]
    rw [show ((W_smooth W).ord_P P (0 : W.toAffine.FunctionField)) = ⊤ from
        Curves.SmoothPlaneCurve.ord_P_zero]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤ from
        (W_smooth W).ordAtInfty_zero]
  · have hc_alg : algebraMap F W.toAffine.FunctionField c ≠ 0 := fun h ↦ hc <|
      FaithfulSMul.algebraMap_injective F W.toAffine.FunctionField
        (h.trans (map_zero _).symm)
    have h_const : (W_smooth W).ord_P P
        (translateAlgEquivOfPoint W k
          (algebraMap F W.toAffine.FunctionField c)) =
        (W_smooth W).ordAtInfty
          (algebraMap F W.toAffine.FunctionField c) :=
      ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty W P k c
    exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
      W P k _ f hc_alg hf h_const h_f

end HasseWeil
