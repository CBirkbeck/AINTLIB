/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.AdditionPullback.SilvermanIV14
import HasseWeil.Curves.PointFunctor
import HasseWeil.Curves.ProjectiveDivisor
import HasseWeil.Curves.RamificationAtInfinity
import HasseWeil.EC.TranslateValuation
import HasseWeil.FrobeniusIsogeny
import HasseWeil.Hasse.IsogOneSubXyFamily
import HasseWeil.Hasse.OneSubFrobenius
import HasseWeil.Hasse.PointFix
import HasseWeil.Hasse.Witnesses
import HasseWeil.Ramification

/-!
# Pole-divisor fallback for `#ker(1−π) = deg(1−π)` (T-POLE-DIVISOR-FALLBACK)

Plan-C path to `pc_sepDeg_eq_pointCount` for `γ = isogOneSub_negFrobenius`,
self-contained on F_q-side scaffolding (no base-change required).

## Strategy (per reviewer 2026-05-08)

Five concrete lemmas establish the degree-of-`γ.pullback x_gen`-as-map identity:

1. **Pole at `0` (point at infinity)**: `ord_∞(γ.pullback x_gen) = -2`.
   Direct corollary of Worker A's `ord_addPullback_x_negFrobenius`
   (`HasseWeil/AdditionPullback/Frobenius.lean`) composed with
   `addPullbackAlgHom_negFrobenius_x_gen_eq`
   (`HasseWeil/AdditionPullback/SilvermanIV14.lean`).
2. **Translation invariance**: `τ_T*(γ.pullback x_gen) = γ.pullback x_gen`
   for `T ∈ ker γ`.
3. **Pole at every kernel point**: `ord_T(γ.pullback x_gen) = -2` for
   `T ∈ ker γ`. Consequence of (1)+(2): translation moves the pole at
   `0` to a pole at `T`.
4. **No poles off the kernel**: for `P ∉ ker γ`, `0 ≤ ord_P(γ.pullback x_gen)`.
   Since `x` has only a pole at `O`, `γ.pullback x_gen` can only have poles
   where `γ(P) = O`, i.e., `P ∈ ker γ`.
5. **Pole divisor degree**: summing `(3)+(4)` gives
   `deg(poleDivisor(γ.pullback x_gen)) = 2 · #ker γ`.

The final tower argument:
* `[K(E) : K(γ.pullback x_gen)] = pole-divisor-degree = 2 · #ker γ`.
* `[K(E) : K(γ.pullback x_gen)] = [K(E) : γ*K(E)] · [γ*K(E) : K(γ.pullback x_gen)]
  = γ.degree · 2` (using the shipped `finrank_functionField_eq_two`).
* Equate: `2 · #ker γ = 2 · γ.degree`, hence `#ker γ = γ.degree`.

## Status (this commit)

* **Lemma 1** (pole at `0` / point at infinity): SHIPPED unconditional below.
* **Lemmas 2–5** + tower argument: BLOCKED on missing infrastructure
  (concrete gaps named in the lemma docstrings as `dependency_not_met`
  comments). Specifically:
  - Lemma 2 requires the substantive translation invariance for
    `γ.pullback x_gen` under all `τ_T` with `T ∈ ker γ` — currently only
    σ-invariance under `[-1]` is shipped (`addPullback_x_negFrobenius_sigma_invariant`).
    The full `xy_family` is witness-parametric in `IsogOneSubXyFamily.lean`,
    not unconditional.
  - Lemma 4 requires `ord_P` analysis at every smooth point off `ker γ`,
    which goes through the addition-formula structure not yet shipped at
    that level of generality.
  - Lemma 5 requires divisor-degree infrastructure that sums pole orders
    over all curve points — `Curves.Divisors.lean` has Divisor abstract
    machinery but no lemma connecting "pole orders at named smooth points"
    to "deg(poleDivisor)".
  - The tower argument requires
    `[K(E) : K(γ.pullback x_gen)] = pole-divisor-degree`, which is the
    classical "degree of a function = degree of its pole divisor"
    identity; not shipped at this level for our specific γ.

These gaps are **identical in spirit** to the base-change gaps the user
rejected — both routes have ~200-300 LOC of substantive new infrastructure
beyond what's currently shipped. The lemma decomposition documented here
is the correct skeleton; the substantive sub-pieces are the gaps.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Lemma 1**: `ord_∞(γ.pullback x_gen) = -2` for
`γ = isogOneSub_negFrobenius`. The pole at the elliptic-curve identity
(point at infinity) of order `2`, the foundation for the pole-divisor
degree count. -/
theorem ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  rw [isogOneSub_negFrobenius_pullback]
  rw [addPullbackAlgHom_negFrobenius_x_gen_eq W hq]
  exact ord_addPullback_x_negFrobenius W hq

/-- **Lemma 4 (F_q-rational, vacuous)**: for `γ = isogOneSub_negFrobenius`,
every F_q-rational SmoothPoint lies in `ker γ` (since `γ.toAddMonoidHom = 0`
on K-rational points). Hence the hypothesis "P is a non-kernel F_q-rational
SmoothPoint" is unsatisfiable, and the no-poles claim holds vacuously. -/
theorem no_poles_off_kernel_isogOneSub_negFrobenius
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    (P : (W_smooth W).SmoothPoint)
    (hP : (isogOneSub_negFrobenius W hq).toAddMonoidHom
        (Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P) ≠ 0) :
    ((0 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P P
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) := by
  exfalso
  apply hP
  rw [isogOneSub_negFrobenius_toAddMonoidHom, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
  change (Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P)
    - (Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P) = 0
  exact sub_self _

/-- `(negFrobeniusIsog W).pullback (x_gen W) = x_gen W ^ q ≠ 0`. -/
theorem negFrobeniusIsog_pullback_x_gen_ne_zero
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] :
    (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact pow_ne_zero _ (x_gen_ne_zero W)

/-- `(negFrobeniusIsog W).pullback (y_gen W) ≠ 0` (its order at infinity is `-3q`, finite). -/
theorem negFrobeniusIsog_pullback_y_gen_ne_zero
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 := by
  intro h_zero
  have h_top : (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (y_gen W)) = ⊤ := by
    rw [h_zero]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq] at h_top
  exact WithTop.coe_ne_top h_top

/-- **Specialised Computation A bridge** for `f = γ.pullback x_gen` with
`γ = isogOneSub_negFrobenius`. States the identity
`[K(E) : F(γ.pullback x_gen)] = degreePoleDivisor (γ.pullback x_gen)`
specialised to our specific `γ`.

The pole-divisor degree is expressed as the sum of negative parts of
`projectiveDivisorOf` (over both finite SmoothPoints and the point at
infinity), which under the F_q-rational discharge of Lemma 5 evaluates
to `2 · |ker γ|`.

This is form **(b)** from the reviewer's directive. It is a NAMED
non-trivial divisor-function-degree theorem. **It does NOT need Riemann–Roch**:
the identity `[K(E):F(f)] = degreePoleDivisor f` is the elementary
degree = (weighted) pole-degree formula, supplied by the (proven, non-RR)
`finrank_eq_weighted_poleDegree_of_nonconstant` (the Dedekind
`finrank_eq_sum_ramificationIdx_mul_inertiaDeg` identity), specialised to
`f = γ.pullback x_gen` in `finrank_gamma_pullback_x_eq_weightedPoleDegree`.
The remaining work is the framing bridge (`adjoin K {f} ↔ LinfAt f` on the
left; `projectiveDivisorOf ↔ primesOverFinset/ordAt` on the right). -/
def ComputationA_bridge_pullback_x_gen
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) : Prop :=
  Module.finrank
    (IntermediateField.adjoin K
      ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
        Set W.toAffine.FunctionField))
    W.toAffine.FunctionField =
  ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
    (fun P => (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat)

namespace Conditional

/-- **Step (B'') × invariance**: for a function `f` invariant under
`translateAlgEquivOfPoint W k` (i.e., `τ_k f = f`) and a smooth point
`P` whose translate `P + k` is finite (`IsSome`), the Step (B'')
Valuation-compatibility hypothesis implies the valuation identity

```
  pointValuation P f = pointValuation (P + k) f
```

This is the Lemma-3-style identity at the smooth-point level: the
valuation of an invariant function is constant on the τ-orbit.
Composes the named obligation with Worker A's xy_family content.

depends_on: Step (B'') (`IsTranslateValuationCompatible`) +
Worker A's xy_family τ-invariance.
consumes: invariance + compatibility hypotheses (both witness-parametric
in this Conditional form). -/
theorem pointValuation_eq_of_invariant_and_compatible
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    (h_compat : IsTranslateValuationCompatible W P k h)
    (f : W.toAffine.FunctionField)
    (h_inv : translateAlgEquivOfPoint W k f = f) :
    (W_smooth W).pointValuation P f =
      (W_smooth W).pointValuation (P.translate_of_finite k h) f := by
  have h_transport :
      (W_smooth W).pointValuation P (translateAlgEquivOfPoint W k f) =
        (W_smooth W).pointValuation (P.translate_of_finite k h) f :=
    translateAlgEquivOfPoint_smul_pointValuation_of_compatible W P k h h_compat f
  rw [h_inv] at h_transport
  exact h_transport

/-- **Specialised to γ = isogOneSub_negFrobenius**: composing
`pointValuation_eq_of_invariant_and_compatible` with Worker A's
unconditional `xy_family_isogOneSub_negFrobenius` (the τ_k-invariance of
`γ.pullback x_gen`), the constant-on-orbit identity holds for our
specific γ:

```
  pointValuation P (γ.pullback x_gen) =
    pointValuation (P + k) (γ.pullback x_gen)
```

The invariance hypothesis is **discharged unconditionally** by Worker A;
only the Step (B'') compatibility hypothesis remains witness-parametric.

depends_on: Step (B'') (`IsTranslateValuationCompatible`).
consumes: Step (B'') compatibility hypothesis (single named obligation
in this Conditional form). -/
theorem pointValuation_pullback_x_gen_eq_of_compatible
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    (P : (W_smooth W).SmoothPoint)
    (k : (W_smooth W).toAffine.Point)
    (hk : (k : W.toAffine.Point) ∈ (isogOneSub_negFrobenius W hq).kernel)
    (h : (P.toAffinePoint + k).IsSome)
    (h_compat : IsTranslateValuationCompatible W P k h) :
    (W_smooth W).pointValuation P
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      (W_smooth W).pointValuation (P.translate_of_finite k h)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :=
  pointValuation_eq_of_invariant_and_compatible W P k h h_compat
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
    (xy_family_isogOneSub_negFrobenius W hq ⟨k, hk⟩).1

/-- **Companion (y_gen)**: same identity for `γ.pullback y_gen` via the
y-component of Worker A's xy_family. -/
theorem pointValuation_pullback_y_gen_eq_of_compatible
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    (P : (W_smooth W).SmoothPoint)
    (k : (W_smooth W).toAffine.Point)
    (hk : (k : W.toAffine.Point) ∈ (isogOneSub_negFrobenius W hq).kernel)
    (h : (P.toAffinePoint + k).IsSome)
    (h_compat : IsTranslateValuationCompatible W P k h) :
    (W_smooth W).pointValuation P
        ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) =
      (W_smooth W).pointValuation (P.translate_of_finite k h)
        ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) :=
  pointValuation_eq_of_invariant_and_compatible W P k h h_compat
    ((isogOneSub_negFrobenius W hq).pullback (y_gen W))
    (xy_family_isogOneSub_negFrobenius W hq ⟨k, hk⟩).2

/-- **Lemma 3 finite kernel — value `-2` from Step (C) + xy_family + Lemma 1**:
for `γ = isogOneSub_negFrobenius` and a finite kernel SmoothPoint `T`
with `T + (-T) = 0`, given the Step (C) obligation `IsTranslateOrdAt
InftyCompatible W T (-T.toAffinePoint) h_zero`, derive the value
`ord_T (γ.pullback x_gen) = -2`.

This is the **finite kernel discharge** of Lemma 3 of the pole-divisor
route, witness-parametric on the Step (C) obligation only (Worker A's
xy_family + Lemma 1 are unconditional). -/
theorem ord_P_pullback_x_gen_eq_neg_two_of_step_C
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    (T : (W_smooth W).SmoothPoint)
    (hT_neg : (-T.toAffinePoint :
      W.toAffine.Point) ∈ (isogOneSub_negFrobenius W hq).kernel)
    (h_zero : T.toAffinePoint + (-T.toAffinePoint :
      (W_smooth W).toAffine.Point) = Affine.Point.zero)
    (h_compat : IsTranslateOrdAtInftyCompatible W T
      (-T.toAffinePoint : (W_smooth W).toAffine.Point)
      h_zero) :
    (W_smooth W).ord_P T
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  have h_inv := (xy_family_isogOneSub_negFrobenius W hq
    ⟨-T.toAffinePoint, hT_neg⟩).1
  have h_bridge := ord_P_eq_ordAtInfty_of_invariant_and_compatible
    W T (-T.toAffinePoint : (W_smooth W).toAffine.Point)
    h_zero h_compat
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
    h_inv
  rw [h_bridge]
  exact ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen W hq

/-- **Specialised Lemma 3 finite-kernel discharge — only single-point
Step (C) hypothesis**: weaker form of `ord_P_pullback_x_gen_eq_neg_two_of_step_C`
taking only the **single-instance** Step (C) bridge (specialised to
`f = γ.pullback x_gen`) rather than the full universal
`IsTranslateOrdAtInftyCompatible W T (-T) h_zero` (= ∀ f, ...).

The hypothesis `h_specialized : ord_T (τ_{-T} (γ.pullback x_gen)) =
ordAtInfty (γ.pullback x_gen)` is the bridge AT a single function
(γ.pullback x_gen specifically), which is much easier to discharge than
the universal form.

By Worker A's xy_family invariance, `τ_{-T} (γ.pullback x_gen) =
γ.pullback x_gen`, so the LHS `ord_T (τ_{-T} (γ.pullback x_gen))` equals
`ord_T (γ.pullback x_gen)`. Combined with Lemma 1, gives the value -2.

This is the **smallest viable hypothesis form** for the chain — replacing
the universal-quantified obligation with a specific instance at the only
function we care about. -/
theorem ord_P_pullback_x_gen_eq_neg_two_of_specialized_bridge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    (T : (W_smooth W).SmoothPoint)
    (hT_neg : (-T.toAffinePoint :
      W.toAffine.Point) ∈ (isogOneSub_negFrobenius W hq).kernel)
    (h_specialized : (W_smooth W).ord_P T
        (translateAlgEquivOfPoint W
          (-T.toAffinePoint : W.toAffine.Point)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) :
    (W_smooth W).ord_P T
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  have h_inv := (xy_family_isogOneSub_negFrobenius W hq
    ⟨-T.toAffinePoint, hT_neg⟩).1
  rw [h_inv] at h_specialized
  rw [h_specialized]
  exact ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen W hq

/-- **Step (C) bridge AT f = x_gen for non-2-torsion T**: at the smooth
point T = (xT, yT) (with yT ≠ negY xT yT), `ord_T (τ_{-T} (x_gen)) =
ordAtInfty (x_gen) = -2`. Discharged unconditionally. -/
theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    let T_pt : (W_smooth W).SmoothPoint :=
      ⟨xT, yT, h_ns⟩
    (W_smooth W).ord_P T_pt
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W)) = ((-2 : ℤ) : WithTop ℤ) := by
  simp only
  rw [neg_some_eq_some W xT yT h_ns]
  rw [translateAlgEquivOfPoint_some_apply_x_gen W xT (W.toAffine.negY xT yT)
    ((Affine.nonsingular_neg xT yT).mpr h_ns)]
  have h_negY_negY : W.toAffine.negY xT (W.toAffine.negY xT yT) = yT := by
    change -(W.toAffine.negY xT yT) - W.a₁ * xT - W.a₃ = yT
    change -(-yT - W.a₁ * xT - W.a₃) - W.a₁ * xT - W.a₃ = yT
    ring
  have h_not_2_tor_neg : W.toAffine.negY xT yT ≠
      W.toAffine.negY xT (W.toAffine.negY xT yT) := by
    rw [h_negY_negY]
    exact (Ne.symm h_not_2_tor)
  have h_ord : (W_smooth W).ord_P
      (negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns))
      (translateX_xy W xT (W.toAffine.negY xT yT)) = ((-2 : ℤ) : WithTop ℤ) :=
    ord_P_translateX_xy_eq_neg_two_of_non_2_tor W xT (W.toAffine.negY xT yT)
      ((Affine.nonsingular_neg xT yT).mpr h_ns) h_not_2_tor_neg
  have h_smoothPt_eq :
      negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns) =
      ({ x := xT, y := yT, nonsingular := h_ns } :
        (W_smooth W).SmoothPoint) := by
    apply Curves.SmoothPlaneCurve.SmoothPoint.ext
    · rfl
    · exact h_negY_negY
  rw [← h_smoothPt_eq]
  exact h_ord

/-- **Step (C) bridge AT f = x_gen^q (= frob(x_gen)) for non-2-torsion T**:
combines the bridge at f = x_gen (just shipped, 4e63a2a) with the pow
case (5b3707d) to lift to f = x_gen^q. Useful for the addPullback_x
formula evaluation since `(negFrobeniusIsog W).pullback x_gen = x_gen^q`. -/
theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_pow_card_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    let T_pt : (W_smooth W).SmoothPoint :=
      ⟨xT, yT, h_ns⟩
    (W_smooth W).ord_P T_pt
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) := by
  simp only
  have h_bridge_x_gen :
      (W_smooth W).ord_P ⟨xT, yT, h_ns⟩
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W) := by
    rw [ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two W xT yT h_ns
      h_not_2_tor]
    rw [show ((W_smooth W).ordAtInfty (x_gen W)) = ((-2 : ℤ) : WithTop ℤ) from
      ordAtInfty_x_gen W]
  have h_x_gen_ne : x_gen W ≠ 0 := x_gen_ne_zero W
  exact ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ (x_gen W) h_x_gen_ne h_bridge_x_gen (Fintype.card K)

/-- **Step (C) bridge AT f = y_gen for non-2-torsion T**: at the smooth
point T = (xT, yT) (with yT ≠ negY xT yT), `ord_T (τ_{-T} (y_gen)) =
ordAtInfty (y_gen) = -3`. Discharged unconditionally via the
substantive `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`. The
y-side analog of `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two`. -/
theorem ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    let T_pt : (W_smooth W).SmoothPoint :=
      ⟨xT, yT, h_ns⟩
    (W_smooth W).ord_P T_pt
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W)) = ((-3 : ℤ) : WithTop ℤ) := by
  simp only
  rw [neg_some_eq_some W xT yT h_ns]
  rw [translateAlgEquivOfPoint_some_apply_y_gen W xT (W.toAffine.negY xT yT)
    ((Affine.nonsingular_neg xT yT).mpr h_ns)]
  have h_negY_negY : W.toAffine.negY xT (W.toAffine.negY xT yT) = yT := by
    change -(W.toAffine.negY xT yT) - W.a₁ * xT - W.a₃ = yT
    change -(-yT - W.a₁ * xT - W.a₃) - W.a₁ * xT - W.a₃ = yT
    ring
  have h_not_2_tor_neg : W.toAffine.negY xT yT ≠
      W.toAffine.negY xT (W.toAffine.negY xT yT) := by
    rw [h_negY_negY]
    exact (Ne.symm h_not_2_tor)
  have h_ord : (W_smooth W).ord_P
      (negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns))
      (translateY_xy W xT (W.toAffine.negY xT yT)) = ((-3 : ℤ) : WithTop ℤ) :=
    ord_P_translateY_xy_eq_neg_three_of_non_2_tor W xT (W.toAffine.negY xT yT)
      ((Affine.nonsingular_neg xT yT).mpr h_ns) h_not_2_tor_neg
  have h_smoothPt_eq :
      negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns) =
      ({ x := xT, y := yT, nonsingular := h_ns } :
        (W_smooth W).SmoothPoint) := by
    apply Curves.SmoothPlaneCurve.SmoothPoint.ext
    · rfl
    · exact h_negY_negY
  rw [← h_smoothPt_eq]
  exact h_ord

/-- **Bridge at f = x_gen for non-2-torsion T (clean version)**: applies
the just-shipped `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two`
without requiring the let-binding form. Bridges to the
ordAtInfty value `-2`. -/
theorem bridge_at_x_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W) := by
  rw [ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two W xT yT h_ns
    h_not_2_tor]
  rw [show ((W_smooth W).ordAtInfty (x_gen W)) = ((-2 : ℤ) : WithTop ℤ) from
    ordAtInfty_x_gen W]

/-- **Bridge at f = y_gen for non-2-torsion T (clean version)**: applies
`ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three` without requiring
the let-binding form. Bridges to the ordAtInfty value `-3`. -/
theorem bridge_at_y_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W)) =
      (W_smooth W).ordAtInfty (y_gen W) := by
  rw [ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three W xT yT h_ns
    h_not_2_tor]
  rw [show ((W_smooth W).ordAtInfty (y_gen W)) = ((-3 : ℤ) : WithTop ℤ) from
    ordAtInfty_y_gen W]

/-- **Bridge at f = y_gen^q for non-2-torsion T**: composes
`bridge_at_y_gen_of_non_2_tor` with the pow case to lift to f = y_gen^q.
Useful for the addPullback_x slope-numerator analysis. -/
theorem bridge_at_y_gen_pow_card_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) := by
  exact ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ (y_gen W) (y_gen_ne_zero W)
    (bridge_at_y_gen_of_non_2_tor W xT yT h_ns h_not_2_tor)
    (Fintype.card K)

/-- **Bridge at f = x_gen^q for non-2-torsion T (clean version)**: applies
`ord_T_translateAlgEquivOfPoint_neg_x_gen_pow_card_eq` with the explicit
identifier (without the let-binding form). -/
theorem bridge_at_x_gen_pow_card_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) :=
  ord_T_translateAlgEquivOfPoint_neg_x_gen_pow_card_eq W xT yT h_ns
    h_not_2_tor

/-- **ordAtInfty (x_gen^q) = -2q** as an integer in `WithTop ℤ`, derived
from `ordAtInfty_x_gen = -2` and `ordAtInfty_pow_of_ord_eq`. -/
theorem ordAtInfty_x_gen_pow_card_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] :
    (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) =
      (((Fintype.card K : ℤ) * (-2 : ℤ) : ℤ) : WithTop ℤ) := by
  exact (W_smooth W).ordAtInfty_pow_of_ord_eq (x_gen_ne_zero W) (-2 : ℤ)
    (Fintype.card K) (ordAtInfty_x_gen W)

/-- **Strict comparison: ordAtInfty(x_gen^q) < ordAtInfty(x_gen)** under
`hq : 2 ≤ Fintype.card K`.  Computation: -2q < -2 iff q > 1. -/
theorem ordAtInfty_x_gen_pow_card_lt_x_gen
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) <
      (W_smooth W).ordAtInfty (x_gen W) := by
  rw [ordAtInfty_x_gen_pow_card_eq W, ordAtInfty_x_gen W]
  rw [show (((Fintype.card K : ℤ) * (-2 : ℤ) : ℤ) : WithTop ℤ) =
        ((-(2 * Fintype.card K : ℤ) : ℤ) : WithTop ℤ) by ring_nf]
  rw [show ((-2 : ℤ) : WithTop ℤ) = ((-(2 : ℤ) : ℤ) : WithTop ℤ) by norm_cast]
  rw [WithTop.coe_lt_coe]
  have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  linarith

/-- **Bridge at f = x_gen^q - x_gen for non-2-torsion T**: composes the
strict-comparison sub theorem with the bridges for `x_gen^q` and
`x_gen`, using the strict inequality from
`ordAtInfty_x_gen_pow_card_lt_x_gen`. -/
theorem bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W ^ Fintype.card K - x_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K - x_gen W) :=
  ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_x_gen_pow_card_of_non_2_tor W xT yT h_ns h_not_2_tor)
    (bridge_at_x_gen_of_non_2_tor W xT yT h_ns h_not_2_tor)
    (ordAtInfty_x_gen_pow_card_lt_x_gen W hq)

/-- **Bridge at f = x_gen - x_gen^q for non-2-torsion T**: applies the
neg-bridge to `bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor`, since
`x_gen - x_gen^q = -(x_gen^q - x_gen)`. -/
theorem bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W - x_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (x_gen W - x_gen W ^ Fintype.card K) := by
  have h_eq : x_gen W - x_gen W ^ Fintype.card K =
      -(x_gen W ^ Fintype.card K - x_gen W) := by ring
  rw [h_eq]
  exact ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
    W _ _ _
    (bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- **Closed form: ordAtInfty(x_gen - x_gen^q) = -2q** under
`hq : 2 ≤ Fintype.card K`.  Derived from strict comparison
(`x_gen^q` dominates) plus negation invariance. -/
theorem ordAtInfty_x_gen_sub_x_gen_pow_card_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (x_gen W - x_gen W ^ Fintype.card K) =
      (((-2 * (Fintype.card K : ℤ) : ℤ) : ℤ) : WithTop ℤ) := by
  have h_eq : x_gen W - x_gen W ^ Fintype.card K =
      -(x_gen W ^ Fintype.card K - x_gen W) := by ring
  rw [h_eq]
  have h_neg_eq : (W_smooth W).ordAtInfty
      (-(x_gen W ^ Fintype.card K - x_gen W)) =
      (W_smooth W).ordAtInfty
      (x_gen W ^ Fintype.card K - x_gen W) :=
    (W_smooth W).ordAtInfty_neg _
  rw [h_neg_eq]
  have h_sub_eq_add : x_gen W ^ Fintype.card K - x_gen W =
      x_gen W ^ Fintype.card K + (-x_gen W) := by ring
  rw [h_sub_eq_add]
  have h_neg_x_ord : (W_smooth W).ordAtInfty (-x_gen W) =
      (W_smooth W).ordAtInfty (x_gen W) :=
    (W_smooth W).ordAtInfty_neg (x_gen W)
  have h_lt_neg : (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) <
      (W_smooth W).ordAtInfty (-x_gen W) := by
    rw [h_neg_x_ord]
    exact ordAtInfty_x_gen_pow_card_lt_x_gen W hq
  have h_add_eq : (W_smooth W).ordAtInfty
      (x_gen W ^ Fintype.card K + (-x_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) :=
    (W_smooth W).ordAtInfty_add_eq_of_lt h_lt_neg
  rw [h_add_eq, ordAtInfty_x_gen_pow_card_eq W]
  congr 1; ring

/-- **Closed form: ord_T(translate(x_gen - x_gen^q)) = -2q** for non-2-torsion
T.  Composes `bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor` with the
closed-form value of `ordAtInfty (x_gen - x_gen^q)`. -/
theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_x_gen_pow_card_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W - x_gen W ^ Fintype.card K)) =
      (((-2 * (Fintype.card K : ℤ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor
        W xT yT h_ns h_not_2_tor hq]
  exact ordAtInfty_x_gen_sub_x_gen_pow_card_eq W hq

/-- **`x_gen ≠ x_gen^q`** under `hq : 2 ≤ Fintype.card K`.  Their
ordAtInfty values are -2 and -2q respectively, which are distinct
(one is finite and they differ as integers).  Hence x_gen and
x_gen^q are distinct elements of `K(E)`. -/
theorem x_gen_ne_x_gen_pow_card
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    x_gen W ≠ x_gen W ^ Fintype.card K := by
  intro h_eq
  have h_diff_zero : x_gen W - x_gen W ^ Fintype.card K = 0 := by
    rw [← h_eq]; ring
  have h_ord_inf : (W_smooth W).ordAtInfty
      (x_gen W - x_gen W ^ Fintype.card K) = ⊤ := by
    rw [h_diff_zero]
    exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_x_gen_sub_x_gen_pow_card_eq W hq] at h_ord_inf
  exact (WithTop.coe_ne_top : ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) ≠ ⊤)
    h_ord_inf

/-- **`x_gen ≠ (negFrobeniusIsog W).pullback (x_gen W)`** under
`hq`.  Direct from `negFrobeniusIsog_pullback_x_gen` (= `x_gen^q`)
plus `x_gen_ne_x_gen_pow_card`. -/
theorem x_gen_ne_negFrobeniusIsog_pullback_x_gen
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    x_gen W ≠ (negFrobeniusIsog W).pullback (x_gen W) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact x_gen_ne_x_gen_pow_card W hq

/-- **`addSlope W (negFrobeniusIsog W)` as a secant**: under `hq`,
`x_gen ≠ negFrobeniusIsog.pullback x_gen`, so the slope formula reduces
to the secant `(y_gen − negFrob.pullback y_gen) / (x_gen − negFrob.pullback x_gen)`.
-/
theorem addSlope_negFrobeniusIsog_eq_secant
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    addSlope W (negFrobeniusIsog W) =
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) /
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) := by
  unfold addSlope
  exact (W_KE W).toAffine.slope_of_X_ne
    (x_gen_ne_negFrobeniusIsog_pullback_x_gen W hq)

/-- **Bridge at `f = (negFrobeniusIsog W).pullback (x_gen W)` for non-2-torsion T**:
direct corollary of `bridge_at_x_gen_pow_card_of_non_2_tor` via the
identity `negFrobeniusIsog.pullback x_gen = x_gen ^ q`. -/
theorem bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact bridge_at_x_gen_pow_card_of_non_2_tor W xT yT h_ns h_not_2_tor

/-- **Bridge at the slope denominator `x_gen − negFrob.pullback x_gen`**
for non-2-torsion T under `hq`.  Direct corollary of
`bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor` via
`negFrobeniusIsog.pullback x_gen = x_gen^q`. -/
theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor
    W xT yT h_ns h_not_2_tor hq

/-- **Closed-form ordAtInfty(x_gen − negFrob.pullback x_gen) = -2q** under
`hq`.  Combines `negFrobeniusIsog.pullback x_gen = x_gen^q` with
`ordAtInfty_x_gen_sub_x_gen_pow_card_eq`. -/
theorem ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) =
      (((-2 * (Fintype.card K : ℤ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact ordAtInfty_x_gen_sub_x_gen_pow_card_eq W hq

/-- **Closed-form ord_T(translate(x_gen − negFrob.pullback x_gen)) = -2q** for
non-2-torsion T under `hq`.  Composes the bridge for the slope
denominator with the closed-form ordAtInfty. -/
theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W))) =
      (((-2 * (Fintype.card K : ℤ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
        W xT yT h_ns h_not_2_tor hq]
  exact ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq W hq

/-- **`(negFrob).pullback y_gen` expanded via Frobenius-pullback identity**:
direct rewrite chain `(negFrob).pullback y_gen = -y_gen^q - a₁·x_gen^q - a₃`. -/
theorem negFrobeniusIsog_pullback_y_gen_eq_pow_form
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] :
    (negFrobeniusIsog W).pullback (y_gen W) =
      -(y_gen W ^ Fintype.card K) -
        algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K) -
        algebraMap K W.toAffine.FunctionField W.toAffine.a₃ := by
  rw [negFrobeniusIsog_pullback_y_gen, frobeniusIsog_pullback_apply,
      frobeniusIsog_pullback_apply]

/-- **Strict comparison: ordAtInfty(-y_gen^q) < ordAtInfty(-a₁·x_gen^q - a₃)**
under `hq`.  `-y_gen^q` has ord `-3q` (strictly smaller than the lower bound
`-2q` for the other two terms). -/
theorem ordAtInfty_neg_y_gen_pow_card_lt_rest
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (-(y_gen W ^ Fintype.card K)) <
      (W_smooth W).ordAtInfty
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) +
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) := by
  have h_y_pow : (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) =
      (((Fintype.card K : ℤ) * (-3 : ℤ) : ℤ) : WithTop ℤ) :=
    (W_smooth W).ordAtInfty_pow_of_ord_eq (y_gen_ne_zero W) (-3 : ℤ)
      (Fintype.card K) (ordAtInfty_y_gen W)
  have h_neg_y_pow : (W_smooth W).ordAtInfty (-(y_gen W ^ Fintype.card K)) =
      (((Fintype.card K : ℤ) * (-3 : ℤ) : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_neg (y_gen W ^ Fintype.card K)).trans h_y_pow
  rw [h_neg_y_pow]
  set a1KE := algebraMap K W.toAffine.FunctionField W.toAffine.a₁ with ha1KE
  set a3KE := algebraMap K W.toAffine.FunctionField W.toAffine.a₃ with ha3KE
  set xq := x_gen W ^ Fintype.card K with hxq
  have h_a1x_ord : (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (-(a1KE * xq)) := by
    have h_neg_eq : (W_smooth W).ordAtInfty (-(a1KE * xq)) =
        (W_smooth W).ordAtInfty (a1KE * xq) :=
      (W_smooth W).ordAtInfty_neg _
    rw [h_neg_eq]
    by_cases ha1 : W.toAffine.a₁ = 0
    · have h_a1_zero : a1KE = 0 := by rw [ha1KE, ha1, map_zero]
      rw [h_a1_zero, zero_mul]
      rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
          from (W_smooth W).ordAtInfty_zero]
      exact le_top
    · have h_a1_ne : a1KE ≠ 0 :=
        fun h => ha1 (FaithfulSMul.algebraMap_injective K
          W.toAffine.FunctionField (h.trans (map_zero _).symm))
      have h_xq_ne : xq ≠ 0 := pow_ne_zero _ (x_gen_ne_zero W)
      have h_mul_ord : (W_smooth W).ordAtInfty (a1KE * xq) =
          (W_smooth W).ordAtInfty a1KE +
            (W_smooth W).ordAtInfty xq :=
        (W_smooth W).ordAtInfty_mul h_a1_ne h_xq_ne
      have h_a1_ord : (W_smooth W).ordAtInfty a1KE = 0 :=
        (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha1
      have h_xq_ord : (W_smooth W).ordAtInfty xq =
          (((Fintype.card K : ℤ) * (-2 : ℤ) : ℤ) : WithTop ℤ) :=
        ordAtInfty_x_gen_pow_card_eq W
      rw [h_mul_ord, h_a1_ord, h_xq_ord, zero_add]
      apply le_of_eq
      norm_cast
      ring
  have h_a3_ord : ((0 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (-a3KE) := by
    have h_neg_eq : (W_smooth W).ordAtInfty (-a3KE) =
        (W_smooth W).ordAtInfty a3KE :=
      (W_smooth W).ordAtInfty_neg _
    rw [h_neg_eq]
    by_cases ha3 : W.toAffine.a₃ = 0
    · have h_a3_zero : a3KE = 0 := by rw [ha3KE, ha3, map_zero]
      rw [h_a3_zero]
      rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
          from (W_smooth W).ordAtInfty_zero]
      exact le_top
    · have h_eq : (W_smooth W).ordAtInfty a3KE = 0 :=
        (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha3
      rw [h_eq]
      norm_cast
  have h_2q_le_zero : (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      ((0 : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_le_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  have h_min_ge : (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      min ((W_smooth W).ordAtInfty (-(a1KE * xq)))
          ((W_smooth W).ordAtInfty (-a3KE)) :=
    le_min h_a1x_ord (h_2q_le_zero.trans h_a3_ord)
  have h_add_ge :
      min ((W_smooth W).ordAtInfty (-(a1KE * xq)))
          ((W_smooth W).ordAtInfty (-a3KE)) ≤
      (W_smooth W).ordAtInfty (-(a1KE * xq) + (-a3KE)) :=
    (W_smooth W).ordAtInfty_add_ge_min _ _
  have h_sum_ge : (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (-(a1KE * xq) + (-a3KE)) :=
    h_min_ge.trans h_add_ge
  have h_lt : (((Fintype.card K : ℤ) * (-3 : ℤ) : ℤ) : WithTop ℤ) <
      (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact h_lt.trans_le h_sum_ge

/-- **Bridge at `(negFrob).pullback y_gen` for non-2-torsion T**: composes
the algebraic-closure framework with the closed-form expansion
`(negFrob).pullback y_gen = -y_gen^q - a₁·x_gen^q - a₃`.

Strategy: regroup as `-y_gen^q + (-(a₁·x_gen^q) + (-a₃))`, apply
strict-comparison addition with the bridge for `-y_gen^q` strictly
smaller (-3q < -2q ≤ ord(-(a₁·x_gen^q) + (-a₃))). -/
theorem bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (y_gen W)) := by
  rw [negFrobeniusIsog_pullback_y_gen_eq_pow_form]
  set P : (W_smooth W).SmoothPoint := ⟨xT, yT, h_ns⟩ with hP
  set k : W.toAffine.Point :=
    -(Affine.Point.some xT yT h_ns) with hk
  have h_y_pow_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k (y_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) :=
    bridge_at_y_gen_pow_card_of_non_2_tor W xT yT h_ns h_not_2_tor
  have h_neg_y_pow_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k (-(y_gen W ^ Fintype.card K))) =
      (W_smooth W).ordAtInfty (-(y_gen W ^ Fintype.card K)) :=
    ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
      W P k _ h_y_pow_bridge
  have h_x_pow_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k (x_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) :=
    bridge_at_x_gen_pow_card_of_non_2_tor W xT yT h_ns h_not_2_tor
  have h_xq_ne : x_gen W ^ Fintype.card K ≠ 0 :=
    pow_ne_zero _ (x_gen_ne_zero W)
  have h_a1xq_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K)) :=
    ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
      W P k W.toAffine.a₁ _ h_xq_ne h_x_pow_bridge
  have h_neg_a1xq_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K)))) =
      (W_smooth W).ordAtInfty
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K))) :=
    ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
      W P k _ h_a1xq_bridge
  have h_a3_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) :=
    ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty
      W P k W.toAffine.a₃
  have h_neg_a3_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) =
      (W_smooth W).ordAtInfty
        (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃) :=
    ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
      W P k _ h_a3_bridge
  have h_regroup : -(y_gen W ^ Fintype.card K) -
        algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K) -
        algebraMap K W.toAffine.FunctionField W.toAffine.a₃ =
      -(y_gen W ^ Fintype.card K) +
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K)) +
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) := by
    ring
  rw [h_regroup]
  have h_rest_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) +
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃))) =
      (W_smooth W).ordAtInfty
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) +
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) := by
    by_cases ha1 : W.toAffine.a₁ = 0
    · have h_a1_zero : algebraMap K W.toAffine.FunctionField W.toAffine.a₁ = 0 := by
        rw [ha1, map_zero]
      rw [h_a1_zero, zero_mul, neg_zero, zero_add]
      exact h_neg_a3_bridge
    · have h_a1_ne : algebraMap K W.toAffine.FunctionField W.toAffine.a₁ ≠ 0 :=
        fun h => ha1 (FaithfulSMul.algebraMap_injective K
          W.toAffine.FunctionField (h.trans (map_zero _).symm))
      have h_mul_eq : (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) =
          (W_smooth W).ordAtInfty
            (algebraMap K W.toAffine.FunctionField W.toAffine.a₁) +
          (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) :=
        (W_smooth W).ordAtInfty_mul h_a1_ne h_xq_ne
      have h_a1_ord_zero : (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁) = 0 :=
        (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha1
      have h_a1xq_ord : (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) =
          (((Fintype.card K : ℤ) * (-2 : ℤ) : ℤ) : WithTop ℤ) := by
        rw [h_mul_eq, h_a1_ord_zero, zero_add,
            ordAtInfty_x_gen_pow_card_eq W]
      have h_neg_a1xq_eq : (W_smooth W).ordAtInfty
          (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K))) =
          (W_smooth W).ordAtInfty
            (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K)) :=
        (W_smooth W).ordAtInfty_neg _
      have h_neg_a1xq_ord : (W_smooth W).ordAtInfty
          (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K))) =
          (((Fintype.card K : ℤ) * (-2 : ℤ) : ℤ) : WithTop ℤ) :=
        h_neg_a1xq_eq.trans h_a1xq_ord
      have h_neg_a3_eq : (W_smooth W).ordAtInfty
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃) =
          (W_smooth W).ordAtInfty
            (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) :=
        (W_smooth W).ordAtInfty_neg _
      have h_neg_a3_ord_le : (W_smooth W).ordAtInfty
          (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K))) <
          (W_smooth W).ordAtInfty
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃) := by
        rw [h_neg_a1xq_ord, h_neg_a3_eq]
        by_cases ha3 : W.toAffine.a₃ = 0
        · rw [ha3, map_zero]
          rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
              from (W_smooth W).ordAtInfty_zero]
          exact WithTop.coe_lt_top _
        · have h_a3_ord_zero : (W_smooth W).ordAtInfty
              (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) = 0 :=
            (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha3
          rw [h_a3_ord_zero]
          rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
              WithTop.coe_lt_coe]
          have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
          linarith
      exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
        W P k _ _ h_neg_a1xq_bridge h_neg_a3_bridge h_neg_a3_ord_le
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W P k _ _ h_neg_y_pow_bridge h_rest_bridge
    (ordAtInfty_neg_y_gen_pow_card_lt_rest W hq)

/-- **Bridge at `(x_gen - (negFrob).pullback x_gen)^2` (slope-denominator
squared) for non-2-torsion T**: pow on the just-shipped bridge for
`x_gen - negFrob.pullback x_gen`.  This is the denominator of
`addPullback_x = Num / (x - π·x)²`. -/
theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2)) =
      (W_smooth W).ordAtInfty
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
  have h_ne : x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  exact ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ _ h_ne
    (bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq) 2

/-- **Closed form: ordAtInfty((x_gen - π·x_gen)²) = -4q** under `hq`. -/
theorem ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) =
      (((-4 * (Fintype.card K : ℤ) : ℤ) : ℤ) : WithTop ℤ) := by
  have h_ne : x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  have h_pow : (W_smooth W).ordAtInfty
      ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) =
      (2 : ℕ) • (W_smooth W).ordAtInfty
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) :=
    (W_smooth W).ordAtInfty_pow h_ne 2
  rw [h_pow, ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq W hq,
    two_nsmul, ← WithTop.coe_add]
  congr 1
  ring

/-- **Bridge at `(negFrob).pullback x_gen` ^ 2 for non-2-torsion T**: pow on
shipped bridge for `(negFrob).pullback x_gen`. -/
theorem bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (x_gen W) ^ 2)) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) := by
  have h_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
  exact ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ _ h_ne
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor) 2

/-- **Bridge at `x_gen · ((negFrob).pullback x_gen)^2` (= Num_reduced's term
T7) for non-2-torsion T**: mul on bridge for `x_gen` and bridge for
`((negFrob).pullback x_gen)^2`.  This is the strictly-smallest term in
the reduced numerator with ord `-4q - 2`. -/
theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2)) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) := by
  have h_pix_sq_ne : (negFrobeniusIsog W).pullback (x_gen W) ^ 2 ≠ 0 :=
    pow_ne_zero _ (negFrobeniusIsog_pullback_x_gen_ne_zero W)
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W ⟨xT, yT, h_ns⟩ _ _ _ (x_gen_ne_zero W) h_pix_sq_ne
    (bridge_at_x_gen_of_non_2_tor W xT yT h_ns h_not_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor
      W xT yT h_ns h_not_2_tor)

/-- **Bridge at T6 = `x_gen² · (negFrob).pullback x_gen`** for non-2-torsion T:
mul on bridge for `x_gen²` (pow) and `(negFrob).pullback x_gen` (shipped). -/
theorem bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_x_sq_ne : x_gen W ^ 2 ≠ 0 := pow_ne_zero _ (x_gen_ne_zero W)
  have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
  have h_x_sq_bridge : (W_smooth W).ord_P
      (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
      (translateAlgEquivOfPoint W
        (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
        (x_gen W ^ 2)) =
      (W_smooth W).ordAtInfty (x_gen W ^ 2) :=
    ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
      W _ _ _ (x_gen_ne_zero W)
      (bridge_at_x_gen_of_non_2_tor W xT yT h_ns h_not_2_tor) 2
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ h_x_sq_ne h_pix_ne h_x_sq_bridge
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor)

/-- **Bridge at `x_gen · (negFrob).pullback x_gen`** for non-2-torsion T:
mul on bridges for `x_gen` (shipped) and `(negFrob).pullback x_gen` (shipped).
This is the building block for T8 = `2·a₂·x_gen·(negFrob).pullback x_gen`. -/
theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ (x_gen_ne_zero W) h_pix_ne
    (bridge_at_x_gen_of_non_2_tor W xT yT h_ns h_not_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor)

/-- **Bridge at `y_gen * (negFrob).pullback y_gen`** for non-2-torsion T
under `hq`: mul on bridges for `y_gen` (shipped) and `(negFrob).pullback y_gen`
(shipped). Building block for T4 = `-2·y·π·y`. -/
theorem bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W * (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) := by
  have h_piy_ne := negFrobeniusIsog_pullback_y_gen_ne_zero W hq
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ (y_gen_ne_zero W) h_piy_ne
    (bridge_at_y_gen_of_non_2_tor W xT yT h_ns h_not_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- **Bridge at `x_gen * (negFrob).pullback y_gen`** for non-2-torsion T
under `hq`: mul on bridges for `x_gen` (shipped) and `(negFrob).pullback y_gen`
(shipped). Building block for T5. -/
theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) := by
  have h_piy_ne := negFrobeniusIsog_pullback_y_gen_ne_zero W hq
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ (x_gen_ne_zero W) h_piy_ne
    (bridge_at_x_gen_of_non_2_tor W xT yT h_ns h_not_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- **Bridge at `(negFrob).pullback x_gen * y_gen`** for non-2-torsion T:
mul on bridges for `(negFrob).pullback x_gen` (shipped) and `y_gen`
(shipped). Building block for T5. -/
theorem bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
  have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ h_pix_ne (y_gen_ne_zero W)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor)
    (bridge_at_y_gen_of_non_2_tor W xT yT h_ns h_not_2_tor)

/-- **Bridge at `x_gen + (negFrob).pullback x_gen`** for non-2-torsion T
under `hq`: strict-add with `(negFrob).pullback x_gen` having strictly
smaller ord (-2q < -2). -/
theorem bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [show x_gen W + (negFrobeniusIsog W).pullback (x_gen W) =
      (negFrobeniusIsog W).pullback (x_gen W) + x_gen W by ring]
  have h_lt : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (x_gen W)) <
      (W_smooth W).ordAtInfty (x_gen W) := by
    rw [ordAtInfty_negFrobeniusIsog_pullback_x_gen W,
        ordAtInfty_x_gen W]
    change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
        (((-2 : ℤ) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor)
    (bridge_at_x_gen_of_non_2_tor W xT yT h_ns h_not_2_tor) h_lt

/-- **Bridge at `y_gen + (negFrob).pullback y_gen`** for non-2-torsion T
under `hq`: strict-add with `(negFrob).pullback y_gen` having strictly
smaller ord (-3q < -3). -/
theorem bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)) := by
  rw [show y_gen W + (negFrobeniusIsog W).pullback (y_gen W) =
      (negFrobeniusIsog W).pullback (y_gen W) + y_gen W by ring]
  have h_lt : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (y_gen W)) <
      (W_smooth W).ordAtInfty (y_gen W) := by
    rw [ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq,
        ordAtInfty_y_gen W]
    change (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
        (((-3 : ℤ) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)
    (bridge_at_y_gen_of_non_2_tor W xT yT h_ns h_not_2_tor) h_lt

/-- **Bridge at T1 = `a₄ · (x_gen + (negFrob).pullback x_gen)`** for non-2-torsion T
under `hq`: const_mul on the just-shipped strict-add bridge. -/
theorem bridge_at_T1_a4_x_add_pi_x_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))) := by
  have h_sum_ne : x_gen W + (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 := by
    intro h_zero
    have h_top : (W_smooth W).ordAtInfty
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) = ⊤ := by
      rw [h_zero]; exact (W_smooth W).ordAtInfty_zero
    have h_lt : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W)) <
        (W_smooth W).ordAtInfty (x_gen W) := by
      rw [ordAtInfty_negFrobeniusIsog_pullback_x_gen W,
          ordAtInfty_x_gen W]
      change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
          (((-2 : ℤ) : ℤ) : WithTop ℤ)
      rw [WithTop.coe_lt_coe]
      have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
      linarith
    have h_eq : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) + x_gen W) =
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W)) :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
    rw [show x_gen W + (negFrobeniusIsog W).pullback (x_gen W) =
        (negFrobeniusIsog W).pullback (x_gen W) + x_gen W by ring,
        h_eq, ordAtInfty_negFrobeniusIsog_pullback_x_gen W] at h_top
    exact WithTop.coe_ne_top h_top
  exact ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ W.toAffine.a₄ _ h_sum_ne
    (bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- Helper: `x_gen + (negFrob).pullback x_gen ≠ 0` under `hq`. -/
theorem x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    x_gen W + (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  intro h_zero
  have h_top : (W_smooth W).ordAtInfty
      (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) = ⊤ := by
    rw [h_zero]; exact (W_smooth W).ordAtInfty_zero
  have h_lt : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (x_gen W)) <
      (W_smooth W).ordAtInfty (x_gen W) := by
    rw [ordAtInfty_negFrobeniusIsog_pullback_x_gen W, ordAtInfty_x_gen W]
    change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
        (((-2 : ℤ) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  have h_eq : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (x_gen W) + x_gen W) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W)) :=
    (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
  rw [show x_gen W + (negFrobeniusIsog W).pullback (x_gen W) =
      (negFrobeniusIsog W).pullback (x_gen W) + x_gen W by ring,
      h_eq, ordAtInfty_negFrobeniusIsog_pullback_x_gen W] at h_top
  exact WithTop.coe_ne_top h_top

/-- Helper: `y_gen + (negFrob).pullback y_gen ≠ 0` under `hq`. -/
theorem y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    y_gen W + (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 := by
  intro h_zero
  have h_top : (W_smooth W).ordAtInfty
      (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)) = ⊤ := by
    rw [h_zero]; exact (W_smooth W).ordAtInfty_zero
  have h_lt : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (y_gen W)) <
      (W_smooth W).ordAtInfty (y_gen W) := by
    rw [ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq, ordAtInfty_y_gen W]
    change (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
        (((-3 : ℤ) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  have h_eq : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (y_gen W) + y_gen W) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (y_gen W)) :=
    (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
  rw [show y_gen W + (negFrobeniusIsog W).pullback (y_gen W) =
      (negFrobeniusIsog W).pullback (y_gen W) + y_gen W by ring,
      h_eq, ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq] at h_top
  exact WithTop.coe_ne_top h_top

/-- **Bridge at T2 = `(2 : K(E)) · a₆`** for non-2-torsion T: this is just
`algebraMap (2 · a₆)` since `2 = algebraMap 2`.  Trivial constant bridge. -/
theorem bridge_at_T2_two_a6_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT)
    (_h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((2 : W.toAffine.FunctionField) *
            algebraMap K W.toAffine.FunctionField W.toAffine.a₆)) =
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₆) := by
  have h_eq : (2 : W.toAffine.FunctionField) *
      algebraMap K W.toAffine.FunctionField W.toAffine.a₆ =
      algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₆) := by
    rw [map_mul, map_ofNat]
  rw [h_eq]
  exact ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty
    W _ _ (2 * W.toAffine.a₆)

/-- **Bridge at T3-without-neg = `a₃ · (y_gen + (negFrob).pullback y_gen)`**
for non-2-torsion T under `hq`: const_mul on the strict-add bridge. -/
theorem bridge_at_T3_a3_y_add_pi_y_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
            (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))) :=
  ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ W.toAffine.a₃ _
    (y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero W hq)
    (bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- **Bridge at T4-without-neg = `(2 : K(E)) · y_gen · (negFrob).pullback y_gen`**
for non-2-torsion T under `hq`: regroup as `algMap 2 · (y · π·y)` and
const_mul on the bridge for `y · π·y`. -/
theorem bridge_at_T4_two_y_pi_y_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((2 : W.toAffine.FunctionField) * y_gen W *
            (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) * y_gen W *
          (negFrobeniusIsog W).pullback (y_gen W)) := by
  rw [show (2 : W.toAffine.FunctionField) * y_gen W *
      (negFrobeniusIsog W).pullback (y_gen W) =
      algebraMap K W.toAffine.FunctionField (2 : K) *
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) by
    rw [map_ofNat]; ring]
  have h_y_pi_y_ne : y_gen W * (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 :=
    mul_ne_zero (y_gen_ne_zero W) (negFrobeniusIsog_pullback_y_gen_ne_zero W hq)
  exact ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ (2 : K) _ h_y_pi_y_ne
    (bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- **Bridge at T8 = `(2 : K(E)) · a₂ · x_gen · (negFrob).pullback x_gen`** for
non-2-torsion T: regroup and const_mul on x·π·x bridge. -/
theorem bridge_at_T8_two_a2_x_pi_x_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((2 : W.toAffine.FunctionField) *
            algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
            x_gen W * (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
          x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [show (2 : W.toAffine.FunctionField) *
      algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
      x_gen W * (negFrobeniusIsog W).pullback (x_gen W) =
      algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₂) *
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) by
    rw [map_mul, map_ofNat]; ring]
  have h_x_pi_x_ne : x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    mul_ne_zero (x_gen_ne_zero W) (negFrobeniusIsog_pullback_x_gen_ne_zero W)
  exact ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ (2 * W.toAffine.a₂) _ h_x_pi_x_ne
    (bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor)

/-- **Bridge at `x_gen · (negFrob).pullback y_gen + (negFrob).pullback x_gen · y_gen`**
under `hq` for non-2-torsion T: strict-add with `x_gen · π·y` having
strictly smaller ord (-3q - 2 < -2q - 3 for q ≥ 2). -/
theorem bridge_at_x_pi_y_add_pi_x_y_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
  have h_piy_ne := negFrobeniusIsog_pullback_y_gen_ne_zero W hq
  have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
  have h_xy_mul_split : (W_smooth W).ordAtInfty
      (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W) +
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (y_gen W)) :=
    (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_piy_ne
  have h_xy_ord : (W_smooth W).ordAtInfty
      (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
      (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) := by
    rw [h_xy_mul_split, ordAtInfty_x_gen W,
        ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq]
    change (((-2 : ℤ) : ℤ) : WithTop ℤ) +
        (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
        (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add]
    congr 1
    ring
  have h_pxy_mul_split : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W)) +
        (W_smooth W).ordAtInfty (y_gen W) :=
    (W_smooth W).ordAtInfty_mul h_pix_ne (y_gen_ne_zero W)
  have h_pxy_ord : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
      (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) := by
    rw [h_pxy_mul_split, ordAtInfty_negFrobeniusIsog_pullback_x_gen W,
        ordAtInfty_y_gen W]
    change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) +
        (((-3 : ℤ) : ℤ) : WithTop ℤ) =
        (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add]
    congr 1
  have h_lt : (W_smooth W).ordAtInfty
      (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) <
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
    rw [h_xy_ord, h_pxy_ord]
    rw [WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_non_2_tor
      W xT yT h_ns h_not_2_tor) h_lt

/-- **Bridge at T5-without-neg = `a₁ · (x · π·y + π·x · y)`** under `hq` for
non-2-torsion T: const_mul on the strict-add bridge. -/
theorem bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
              (negFrobeniusIsog W).pullback (x_gen W) * y_gen W))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) := by
  have h_sum_ne : x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
      (negFrobeniusIsog W).pullback (x_gen W) * y_gen W ≠ 0 := by
    intro h_zero
    have h_top : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) = ⊤ := by
      rw [h_zero]; exact (W_smooth W).ordAtInfty_zero
    have h_piy_ne := negFrobeniusIsog_pullback_y_gen_ne_zero W hq
    have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
    have h_xy_mul_split : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
        (W_smooth W).ordAtInfty (x_gen W) +
          (W_smooth W).ordAtInfty
            ((negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_piy_ne
    have h_xy_ord : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
        (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) := by
      rw [h_xy_mul_split, ordAtInfty_x_gen W,
          ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq]
      change (((-2 : ℤ) : ℤ) : WithTop ℤ) +
          (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
          (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
      ring
    have h_pxy_mul_split : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W)) +
          (W_smooth W).ordAtInfty (y_gen W) :=
      (W_smooth W).ordAtInfty_mul h_pix_ne (y_gen_ne_zero W)
    have h_pxy_ord : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) := by
      rw [h_pxy_mul_split, ordAtInfty_negFrobeniusIsog_pullback_x_gen W,
          ordAtInfty_y_gen W]
      change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) +
          (((-3 : ℤ) : ℤ) : WithTop ℤ) =
          (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
    have h_lt : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) <
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
      rw [h_xy_ord, h_pxy_ord]
      rw [WithTop.coe_lt_coe]
      have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
      linarith
    have h_eq : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
    rw [h_eq, h_xy_ord] at h_top
    exact WithTop.coe_ne_top h_top
  exact ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ W.toAffine.a₁ _ h_sum_ne
    (bridge_at_x_pi_y_add_pi_x_y_of_non_2_tor W xT yT h_ns h_not_2_tor hq)

/-- **Strict comparison helper**: `a < b` (over ℤ) plus a `b ≤ x` bound on
`x : WithTop ℤ` gives `((a : ℤ) : WithTop ℤ) < x`. -/
theorem withTop_int_lt_of_lt_of_le {a b : ℤ} (h : a < b)
    {x : WithTop ℤ} (hx : ((b : ℤ) : WithTop ℤ) ≤ x) :
    ((a : ℤ) : WithTop ℤ) < x :=
  (WithTop.coe_lt_coe.mpr h).trans_le hx

/-- **Closed-form ordAtInfty bound for T1 = `a₄·(x+π·x)`**: `≥ -3 - 3q`. -/
theorem ordAtInfty_T1_ge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))) := by
  by_cases ha4 : W.toAffine.a₄ = 0
  · rw [ha4, map_zero, zero_mul]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
        from (W_smooth W).ordAtInfty_zero]
    exact le_top
  · have h_a4_ne : algebraMap K W.toAffine.FunctionField W.toAffine.a₄ ≠ 0 :=
      fun h => ha4 (FaithfulSMul.algebraMap_injective K
        W.toAffine.FunctionField (h.trans (map_zero _).symm))
    have h_sum_ne :
        x_gen W + (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
      x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero W hq
    have h_mul_eq : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))) =
        (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₄) +
          (W_smooth W).ordAtInfty
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) :=
      (W_smooth W).ordAtInfty_mul h_a4_ne h_sum_ne
    have h_a4_ord : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₄) = 0 :=
      (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha4
    have h_x_lt : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W)) <
        (W_smooth W).ordAtInfty (x_gen W) := by
      rw [ordAtInfty_negFrobeniusIsog_pullback_x_gen W, ordAtInfty_x_gen W]
      change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
          (((-2 : ℤ) : ℤ) : WithTop ℤ)
      rw [WithTop.coe_lt_coe]
      have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
      linarith
    have h_xpix_eq : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) + x_gen W) =
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W)) :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_x_lt
    have h_xsum_ord : (W_smooth W).ordAtInfty
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) =
        (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
      rw [show x_gen W + (negFrobeniusIsog W).pullback (x_gen W) =
          (negFrobeniusIsog W).pullback (x_gen W) + x_gen W by ring]
      rw [h_xpix_eq]
      exact ordAtInfty_negFrobeniusIsog_pullback_x_gen W
    rw [h_mul_eq, h_a4_ord, zero_add, h_xsum_ord]
    change (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
        (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_le_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith

/-- **Bound for T2 = `(2 : K(E)) · a₆`**: `≥ 0 ≥ -3 - 3q` for `q ≥ 0`. -/
theorem ordAtInfty_T2_ge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₆) := by
  have h_eq : (2 : W.toAffine.FunctionField) *
      algebraMap K W.toAffine.FunctionField W.toAffine.a₆ =
      algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₆) := by
    rw [map_mul, map_ofNat]
  rw [h_eq]
  by_cases h2a6 : (2 * W.toAffine.a₆ : K) = 0
  · rw [h2a6, map_zero]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
        from (W_smooth W).ordAtInfty_zero]
    exact le_top
  · have h_eq2 : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₆)) = 0 :=
      (W_smooth W).ordAtInfty_algebraMap_F_nonzero h2a6
    rw [h_eq2]
    change (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
        ((0 : ℤ) : WithTop ℤ)
    rw [WithTop.coe_le_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith

/-- **Bound for `-T3 = -(a₃·(y + π·y))`**: `≥ -3q ≥ -3 - 3q`. -/
theorem ordAtInfty_neg_T3_ge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)))) := by
  have h_neg_eq : (W_smooth W).ordAtInfty
      (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))) :=
    (W_smooth W).ordAtInfty_neg _
  rw [h_neg_eq]
  by_cases ha3 : W.toAffine.a₃ = 0
  · rw [ha3, map_zero, zero_mul]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
        from (W_smooth W).ordAtInfty_zero]
    exact le_top
  · have h_a3_ne : algebraMap K W.toAffine.FunctionField W.toAffine.a₃ ≠ 0 :=
      fun h => ha3 (FaithfulSMul.algebraMap_injective K
        W.toAffine.FunctionField (h.trans (map_zero _).symm))
    have h_ypy_ne : y_gen W + (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 :=
      y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero W hq
    have h_mul : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))) =
        (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) +
        (W_smooth W).ordAtInfty
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_mul h_a3_ne h_ypy_ne
    have h_a3_ord_zero : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) = 0 :=
      (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha3
    have h_y_lt : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (y_gen W)) <
        (W_smooth W).ordAtInfty (y_gen W) := by
      rw [ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq, ordAtInfty_y_gen W]
      change (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
          (((-3 : ℤ) : ℤ) : WithTop ℤ)
      rw [WithTop.coe_lt_coe]
      have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
      linarith
    have h_ypy_eq : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (y_gen W) + y_gen W) =
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_y_lt
    have h_ypy_ord : (W_smooth W).ordAtInfty
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)) =
        (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
      rw [show y_gen W + (negFrobeniusIsog W).pullback (y_gen W) =
          (negFrobeniusIsog W).pullback (y_gen W) + y_gen W by ring,
          h_ypy_eq, ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq]
      rfl
    rw [h_mul, h_a3_ord_zero, zero_add, h_ypy_ord]
    change (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
        (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_le_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith

/-- **Bound for `-T4 = -((2 : K(E)) · y · π·y)`**: `= -3 - 3q` exactly. -/
theorem ordAtInfty_neg_T4_ge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (-((2 : W.toAffine.FunctionField) * y_gen W *
          (negFrobeniusIsog W).pullback (y_gen W))) := by
  have h_neg_eq : (W_smooth W).ordAtInfty
      (-((2 : W.toAffine.FunctionField) * y_gen W *
        (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) * y_gen W *
          (negFrobeniusIsog W).pullback (y_gen W)) :=
    (W_smooth W).ordAtInfty_neg _
  rw [h_neg_eq]
  have h_eq : (2 : W.toAffine.FunctionField) * y_gen W *
      (negFrobeniusIsog W).pullback (y_gen W) =
      algebraMap K W.toAffine.FunctionField (2 : K) *
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) := by
    rw [map_ofNat]; ring
  rw [h_eq]
  have h_piy_ne := negFrobeniusIsog_pullback_y_gen_ne_zero W hq
  have h_ypy_ne : y_gen W * (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 :=
    mul_ne_zero (y_gen_ne_zero W) h_piy_ne
  by_cases h2z : (2 : K) = 0
  · have : algebraMap K W.toAffine.FunctionField (2 : K) = 0 := by
      rw [h2z, map_zero]
    rw [this, zero_mul]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
        from (W_smooth W).ordAtInfty_zero]
    exact le_top
  · have h_alg2_ne : algebraMap K W.toAffine.FunctionField (2 : K) ≠ 0 :=
      fun h => h2z (FaithfulSMul.algebraMap_injective K
        W.toAffine.FunctionField (h.trans (map_zero _).symm))
    have h_mul : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField (2 : K) *
          (y_gen W * (negFrobeniusIsog W).pullback (y_gen W))) =
        (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField (2 : K)) +
        (W_smooth W).ordAtInfty
          (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_mul h_alg2_ne h_ypy_ne
    have h_inner : (W_smooth W).ordAtInfty
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
        (W_smooth W).ordAtInfty (y_gen W) +
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_mul (y_gen_ne_zero W) h_piy_ne
    have h_2_zero : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField (2 : K)) = 0 :=
      (W_smooth W).ordAtInfty_algebraMap_F_nonzero h2z
    rw [h_mul, h_2_zero, zero_add, h_inner, ordAtInfty_y_gen W,
        ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq]
    change (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
        (((-3 : ℤ) : ℤ) : WithTop ℤ) +
          (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    linarith

/-- **Bound for `-T5 = -(a₁·(x · π·y + π·x · y))`**: `≥ -3q-2 ≥ -3 - 3q`. -/
theorem ordAtInfty_neg_T5_ge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W))) := by
  have h_neg_eq : (W_smooth W).ordAtInfty
      (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) :=
    (W_smooth W).ordAtInfty_neg _
  rw [h_neg_eq]
  by_cases ha1 : W.toAffine.a₁ = 0
  · rw [ha1, map_zero, zero_mul]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
        from (W_smooth W).ordAtInfty_zero]
    exact le_top
  · have h_a1_ne : algebraMap K W.toAffine.FunctionField W.toAffine.a₁ ≠ 0 :=
      fun h => ha1 (FaithfulSMul.algebraMap_injective K
        W.toAffine.FunctionField (h.trans (map_zero _).symm))
    have h_piy_ne := negFrobeniusIsog_pullback_y_gen_ne_zero W hq
    have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
    have h_xy_ord : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
        (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) := by
      have h_split : (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
          (W_smooth W).ordAtInfty (x_gen W) +
          (W_smooth W).ordAtInfty
            ((negFrobeniusIsog W).pullback (y_gen W)) :=
        (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_piy_ne
      rw [h_split, ordAtInfty_x_gen W,
          ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq]
      change (((-2 : ℤ) : ℤ) : WithTop ℤ) +
          (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
          (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]; congr 1; ring
    have h_pyx_ord : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) := by
      have h_split : (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
          (W_smooth W).ordAtInfty
            ((negFrobeniusIsog W).pullback (x_gen W)) +
          (W_smooth W).ordAtInfty (y_gen W) :=
        (W_smooth W).ordAtInfty_mul h_pix_ne (y_gen_ne_zero W)
      rw [h_split, ordAtInfty_negFrobeniusIsog_pullback_x_gen W,
          ordAtInfty_y_gen W]
      change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) +
          (((-3 : ℤ) : ℤ) : WithTop ℤ) =
          (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]; congr 1
    have h_inner_lt : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) <
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
      rw [h_xy_ord, h_pyx_ord, WithTop.coe_lt_coe]
      have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
      linarith
    have h_sum_ord : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ordAtInfty_add_eq_of_lt h_inner_lt).trans h_xy_ord
    have h_sum_ne : x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
        (negFrobeniusIsog W).pullback (x_gen W) * y_gen W ≠ 0 := by
      intro hz
      have : (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) = ⊤ := by
        rw [hz]; exact (W_smooth W).ordAtInfty_zero
      rw [h_sum_ord] at this
      exact WithTop.coe_ne_top this
    have h_mul_split : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) =
        (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁) +
        (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) :=
      (W_smooth W).ordAtInfty_mul h_a1_ne h_sum_ne
    have h_a1_zero : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁) = 0 :=
      (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha1
    rw [h_mul_split, h_a1_zero, zero_add, h_sum_ord]
    change (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
        (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_le_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith

/-- **Bound for T6 = `x² · π·x`**: `= -2q - 4 ≥ -3 - 3q` for `q ≥ 1`. -/
theorem ordAtInfty_T6_ge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_x_sq_ne : x_gen W ^ 2 ≠ 0 := pow_ne_zero _ (x_gen_ne_zero W)
  have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
  have h_mul : (W_smooth W).ordAtInfty
      (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W ^ 2) +
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W)) :=
    (W_smooth W).ordAtInfty_mul h_x_sq_ne h_pix_ne
  have h_x_sq_ord : (W_smooth W).ordAtInfty (x_gen W ^ 2) =
      (((-4 : ℤ) : ℤ) : WithTop ℤ) := by
    have h_pow : (W_smooth W).ordAtInfty (x_gen W ^ 2) =
        (2 : ℕ) • (W_smooth W).ordAtInfty (x_gen W) :=
      (W_smooth W).ordAtInfty_pow (x_gen_ne_zero W) 2
    rw [h_pow, ordAtInfty_x_gen W]; rfl
  rw [h_mul, h_x_sq_ord, ordAtInfty_negFrobeniusIsog_pullback_x_gen W]
  change (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (((-4 : ℤ) : ℤ) : WithTop ℤ) +
        (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  linarith

/-- **Bound for T8 = `(2 : K(E)) · a₂ · x · π·x`**: `≥ -2q-2 ≥ -3 - 3q`. -/
theorem ordAtInfty_T8_ge
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
          x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_eq : (2 : W.toAffine.FunctionField) *
      algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
      x_gen W * (negFrobeniusIsog W).pullback (x_gen W) =
      algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₂) *
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
    rw [map_mul, map_ofNat]; ring
  rw [h_eq]
  by_cases h2a2 : (2 * W.toAffine.a₂ : K) = 0
  · rw [h2a2, map_zero, zero_mul]
    rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
        from (W_smooth W).ordAtInfty_zero]
    exact le_top
  · have h_alg_ne : algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₂)
        ≠ 0 := fun h => h2a2 (FaithfulSMul.algebraMap_injective K
          W.toAffine.FunctionField (h.trans (map_zero _).symm))
    have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
    have h_xpix_ne : x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
      mul_ne_zero (x_gen_ne_zero W) h_pix_ne
    have h_mul : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₂) *
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W))) =
        (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₂)) +
        (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) :=
      (W_smooth W).ordAtInfty_mul h_alg_ne h_xpix_ne
    have h_inner : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) =
        (W_smooth W).ordAtInfty (x_gen W) +
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W)) :=
      (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_pix_ne
    have h_alg_zero : (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₂)) = 0 :=
      (W_smooth W).ordAtInfty_algebraMap_F_nonzero h2a2
    rw [h_mul, h_alg_zero, zero_add, h_inner, ordAtInfty_x_gen W,
        ordAtInfty_negFrobeniusIsog_pullback_x_gen W]
    change (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
        (((-2 : ℤ) : ℤ) : WithTop ℤ) +
          (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith

/-- Helper: rearrangement of `addPullbackNumerator_reduced_negFrobenius`
expression to put the dominant term `x · π·x²` first, with the remaining
seven terms forming a List.sum. -/
theorem reduced_form_eq_dom_plus_list (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] :
    algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) +
      (2 : W.toAffine.FunctionField) *
        algebraMap K W.toAffine.FunctionField W.toAffine.a₆ -
      algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)) -
      (2 : W.toAffine.FunctionField) * y_gen W *
        (negFrobeniusIsog W).pullback (y_gen W) -
      algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) +
      x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W) +
      x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2 +
      (2 : W.toAffine.FunctionField) *
        algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
        x_gen W * (negFrobeniusIsog W).pullback (x_gen W) =
      x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2 +
      List.sum [
        algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)),
        (2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₆,
        -(algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))),
        -((2 : W.toAffine.FunctionField) * y_gen W *
          (negFrobeniusIsog W).pullback (y_gen W)),
        -(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)),
        x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W),
        (2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
          x_gen W * (negFrobeniusIsog W).pullback (x_gen W)] := by
  simp only [List.sum_cons, List.sum_nil, add_zero]
  ring

/-- **Bridge at `addPullbackNumerator_negFrobenius`** for non-2-torsion T
under `hq`, **unconditional**.

Apply the strict-add chain combinator
`ord_P_translateAlgEquivOfPoint_sum_dominant` with `dom = x · π·x²`
(T7, ord = -4q-2) and rest = list of the 7 other terms (each ord ≥ -3-3q
via shipped `ordAtInfty_T*_ge` bounds).  Strict comparison
`-2 - 4q < -3 - 3q` for `q ≥ 2` closes the chain via the
`withTop_int_lt_of_lt_of_le` helper. -/
theorem bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (addPullbackNumerator_negFrobenius W)) =
      (W_smooth W).ordAtInfty
        (addPullbackNumerator_negFrobenius W) := by
  rw [addPullbackNumerator_negFrobenius_eq_reduced]
  unfold addPullbackNumerator_reduced_negFrobenius
  rw [reduced_form_eq_dom_plus_list W]
  have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  apply ord_P_translateAlgEquivOfPoint_sum_dominant
  · exact bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor
      W xT yT h_ns h_not_2_tor
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with hT1 | hT2 | hT3 | hT4 | hT5 | hT6 | hT8
    · exact hT1 ▸ bridge_at_T1_a4_x_add_pi_x_of_non_2_tor
        W xT yT h_ns h_not_2_tor hq
    · exact hT2 ▸ bridge_at_T2_two_a6_of_non_2_tor W xT yT h_ns h_not_2_tor
    · exact hT3 ▸ ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
        W _ _ _ (bridge_at_T3_a3_y_add_pi_y_of_non_2_tor
          W xT yT h_ns h_not_2_tor hq)
    · exact hT4 ▸ ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
        W _ _ _ (bridge_at_T4_two_y_pi_y_of_non_2_tor
          W xT yT h_ns h_not_2_tor hq)
    · exact hT5 ▸ ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
        W _ _ _ (bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_non_2_tor
          W xT yT h_ns h_not_2_tor hq)
    · exact hT6 ▸
        bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor
          W xT yT h_ns h_not_2_tor
    · exact hT8 ▸ bridge_at_T8_two_a2_x_pi_x_of_non_2_tor
        W xT yT h_ns h_not_2_tor
  · intro f hf
    have h_pix_ne := negFrobeniusIsog_pullback_x_gen_ne_zero W
    have h_pix_sq_ne : (negFrobeniusIsog W).pullback (x_gen W) ^ 2 ≠ 0 :=
      pow_ne_zero _ h_pix_ne
    have h_pix_sq_ord : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
        (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
      have h_pow : (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
          (2 : ℕ) • (W_smooth W).ordAtInfty
            ((negFrobeniusIsog W).pullback (x_gen W)) :=
        (W_smooth W).ordAtInfty_pow h_pix_ne 2
      rw [h_pow, ordAtInfty_negFrobeniusIsog_pullback_x_gen W]
      change (2 : ℕ) • (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
          (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
      rw [two_nsmul, ← WithTop.coe_add]
      congr 1; ring
    have h_T7_mul : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
        (W_smooth W).ordAtInfty (x_gen W) +
          (W_smooth W).ordAtInfty
            ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) :=
      (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_pix_sq_ne
    have h_T7_ord : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
        (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
      rw [h_T7_mul, ordAtInfty_x_gen W, h_pix_sq_ord, ← WithTop.coe_add]
      congr 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    have h_int_lt : (-2 - 4 * (Fintype.card K : ℤ)) <
        (-3 - 3 * (Fintype.card K : ℤ)) := by linarith
    have h_lt_helper : ∀ {x : WithTop ℤ},
        (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤ x →
        (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) < x := by
      intro x hx
      rw [h_T7_ord]
      exact withTop_int_lt_of_lt_of_le h_int_lt hx
    rcases hf with hT1 | hT2 | hT3 | hT4 | hT5 | hT6 | hT8
    · exact hT1 ▸ h_lt_helper (ordAtInfty_T1_ge W hq)
    · exact hT2 ▸ h_lt_helper (ordAtInfty_T2_ge W hq)
    · exact hT3 ▸ h_lt_helper (ordAtInfty_neg_T3_ge W hq)
    · exact hT4 ▸ h_lt_helper (ordAtInfty_neg_T4_ge W hq)
    · exact hT5 ▸ h_lt_helper (ordAtInfty_neg_T5_ge W hq)
    · exact hT6 ▸ h_lt_helper (ordAtInfty_T6_ge W hq)
    · exact hT8 ▸ h_lt_helper (ordAtInfty_T8_ge W hq)

/-- **Conditional Lemma 3** (parametric on bridge for `addPullback_x` AND
τ_T-invariance of `γ.pullback x_gen`): given the bridge `ord_T(translate
addPullback_x) = ordAtInfty(addPullback_x) = -2` AND τ_T-invariance for
the K-rational kernel point T, derives the unconditional value
`ord_T(γ.pullback x_gen) = -2`.

Composition: `ord_T(γ.pullback x_gen) = ord_T(addPullback_x)
= ord_T(translate addPullback_x)` (by τ_T-invariance, where γ.pullback
x_gen = addPullback_x via shipped Helper 1) `= ordAtInfty(addPullback_x)
= -2` (by bridge + Worker A's `ord_addPullback_x_negFrobenius`).

This is **Lemma 3 conditional** — the bound's substantive content
factored into upstream witnesses (bridge + invariance), each
independently dischargeable via the framework. -/
theorem Conditional.lemma3_pole_at_T_of_bridge_and_invariance
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (hq : 2 ≤ Fintype.card K)
    (h_bridge : (W_smooth W).ord_P
        (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (addPullback_x W (negFrobeniusIsog W))) =
      (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)))
    (h_inv : translateAlgEquivOfPoint W
        (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      (isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  rw [isogOneSub_negFrobenius_pullback]
  rw [addPullbackAlgHom_negFrobenius_x_gen_eq W hq]
  have h_inv' : translateAlgEquivOfPoint W
      (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
      (addPullback_x W (negFrobeniusIsog W)) =
      addPullback_x W (negFrobeniusIsog W) := by
    have : (isogOneSub_negFrobenius W hq).pullback (x_gen W) =
        addPullback_x W (negFrobeniusIsog W) := by
      rw [isogOneSub_negFrobenius_pullback,
          addPullbackAlgHom_negFrobenius_x_gen_eq W hq]
    rw [← this]
    exact h_inv
  rw [show (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
      (addPullback_x W (negFrobeniusIsog W)) =
      (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
      (translateAlgEquivOfPoint W
        (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
        (addPullback_x W (negFrobeniusIsog W))) by rw [h_inv']]
  rw [h_bridge]
  exact ord_addPullback_x_negFrobenius W hq

/-- **Conditional bridge at `addPullback_x W (negFrobeniusIsog W)` for
non-2-torsion T**, parametric on the bridge for `addPullbackNumerator_
negFrobenius`.  Composes Worker A's division identity
(`addPullback_x = Num / (x - π·x)²`) with `div` bridge.

The hypothesis `h_Num_bridge` is the substantive obligation (upstream
content): bridge holds for the polynomial-form numerator.  Once
discharged, this gives the unconditional bridge for `addPullback_x`. -/
theorem bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K)
    (h_Num_bridge : (W_smooth W).ord_P
        (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (addPullbackNumerator_negFrobenius W)) =
      (W_smooth W).ordAtInfty (addPullbackNumerator_negFrobenius W)) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (addPullback_x W (negFrobeniusIsog W))) =
      (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)) := by
  have h_pix_ne : x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  have h_pix_sq_ne : (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 h_pix_ne
  have h_div_eq : addPullback_x W (negFrobeniusIsog W) =
      addPullbackNumerator_negFrobenius W /
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    rw [addPullbackNumerator_negFrobenius_eq W,
        mul_div_cancel_left₀ _ h_pix_sq_ne]
  rw [h_div_eq]
  have h_Num_ord_eq : (W_smooth W).ordAtInfty
      (addPullbackNumerator_negFrobenius W) =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [addPullbackNumerator_negFrobenius_eq_reduced]
    exact ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq W hq
  have h_Num_ne : addPullbackNumerator_negFrobenius W ≠ 0 := fun h => by
    have h_top : (W_smooth W).ordAtInfty
        (addPullbackNumerator_negFrobenius W) = ⊤ := by
      rw [h]; exact (W_smooth W).ordAtInfty_zero
    rw [h_Num_ord_eq] at h_top
    exact WithTop.coe_ne_top h_top
  exact ord_P_translateAlgEquivOfPoint_div_eq_ordAtInfty_of_each
    W ⟨xT, yT, h_ns⟩ _ _ _
    h_Num_ne
    h_pix_sq_ne h_Num_bridge
    (bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- **Bridge at `addPullback_x W (negFrobeniusIsog W)`** for non-2-torsion T
under `hq`, **UNCONDITIONAL**.  Discharges the
`bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num` Conditional consumer
using the just-shipped Num bridge. -/
theorem bridge_at_addPullback_x_negFrobenius_of_non_2_tor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (addPullback_x W (negFrobeniusIsog W))) =
      (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)) :=
  bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num
    W xT yT h_ns h_not_2_tor hq
    (bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq)

/-- **LEMMA 3 UNCONDITIONAL** (Pole at every kernel point):
`ord_T(γ.pullback x_gen) = -2` at any non-2-torsion T = (xT, yT) ∈ E(F_q),
for `γ = isogOneSub_negFrobenius`.

Composition of:
* `bridge_at_addPullback_x_negFrobenius_of_non_2_tor` (just shipped
  unconditional via Num bridge + Conditional discharge).
* `xy_family_isogOneSub_negFrobenius` (Worker A, unconditional via
  curve-level addX/addY identities).
* The fact that K-rational points lie in `ker(γ)` (since π fixes K-rational
  points, so `(1 - π)(T) = 0` for K-rational T). -/
theorem lemma3_pole_at_T_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_not_2_tor : yT ≠ W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  apply Conditional.lemma3_pole_at_T_of_bridge_and_invariance
    W xT yT h_ns hq
  · exact bridge_at_addPullback_x_negFrobenius_of_non_2_tor
      W xT yT h_ns h_not_2_tor hq
  · have h_neg_T_in_ker : -(Affine.Point.some xT yT h_ns) ∈
        (isogOneSub_negFrobenius W hq).kernel := by
      change (isogOneSub_negFrobenius W hq).toAddMonoidHom
        (-(Affine.Point.some xT yT h_ns)) = 0
      rw [isogOneSub_negFrobenius_toAddMonoidHom, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
      change (-(Affine.Point.some xT yT h_ns)) - (-(Affine.Point.some xT yT h_ns)) = 0
      exact sub_self _
    exact (xy_family_isogOneSub_negFrobenius W hq
      ⟨-(Affine.Point.some xT yT h_ns), h_neg_T_in_ker⟩).1

/-- **Tower argument with Computation A + Lemma 5 → V.1.3** (B3
specification, witness-parametric on the substantive obligations B1
and B2).

Signature: given Computation A bridge for our γ + an explicit Lemma 5
(`degreePoleDivisor = 2 · |ker γ|`), discharge `pc_sepDeg_eq_pointCount`.

Expression of Lemma 5 in this consumer: a hypothesis
`h_lemma5 : degreePoleDivisor = 2 * #ker γ` over the same
`projectiveDivisorOf`-derived value Computation A uses.

This consumer is bound-specific — only delivers the discharge for
`γ = isogOneSub_negFrobenius` (the F_q-side fallback). Worker C's
downstream consumers (T-III-4-016 specialised) compose this with their
infrastructure to close the bound chain.

depends_on: T-POLE-DIVISOR-FALLBACK (B1 + B2)
consumes: Computation A bridge (Riemann–Roch for principal divisors,
specialised to our γ) + Lemma 5 (pole-divisor sum over kernel).
-/
theorem pc_sepDeg_eq_pointCount_of_computationA_and_lemma5
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    {hq : 2 ≤ Fintype.card K} (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _
      (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
    (h_compA : ComputationA_bridge_pullback_x_gen W hq)
    (h_finrank_eq_2_deg :
      Module.finrank
        (IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
        W.toAffine.FunctionField =
      2 * (isogOneSub_negFrobenius W hq).degree)
    (h_lemma5 :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
        (fun P => (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) =
      2 * pointCount W.toAffine) :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine := by
  have h_2deg_eq_2pc : 2 * (isogOneSub_negFrobenius W hq).degree =
      2 * pointCount W.toAffine := by
    rw [← h_finrank_eq_2_deg, h_compA, h_lemma5]
  have h_deg_eq_pc : (isogOneSub_negFrobenius W hq).degree =
      pointCount W.toAffine := by
    have h2 : (2 : ℕ) ≠ 0 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h_2deg_eq_2pc
  have h_sep_eq_deg : (isogOneSub_negFrobenius W hq).sepDegree =
      (isogOneSub_negFrobenius W hq).degree :=
    (Isogeny.isSeparable_iff_sepDegree_eq_degree _ h_pc_fin).mp h_pc_sep
  rw [h_sep_eq_deg, h_deg_eq_pc]

/-- **Lemma 5 (bookkeeping form, witness-parametric)**: given per-point
pole-order values + support equality, the pole-divisor sum equals
`2 · pointCount`.

The hypothesis `h_pole_orders` packages the per-point claim that every
point in the support contributes `-2` to `projectiveDivisorOf`, and
`h_support_card` packages the support cardinality (= `pointCount`, since
the support is `{∞} ∪ {F_q-rational SmoothPoints}` for our γ). Together
they reduce Lemma 5 to a pure summation. -/
theorem lemma5_of_pole_orders_and_support_card
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_pole_orders :
      ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P).toNat = 0 ∧
      (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat = 2)
    (h_support_card :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.card =
      pointCount W.toAffine) :
    ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
      (fun P => (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) =
    2 * pointCount W.toAffine := by
  set S := ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support with hS
  set D := Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) with hD
  have h_sum_const : S.sum (fun P => (-(D P)).toNat) =
      S.sum (fun _ => (2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro P hP
    exact (h_pole_orders P hP).2
  rw [h_sum_const, Finset.sum_const, smul_eq_mul]
  rw [h_support_card]
  ring

end Conditional

namespace Conditional

/-- **Declaration 1 (Tier-2.5 #3 prep)**: at any F_q-rational SmoothPoint
`P` of E, if `ord_P P (γ.pullback x_gen) < 0` (i.e. `P` is a pole of
`γ.pullback x_gen`) then `P ∈ ker γ`. Direct contrapositive of the
already-shipped `no_poles_off_kernel_isogOneSub_negFrobenius`. -/
theorem pole_gamma_pullback_x_imp_kernel
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    (P : (W_smooth W).SmoothPoint)
    (h_pole : (W_smooth W).ord_P P
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) <
      ((0 : ℤ) : WithTop ℤ)) :
    (isogOneSub_negFrobenius W hq).toAddMonoidHom
      (Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P) = 0 := by
  by_contra h_not_ker
  have h_nonneg := no_poles_off_kernel_isogOneSub_negFrobenius W hq P h_not_ker
  exact not_le_of_gt h_pole h_nonneg

/-- **Closed-point Lemma 4 (Action 3 γ-form, Sinf-prime level)**.

For any height-one prime `P` of `data.carrier` that does NOT lie over the
X-prime, `0 ≤ data.ordAt P` — equivalently, `γ.pullback x_gen` has no pole
at such a prime. This rules out non-`F_q`-rational closed-point poles at
the algebraic level, which milestone #2's Bridge B needs.

Mathematical content: the Sinf primes lying over `xIdeal := (X)` are
exactly the closed points where `f⁻¹` vanishes (= poles of `f`); a prime
NOT over X corresponds to a closed point where `f` is regular, so its
order `data.ordAt P = -ramificationIdx _ xIdeal P` equals `-0 = 0 ≥ 0`.

Proof: `xIdeal` is maximal (`xIdeal_isMaximal`); if `map xIdeal ≤ P` then
by maximality `xIdeal = P.comap`, hence `P.LiesOver xIdeal` —
contradicting the hypothesis. So `¬ map xIdeal ≤ P`, hence
`ramificationIdx = 0` (`Ideal.ramificationIdx_of_not_le`), hence
`data.ordAt P = -0 = 0 ≥ 0`. -/
theorem pole_gamma_pullback_x_imp_kernel_closed_point
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback
        (x_gen W)) : (W_smooth W).FunctionField))
    (P :
      letI := data.commRing
      Ideal data.carrier)
    [hP_prime :
      letI := data.commRing
      P.IsPrime]
    (hP_not_over :
      letI := data.commRing
      letI := data.algPoly
      ¬ P.LiesOver (Curves.RamificationAtInfinity.xIdeal (k := K))) :
    letI := data.commRing
    letI := data.algPoly
    0 ≤ data.ordAt P := by
  letI := data.commRing
  letI := data.algPoly
  have h_rampidx_zero : Ideal.ramificationIdx
      (Curves.RamificationAtInfinity.xIdeal (k := K)) P = 0 := by
    apply Ideal.ramificationIdx_of_not_le
    intro h_map_le
    apply hP_not_over
    rw [Ideal.map_le_iff_le_comap] at h_map_le
    have h_x_max : (Curves.RamificationAtInfinity.xIdeal (k := K)).IsMaximal :=
      Curves.RamificationAtInfinity.xIdeal_isMaximal
    have h_comap_ne_top : P.comap (algebraMap (Polynomial K) data.carrier) ≠ ⊤ := by
      rw [Ne, Ideal.comap_eq_top_iff]
      exact hP_prime.ne_top
    have h_eq : Curves.RamificationAtInfinity.xIdeal (k := K) =
        P.comap (algebraMap (Polynomial K) data.carrier) :=
      h_x_max.eq_of_le h_comap_ne_top h_map_le
    exact ⟨h_eq⟩
  unfold Curves.RamificationAtInfinity.Sinf.ordAt
  rw [h_rampidx_zero]
  norm_num

/-- **Bridge A (Tier-2.5 #3 prep, field-identification finrank equality)**.

Identifies the consumer-side `Module.finrank (IntermediateField.adjoin K {f})
K(E)` with the abstract-side `@Module.finrank (FractionRing (Polynomial K))
(LinfAt f)` (with the explicit `algebraFractionRing`-derived module instance).
Both compute `[K(E) : K(f)]`.

The canonical identification: `FractionRing (Polynomial K) → K(E)` via
`X ↦ f⁻¹` (the `algebraFractionRing` instance) has image
`K⟮f⁻¹⟯ = K⟮f⟯ = IntermediateField.adjoin K {f}` inside `K(E)`. The two
`Module.finrank` values are therefore equal.

Proof composes Mathlib's `RatFunc.algEquivOfTranscendental f⁻¹ h_inv :
RatFunc K ≃ₐ[K] K⟮f⁻¹⟯` + `K⟮f⟯ = K⟮f⁻¹⟯` (intermediate-field closure
under inverse) + `RatFunc.toFractionRingAlgEquiv` (Mathlib's canonical
`RatFunc K ≃ₐ[K] FractionRing K[X]`) into a `K⟮f⟯ ≃ₐ[K] FractionRing K[X]`
algebra equivalence, then transports the finrank along it via
`Algebra.finrank_eq_of_equiv_equiv`. The commuting square reduces to
checking agreement on the generator `f` (via
`IntermediateField.adjoin_algHom_ext`), which traces through
`f = (f⁻¹)⁻¹`. -/
theorem bridgeA_intermediateField_adjoin_eq_fractionRing_finrank
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    [hf : Fact (Transcendental K (((isogOneSub_negFrobenius W hq).pullback
      (x_gen W)) : (W_smooth W).FunctionField)⁻¹)] :
    Module.finrank
        (IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
        W.toAffine.FunctionField =
      @Module.finrank (FractionRing (Polynomial K))
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
        (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
          (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule := by
  set f : W.toAffine.FunctionField :=
    (isogOneSub_negFrobenius W hq).pullback (x_gen W) with hf_def
  have h_inv : Transcendental K f⁻¹ := hf.out
  have h_adj_eq :
      IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField) =
      IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h1 : f⁻¹ ∈ IntermediateField.adjoin K ({f⁻¹} : Set _) :=
        IntermediateField.mem_adjoin_simple_self K f⁻¹
      have h2 : (f⁻¹)⁻¹ ∈ IntermediateField.adjoin K ({f⁻¹} : Set _) := inv_mem h1
      rwa [inv_inv] at h2
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K f)
  let e1 : (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)) ≃ₐ[K]
           IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField) :=
    IntermediateField.equivOfEq h_adj_eq
  let e2 : (IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField)) ≃ₐ[K]
           RatFunc K :=
    (RatFunc.algEquivOfTranscendental (K := K) f⁻¹ h_inv).symm
  let e3 : RatFunc K ≃ₐ[K] FractionRing (Polynomial K) :=
    RatFunc.toFractionRingAlgEquiv K K
  let e : (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)) ≃ₐ[K]
          FractionRing (Polynomial K) := (e1.trans e2).trans e3
  refine Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv
    (RingEquiv.refl W.toAffine.FunctionField) ?_
  let algMapAlg :
      FractionRing (Polynomial K) →ₐ[K]
        Curves.RamificationAtInfinity.LinfAt (k := K) f :=
    IsScalarTower.toAlgHom K (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K) f)
  let inclSymm : FractionRing (Polynomial K) →ₐ[K] W.toAffine.FunctionField :=
    ((IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)).val).comp
      e.symm.toAlgHom
  have h_alg_eq : (algMapAlg : FractionRing (Polynomial K) →ₐ[K] W.toAffine.FunctionField) =
      inclSymm := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    change algMapAlg (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X) =
        inclSymm (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)
    have h_LHS : algMapAlg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X) = f⁻¹ := by
      change algebraMap (FractionRing (Polynomial K))
          (Curves.RamificationAtInfinity.LinfAt (k := K) f)
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X) = f⁻¹
      rw [← IsScalarTower.algebraMap_apply (Polynomial K) (FractionRing (Polynomial K))
            (Curves.RamificationAtInfinity.LinfAt (k := K) f)]
      rw [Curves.RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply,
          Curves.RamificationAtInfinity.polyToFieldOfInv_X]
    -- Use .val equality (Subtype.ext) to avoid proof-irrelevance issues.
    have h_RHS : inclSymm (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X) = f⁻¹ := by
      change (e.symm (algebraMap (Polynomial K) (FractionRing (Polynomial K))
          Polynomial.X)).val = f⁻¹
      change (((e1.trans e2).trans e3).symm
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)).val =
        f⁻¹
      rw [AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply]
      have h_e3_symm_X : (e3.symm
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)) =
          RatFunc.X := by
        have h_e3_X : e3 (RatFunc.X) =
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X := by
          change (RatFunc.toFractionRingAlgEquiv K K) RatFunc.X = _
          simp only [RatFunc.toFractionRingAlgEquiv_apply]
          change ((algebraMap (Polynomial K) (RatFunc K)) Polynomial.X).toFractionRing = _
          rw [← RatFunc.ofFractionRing_algebraMap (K := K)]
        rw [← h_e3_X, AlgEquiv.symm_apply_apply]
      rw [h_e3_symm_X]
      change (e1.symm ((RatFunc.algEquivOfTranscendental (K := K) f⁻¹ h_inv) RatFunc.X)).val =
        f⁻¹
      have h_e1_symm_val : ∀ x : IntermediateField.adjoin K ({f⁻¹} :
            Set W.toAffine.FunctionField),
          (e1.symm x).val = x.val := fun x => rfl
      rw [h_e1_symm_val]
      exact RatFunc.algEquivOfTranscendental_X f⁻¹ h_inv
    rw [h_LHS, h_RHS]
  apply RingHom.ext
  intro y
  have h := DFunLike.congr_fun h_alg_eq (e y)
  change (algebraMap (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K) f)) (e.toRingEquiv y) = y.val
  calc (algebraMap (FractionRing (Polynomial K))
            (Curves.RamificationAtInfinity.LinfAt (k := K) f)) (e.toRingEquiv y)
      = algMapAlg (e y) := rfl
    _ = inclSymm (e y) := h
    _ = (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)).val
        (e.symm (e y)) := rfl
    _ = (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)).val y := by
        rw [AlgEquiv.symm_apply_apply]
    _ = y.val := rfl

/-- **Weighted pole degree of `f = γ.pullback x_gen` in the `LinfAt f` framing**:
`[K(E) : K(f⁻¹)] = ∑_P (−ord_P f).toNat · inertiaDeg xIdeal P` over
`primesOverFinset xIdeal data.carrier`. Specialises
`finrank_eq_weighted_poleDegree_of_nonconstant`. The conclusion uses the
`@`-explicit `algebraFractionRing`-derived module instance (which sends `X ↦ f⁻¹`),
not the project `FunctionField` instance (which sends `X ↦ x_gen`, giving the
different value `[K(E) : K(x_gen)] = 2`). -/
theorem finrank_gamma_pullback_x_eq_weightedPoleDegree
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    [hf : Fact (Transcendental K
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)]
    (hMF : @Module.Finite (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) :
    letI := data.commRing
    letI := data.isDedekindDomain
    letI := data.algPoly
    @Module.finrank (FractionRing (Polynomial K))
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
        (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
          (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule =
      ∑ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        (-(data.ordAt P)).toNat *
          Ideal.inertiaDeg
            (Curves.RamificationAtInfinity.xIdeal (k := K)) P := by
  exact @Curves.RamificationAtInfinity.finrank_eq_weighted_poleDegree_of_nonconstant
    K _ _ _ _ ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) hf hMF data

/-- **SK-L6CA-HYPS helper**: transcendence is preserved under inversion in a field
(`K(y) = K(y⁻¹)`). Turns `Transcendental K (γ*x)` into the `Transcendental K (γ*x)⁻¹` that
`LinfAt`/`finrank_gamma...` require. -/
theorem transcendental_inv {L : Type*} [Field L] [Algebra K L] {y : L}
    (h : Transcendental K y) : Transcendental K y⁻¹ := fun halg => h (by simpa using halg.inv)

/-- **SK-L6CA-HYPS helper**: `γ*x = (1-π)*x_gen` is transcendental over `K`. The isogeny pullback
is an injective `K`-algebra hom and `x_gen` is transcendental (`x_gen_transcendental`), so its
image is too (aeval-commutation + injectivity). -/
theorem transcendental_gamma_pullback_x (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) :
    Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) := by
  intro halg
  obtain ⟨p, hp, hpg⟩ := halg
  refine x_gen_transcendental W ⟨p, hp, ?_⟩
  have h1 : (isogOneSub_negFrobenius W hq).pullback (Polynomial.aeval (x_gen W) p) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]; exact hpg
  exact (isogOneSub_negFrobenius W hq).pullback_injective (by rw [h1, map_zero])

/-- The `Fact (Transcendental K (γ.pullback x_gen)⁻¹)` instance required by the `LinfAt`
machinery, for `γ = isogOneSub_negFrobenius`. -/
theorem fact_transcendental_gamma_pullback_x_inv (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) :
    Fact (Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹) :=
  ⟨transcendental_inv (transcendental_gamma_pullback_x W hq)⟩

/-- **SK-L6CA-LHS framing bridge** (non-RR): the `[K(E):F(f)]` in `ComputationA_bridge`'s
`adjoin K {f}` framing equals the `finrank (FractionRing(Poly K)) (LinfAt f)` framing of
`finrank_gamma_pullback_x_eq_weightedPoleDegree`. Both are `[K(E):K(f)] = [K(E):K(f⁻¹)]`.
Proof route: `RatFunc.algEquivOfTranscendental` (needs `f` transcendental) + `gammaBar`-style
`AlgEquiv` + `Algebra.finrank_eq_of_equiv_equiv`, mirroring `GapSpines` `l6_v_1_3`. -/
theorem finrank_adjoin_eq_finrank_LinfAt
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    [Fact (Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)] :
    Module.finrank
      (IntermediateField.adjoin K
        ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
          Set W.toAffine.FunctionField))
      W.toAffine.FunctionField =
    @Module.finrank (FractionRing (Polynomial K))
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
        (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
          (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule := by
  set f : W.toAffine.FunctionField := (isogOneSub_negFrobenius W hq).pullback (x_gen W) with hf_def
  have h_f_inv : Transcendental K f⁻¹ := Fact.out
  let e₁ : FractionRing (Polynomial K) ≃ₐ[K]
      ↥(IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField)) :=
    (RatFunc.toFractionRingAlgEquiv K K).symm.trans
      (RatFunc.algEquivOfTranscendental (K := K) f⁻¹ h_f_inv)
  have hgen : ∀ a : W.toAffine.FunctionField,
      a ∈ IntermediateField.adjoin K ({a⁻¹} : Set W.toAffine.FunctionField) := fun a => by
    have h1 : a⁻¹ ∈ IntermediateField.adjoin K ({a⁻¹} : Set W.toAffine.FunctionField) :=
      IntermediateField.subset_adjoin K {a⁻¹} (Set.mem_singleton _)
    simpa using inv_mem h1
  have hadj : IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)
      = IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]; intro x hx
      simp only [Set.mem_singleton_iff] at hx; subst hx; exact hgen f
    · rw [IntermediateField.adjoin_le_iff]; intro x hx
      simp only [Set.mem_singleton_iff] at hx; subst hx
      simpa using hgen f⁻¹
  rw [hadj]
  let e₂ : Curves.RamificationAtInfinity.LinfAt (k := K) f ≃+* W.toAffine.FunctionField :=
    RingEquiv.refl W.toAffine.FunctionField
  have hc : (algebraMap
        ↥(IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField))
        W.toAffine.FunctionField).comp e₁.toRingEquiv.toRingHom =
      e₂.toRingHom.comp
        (algebraMap (FractionRing (Polynomial K))
          (Curves.RamificationAtInfinity.LinfAt (k := K) f)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial K)) ?_
    refine Polynomial.ringHom_ext ?_ ?_
    · -- Reduce `C a` via the `e₁.toRingEquiv.toRingHom` coe (not `e₁`) so `AlgEquiv.commutes`
      -- applies without needing `IsScalarTower K ↥K⟮f⁻¹⟯ K(E)` synthesis.
      intro a
      have hCa : algebraMap (Polynomial K) (FractionRing (Polynomial K)) (Polynomial.C a)
          = algebraMap K (FractionRing (Polynomial K)) a := by
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      have h1 : e₁.toRingEquiv.toRingHom (algebraMap K (FractionRing (Polynomial K)) a)
          = algebraMap K ↥(IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField)) a :=
        e₁.commutes a
      have hLHS : (algebraMap
            ↥(IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField))
            W.toAffine.FunctionField)
          (e₁.toRingEquiv.toRingHom (algebraMap K (FractionRing (Polynomial K)) a))
          = algebraMap K W.toAffine.FunctionField a := by
        rw [h1]; rfl
      have hRHS : e₂.toRingHom ((algebraMap (FractionRing (Polynomial K))
          (Curves.RamificationAtInfinity.LinfAt (k := K) f))
          (algebraMap K (FractionRing (Polynomial K)) a))
          = algebraMap K W.toAffine.FunctionField a := by
        rw [(IsScalarTower.algebraMap_apply K (FractionRing (Polynomial K))
          (Curves.RamificationAtInfinity.LinfAt (k := K) f) a).symm]
        rfl
      simp only [RingHom.comp_apply, hCa]
      exact hLHS.trans hRHS.symm
    · simp only [RingHom.comp_apply]
      have h_symm_X : (RatFunc.toFractionRingAlgEquiv K K).symm
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)
          = (RatFunc.X : RatFunc K) := by
        have h_e3_X : RatFunc.toFractionRingAlgEquiv K K (RatFunc.X : RatFunc K) =
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X := by
          change (RatFunc.toFractionRingAlgEquiv K K) RatFunc.X = _
          simp only [RatFunc.toFractionRingAlgEquiv_apply]
          change ((algebraMap (Polynomial K) (RatFunc K)) Polynomial.X).toFractionRing = _
          rw [← RatFunc.ofFractionRing_algebraMap (K := K)]
        rw [← h_e3_X, AlgEquiv.symm_apply_apply]
      have hL : ((algebraMap
            ↥(IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField))
            W.toAffine.FunctionField)
          (e₁.toRingEquiv.toRingHom
            (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X))) = f⁻¹ := by
        change (((RatFunc.toFractionRingAlgEquiv K K).symm.trans
            (RatFunc.algEquivOfTranscendental (K := K) f⁻¹ h_f_inv))
            (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)).val = f⁻¹
        rw [AlgEquiv.trans_apply, h_symm_X, RatFunc.algEquivOfTranscendental_X]
      have hR : e₂.toRingHom
          ((algebraMap (FractionRing (Polynomial K))
            (Curves.RamificationAtInfinity.LinfAt (k := K) f))
            (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)) = f⁻¹ := by
        change ((algebraMap (FractionRing (Polynomial K))
            (Curves.RamificationAtInfinity.LinfAt (k := K) f))
            (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X) :
              W.toAffine.FunctionField) = f⁻¹
        rw [Curves.RamificationAtInfinity.LinfAt.algebraMap_fractionRing_apply,
          Curves.RamificationAtInfinity.ratFunToFieldOfInv,
          IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
        exact Curves.RamificationAtInfinity.polyToFieldOfInv_X f
      exact hL.trans hR.symm
  exact (Algebra.finrank_eq_of_equiv_equiv e₁.toRingEquiv e₂ hc).symm

/-- **`Algebra.IsSeparable` transfer to the `LinfAt` structure**: given separability of
`K(E)` over `K⟮f⟯` (the `IntermediateField.adjoin` form), `K(E)` is separable over
`FractionRing K[X]` in its `LinfAt f` framing, for `f = γ.pullback x_gen`. -/
theorem K_E_separable_of_KofF_separable
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K)
    [hf : Fact (Transcendental K
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)]
    (h_KofF_sep : @Algebra.IsSeparable
      ↥(IntermediateField.adjoin K
        ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
          Set W.toAffine.FunctionField))
      W.toAffine.FunctionField _ _
      (Subalgebra.toAlgebra
        (IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField)).toSubalgebra)) :
    @Algebra.IsSeparable (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) := by
  set f : W.toAffine.FunctionField :=
    (isogOneSub_negFrobenius W hq).pullback (x_gen W) with hf_def
  have h_inv : Transcendental K f⁻¹ := hf.out
  have h_adj_eq :
      IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField) =
      IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h1 : f⁻¹ ∈ IntermediateField.adjoin K ({f⁻¹} : Set _) :=
        IntermediateField.mem_adjoin_simple_self K f⁻¹
      have h2 : (f⁻¹)⁻¹ ∈ IntermediateField.adjoin K ({f⁻¹} : Set _) := inv_mem h1
      rwa [inv_inv] at h2
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K f)
  let e1 : (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)) ≃ₐ[K]
           IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField) :=
    IntermediateField.equivOfEq h_adj_eq
  let e2 : (IntermediateField.adjoin K ({f⁻¹} : Set W.toAffine.FunctionField)) ≃ₐ[K]
           RatFunc K :=
    (RatFunc.algEquivOfTranscendental (K := K) f⁻¹ h_inv).symm
  let e3 : RatFunc K ≃ₐ[K] FractionRing (Polynomial K) :=
    RatFunc.toFractionRingAlgEquiv K K
  let e : (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)) ≃ₐ[K]
          FractionRing (Polynomial K) := (e1.trans e2).trans e3
  -- to bypass IntermediateField.toAlgebra instance-synthesis quirks.
  have h_KofF_sep' := h_KofF_sep
  refine @Algebra.IsSeparable.of_equiv_equiv
    (↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)))
    W.toAffine.FunctionField
    (FractionRing (Polynomial K))
    (Curves.RamificationAtInfinity.LinfAt (k := K) f)
    _ _ _ _
    (Subalgebra.toAlgebra
      (IntermediateField.adjoin K
        ({f} : Set W.toAffine.FunctionField)).toSubalgebra)
    (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing (k := K) f)
    e.toRingEquiv
    (RingEquiv.refl W.toAffine.FunctionField)
    ?_ h_KofF_sep'
  apply RingHom.ext
  intro y
  let algMapAlg :
      FractionRing (Polynomial K) →ₐ[K]
        Curves.RamificationAtInfinity.LinfAt (k := K) f :=
    IsScalarTower.toAlgHom K (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K) f)
  let inclSymm : FractionRing (Polynomial K) →ₐ[K] W.toAffine.FunctionField :=
    ((IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)).val).comp
      e.symm.toAlgHom
  have h_alg_eq : (algMapAlg : FractionRing (Polynomial K) →ₐ[K]
      W.toAffine.FunctionField) = inclSymm := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    change algMapAlg (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X) =
        inclSymm (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)
    have h_LHS : algMapAlg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X) = f⁻¹ := by
      change algebraMap (FractionRing (Polynomial K))
          (Curves.RamificationAtInfinity.LinfAt (k := K) f)
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X) = f⁻¹
      rw [← IsScalarTower.algebraMap_apply (Polynomial K) (FractionRing (Polynomial K))
            (Curves.RamificationAtInfinity.LinfAt (k := K) f)]
      rw [Curves.RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply,
          Curves.RamificationAtInfinity.polyToFieldOfInv_X]
    have h_RHS : inclSymm (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X) = f⁻¹ := by
      change (e.symm (algebraMap (Polynomial K) (FractionRing (Polynomial K))
          Polynomial.X)).val = f⁻¹
      change (((e1.trans e2).trans e3).symm
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)).val =
        f⁻¹
      rw [AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply]
      have h_e3_symm_X : (e3.symm
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)) =
          RatFunc.X := by
        have h_e3_X : e3 (RatFunc.X) =
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X := by
          change (RatFunc.toFractionRingAlgEquiv K K) RatFunc.X = _
          simp only [RatFunc.toFractionRingAlgEquiv_apply]
          change ((algebraMap (Polynomial K) (RatFunc K)) Polynomial.X).toFractionRing = _
          rw [← RatFunc.ofFractionRing_algebraMap (K := K)]
        rw [← h_e3_X, AlgEquiv.symm_apply_apply]
      rw [h_e3_symm_X]
      change (e1.symm ((RatFunc.algEquivOfTranscendental (K := K) f⁻¹ h_inv) RatFunc.X)).val =
        f⁻¹
      have h_e1_symm_val : ∀ x : IntermediateField.adjoin K ({f⁻¹} :
            Set W.toAffine.FunctionField),
          (e1.symm x).val = x.val := fun x => rfl
      rw [h_e1_symm_val]
      exact RatFunc.algEquivOfTranscendental_X f⁻¹ h_inv
    rw [h_LHS, h_RHS]
  have h := DFunLike.congr_fun h_alg_eq (e y)
  change (algebraMap (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K) f)) (e.toRingEquiv y) = y.val
  calc (algebraMap (FractionRing (Polynomial K))
            (Curves.RamificationAtInfinity.LinfAt (k := K) f)) (e.toRingEquiv y)
      = algMapAlg (e y) := rfl
    _ = inclSymm (e y) := h
    _ = (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)).val
        (e.symm (e y)) := rfl
    _ = (IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)).val y := by
        rw [AlgEquiv.symm_apply_apply]
    _ = y.val := rfl

/-- Builds `Algebra.IsSeparable (FractionRing K[X]) (LinfAt f)` for
`f = γ.pullback x_gen` unconditionally (no witness hypothesis at the top)
via tower argument K⟮f⟯ ⊆ γ.pullback.fieldRange ⊆ K(E). -/
theorem K_E_separable_over_LinfAt_gamma_pullback_x_gen
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 2 ≤ Fintype.card K)
    [hf : Fact (Transcendental K
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)] :
    @Algebra.IsSeparable (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) := by
  set γ := isogOneSub_negFrobenius W hq with hγ_def
  set f : W.toAffine.FunctionField := γ.pullback (x_gen W) with hf_def
  have h_inv : Transcendental K f⁻¹ := hf.out
  have h_f : Transcendental K f := fun h_alg =>
    h_inv ((IsAlgebraic.inv_iff (R := K) (x := f)).mpr h_alg)
  have h_pc_sep : γ.IsSeparable := isogOneSub_negFrobenius_isSeparable W p hq
  have h_le :
      IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField) ≤
        γ.pullback.fieldRange := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact ⟨x_gen W, rfl⟩
  have h_KofF_sep :
      @Algebra.IsSeparable
        ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
        W.toAffine.FunctionField _ _
        (Subalgebra.toAlgebra
          (IntermediateField.adjoin K
            ({f} : Set W.toAffine.FunctionField)).toSubalgebra) := by
    let gammaBar : W.toAffine.FunctionField ≃ₐ[K]
        ↥γ.pullback.fieldRange :=
      AlgEquiv.ofInjectiveField γ.pullback
    haveI h_KE_γ : @Algebra.IsSeparable W.toAffine.FunctionField W.toAffine.FunctionField
        _ _ γ.toAlgebra := h_pc_sep
    haveI h_proj :
        Algebra.IsSeparable (FractionRing (Polynomial K)) W.toAffine.FunctionField :=
      functionField_isSeparable W.toAffine
    have h_upper :
        @Algebra.IsSeparable
          (↥γ.pullback.fieldRange) W.toAffine.FunctionField
          _ _ γ.pullback.fieldRange.toAlgebra := by
      refine @Algebra.IsSeparable.of_equiv_equiv
        W.toAffine.FunctionField W.toAffine.FunctionField
        (↥γ.pullback.fieldRange) W.toAffine.FunctionField
        _ _ _ _
        γ.toAlgebra
        γ.pullback.fieldRange.toAlgebra
        gammaBar.toRingEquiv
        (RingEquiv.refl W.toAffine.FunctionField)
        ?_ h_KE_γ
      apply RingHom.ext
      intro y
      change ((gammaBar y) : W.toAffine.FunctionField) = γ.pullback y
      rfl
    let e_f : FractionRing (Polynomial K) ≃ₐ[K]
              ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)) :=
      (RatFunc.toFractionRingAlgEquiv K K).symm.trans
        (RatFunc.algEquivOfTranscendental (K := K) f h_f)
    have h_lower :
        @Algebra.IsSeparable
          ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
          ↥γ.pullback.fieldRange _ _
          (IntermediateField.inclusion h_le).toRingHom.toAlgebra := by
      refine @Algebra.IsSeparable.of_equiv_equiv
        (FractionRing (Polynomial K)) W.toAffine.FunctionField
        ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
        ↥γ.pullback.fieldRange
        _ _ _ _
        _
        (IntermediateField.inclusion h_le).toRingHom.toAlgebra
        e_f.toRingEquiv
        gammaBar.toRingEquiv
        ?_ h_proj
      apply RingHom.ext
      intro r
      let lhs_alg : FractionRing (Polynomial K) →ₐ[K] ↥γ.pullback.fieldRange :=
        (IntermediateField.inclusion h_le).comp e_f.toAlgHom
      let rhs_alg : FractionRing (Polynomial K) →ₐ[K] ↥γ.pullback.fieldRange :=
        gammaBar.toAlgHom.comp
          (IsScalarTower.toAlgHom K (FractionRing (Polynomial K))
            W.toAffine.FunctionField)
      have h_eq : lhs_alg = rhs_alg := by
        apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
        apply Polynomial.algHom_ext
        apply Subtype.ext
        change ((lhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
            Polynomial.X)) : W.toAffine.FunctionField) =
          ((rhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
            Polynomial.X)) : W.toAffine.FunctionField)
        have h_LHS :
            ((lhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
              Polynomial.X)) : W.toAffine.FunctionField) = f := by
          change ((IntermediateField.inclusion h_le)
              (e_f (algebraMap (Polynomial K) (FractionRing (Polynomial K))
                Polynomial.X)) : W.toAffine.FunctionField) = f
          rw [IntermediateField.coe_inclusion]
          change (((RatFunc.toFractionRingAlgEquiv K K).symm.trans
              (RatFunc.algEquivOfTranscendental (K := K) f h_f))
              (algebraMap (Polynomial K) (FractionRing (Polynomial K))
                Polynomial.X)).val = f
          rw [AlgEquiv.trans_apply]
          have h_e3_symm_X :
              (RatFunc.toFractionRingAlgEquiv K K).symm
                (algebraMap (Polynomial K) (FractionRing (Polynomial K))
                  Polynomial.X) = (RatFunc.X : RatFunc K) := by
            have h_e3_X :
                RatFunc.toFractionRingAlgEquiv K K (RatFunc.X : RatFunc K) =
                algebraMap (Polynomial K) (FractionRing (Polynomial K))
                  Polynomial.X := by
              change (RatFunc.toFractionRingAlgEquiv K K) RatFunc.X = _
              simp only [RatFunc.toFractionRingAlgEquiv_apply]
              change ((algebraMap (Polynomial K) (RatFunc K)) Polynomial.X).toFractionRing = _
              rw [← RatFunc.ofFractionRing_algebraMap (K := K)]
            rw [← h_e3_X, AlgEquiv.symm_apply_apply]
          rw [h_e3_symm_X]
          change ((RatFunc.algEquivOfTranscendental (K := K) f h_f)
              (RatFunc.X : RatFunc K)).val = f
          rw [RatFunc.algEquivOfTranscendental_X]
        have h_RHS :
            ((rhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
              Polynomial.X)) : W.toAffine.FunctionField) = f := by
          change ((gammaBar (algebraMap (FractionRing (Polynomial K))
              W.toAffine.FunctionField
              (algebraMap (Polynomial K) (FractionRing (Polynomial K))
                Polynomial.X))) : W.toAffine.FunctionField) = f
          rw [← IsScalarTower.algebraMap_apply (Polynomial K)
            (FractionRing (Polynomial K)) W.toAffine.FunctionField]
          change ((gammaBar (x_gen W)) : W.toAffine.FunctionField) = f
          rfl
        rw [h_LHS, h_RHS]
      exact DFunLike.congr_fun h_eq r
    have h_tower : @IsScalarTower
        ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
        (↥γ.pullback.fieldRange) W.toAffine.FunctionField
        (IntermediateField.inclusion h_le).toRingHom.toAlgebra.toSMul
        γ.pullback.fieldRange.toAlgebra.toSMul
        (Subalgebra.toAlgebra
          (IntermediateField.adjoin K
            ({f} : Set W.toAffine.FunctionField)).toSubalgebra).toSMul := by
      refine @IsScalarTower.of_algebraMap_eq
        ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
        (↥γ.pullback.fieldRange) W.toAffine.FunctionField _ _ _
        (IntermediateField.inclusion h_le).toRingHom.toAlgebra
        γ.pullback.fieldRange.toAlgebra _ ?_
      intro x
      rfl
    exact @Algebra.IsSeparable.trans
      ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
      (↥γ.pullback.fieldRange) _ _
      (IntermediateField.inclusion h_le).toRingHom.toAlgebra
      W.toAffine.FunctionField _
      (Subalgebra.toAlgebra
        (IntermediateField.adjoin K
          ({f} : Set W.toAffine.FunctionField)).toSubalgebra)
      γ.pullback.fieldRange.toAlgebra
      h_tower h_lower h_upper
  exact K_E_separable_of_KofF_separable W hq h_KofF_sep

/-- **Weighted pole degree of `γ.pullback x_gen` is `2 · pointCount`** (Tier-2.5
milestone #2): given uniform pole order `-2`, inertia degree `1`, and support
cardinality `pointCount` over `primesOverFinset xIdeal`, the weighted sum
`∑ (-ord_P).toNat · inertiaDeg` equals `2 · pointCount`. -/
theorem weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K) (data : Curves.RamificationAtInfinity.Sinf (k := K)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    (h_uniform_pole_order :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        data.ordAt P = -2)
    (h_inertia_one :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        Ideal.inertiaDeg
          (Curves.RamificationAtInfinity.xIdeal (k := K)) P = 1)
    (h_card :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      (primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier).card =
      pointCount W.toAffine) :
    letI := data.commRing
    letI := data.isDedekindDomain
    letI := data.algPoly
    ∑ P ∈ primesOverFinset
      (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      (-(data.ordAt P)).toNat *
        Ideal.inertiaDeg
          (Curves.RamificationAtInfinity.xIdeal (k := K)) P =
    2 * pointCount W.toAffine := by
  letI := data.commRing
  letI := data.isDedekindDomain
  letI := data.algPoly
  have h_sum_eq :
      ∑ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        (-(data.ordAt P)).toNat *
          Ideal.inertiaDeg
            (Curves.RamificationAtInfinity.xIdeal (k := K)) P =
      ∑ _P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro P hP
    rw [h_uniform_pole_order P hP, h_inertia_one P hP]
    decide
  rw [h_sum_eq, Finset.sum_const, smul_eq_mul, h_card]
  ring

/-- **Bridge B**: the abstract `primesOverFinset xIdeal` weighted sum
`∑ (-data.ordAt P).toNat · inertiaDeg xIdeal P` equals the project's
`projectiveDivisorOf`-support weighted sum, for `f = γ.pullback x_gen`. Both encode
the pole degree `2 · pointCount` of `f`, under their respective witness chains. -/
theorem bridgeB_weightedPoleDegree_eq_projectiveDivisorOf_sum
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K) (data : Curves.RamificationAtInfinity.Sinf (k := K)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    (h_uniform_pole_order :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        data.ordAt P = -2)
    (h_inertia_one :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        Ideal.inertiaDeg
          (Curves.RamificationAtInfinity.xIdeal (k := K)) P = 1)
    (h_card :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      (primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier).card =
      pointCount W.toAffine)
    (h_pole_orders :
      ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P).toNat = 0 ∧
      (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat = 2)
    (h_support_card :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.card =
      pointCount W.toAffine) :
    letI := data.commRing
    letI := data.isDedekindDomain
    letI := data.algPoly
    (∑ P ∈ primesOverFinset
      (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      (-(data.ordAt P)).toNat *
        Ideal.inertiaDeg
          (Curves.RamificationAtInfinity.xIdeal (k := K)) P) =
    ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
      (fun P => (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) := by
  rw [weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount
        W hq data h_uniform_pole_order h_inertia_one h_card,
      ← lemma5_of_pole_orders_and_support_card W hq h_pole_orders h_support_card]

/-- **Declaration 2 final-form** (consumer-facing): `[K(E) : K⟮f⟯]` (in
`IntermediateField.adjoin` form) equals the `projectiveDivisorOf`-support pole sum,
for `f = γ.pullback x_gen`. Composes Bridge A, the `LinfAt`-form weighted-pole-degree
identity, and Bridge B. -/
theorem finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    [hf : Fact (Transcendental K
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)]
    (hMF : @Module.Finite (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    (h_uniform_pole_order :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        data.ordAt P = -2)
    (h_inertia_one :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        Ideal.inertiaDeg
          (Curves.RamificationAtInfinity.xIdeal (k := K)) P = 1)
    (h_card :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      (primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier).card =
      pointCount W.toAffine)
    (h_pole_orders :
      ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P).toNat = 0 ∧
      (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat = 2)
    (h_support_card :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.card =
      pointCount W.toAffine) :
    Module.finrank
        (IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
        W.toAffine.FunctionField =
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
        (fun P => (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) := by
  rw [bridgeA_intermediateField_adjoin_eq_fractionRing_finrank W hq]
  rw [finrank_gamma_pullback_x_eq_weightedPoleDegree W hq hMF data]
  exact bridgeB_weightedPoleDegree_eq_projectiveDivisorOf_sum
    W hq data h_uniform_pole_order h_inertia_one h_card h_pole_orders h_support_card

end Conditional

end HasseWeil
