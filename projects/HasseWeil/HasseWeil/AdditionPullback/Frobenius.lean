/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback
import HasseWeil.Curves.WithTopArith
import HasseWeil.Frobenius
import HasseWeil.EC.GenericPointZsmul
import HasseWeil.EC.MulByIntBaseCase

/-!
# Frobenius-specialized addition-pullback ord-at-infinity computations

For `α = frobeniusIsog W` (the Frobenius endomorphism over a finite field
`K` with `q = #K ≥ 2`), we compute the order at infinity of the addition-
formula slope and related quantities. These are the building blocks for the
pole bound `ord_∞(addPullback_x W (frobeniusIsog W)) ≤ -2`, which closes
Sorry 1 of `HasseWeil/AdditionPullback.lean` for the case actually used by
HOLE D in the unconditional Hasse-Weil bound.

## Main lemmas

* `ordAtInfty_addSlope_frobenius`: `ord_∞(L) = -q` where `L = addSlope W π`.
* `ordAtInfty_addSlope_sq_frobenius`: `ord_∞(L²) = -2q`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, IV.1 (orders at infinity).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- For `q = #K ≥ 2`, `x_gen W ≠ (frobeniusIsog W).pullback (x_gen W)` as elements
of `K(E)`: their orders at infinity differ (`-2` vs `-2q`), so they cannot be
equal. -/
theorem x_gen_ne_frobeniusIsog_pullback_x_gen :
    x_gen W ≠ (frobeniusIsog W).pullback (x_gen W) := by
  intro h
  have h_ord_eq := congrArg (W_smooth W).ordAtInfty h
  rw [ordAtInfty_x_gen, ordAtInfty_frobeniusIsog_pullback_x_gen] at h_ord_eq
  have hq := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
  have h_int : ((-2 : ℤ) : WithTop ℤ) ≠ ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
    intro h_eq
    have : (-2 : ℤ) = -2 * (Fintype.card K : ℤ) := WithTop.coe_inj.mp h_eq
    have h_card_int : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact h_int h_ord_eq

/-- The slope formula at α = π: for the Frobenius `π = frobeniusIsog W`,
`addSlope W π = (y_gen - π·y) / (x_gen - π·x)`. Direct from
`Affine.slope_of_X_ne` since `x_gen ≠ π·x`. -/
theorem addSlope_frobenius_eq :
    addSlope W (frobeniusIsog W) =
      (y_gen W - (frobeniusIsog W).pullback (y_gen W)) /
      (x_gen W - (frobeniusIsog W).pullback (x_gen W)) := by
  unfold addSlope
  exact Affine.slope_of_X_ne (x_gen_ne_frobeniusIsog_pullback_x_gen W)

/-- `ord_∞(x_gen − π·x) = -2q` (sign-flipped form of the previously-shipped
`ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`). -/
theorem ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen :
    (W_smooth W).ordAtInfty (x_gen W - (frobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_eq : x_gen W - (frobeniusIsog W).pullback (x_gen W) =
      -((frobeniusIsog W).pullback (x_gen W) - x_gen W) := by ring
  rw [h_eq]
  exact ((W_smooth W).ordAtInfty_neg
    ((frobeniusIsog W).pullback (x_gen W) - x_gen W)).trans
    (ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen W)

/-- `ord_∞(y_gen − π·y) = -3q`. -/
theorem ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen :
    (W_smooth W).ordAtInfty (y_gen W - (frobeniusIsog W).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_eq : y_gen W - (frobeniusIsog W).pullback (y_gen W) =
      -((frobeniusIsog W).pullback (y_gen W) - y_gen W) := by ring
  rw [h_eq]
  exact ((W_smooth W).ordAtInfty_neg
    ((frobeniusIsog W).pullback (y_gen W) - y_gen W)).trans
    (ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen W)

/-- The denominator `x_gen − π·x` is nonzero (its ord is finite). -/
theorem x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero :
    x_gen W - (frobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      (x_gen W - (frobeniusIsog W).pullback (x_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen] at h_top
  exact WithTop.coe_ne_top h_top

/-- **`ord_∞(addSlope W π) = -q`** where `q = #K`. Direct from
`ordAtInfty_div_of_ord_eq` with the shipped sub-ord lemmas. -/
theorem ordAtInfty_addSlope_frobenius :
    (W_smooth W).ordAtInfty (addSlope W (frobeniusIsog W)) =
      ((-(Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [addSlope_frobenius_eq]
  have h_eq := (W_smooth W).ordAtInfty_div_of_ord_eq
    (x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W)
    (-3 * (Fintype.card K : ℤ)) (-2 * (Fintype.card K : ℤ))
    (ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen W)
    (ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen W)
  refine h_eq.trans ?_
  congr 1
  ring

/-- The slope is nonzero (its ord is finite). -/
theorem addSlope_frobenius_ne_zero :
    addSlope W (frobeniusIsog W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty (addSlope W (frobeniusIsog W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_addSlope_frobenius] at h_top
  exact WithTop.coe_ne_top h_top

/-- **`ord_∞(L²) = -2q`** where `L = addSlope W π`. -/
theorem ordAtInfty_addSlope_sq_frobenius :
    (W_smooth W).ordAtInfty (addSlope W (frobeniusIsog W) ^ 2) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  refine ((W_smooth W).ordAtInfty_pow_of_ord_eq (addSlope_frobenius_ne_zero W)
    (-(Fintype.card K : ℤ)) 2 (ordAtInfty_addSlope_frobenius W)).trans ?_
  congr 1
  push_cast
  ring

/-- **Witness-parametric Sorry 1 closure for the Frobenius case** (Path Y):
given a pole hypothesis on `addPullback_x W (frobeniusIsog W)`, derive False
from `addPullback_x = algebraMap K _ c`. -/
theorem addPullback_x_ne_const_frobenius_of_pole
    (hxy : AddNonInverse W (frobeniusIsog W))
    (h_pole :
      (W_smooth W).ordAtInfty (addPullback_x W (frobeniusIsog W)) < 0)
    (c : K) (hc : addPullback_x W (frobeniusIsog W) = algebraMap K KE c) :
    False :=
  addPullback_x_ne_const_of_pole hxy c h_pole hc

/-! ### Path X-prime: pole bound for q ≥ 3 with cancellation witness

`addPullback_x = L² + a₁L - a₂ - x_gen - π·x`. Regroup as
`(L² - π·x) + (a₁L - a₂ - x_gen)`. The right group has ord exactly `-q`
for `q ≥ 3, a₁ ≠ 0, a₂ ≠ 0` (chain strict non-arch). The left group has
the cancellation issue.

A clean structural witness rules out the only edge case where the basic
chain fails: `ord(L² - π·x) ≠ -q`. Then strict non-arch on the regrouped
sum gives `ord ≤ -2`. -/

/-- `ord_∞(a₁ · L) = -q` where `L = addSlope` (Frobenius), `a₁ ≠ 0`. -/
private lemma ordAtInfty_a1_mul_addSlope_frobenius (ha1 : W.toAffine.a₁ ≠ 0) :
    (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₁ * addSlope W (frobeniusIsog W)) =
      ((-(Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_a1_alg_ne : algebraMap K KE W.toAffine.a₁ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap K KE)]
    exact fun h ↦ ha1 (FaithfulSMul.algebraMap_injective _ _ h)
  have h_ord_a1 : (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁) = 0 :=
    ordAtInfty_algebraMap_F_nonzero W ha1
  have h_mul := (W_smooth W).ordAtInfty_mul h_a1_alg_ne (addSlope_frobenius_ne_zero W)
  rw [h_ord_a1, ordAtInfty_addSlope_frobenius] at h_mul
  refine h_mul.trans ?_
  show (0 : WithTop ℤ) + ((-(Fintype.card K : ℤ)) : WithTop ℤ) =
    ((-(Fintype.card K : ℤ)) : WithTop ℤ)
  rw [zero_add]

/-- `ord_∞(a₁L - a₂) = -q` (strict non-arch: `ord(a₁L) = -q < 0 = ord(a₂)`). -/
private lemma ordAtInfty_a1L_minus_a2_frobenius (ha1 : W.toAffine.a₁ ≠ 0)
    (ha2 : W.toAffine.a₂ ≠ 0) (hq : 1 < Fintype.card K) :
    (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₁ * addSlope W (frobeniusIsog W) -
          algebraMap K KE W.toAffine.a₂) =
      ((-(Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_neg_q_lt_0 : (-(Fintype.card K : ℤ)) < 0 := by
    have : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact (W_smooth W).ord_sub_lt_concrete (-(Fintype.card K : ℤ)) 0 h_neg_q_lt_0
    (ordAtInfty_a1_mul_addSlope_frobenius W ha1) (ordAtInfty_algebraMap_F_nonzero W ha2)

/-- `ord_∞(a₁L - a₂ - x_gen) = -q` for q ≥ 3, a₁ ≠ 0, a₂ ≠ 0. Chain of strict
non-archimedean: `ord(a₁L) = -q`, `ord(-a₂) = 0`, `ord(-x_gen) = -2`, with
`-q < -2 < 0` for q ≥ 3. -/
theorem ordAtInfty_a1L_minus_a2_minus_xgen_frobenius
    (hq : 3 ≤ Fintype.card K)
    (ha1 : W.toAffine.a₁ ≠ 0) (ha2 : W.toAffine.a₂ ≠ 0) :
    (W_smooth W).ordAtInfty
      (algebraMap K KE W.toAffine.a₁ * addSlope W (frobeniusIsog W) -
       algebraMap K KE W.toAffine.a₂ - x_gen W) =
      ((-(Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_ord_a1L_minus_a2 :=
    ordAtInfty_a1L_minus_a2_frobenius W ha1 ha2 (by omega : 1 < Fintype.card K)
  have h_q_ge_3 : (3 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_neg_q_lt_neg2 : (-(Fintype.card K : ℤ)) < (-2 : ℤ) := by linarith
  have h_ord_x_gen : (W_smooth W).ordAtInfty (x_gen W) =
      ((-2 : ℤ) : WithTop ℤ) := ordAtInfty_x_gen W
  exact (W_smooth W).ord_sub_lt_concrete (-(Fintype.card K : ℤ)) (-2) h_neg_q_lt_neg2
    h_ord_a1L_minus_a2 h_ord_x_gen

/-- **Strict non-archimedean pole bound**: if `ord B = -q` and `ord A ≠ -q`
(with `3 ≤ |K|`), then `ord(A + B) ≤ -2`. Either `ord A < -q` (so `ord(A+B) =
ord A < -q ≤ -2`) or `ord A > -q` (so `ord(A+B) = ord B = -q ≤ -2`). -/
private theorem ordAtInfty_add_le_neg_two {A B : KE} (hq : 3 ≤ Fintype.card K)
    (h_ord_B : (W_smooth W).ordAtInfty B = ((-(Fintype.card K : ℤ)) : WithTop ℤ))
    (h_witness : (W_smooth W).ordAtInfty A ≠ ((-(Fintype.card K : ℤ)) : WithTop ℤ)) :
    (W_smooth W).ordAtInfty (A + B) ≤ ((-2 : ℤ) : WithTop ℤ) := by
  rcases lt_or_gt_of_ne h_witness with h_A_lt | h_A_gt
  · have h_lt : (W_smooth W).ordAtInfty A < (W_smooth W).ordAtInfty B := by
      rw [h_ord_B]; exact h_A_lt
    have h_eq_A := (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
    have h_neg_q_le_neg2 : ((-(Fintype.card K : ℤ)) : WithTop ℤ) ≤
        ((-2 : ℤ) : WithTop ℤ) := by
      apply WithTop.coe_le_coe.mpr
      have : (3 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
      linarith
    exact h_eq_A.le.trans (h_A_lt.le.trans h_neg_q_le_neg2)
  · have h_lt : (W_smooth W).ordAtInfty B < (W_smooth W).ordAtInfty A := by
      rw [h_ord_B]; exact h_A_gt
    have h_BA_eq : (W_smooth W).ordAtInfty (B + A) = (W_smooth W).ordAtInfty B :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
    have h_AB_eq : (W_smooth W).ordAtInfty (A + B) = (W_smooth W).ordAtInfty B := by
      rw [show A + B = B + A from by ring]; exact h_BA_eq
    rw [h_AB_eq, h_ord_B]
    apply WithTop.coe_le_coe.mpr
    have : (3 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith

/-- **Pole bound for q ≥ 3 with cancellation witness** (Path X-prime,
**SUPERSEDED**): `ord_∞(addPullback_x W π) ≤ -2`, given the structural
witness `ord(L² - π·x) ≠ -q`.

**Status: SUPERSEDED.** The hypothesised witness is unprovable when
`a₁ ≠ 0`. Direct term-by-term ord arithmetic on the `(y - π·y)²
- π·x · (x - π·x)²` numerator shows that the term `-a₁·π·x·π·y` at
ord `-5q` is the unique smallest (when `a₁ ≠ 0`), forcing
`ord(L² - π·x) = -q` exactly. So `lt_or_gt_of_ne h_witness` cannot
be applied: the witness is false in the case it is supposed to discharge.

The replacement is the direct numerator-of-`addPullback_x` analysis
shipped below as `addPullbackNumerator_frobenius`, which sidesteps the
`L² - π·x` regrouping entirely. The lemmas immediately below are kept
for now to preserve a stable API in case downstream callers reference
them, but should not be used to close Sorry 1.

The witness-parametric form remains formally true (vacuously, since
the witness premise is unsatisfiable in the relevant case) but yields
no usable closure. -/
theorem addPullback_x_pole_frobenius_of_lc_witness
    (hq : 3 ≤ Fintype.card K)
    (ha1 : W.toAffine.a₁ ≠ 0) (ha2 : W.toAffine.a₂ ≠ 0)
    (h_witness :
      (W_smooth W).ordAtInfty
        (addSlope W (frobeniusIsog W) ^ 2 -
         (frobeniusIsog W).pullback (x_gen W)) ≠
      ((-(Fintype.card K : ℤ)) : WithTop ℤ)) :
    (W_smooth W).ordAtInfty (addPullback_x W (frobeniusIsog W)) ≤
      ((-2 : ℤ) : WithTop ℤ) := by
  set L := addSlope W (frobeniusIsog W) with hL_def
  set A : KE := L ^ 2 - (frobeniusIsog W).pullback (x_gen W) with hA_def
  set B : KE := algebraMap K KE W.toAffine.a₁ * L -
    algebraMap K KE W.toAffine.a₂ - x_gen W with hB_def
  -- Step 1: addPullback_x = A + B (algebraic identity).
  have h_eq : addPullback_x W (frobeniusIsog W) = A + B := by
    show (W_KE W).toAffine.addX (x_gen W)
      ((frobeniusIsog W).pullback (x_gen W)) L = A + B
    unfold WeierstrassCurve.Affine.addX
    show L ^ 2 + (W_KE W).toAffine.a₁ * L - (W_KE W).toAffine.a₂ -
      x_gen W - (frobeniusIsog W).pullback (x_gen W) = A + B
    have h_a1_lift : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
    have h_a2_lift : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
    rw [h_a1_lift, h_a2_lift]
    show L ^ 2 + algebraMap K KE W.toAffine.a₁ * L -
      algebraMap K KE W.toAffine.a₂ - x_gen W -
      (frobeniusIsog W).pullback (x_gen W) = A + B
    rw [hA_def, hB_def]; ring
  rw [h_eq]
  -- Step 2: ord(B) = -q.
  have h_ord_B : (W_smooth W).ordAtInfty B =
      ((-(Fintype.card K : ℤ)) : WithTop ℤ) :=
    ordAtInfty_a1L_minus_a2_minus_xgen_frobenius W hq ha1 ha2
  exact ordAtInfty_add_le_neg_two W hq h_ord_B h_witness

/-- **Sorry 1 closure for Frobenius case (q ≥ 3)** with leading-coefficient
witness. Composes the pole bound with `addPullback_x_ne_const_frobenius_of_pole`. -/
theorem addPullback_x_ne_const_frobenius_q_ge_3_of_witness
    (hq : 3 ≤ Fintype.card K)
    (ha1 : W.toAffine.a₁ ≠ 0) (ha2 : W.toAffine.a₂ ≠ 0)
    (h_witness :
      (W_smooth W).ordAtInfty
        (addSlope W (frobeniusIsog W) ^ 2 -
         (frobeniusIsog W).pullback (x_gen W)) ≠
      ((-(Fintype.card K : ℤ)) : WithTop ℤ))
    (hxy : AddNonInverse W (frobeniusIsog W)) (c : K)
    (hc : addPullback_x W (frobeniusIsog W) = algebraMap K KE c) : False := by
  have h_pole : (W_smooth W).ordAtInfty (addPullback_x W (frobeniusIsog W)) < 0 := by
    have h_le_neg_2 :=
      addPullback_x_pole_frobenius_of_lc_witness W hq ha1 ha2 h_witness
    refine lt_of_le_of_lt h_le_neg_2 ?_
    exact_mod_cast (by norm_num : (-2 : ℤ) < 0)
  exact addPullback_x_ne_const_frobenius_of_pole W hxy h_pole c hc

/-! ### Direct numerator approach (replaces the broken `_lc_witness` path)

The witness `ord(L² - π·x) ≠ -q` is unprovable because `ord(L² - π·x) = -q`
exactly when `a₁ ≠ 0` (the case of interest). Instead we work directly with
the numerator of `addPullback_x · (x - π·x)²`.

Multiplying the addition formula `addPullback_x = L² + a₁·L - a₂ - x_gen - π·x`
through by `(x - π·x)²` (using `L = (y - π·y)/(x - π·x)`) yields the polynomial-
shaped element

```
T₁ + T₂ - T₃
  with T₁ = (y_gen - π·y)²,
       T₂ = a₁ · (x_gen - π·x) · (y_gen - π·y),
       T₃ = (x_gen - π·x)² · (a₂ + x_gen + π·x).
```

The `ord_∞` values, for `q ≥ 2`:

| term | ord  |
|------|------|
| `T₁` | `-6q` |
| `T₂` | `-5q` (when `a₁ ≠ 0`) |
| `T₃` | `-6q` |

The leading-coefficient analysis at `-6q` (deferred to a follow-up session)
gives `lc(T₁) + lc(-T₃) = 2·c_x^{3q} ≠ 0` in characteristic `≠ 2`, hence
`ord(T₁ + T₂ - T₃) = -6q` and `ord(addPullback_x) = -6q + 4q = -2q < 0`.

These lemmas ship the term-ord half of the analysis. -/

/-- The denominator `y_gen − π·y` is nonzero (its ord is finite). -/
theorem y_gen_sub_frobeniusIsog_pullback_y_gen_ne_zero :
    y_gen W - (frobeniusIsog W).pullback (y_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      (y_gen W - (frobeniusIsog W).pullback (y_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen] at h_top
  exact WithTop.coe_ne_top h_top

/-- The numerator obtained by clearing the `(x − π·x)²` denominator from
`addPullback_x W π`. Concretely, `addPullbackNumerator_frobenius W = T₁ + T₂ - T₃`
where `T₁ = (y_gen − π·y)²`, `T₂ = a₁·(x_gen − π·x)·(y_gen − π·y)` and
`T₃ = (x_gen − π·x)²·(a₂ + x_gen + π·x)`.

By the identity `addPullbackNumerator_frobenius_eq`, this equals
`(x_gen − π·x)² · addPullback_x W (frobeniusIsog W)`. -/
noncomputable def addPullbackNumerator_frobenius : KE :=
  (y_gen W - (frobeniusIsog W).pullback (y_gen W)) ^ 2 +
    algebraMap K KE W.toAffine.a₁ *
      (x_gen W - (frobeniusIsog W).pullback (x_gen W)) *
      (y_gen W - (frobeniusIsog W).pullback (y_gen W)) -
    (x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2 *
      (algebraMap K KE W.toAffine.a₂ + x_gen W +
        (frobeniusIsog W).pullback (x_gen W))

/-- The defining identity:
`addPullbackNumerator_frobenius W = (x_gen − π·x)² · addPullback_x W π`.

Direct algebraic consequence of the slope formula
`L = (y_gen − π·y)/(x_gen − π·x)` and the addition formula
`addX = L² + a₁L − a₂ − x_gen − π·x`. -/
theorem addPullbackNumerator_frobenius_eq :
    addPullbackNumerator_frobenius W =
      (x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2 *
        addPullback_x W (frobeniusIsog W) := by
  set d := x_gen W - (frobeniusIsog W).pullback (x_gen W) with hd_def
  set n := y_gen W - (frobeniusIsog W).pullback (y_gen W) with hn_def
  have hd_ne : d ≠ 0 := x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W
  have hL : addSlope W (frobeniusIsog W) = n / d := addSlope_frobenius_eq W
  unfold addPullbackNumerator_frobenius addPullback_x
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ + x_gen W +
            (frobeniusIsog W).pullback (x_gen W)) =
      d ^ 2 * (W_KE W).toAffine.addX (x_gen W)
        ((frobeniusIsog W).pullback (x_gen W)) (addSlope W (frobeniusIsog W))
  unfold WeierstrassCurve.Affine.addX
  rw [hL]
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ + x_gen W +
            (frobeniusIsog W).pullback (x_gen W)) =
      d ^ 2 * ((n / d) ^ 2 + (W_KE W).toAffine.a₁ * (n / d) -
        (W_KE W).toAffine.a₂ - x_gen W - (frobeniusIsog W).pullback (x_gen W))
  have h_a1_lift : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2_lift : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  rw [h_a1_lift, h_a2_lift]
  field_simp
  ring

/-- **`ord_∞(T₁) = -6q`** where `T₁ = (y_gen − π·y)²` and `q = #K`.
Direct from `ordAtInfty_pow_of_ord_eq` applied to the shipped
`ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen`. -/
theorem ordAtInfty_T1_frobenius :
    (W_smooth W).ordAtInfty
      ((y_gen W - (frobeniusIsog W).pullback (y_gen W)) ^ 2) =
      ((-6 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  refine ((W_smooth W).ord_pow_concrete
    (y_gen_sub_frobeniusIsog_pullback_y_gen_ne_zero W)
    (-3 * (Fintype.card K : ℤ)) 2
    (ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen W)).trans ?_
  congr 1
  push_cast
  ring

/-- **`ord_∞(T₂) = -5q`** where `T₂ = a₁·(x_gen − π·x)·(y_gen − π·y)`
and `a₁ ≠ 0`. Multiplicativity of `ord_∞` plus the shipped sub-ord lemmas. -/
theorem ordAtInfty_T2_frobenius (ha₁ : W.toAffine.a₁ ≠ 0) :
    (W_smooth W).ordAtInfty
      (algebraMap K KE W.toAffine.a₁ *
        (x_gen W - (frobeniusIsog W).pullback (x_gen W)) *
        (y_gen W - (frobeniusIsog W).pullback (y_gen W))) =
      ((-5 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_a1_alg_ne : algebraMap K KE W.toAffine.a₁ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap K KE)]
    exact fun h ↦ ha₁ (FaithfulSMul.algebraMap_injective _ _ h)
  have h_x_ne : x_gen W - (frobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W
  have h_y_ne : y_gen W - (frobeniusIsog W).pullback (y_gen W) ≠ 0 :=
    y_gen_sub_frobeniusIsog_pullback_y_gen_ne_zero W
  -- Compute via congrArg₂-based term-level substitution to dodge `rw` matching
  -- glitches on dot-notation terms.
  have h_a1_eq : (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁) = 0 :=
    ordAtInfty_algebraMap_F_nonzero W ha₁
  have h_x_eq := ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen W
  have h_y_eq := ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen W
  have h_inner_eq :
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₁ *
          (x_gen W - (frobeniusIsog W).pullback (x_gen W))) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_mul h_a1_alg_ne h_x_ne).trans
      ((congrArg₂ (· + ·) h_a1_eq h_x_eq).trans (zero_add _))
  refine ((W_smooth W).ordAtInfty_mul (mul_ne_zero h_a1_alg_ne h_x_ne) h_y_ne).trans ?_
  refine (congrArg₂ (· + ·) h_inner_eq h_y_eq).trans ?_
  change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) +
         (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
         (((-5 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add]
  congr 1
  ring

/-- `ord_∞(a₂ + x_gen + π·x) = -2q` for `q ≥ 2`. The π·x term dominates
strictly: `ord(π·x) = -2q < ord(x_gen) = -2 < ord(a₂) ≤ 0`, so chained
strict non-arch picks the most negative. -/
theorem ordAtInfty_a2_plus_x_gen_plus_pi_x_frobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
      (algebraMap K KE W.toAffine.a₂ + x_gen W +
        (frobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_q_int : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  -- Step 1: ord(x_gen + π·x) = -2q (strict non-arch since -2q < -2).
  have h_neg_2q_lt_neg_2 : (-2 * (Fintype.card K : ℤ)) < (-2 : ℤ) := by linarith
  have h_ord_pi_x :
      (W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (x_gen W)) =
        ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) :=
    ordAtInfty_frobeniusIsog_pullback_x_gen W
  have h_ord_x_gen : (W_smooth W).ordAtInfty (x_gen W) =
      ((-2 : ℤ) : WithTop ℤ) := ordAtInfty_x_gen W
  -- Goal needs (a₂ + x_gen) + π·x rebracketed.
  have h_assoc : algebraMap K KE W.toAffine.a₂ + x_gen W +
      (frobeniusIsog W).pullback (x_gen W) =
      (frobeniusIsog W).pullback (x_gen W) +
      (algebraMap K KE W.toAffine.a₂ + x_gen W) := by ring
  rw [h_assoc]
  -- ord(a₂ + x_gen): by_cases on a₂.
  by_cases ha₂ : W.toAffine.a₂ = 0
  · -- a₂ = 0: ord(0 + x_gen) = -2.
    have h_simp : algebraMap K KE W.toAffine.a₂ + x_gen W = x_gen W := by
      rw [ha₂, map_zero, zero_add]
    rw [h_simp]
    exact (W_smooth W).ord_add_lt_concrete (-2 * (Fintype.card K : ℤ)) (-2)
      h_neg_2q_lt_neg_2 h_ord_pi_x h_ord_x_gen
  · -- a₂ ≠ 0: ord(a₂ + x_gen) = -2 (strict non-arch, 0 ≠ -2).
    have h_a2_alg_ne : algebraMap K KE W.toAffine.a₂ ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap K KE)]
      exact fun h ↦ ha₂ (FaithfulSMul.algebraMap_injective _ _ h)
    have h_ord_a2 :
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₂) = 0 :=
      ordAtInfty_algebraMap_F_nonzero W ha₂
    have h_neg_2_lt_0 : (-2 : ℤ) < 0 := by norm_num
    have h_ord_a2_plus_x_gen :
        (W_smooth W).ordAtInfty
          (algebraMap K KE W.toAffine.a₂ + x_gen W) =
          ((-2 : ℤ) : WithTop ℤ) := by
      have h_swap : algebraMap K KE W.toAffine.a₂ + x_gen W =
          x_gen W + algebraMap K KE W.toAffine.a₂ := by ring
      rw [h_swap]
      exact (W_smooth W).ord_add_lt_concrete (-2) 0 h_neg_2_lt_0
        h_ord_x_gen h_ord_a2
    exact (W_smooth W).ord_add_lt_concrete (-2 * (Fintype.card K : ℤ)) (-2)
      h_neg_2q_lt_neg_2 h_ord_pi_x h_ord_a2_plus_x_gen

/-- `a₂ + x_gen + π·x ≠ 0` (its `ord_∞` is `-2q ≠ ⊤`). -/
private lemma a2_plus_x_gen_plus_pi_x_frobenius_ne_zero (hq : 2 ≤ Fintype.card K) :
    algebraMap K KE W.toAffine.a₂ + x_gen W +
      (frobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      (algebraMap K KE W.toAffine.a₂ + x_gen W +
        (frobeniusIsog W).pullback (x_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_a2_plus_x_gen_plus_pi_x_frobenius W hq] at h_top
  exact WithTop.coe_ne_top h_top

/-- `ord_∞((x_gen − π·x)²) = 2·(−2q) = −4q`. -/
private lemma ordAtInfty_x_gen_sub_pi_x_sq_frobenius :
    (W_smooth W).ordAtInfty
        ((x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2) =
      ((((2 : ℤ) * (-2 * (Fintype.card K : ℤ))) : ℤ) : WithTop ℤ) :=
  (W_smooth W).ord_pow_concrete (x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W)
    (-2 * (Fintype.card K : ℤ)) 2
    (ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen W)

/-- **`ord_∞(T₃) = -6q`** where `T₃ = (x_gen − π·x)²·(a₂ + x_gen + π·x)`
and `q ≥ 2`. Multiplicativity plus `ordAtInfty_a2_plus_x_gen_plus_pi_x_frobenius`. -/
theorem ordAtInfty_T3_frobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
      ((x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2 *
        (algebraMap K KE W.toAffine.a₂ + x_gen W +
          (frobeniusIsog W).pullback (x_gen W))) =
      ((-6 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_x_sq_ne : (x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W)
  refine ((W_smooth W).ordAtInfty_mul h_x_sq_ne
    (a2_plus_x_gen_plus_pi_x_frobenius_ne_zero W hq)).trans ?_
  refine (congrArg₂ (· + ·) (ordAtInfty_x_gen_sub_pi_x_sq_frobenius W)
    (ordAtInfty_a2_plus_x_gen_plus_pi_x_frobenius W hq)).trans ?_
  change (((2 : ℤ) * (-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) +
         (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
         (((-6 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add]
  congr 1
  ring

/-! ### Weierstrass-reduced form of the numerator

The naive `T₁ + T₂ - T₃` form has `(y_gen - π·y)²` with order `-6q` and
`(x_gen - π·x)² · (a₂ + x_gen + π·x)` also with order `-6q`. After
substituting both Weierstrass equations (`y² = x³ + a₂x² + a₄x + a₆ -
a₁xy - a₃y` for both `(x_gen, y_gen)` and `(π·x, π·y)`), the dominant
`x³, X³, a₂(x²+X²)` terms cancel exactly with `T₃`'s expansion, leaving
a polynomial-shaped expression whose unique smallest-order term is
`x_gen · (π·x)²` at order `-2 - 4q`.

This reduction yields `ord_∞(addPullback_x) = -2` (independent of q!),
which immediately closes Sorry 1 for `q ≥ 3` in **any characteristic**
(the `x_gen · (π·x)²` term has coefficient `1`, never vanishing). -/

/-- The Weierstrass-reduced form of `addPullbackNumerator_frobenius`.

Concretely:
```
addPullbackNumerator_reduced =
   a₄·(x_gen + π·x) + 2·a₆
   - a₃·(y_gen + π·y) - 2·y_gen·π·y - a₁·(x_gen·π·y + π·x·y_gen)
   + x_gen²·π·x + x_gen·(π·x)² + 2·a₂·x_gen·π·x
```

The `x_gen·(π·x)²` term, with coefficient `1` (not `2`), is the unique
smallest-order term for `q ≥ 3`. -/
noncomputable def addPullbackNumerator_reduced_frobenius : KE :=
  algebraMap K KE W.toAffine.a₄ *
      (x_gen W + (frobeniusIsog W).pullback (x_gen W))
    + 2 * algebraMap K KE W.toAffine.a₆
    - algebraMap K KE W.toAffine.a₃ *
        (y_gen W + (frobeniusIsog W).pullback (y_gen W))
    - 2 * y_gen W * (frobeniusIsog W).pullback (y_gen W)
    - algebraMap K KE W.toAffine.a₁ *
        (x_gen W * (frobeniusIsog W).pullback (y_gen W) +
         (frobeniusIsog W).pullback (x_gen W) * y_gen W)
    + x_gen W ^ 2 * (frobeniusIsog W).pullback (x_gen W)
    + x_gen W * (frobeniusIsog W).pullback (x_gen W) ^ 2
    + 2 * algebraMap K KE W.toAffine.a₂ *
        x_gen W * (frobeniusIsog W).pullback (x_gen W)

/-- Weierstrass relation at the generic point `(x_gen, y_gen)`, in
`algebraMap K KE`-coefficient form. -/
private theorem weierstrass_relation_x_gen_y_gen :
    y_gen W ^ 2 +
        algebraMap K KE W.toAffine.a₁ * x_gen W * y_gen W +
        algebraMap K KE W.toAffine.a₃ * y_gen W -
        (x_gen W ^ 3 +
         algebraMap K KE W.toAffine.a₂ * x_gen W ^ 2 +
         algebraMap K KE W.toAffine.a₄ * x_gen W +
         algebraMap K KE W.toAffine.a₆) = 0 := by
  have h := generic_equation W
  rw [WeierstrassCurve.Affine.equation_iff'] at h
  have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  have h_a3 : (W_KE W).toAffine.a₃ = algebraMap K KE W.toAffine.a₃ := rfl
  have h_a4 : (W_KE W).toAffine.a₄ = algebraMap K KE W.toAffine.a₄ := rfl
  have h_a6 : (W_KE W).toAffine.a₆ = algebraMap K KE W.toAffine.a₆ := rfl
  rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h
  exact h

/-- Weierstrass relation at the Frobenius pullback `(π·x, π·y)`, in
`algebraMap K KE`-coefficient form (via `pullback_equation`). -/
private theorem weierstrass_relation_frobenius_pullback :
    (frobeniusIsog W).pullback (y_gen W) ^ 2 +
        algebraMap K KE W.toAffine.a₁ *
          (frobeniusIsog W).pullback (x_gen W) *
          (frobeniusIsog W).pullback (y_gen W) +
        algebraMap K KE W.toAffine.a₃ *
          (frobeniusIsog W).pullback (y_gen W) -
        ((frobeniusIsog W).pullback (x_gen W) ^ 3 +
         algebraMap K KE W.toAffine.a₂ *
           (frobeniusIsog W).pullback (x_gen W) ^ 2 +
         algebraMap K KE W.toAffine.a₄ *
           (frobeniusIsog W).pullback (x_gen W) +
         algebraMap K KE W.toAffine.a₆) = 0 := by
  have h := pullback_equation W (frobeniusIsog W)
  rw [WeierstrassCurve.Affine.equation_iff'] at h
  have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  have h_a3 : (W_KE W).toAffine.a₃ = algebraMap K KE W.toAffine.a₃ := rfl
  have h_a4 : (W_KE W).toAffine.a₄ = algebraMap K KE W.toAffine.a₄ := rfl
  have h_a6 : (W_KE W).toAffine.a₆ = algebraMap K KE W.toAffine.a₆ := rfl
  rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h
  exact h

/-- **The Weierstrass reduction**: `addPullbackNumerator_frobenius W =
addPullbackNumerator_reduced_frobenius W` in `K(E)`.

Proof: the difference between the two sides is
`h_y² + h_Y²`, where
* `h_y² := y_gen² + a₁·x_gen·y_gen + a₃·y_gen − (x_gen³ + a₂·x_gen² + a₄·x_gen + a₆) = 0`
  (Weierstrass for `(x_gen, y_gen)`),
* `h_Y² := (π·y)² + a₁·π·x·π·y + a₃·π·y − ((π·x)³ + a₂·(π·x)² + a₄·π·x + a₆) = 0`
  (Weierstrass for `(π·x, π·y)`, via `pullback_equation`).

`linear_combination` closes the identity given these two hypotheses. -/
theorem addPullbackNumerator_frobenius_eq_reduced :
    addPullbackNumerator_frobenius W =
      addPullbackNumerator_reduced_frobenius W := by
  have h_y_sq := weierstrass_relation_x_gen_y_gen W
  have h_Y_sq := weierstrass_relation_frobenius_pullback W
  unfold addPullbackNumerator_frobenius addPullbackNumerator_reduced_frobenius
  linear_combination h_y_sq + h_Y_sq

/-! ### `ord_∞` of the reduced numerator

For `q ≥ 2`, every term in `addPullbackNumerator_reduced_frobenius` other
than `x_gen · (π·x)²` has `ord_∞ ≥ -3 - 3q`. The dominant term has
`ord_∞ = -2 - 4q`. Since `-3 - 3q > -2 - 4q` for `q ≥ 2`, strict
non-archimedean additivity gives `ord(reduced) = -2 - 4q`. -/

/-- Helper: `ord(algebraMap c · f) ≥ ord(f)`. The `algebraMap K KE c`
factor never makes the order more negative — when `c = 0` the product
is zero (ord `⊤`), and when `c ≠ 0` the algebraMap value has ord 0. -/
private lemma ord_algebraMap_mul_ge {f : KE} (c : K) {n : WithTop ℤ}
    (hf : n ≤ (W_smooth W).ordAtInfty f) :
    n ≤ (W_smooth W).ordAtInfty (algebraMap K KE c * f) := by
  by_cases hc : c = 0
  · rw [hc, map_zero, zero_mul]
    exact (W_smooth W).ordAtInfty_zero.symm ▸ (le_top : n ≤ (⊤ : WithTop ℤ))
  by_cases hf_ne : f = 0
  · rw [hf_ne, mul_zero]
    exact (W_smooth W).ordAtInfty_zero.symm ▸ (le_top : n ≤ (⊤ : WithTop ℤ))
  have h_alg_ne : algebraMap K KE c ≠ 0 := fun h ↦
    hc (FaithfulSMul.algebraMap_injective K KE (h.trans (map_zero _).symm))
  calc n ≤ (W_smooth W).ordAtInfty f := hf
    _ = (W_smooth W).ordAtInfty (algebraMap K KE c) + (W_smooth W).ordAtInfty f := by
        rw [ordAtInfty_algebraMap_F_nonzero W hc, zero_add]
    _ = (W_smooth W).ordAtInfty (algebraMap K KE c * f) :=
        ((W_smooth W).ordAtInfty_mul h_alg_ne hf_ne).symm

/-- Helper: `ord(2 · f) ≥ ord(f)`. Uses the algebraic identity `2 · f = f + f`
to dodge the question of whether `(2 : KE)` is zero (char 2). -/
private lemma ord_two_mul_ge {f : KE} {n : WithTop ℤ}
    (hf : n ≤ (W_smooth W).ordAtInfty f) :
    n ≤ (W_smooth W).ordAtInfty ((2 : KE) * f) := by
  rw [show ((2 : KE) * f) = f + f from by ring]
  have h := (W_smooth W).ordAtInfty_add_ge_min f f
  rw [min_self] at h
  exact le_trans hf h

/-- For `q ≥ 2`, `ord(x_gen + π·x_gen) = -2q`. The `π·x` term dominates
strictly (`-2q < -2`). -/
private lemma ord_x_gen_add_pi_x_eq (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (x_gen W + (frobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_lt : (-2 * (Fintype.card K : ℤ)) < (-2 : ℤ) := by linarith
  have h_swap : x_gen W + (frobeniusIsog W).pullback (x_gen W) =
      (frobeniusIsog W).pullback (x_gen W) + x_gen W := by ring
  rw [h_swap]
  exact (W_smooth W).ord_add_lt_concrete (-2 * (Fintype.card K : ℤ)) (-2) h_lt
    (ordAtInfty_frobeniusIsog_pullback_x_gen W) (ordAtInfty_x_gen W)

/-- For `q ≥ 2`, `ord(y_gen + π·y_gen) = -3q`. -/
private lemma ord_y_gen_add_pi_y_eq (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (y_gen W + (frobeniusIsog W).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_lt : (-3 * (Fintype.card K : ℤ)) < (-3 : ℤ) := by linarith
  have h_swap : y_gen W + (frobeniusIsog W).pullback (y_gen W) =
      (frobeniusIsog W).pullback (y_gen W) + y_gen W := by ring
  rw [h_swap]
  exact (W_smooth W).ord_add_lt_concrete (-3 * (Fintype.card K : ℤ)) (-3) h_lt
    (ordAtInfty_frobeniusIsog_pullback_y_gen W) (ordAtInfty_y_gen W)

/-- `(frobeniusIsog W).pullback (x_gen W) ≠ 0`. -/
private lemma pi_x_gen_ne_zero : (frobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      ((frobeniusIsog W).pullback (x_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_frobeniusIsog_pullback_x_gen] at h_top
  exact WithTop.coe_ne_top h_top

/-- `(frobeniusIsog W).pullback (y_gen W) ≠ 0`. -/
private lemma pi_y_gen_ne_zero : (frobeniusIsog W).pullback (y_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      ((frobeniusIsog W).pullback (y_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_frobeniusIsog_pullback_y_gen] at h_top
  exact WithTop.coe_ne_top h_top

/-- `ord(x_gen · π·x_gen) = -2 - 2q`. -/
private lemma ord_x_gen_mul_pi_x_eq :
    (W_smooth W).ordAtInfty
        (x_gen W * (frobeniusIsog W).pullback (x_gen W)) =
      ((-2 - 2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  refine ((W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) (pi_x_gen_ne_zero W)).trans ?_
  refine (congrArg₂ (· + ·) (ordAtInfty_x_gen W)
    (ordAtInfty_frobeniusIsog_pullback_x_gen W)).trans ?_
  rfl

/-- `ord(x_gen² · π·x_gen) = -4 - 2q`. -/
private lemma ord_x_gen_sq_mul_pi_x_eq :
    (W_smooth W).ordAtInfty
        (x_gen W ^ 2 * (frobeniusIsog W).pullback (x_gen W)) =
      ((-4 - 2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_x_sq_ne : x_gen W ^ 2 ≠ 0 := pow_ne_zero 2 (x_gen_ne_zero W)
  have h_x_sq_eq : (W_smooth W).ordAtInfty (x_gen W ^ 2) =
      (((-4 : ℤ)) : WithTop ℤ) := by
    refine ((W_smooth W).ord_pow_concrete (x_gen_ne_zero W) (-2) 2
      (ordAtInfty_x_gen W)).trans ?_
    norm_num
  refine ((W_smooth W).ordAtInfty_mul h_x_sq_ne (pi_x_gen_ne_zero W)).trans ?_
  refine (congrArg₂ (· + ·) h_x_sq_eq
    (ordAtInfty_frobeniusIsog_pullback_x_gen W)).trans ?_
  rfl

/-- `ord(x_gen · (π·x_gen)²) = -2 - 4q`. The dominant term. -/
private lemma ord_x_gen_mul_pi_x_sq_eq :
    (W_smooth W).ordAtInfty
        (x_gen W * (frobeniusIsog W).pullback (x_gen W) ^ 2) =
      ((-2 - 4 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_pi_x_sq_ne : (frobeniusIsog W).pullback (x_gen W) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (pi_x_gen_ne_zero W)
  have h_pi_x_sq_eq : (W_smooth W).ordAtInfty
      ((frobeniusIsog W).pullback (x_gen W) ^ 2) =
      (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ord_pow_concrete (pi_x_gen_ne_zero W)
      (-2 * (Fintype.card K : ℤ)) 2
      (ordAtInfty_frobeniusIsog_pullback_x_gen W)).trans ?_
    congr 1
    push_cast
    ring
  refine ((W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_pi_x_sq_ne).trans ?_
  refine (congrArg₂ (· + ·) (ordAtInfty_x_gen W) h_pi_x_sq_eq).trans ?_
  rfl

/-- `ord(y_gen · π·y_gen) = -3 - 3q`. -/
private lemma ord_y_gen_mul_pi_y_eq :
    (W_smooth W).ordAtInfty
        (y_gen W * (frobeniusIsog W).pullback (y_gen W)) =
      ((-3 - 3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  refine ((W_smooth W).ordAtInfty_mul (y_gen_ne_zero W) (pi_y_gen_ne_zero W)).trans ?_
  refine (congrArg₂ (· + ·) (ordAtInfty_y_gen W)
    (ordAtInfty_frobeniusIsog_pullback_y_gen W)).trans ?_
  rfl

/-- For `q ≥ 2`, `ord(x_gen · π·y_gen + π·x_gen · y_gen) ≥ -2 - 3q`. The
two terms have orders `-2 - 3q` and `-3 - 2q` resp.; for `q ≥ 2`,
`-2 - 3q < -3 - 2q`, so the min is `-2 - 3q`. -/
private lemma ord_x_pi_y_plus_pi_x_y_ge (hq : 2 ≤ Fintype.card K) :
    (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (x_gen W * (frobeniusIsog W).pullback (y_gen W) +
         (frobeniusIsog W).pullback (x_gen W) * y_gen W) := by
  -- ord(x · π·y) = -2 + (-3q) = -2-3q.
  have h_x_pi_y :
      (W_smooth W).ordAtInfty (x_gen W * (frobeniusIsog W).pullback (y_gen W)) =
        (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) (pi_y_gen_ne_zero W)).trans ?_
    refine (congrArg₂ (· + ·) (ordAtInfty_x_gen W)
      (ordAtInfty_frobeniusIsog_pullback_y_gen W)).trans ?_
    rfl
  -- ord(π·x · y) = -2q + (-3) = -3-2q. Use mul_comm to put the integer
  -- term first, so the resulting `↑(-3) + ↑(-2*#K)` matches `↑(-3 - 2*#K)`
  -- by `Int.sub_eq_add_neg` defeq (the order matters for `rfl`).
  have h_pi_x_y :
      (W_smooth W).ordAtInfty
        ((frobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (((-3 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [mul_comm]
    refine ((W_smooth W).ordAtInfty_mul (y_gen_ne_zero W) (pi_x_gen_ne_zero W)).trans ?_
    refine (congrArg₂ (· + ·) (ordAtInfty_y_gen W)
      (ordAtInfty_frobeniusIsog_pullback_x_gen W)).trans ?_
    rfl
  -- ord(sum) ≥ min(ord(x·π·y), ord(π·x·y)) = ord(x·π·y) = -2-3q for q ≥ 2.
  have h_min_le := (W_smooth W).ordAtInfty_add_ge_min
    (x_gen W * (frobeniusIsog W).pullback (y_gen W))
    ((frobeniusIsog W).pullback (x_gen W) * y_gen W)
  rw [h_x_pi_y, h_pi_x_y] at h_min_le
  refine le_trans ?_ h_min_le
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_ineq : (-2 - 3 * (Fintype.card K : ℤ) : ℤ) ≤
      min (-2 - 3 * (Fintype.card K : ℤ)) (-3 - 2 * (Fintype.card K : ℤ)) := by
    apply le_min (le_refl _)
    linarith
  exact_mod_cast h_ineq

/-- Helper: `ord(f + g) ≥ n` when both have ord `≥ n`. Direct from
`ordAtInfty_add_ge_min`. -/
private lemma ord_add_ge_of_both_ge {f g : KE} {n : WithTop ℤ}
    (hf : n ≤ (W_smooth W).ordAtInfty f) (hg : n ≤ (W_smooth W).ordAtInfty g) :
    n ≤ (W_smooth W).ordAtInfty (f + g) :=
  (le_min hf hg).trans ((W_smooth W).ordAtInfty_add_ge_min f g)

/-- Helper: `ord(-f) ≥ n` iff `ord(f) ≥ n` (by `ordAtInfty_neg`). -/
private lemma ord_neg_ge {f : KE} {n : WithTop ℤ}
    (hf : n ≤ (W_smooth W).ordAtInfty f) :
    n ≤ (W_smooth W).ordAtInfty (-f) :=
  ((W_smooth W).ordAtInfty_neg f).symm ▸ hf

/-- Helper: `ord(f - g) ≥ n` when both have ord `≥ n`. -/
private lemma ord_sub_ge_of_both_ge {f g : KE} {n : WithTop ℤ}
    (hf : n ≤ (W_smooth W).ordAtInfty f) (hg : n ≤ (W_smooth W).ordAtInfty g) :
    n ≤ (W_smooth W).ordAtInfty (f - g) := by
  rw [sub_eq_add_neg]
  exact ord_add_ge_of_both_ge W hf (ord_neg_ge W hg)

/-- Helper: `ord_∞(a₄ · (x_gen + π·x)) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_a4_mul_x_add_pi_x_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₄ *
          (x_gen W + (frobeniusIsog W).pullback (x_gen W))) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -2 * (Fintype.card K : ℤ) := by linarith
  refine ord_algebraMap_mul_ge W W.toAffine.a₄ ?_
  rw [ord_x_gen_add_pi_x_eq W hq]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(2 · a₆) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_two_mul_a6_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty ((2 : KE) * algebraMap K KE W.toAffine.a₆) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ (0 : ℤ) := by linarith
  refine ord_two_mul_ge W ?_
  by_cases ha₆ : W.toAffine.a₆ = 0
  · rw [ha₆, map_zero]
    exact (W_smooth W).ordAtInfty_zero.symm ▸
      (le_top : (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤ ⊤)
  · rw [ordAtInfty_algebraMap_F_nonzero W ha₆]
    exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(a₃ · (y_gen + π·y)) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_a3_mul_y_add_pi_y_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₃ *
          (y_gen W + (frobeniusIsog W).pullback (y_gen W))) := by
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -3 * (Fintype.card K : ℤ) := by linarith
  refine ord_algebraMap_mul_ge W W.toAffine.a₃ ?_
  rw [ord_y_gen_add_pi_y_eq W hq]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(2 · y_gen · π·y) ≥ -3 - 3q`. -/
private lemma ord_two_mul_y_mul_pi_y_ge :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((2 : KE) * y_gen W * (frobeniusIsog W).pullback (y_gen W)) := by
  rw [show (2 : KE) * y_gen W * (frobeniusIsog W).pullback (y_gen W) =
      (2 : KE) * (y_gen W * (frobeniusIsog W).pullback (y_gen W)) from by ring]
  refine ord_two_mul_ge W ?_
  rw [ord_y_gen_mul_pi_y_eq W]
  exact le_refl _

/-- Helper: `ord_∞(a₁ · (x_gen · π·y + π·x · y_gen)) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_a1_mul_cross_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₁ *
          (x_gen W * (frobeniusIsog W).pullback (y_gen W) +
           (frobeniusIsog W).pullback (x_gen W) * y_gen W)) := by
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -2 - 3 * (Fintype.card K : ℤ) := by linarith
  refine ord_algebraMap_mul_ge W W.toAffine.a₁ ?_
  refine le_trans ?_ (ord_x_pi_y_plus_pi_x_y_ge W hq)
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(x_gen² · π·x) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_x_sq_mul_pi_x_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (x_gen W ^ 2 * (frobeniusIsog W).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -4 - 2 * (Fintype.card K : ℤ) := by linarith
  rw [ord_x_gen_sq_mul_pi_x_eq W]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(2 · a₂ · x_gen · π·x) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_two_mul_a2_mul_x_mul_pi_x_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((2 : KE) * algebraMap K KE W.toAffine.a₂ * x_gen W *
          (frobeniusIsog W).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -2 - 2 * (Fintype.card K : ℤ) := by linarith
  rw [show (2 : KE) * algebraMap K KE W.toAffine.a₂ * x_gen W *
      (frobeniusIsog W).pullback (x_gen W) =
      (2 : KE) * (algebraMap K KE W.toAffine.a₂ *
        (x_gen W * (frobeniusIsog W).pullback (x_gen W))) from by ring]
  refine ord_two_mul_ge W ?_
  refine ord_algebraMap_mul_ge W W.toAffine.a₂ ?_
  rw [ord_x_gen_mul_pi_x_eq W]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: the six non-dominant "rest" terms of the reduced numerator together
have `ord_∞ ≥ -3 - 3q` for `q ≥ 2` (chains the seven term bounds). -/
private lemma ord_addPullbackNumerator_reduced_rest_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (
        algebraMap K KE W.toAffine.a₄ *
            (x_gen W + (frobeniusIsog W).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (y_gen W + (frobeniusIsog W).pullback (y_gen W))
          - (2 : KE) * y_gen W * (frobeniusIsog W).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (x_gen W * (frobeniusIsog W).pullback (y_gen W) +
               (frobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (frobeniusIsog W).pullback (x_gen W)
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              x_gen W * (frobeniusIsog W).pullback (x_gen W)) := by
  have h12 := ord_add_ge_of_both_ge W (ord_a4_mul_x_add_pi_x_ge W hq) (ord_two_mul_a6_ge W hq)
  have h123 := ord_sub_ge_of_both_ge W h12 (ord_a3_mul_y_add_pi_y_ge W hq)
  have h1234 := ord_sub_ge_of_both_ge W h123 (ord_two_mul_y_mul_pi_y_ge W)
  have h12345 := ord_sub_ge_of_both_ge W h1234 (ord_a1_mul_cross_ge W hq)
  have h123456 := ord_add_ge_of_both_ge W h12345 (ord_x_sq_mul_pi_x_ge W hq)
  exact ord_add_ge_of_both_ge W h123456 (ord_two_mul_a2_mul_x_mul_pi_x_ge W hq)

/-- Helper: the Weierstrass reduction splits the reduced numerator as the
dominant term `x_gen · (π·x)²` plus the rest sum. -/
private lemma addPullbackNumerator_reduced_frobenius_eq_dom_add_rest :
    addPullbackNumerator_reduced_frobenius W =
      x_gen W * (frobeniusIsog W).pullback (x_gen W) ^ 2 +
      (algebraMap K KE W.toAffine.a₄ *
            (x_gen W + (frobeniusIsog W).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (y_gen W + (frobeniusIsog W).pullback (y_gen W))
          - (2 : KE) * y_gen W * (frobeniusIsog W).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (x_gen W * (frobeniusIsog W).pullback (y_gen W) +
               (frobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (frobeniusIsog W).pullback (x_gen W)
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              x_gen W * (frobeniusIsog W).pullback (x_gen W)) := by
  unfold addPullbackNumerator_reduced_frobenius
  ring

/-- Helper: the dominant term has strictly smaller `ord_∞` than the rest sum
(`-2 - 4q < -3 - 3q` for `q ≥ 2`). -/
private lemma ord_dom_lt_rest (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (x_gen W * (frobeniusIsog W).pullback (x_gen W) ^ 2) <
      (W_smooth W).ordAtInfty (
        algebraMap K KE W.toAffine.a₄ *
            (x_gen W + (frobeniusIsog W).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (y_gen W + (frobeniusIsog W).pullback (y_gen W))
          - (2 : KE) * y_gen W * (frobeniusIsog W).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (x_gen W * (frobeniusIsog W).pullback (y_gen W) +
               (frobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (frobeniusIsog W).pullback (x_gen W)
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              x_gen W * (frobeniusIsog W).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int_dom : (-2 - 4 * (Fintype.card K : ℤ) : ℤ) <
      -3 - 3 * (Fintype.card K : ℤ) := by linarith
  rw [ord_x_gen_mul_pi_x_sq_eq W]
  refine lt_of_lt_of_le ?_ (ord_addPullbackNumerator_reduced_rest_ge W hq)
  exact WithTop.coe_lt_coe.mpr h_int_dom

/-- **`ord_∞(addPullbackNumerator_reduced_frobenius) = -2 - 4q`** for `q ≥ 2`.

The unique smallest-order term is `x_gen · (π·x)²` at `-2 - 4q`. Every
other term has `ord ≥ -3 - 3q` (a uniform bound that holds even in
characteristic 2 where the `2·a₆`, `−2·y·π·y`, `2·a₂·x·π·x` terms
vanish). Since `-2 - 4q < -3 - 3q` for `q ≥ 2`, strict non-archimedean
additivity picks out the dominant term. -/
theorem ordAtInfty_addPullbackNumerator_reduced_frobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (addPullbackNumerator_reduced_frobenius W) =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  have h_eq := addPullbackNumerator_reduced_frobenius_eq_dom_add_rest W
  exact h_eq.symm ▸
    ((W_smooth W).ordAtInfty_add_eq_of_lt (ord_dom_lt_rest W hq)).trans
      (ord_x_gen_mul_pi_x_sq_eq W)

/-! ### Sorry 1 closure for Frobenius case (q ≥ 2, any characteristic) -/

/-- **`ord_∞(addPullback_x W π) = -2`** for `q ≥ 2` (any characteristic).

Combines `addPullbackNumerator_frobenius_eq_reduced` (the Weierstrass
reduction) and `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
(the strict non-arch dominant-term computation), then divides through
by `(x_gen − π·x)²` (which has ord `-4q`). -/
theorem ord_addPullback_x_frobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (addPullback_x W (frobeniusIsog W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  have h_pix_ne : x_gen W - (frobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W
  have h_pix_sq_ne : (x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 h_pix_ne
  -- ord((x - π·x)²) = -4q.
  have h_den_ord : (W_smooth W).ordAtInfty
      ((x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2) =
      (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ord_pow_concrete h_pix_ne
      (-2 * (Fintype.card K : ℤ)) 2
      (ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen W)).trans ?_
    congr 1; push_cast; ring
  -- ord(addPullbackNumerator) = -2 - 4q (via reduction identity).
  have h_num_ord : (W_smooth W).ordAtInfty (addPullbackNumerator_frobenius W) =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) :=
    (addPullbackNumerator_frobenius_eq_reduced W).symm ▸
      ordAtInfty_addPullbackNumerator_reduced_frobenius_eq W hq
  -- addPullback_x = addPullbackNumerator / (x - π·x)².
  have h_div_eq : addPullback_x W (frobeniusIsog W) =
      addPullbackNumerator_frobenius W /
        ((x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    rw [addPullbackNumerator_frobenius_eq W, mul_div_cancel_left₀ _ h_pix_sq_ne]
  -- ord(num / den) = -2 - 4q - (-4q) = -2.
  rw [h_div_eq]
  refine ((W_smooth W).ord_div_concrete h_pix_sq_ne
    (-2 - 4 * (Fintype.card K : ℤ))
    (-4 * (Fintype.card K : ℤ)) h_num_ord h_den_ord).trans ?_
  congr 1
  ring

/-- **Sorry 1 closure for the Frobenius case** (`q ≥ 2`, any characteristic):
`addPullback_x W (frobeniusIsog W)` is not the image of any constant `c ∈ K`.

Direct from `ord_addPullback_x_frobenius` (which gives `ord = -2 < 0`,
a pole) plus `addPullback_x_ne_const_of_pole`. -/
theorem addPullback_x_ne_const_frobenius
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (frobeniusIsog W)) (c : K)
    (hc : addPullback_x W (frobeniusIsog W) = algebraMap K KE c) : False := by
  refine addPullback_x_ne_const_of_pole hxy c ?_ hc
  rw [ord_addPullback_x_frobenius W hq]
  exact_mod_cast (by norm_num : (-2 : ℤ) < 0)

/-- **Inequality wrapper** for `ord_addPullback_x_frobenius`.

Some downstream consumers (CLOSE-A-1 ticket spec) want the `≤ -2` form
rather than the equality. Trivial corollary. -/
theorem ordAtInfty_addPullback_x_frobenius_le_neg_two
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (addPullback_x W (frobeniusIsog W)) ≤
      ((-2 : ℤ) : WithTop ℤ) :=
  (ord_addPullback_x_frobenius W hq).le

/-! ### `negFrobeniusIsog`: the `−π` isogeny (HOLE-D-bound work, Day 1)

For HOLE D, we ultimately need the addition-pullback for `1 − π`, which
is `id + α` with `α = −π`. The `−π` isogeny is constructed as the
composition `[-1] ∘ π` via the existing `Isogeny.comp` and `mulByInt _ (-1)`.

By `Isogeny.comp_algebraMap_eq`, the resulting pullback is
`f ↦ frobeniusIsog.pullback (mulByInt _ (-1)).pullback f`. For the two
generators:
* `(negFrobeniusIsog W).pullback (x_gen W)` reduces to
  `(frobeniusIsog W).pullback (x_gen W) = π·x_gen` (since `[-1]` fixes
  `x_gen`).
* `(negFrobeniusIsog W).pullback (y_gen W)` reduces to
  `(frobeniusIsog W).pullback (negY x_gen y_gen) =
   (frobeniusIsog W).pullback (-y_gen - a₁·x_gen - a₃)`. By Frobenius
  being a ring hom and `a_i^q = a_i` in `K = F_q`, this equals
  `-π·y_gen - a₁·π·x_gen - a₃` in any characteristic (in char 2 the
  signs are no-ops).

Both pullbacks have the same `ord_∞` as the Frobenius case (`-2q` and
`-3q` respectively), so the term-ord chain shipped earlier in this file
templates over to `negFrobeniusIsog` with name-prefix swaps. The reduced-
numerator analysis (Weierstrass identity certificate) also carries
forward, since `(π·x_gen, negY π·x π·y)` is on the curve by `equation_neg`.

This file ships only the structural definition tonight. The Day 2 work
(ord lemmas + pullback formulas + Sorry 1 closure for `α = -π`) is
factored separately and reuses the existing helpers verbatim. -/

/-- The `-π` isogeny as `[-1] ∘ π`, via `Isogeny.comp` of the existing
`mulByInt _ (-1)` and `frobeniusIsog W` isogenies. -/
noncomputable def negFrobeniusIsog : Isogeny W.toAffine W.toAffine :=
  Isogeny.comp (mulByInt W.toAffine (-1)) (frobeniusIsog W)

/-- The `toAddMonoidHom` of `negFrobeniusIsog` is the negation of Frobenius's
`toAddMonoidHom`. Direct from `Isogeny.comp_toAddMonoidHom` and
`mulByInt`'s `toAddMonoidHom = zsmulAddGroupHom (-1)` (which on any
abelian group is `P ↦ -P`). -/
theorem negFrobeniusIsog_toAddMonoidHom_apply (P : W.toAffine.Point) :
    (negFrobeniusIsog W).toAddMonoidHom P = -((frobeniusIsog W).toAddMonoidHom P) := by
  unfold negFrobeniusIsog
  rw [Isogeny.comp_toAddMonoidHom]
  show ((mulByInt W.toAffine (-1)).toAddMonoidHom)
      ((frobeniusIsog W).toAddMonoidHom P) = -_
  rw [mulByInt_apply]
  exact (neg_one_zsmul _).trans rfl

/-- The `[-1]`-pullback sends `y_gen` to `negY x_gen y_gen = -y_gen − a₁·x_gen
− a₃` (the curve-negation formula).

Direct from `mulByInt_y_neg` (= `negY` of `[1]`-image) plus `mulByInt_x_one`,
`mulByInt_y_one`. The final `negY` unfolds via the definitional equality
`(W_KE W).toAffine.a_i = algebraMap K KE W.toAffine.a_i`. -/
theorem mulByInt_pullback_y_neg_one :
    (mulByInt W.toAffine (-1)).pullback (y_gen W) =
      -y_gen W - algebraMap K KE W.toAffine.a₁ * x_gen W
        - algebraMap K KE W.toAffine.a₃ := by
  -- `(mulByInt W (-1)).pullback (y_gen W) = mulByInt_y W (-1)`.
  have h_pb : (mulByInt W.toAffine (-1)).pullback (y_gen W) = mulByInt_y W (-1) := by
    change (mulByInt W.toAffine (-1)).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial)) = _
    exact mulByInt_pullback_y W (-1) (by norm_num : (-1 : ℤ) ≠ 0)
  rw [h_pb]
  -- `mulByInt_y W (-1) = mulByInt_y W (-(1)) = negY (mulByInt_x W 1) (mulByInt_y W 1)`.
  rw [show (-1 : ℤ) = -(1 : ℤ) from rfl,
    mulByInt_y_neg W 1 (by norm_num : (1 : ℤ) ≠ 0),
    mulByInt_x_one, mulByInt_y_one]
  -- `negY` unfolds to `-y - a₁·x - a₃`. The `(W_KE W).toAffine.a_i = algebraMap K KE _`
  -- is definitional via `W.map`.
  rfl

/-- **`(negFrobeniusIsog W).pullback (x_gen W) = π·x_gen`.**

By `Isogeny.comp_algebraMap_eq`, this pullback is `frobeniusIsog.pullback ∘
[-1].pullback` applied to `x_gen`. The `[-1]`-pullback fixes `x_gen`
(`mulByInt_pullback_x_neg_one`), so the result is just Frobenius applied
to `x_gen`. -/
theorem negFrobeniusIsog_pullback_x_gen :
    (negFrobeniusIsog W).pullback (x_gen W) =
      (frobeniusIsog W).pullback (x_gen W) := by
  unfold negFrobeniusIsog
  rw [Isogeny.comp_algebraMap_eq, mulByInt_pullback_x_neg_one]

/-- **`(negFrobeniusIsog W).pullback (y_gen W) = -π·y_gen − a₁·π·x_gen − a₃`.**

By `Isogeny.comp_algebraMap_eq`, this pullback is `frobeniusIsog.pullback ∘
[-1].pullback` applied to `y_gen`. The `[-1]`-pullback sends `y_gen ↦ -y_gen
- a₁·x_gen - a₃` (`mulByInt_pullback_y_neg_one`). Frobenius is a ring hom,
so it distributes; combined with `frobeniusIsog`'s K-fixing (so `a_i^q = a_i`),
the formula is as stated. -/
theorem negFrobeniusIsog_pullback_y_gen :
    (negFrobeniusIsog W).pullback (y_gen W) =
      -((frobeniusIsog W).pullback (y_gen W))
        - algebraMap K KE W.toAffine.a₁ * (frobeniusIsog W).pullback (x_gen W)
        - algebraMap K KE W.toAffine.a₃ := by
  unfold negFrobeniusIsog
  rw [Isogeny.comp_algebraMap_eq, mulByInt_pullback_y_neg_one]
  -- LHS: frobeniusIsog.pullback (-y_gen W - a₁·x_gen - a₃).
  -- frobeniusIsog.pullback is a K-algebra hom, so it preserves -, *, +,
  -- and fixes algebraMap K KE values.
  simp only [map_sub, map_neg, map_mul,
    AlgHom.commutes (frobeniusIsog W).pullback]

/-! ### `ord_∞` lemmas for the negFrobeniusIsog pullbacks (Day 2 first half)

With the pullback formulas in place, the ord values match the Frobenius
case:

* `ord_∞((negFrobeniusIsog W).pullback (x_gen W)) = -2q` — direct rewrite.
* `ord_∞((negFrobeniusIsog W).pullback (y_gen W)) = -3q` — strict non-arch
  with the `-π·y_gen` term dominating the `a₁·π·x_gen + a₃` correction. -/

/-- **`ord_∞((negFrobeniusIsog W).pullback (x_gen W)) = -2q`**. Direct
from `negFrobeniusIsog_pullback_x_gen` + the existing Frobenius lemma. -/
theorem ordAtInfty_negFrobeniusIsog_pullback_x_gen :
    (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact ordAtInfty_frobeniusIsog_pullback_x_gen W

/-- `ord_∞(a₁·π·x + a₃) ≥ -2q`: `ord(a₁·π·x) ≥ -2q` (algebraMap factor doesn't
lower order, `-2q ≤ ord(π·x)`) and `ord(a₃) ≥ -2q` (case-split on `a₃ = 0`). -/
private lemma a1_pi_x_plus_a3_ge_neg_two_q (hq : 2 ≤ Fintype.card K) :
    (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₁ *
          (frobeniusIsog W).pullback (x_gen W) +
         algebraMap K KE W.toAffine.a₃) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  apply ord_add_ge_of_both_ge
  · refine ord_algebraMap_mul_ge W W.toAffine.a₁ ?_
    exact (ordAtInfty_frobeniusIsog_pullback_x_gen W).symm.le
  · by_cases ha₃ : W.toAffine.a₃ = 0
    · rw [ha₃, map_zero]
      exact (W_smooth W).ordAtInfty_zero.symm ▸
        (le_top : (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤ ⊤)
    · rw [ordAtInfty_algebraMap_F_nonzero W ha₃]
      exact WithTop.coe_le_coe.mpr (by linarith)

/-- Strict non-archimedean subtraction via integer bounds: if `ord A = m`,
`n ≤ ord B`, and `m < n`, then `ord(A - B) = m`. -/
private lemma ordAtInfty_sub_eq_of_coe_lt_le {A B : KE} {m n : ℤ} (hmn : m < n)
    (hA : (W_smooth W).ordAtInfty A = (m : WithTop ℤ))
    (hB : (n : WithTop ℤ) ≤ (W_smooth W).ordAtInfty B) :
    (W_smooth W).ordAtInfty (A - B) = (m : WithTop ℤ) := by
  refine ((W_smooth W).ordAtInfty_sub_eq_of_lt ?_).trans hA
  rw [hA]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hmn) hB

/-- **`ord_∞((negFrobeniusIsog W).pullback (y_gen W)) = -3q`** for `q ≥ 2`.

Regroup `(negFrobeniusIsog W).pullback (y_gen W) = -π·y − (a₁·π·x + a₃)`.
* `ord(-π·y) = -3q` (via `ordAtInfty_neg` + the existing Frobenius lemma).
* `ord(a₁·π·x + a₃) ≥ -2q`: combine `ord(a₁·π·x) ≥ -2q` (via
  `ord_algebraMap_mul_ge` + `-2q ≤ ord(π·x)`) with `ord(a₃) ≥ -2q`
  (case-split on `a₃ = 0`).
* `-3q < -2q` for `q ≥ 1`, so strict non-arch sub gives the answer. -/
theorem ordAtInfty_negFrobeniusIsog_pullback_y_gen
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_y_gen]
  rw [show -((frobeniusIsog W).pullback (y_gen W)) -
      algebraMap K KE W.toAffine.a₁ * (frobeniusIsog W).pullback (x_gen W) -
      algebraMap K KE W.toAffine.a₃ =
      -((frobeniusIsog W).pullback (y_gen W)) -
      (algebraMap K KE W.toAffine.a₁ * (frobeniusIsog W).pullback (x_gen W) +
       algebraMap K KE W.toAffine.a₃) from by ring]
  have h_neg_πy : (W_smooth W).ordAtInfty
      (-((frobeniusIsog W).pullback (y_gen W))) =
      (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_neg _).trans
      (ordAtInfty_frobeniusIsog_pullback_y_gen W)
  have h_lt_q : ((-3 * (Fintype.card K : ℤ)) : ℤ) < -2 * (Fintype.card K : ℤ) := by
    have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact ordAtInfty_sub_eq_of_coe_lt_le W h_lt_q h_neg_πy
    (a1_pi_x_plus_a3_ge_neg_two_q W hq)

/-! ### addPullbackNumerator for negFrobenius (Day 2 second half opener)

Mirrors the Frobenius numerator + reduction identity, with `α = negFrobeniusIsog W`
instead of `α = frobeniusIsog W`. The (u, v) point used in the reduction is
`(negFrob.pullback x_gen, negFrob.pullback y_gen) = (π·x_gen, -π·y_gen − a₁·π·x_gen − a₃)`,
which is on the curve via `pullback_equation W (negFrobeniusIsog W)`. The reviewer's
certificate `linear_combination h_xy + h_uv` closes the reduction identity verbatim. -/

/-- The numerator obtained by clearing the `(x_gen − negFrob.pullback x_gen)²`
denominator from `addPullback_x W (negFrobeniusIsog W)`. Same shape as the
Frobenius version with `frobeniusIsog W` swapped for `negFrobeniusIsog W`. -/
noncomputable def addPullbackNumerator_negFrobenius : KE :=
  (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) ^ 2 +
    algebraMap K KE W.toAffine.a₁ *
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) *
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) -
    (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 *
      (algebraMap K KE W.toAffine.a₂ + x_gen W +
        (negFrobeniusIsog W).pullback (x_gen W))

/-- The Weierstrass-reduced form of `addPullbackNumerator_negFrobenius`.
Same shape as `addPullbackNumerator_reduced_frobenius` with `frobeniusIsog W`
swapped for `negFrobeniusIsog W`. The dominant term `x_gen · (negFrob.pullback
x_gen)²` has the same `ord_∞ = -2 - 4q` since `(negFrobeniusIsog W).pullback
(x_gen W) = (frobeniusIsog W).pullback (x_gen W) = π·x_gen` (per
`negFrobeniusIsog_pullback_x_gen`). -/
noncomputable def addPullbackNumerator_reduced_negFrobenius : KE :=
  algebraMap K KE W.toAffine.a₄ *
      (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
    + 2 * algebraMap K KE W.toAffine.a₆
    - algebraMap K KE W.toAffine.a₃ *
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
    - 2 * y_gen W * (negFrobeniusIsog W).pullback (y_gen W)
    - algebraMap K KE W.toAffine.a₁ *
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
         (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
    + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
    + x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2
    + 2 * algebraMap K KE W.toAffine.a₂ *
        x_gen W * (negFrobeniusIsog W).pullback (x_gen W)

/-- **Weierstrass reduction for negFrobenius**:
`addPullbackNumerator_negFrobenius W = addPullbackNumerator_reduced_negFrobenius W`.

Identical structure to the Frobenius reduction identity. The certificate
`linear_combination h_xy + h_uv` works because:
* `h_xy` is the Weierstrass equation for `(x_gen W, y_gen W)`
  (via `generic_equation W` + `equation_iff'`).
* `h_uv` is the Weierstrass equation for `((negFrobeniusIsog W).pullback (x_gen W),
  (negFrobeniusIsog W).pullback (y_gen W))` — every isogeny preserves the
  curve equation, so `pullback_equation W (negFrobeniusIsog W)` gives this
  for free. -/
theorem addPullbackNumerator_negFrobenius_eq_reduced :
    addPullbackNumerator_negFrobenius W =
      addPullbackNumerator_reduced_negFrobenius W := by
  -- Weierstrass for (x_gen, y_gen).
  have h_xy : y_gen W ^ 2 +
        algebraMap K KE W.toAffine.a₁ * x_gen W * y_gen W +
        algebraMap K KE W.toAffine.a₃ * y_gen W -
        (x_gen W ^ 3 +
         algebraMap K KE W.toAffine.a₂ * x_gen W ^ 2 +
         algebraMap K KE W.toAffine.a₄ * x_gen W +
         algebraMap K KE W.toAffine.a₆) = 0 := by
    have h := generic_equation W
    rw [WeierstrassCurve.Affine.equation_iff'] at h
    have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
    have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
    have h_a3 : (W_KE W).toAffine.a₃ = algebraMap K KE W.toAffine.a₃ := rfl
    have h_a4 : (W_KE W).toAffine.a₄ = algebraMap K KE W.toAffine.a₄ := rfl
    have h_a6 : (W_KE W).toAffine.a₆ = algebraMap K KE W.toAffine.a₆ := rfl
    rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h
    exact h
  -- Weierstrass for (u, v) := ((negFrobeniusIsog W).pullback (x_gen W),
  --                            (negFrobeniusIsog W).pullback (y_gen W)).
  -- Direct from `pullback_equation` applied to `negFrobeniusIsog W`.
  have h_uv : (negFrobeniusIsog W).pullback (y_gen W) ^ 2 +
        algebraMap K KE W.toAffine.a₁ *
          (negFrobeniusIsog W).pullback (x_gen W) *
          (negFrobeniusIsog W).pullback (y_gen W) +
        algebraMap K KE W.toAffine.a₃ *
          (negFrobeniusIsog W).pullback (y_gen W) -
        ((negFrobeniusIsog W).pullback (x_gen W) ^ 3 +
         algebraMap K KE W.toAffine.a₂ *
           (negFrobeniusIsog W).pullback (x_gen W) ^ 2 +
         algebraMap K KE W.toAffine.a₄ *
           (negFrobeniusIsog W).pullback (x_gen W) +
         algebraMap K KE W.toAffine.a₆) = 0 := by
    have h := pullback_equation W (negFrobeniusIsog W)
    rw [WeierstrassCurve.Affine.equation_iff'] at h
    have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
    have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
    have h_a3 : (W_KE W).toAffine.a₃ = algebraMap K KE W.toAffine.a₃ := rfl
    have h_a4 : (W_KE W).toAffine.a₄ = algebraMap K KE W.toAffine.a₄ := rfl
    have h_a6 : (W_KE W).toAffine.a₆ = algebraMap K KE W.toAffine.a₆ := rfl
    rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h
    exact h
  unfold addPullbackNumerator_negFrobenius addPullbackNumerator_reduced_negFrobenius
  linear_combination h_xy + h_uv

/-! ### Term-ord helpers for negFrobenius (mirror of Frobenius helpers) -/

/-- `(negFrobeniusIsog W).pullback (x_gen W) ≠ 0`. Direct from
`negFrobeniusIsog_pullback_x_gen` + `pi_x_gen_ne_zero`. -/
private lemma negFrob_pi_x_gen_ne_zero :
    (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact pi_x_gen_ne_zero W

/-- `(negFrobeniusIsog W).pullback (y_gen W) ≠ 0`. Its ord is `-3q ≠ ⊤`. -/
private lemma negFrob_pi_y_gen_ne_zero (hq : 2 ≤ Fintype.card K) :
    (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (y_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq] at h_top
  exact WithTop.coe_ne_top h_top

/-- `ord(x_gen + negFrob.pb x_gen) = -2q`. The `negFrob.pb x_gen` term
dominates strictly. Reuses the Frobenius helper via the pullback equality. -/
private lemma ord_x_gen_add_negFrob_pi_x_eq (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact ord_x_gen_add_pi_x_eq W hq

/-- `ord(y_gen + negFrob.pb y_gen) = -3q`. The `negFrob.pb y_gen` term
dominates strictly (its ord is `-3q`, smaller than `ord(y_gen) = -3`). -/
private lemma ord_y_gen_add_negFrob_pi_y_eq (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_lt : (-3 * (Fintype.card K : ℤ)) < (-3 : ℤ) := by linarith
  have h_swap : y_gen W + (negFrobeniusIsog W).pullback (y_gen W) =
      (negFrobeniusIsog W).pullback (y_gen W) + y_gen W := by ring
  rw [h_swap]
  exact (W_smooth W).ord_add_lt_concrete (-3 * (Fintype.card K : ℤ)) (-3) h_lt
    (ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq) (ordAtInfty_y_gen W)

/-- `ord(x_gen · negFrob.pb x_gen) = -2 - 2q`. Reuses Frobenius. -/
private lemma ord_x_gen_mul_negFrob_pi_x_eq :
    (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) =
      ((-2 - 2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact ord_x_gen_mul_pi_x_eq W

/-- `ord(x_gen² · negFrob.pb x_gen) = -4 - 2q`. Reuses Frobenius. -/
private lemma ord_x_gen_sq_mul_negFrob_pi_x_eq :
    (W_smooth W).ordAtInfty
        (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)) =
      ((-4 - 2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact ord_x_gen_sq_mul_pi_x_eq W

/-- `ord(x_gen · (negFrob.pb x_gen)²) = -2 - 4q`. The dominant term. Reuses Frobenius. -/
private lemma ord_x_gen_mul_negFrob_pi_x_sq_eq :
    (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
      ((-2 - 4 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact ord_x_gen_mul_pi_x_sq_eq W

/-- `ord(y_gen · negFrob.pb y_gen) = -3 - 3q`. -/
private lemma ord_y_gen_mul_negFrob_pi_y_eq (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
      ((-3 - 3 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  refine ((W_smooth W).ordAtInfty_mul (y_gen_ne_zero W)
    (negFrob_pi_y_gen_ne_zero W hq)).trans ?_
  refine (congrArg₂ (· + ·) (ordAtInfty_y_gen W)
    (ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq)).trans ?_
  rfl

/-- For `q ≥ 2`, `ord(x_gen · negFrob.pb y + negFrob.pb x · y_gen) ≥ -2 - 3q`.
Same structure as Frobenius case (the y-pullback's ord is `-3q` either way). -/
private lemma ord_x_negFrob_pi_y_plus_negFrob_pi_x_y_ge (hq : 2 ≤ Fintype.card K) :
    (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
         (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  -- ord(x · negFrob.pb y) = -2-3q.
  have h_x_pi_y :
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
        (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul (x_gen_ne_zero W)
      (negFrob_pi_y_gen_ne_zero W hq)).trans ?_
    refine (congrArg₂ (· + ·) (ordAtInfty_x_gen W)
      (ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq)).trans ?_
    rfl
  -- ord(negFrob.pb x · y_gen) = -3-2q. Use mul_comm to align order for rfl.
  have h_pi_x_y :
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (((-3 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [mul_comm]
    refine ((W_smooth W).ordAtInfty_mul (y_gen_ne_zero W)
      (negFrob_pi_x_gen_ne_zero W)).trans ?_
    refine (congrArg₂ (· + ·) (ordAtInfty_y_gen W)
      (ordAtInfty_negFrobeniusIsog_pullback_x_gen W)).trans ?_
    rfl
  -- ord(sum) ≥ min(ord(x·negFrob.pb y), ord(negFrob.pb x·y)) = -2-3q for q ≥ 2.
  have h_min_le := (W_smooth W).ordAtInfty_add_ge_min
    (x_gen W * (negFrobeniusIsog W).pullback (y_gen W))
    ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
  rw [h_x_pi_y, h_pi_x_y] at h_min_le
  refine le_trans ?_ h_min_le
  have h_ineq : (-2 - 3 * (Fintype.card K : ℤ) : ℤ) ≤
      min (-2 - 3 * (Fintype.card K : ℤ)) (-3 - 2 * (Fintype.card K : ℤ)) := by
    apply le_min (le_refl _)
    linarith
  exact_mod_cast h_ineq

/-! ### Main theorem: `ord_∞(addPullbackNumerator_reduced_negFrobenius) = -2 - 4q` -/

/-- Helper: `ord_∞(a₄ · (x_gen + negFrob.pb x)) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_a4_mul_x_add_negFrob_pi_x_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₄ *
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -2 * (Fintype.card K : ℤ) := by linarith
  refine ord_algebraMap_mul_ge W W.toAffine.a₄ ?_
  rw [ord_x_gen_add_negFrob_pi_x_eq W hq]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(a₃ · (y_gen + negFrob.pb y)) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_a3_mul_y_add_negFrob_pi_y_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₃ *
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))) := by
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -3 * (Fintype.card K : ℤ) := by linarith
  refine ord_algebraMap_mul_ge W W.toAffine.a₃ ?_
  rw [ord_y_gen_add_negFrob_pi_y_eq W hq]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(2 · y_gen · negFrob.pb y) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_two_mul_y_mul_negFrob_pi_y_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((2 : KE) * y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) := by
  rw [show (2 : KE) * y_gen W * (negFrobeniusIsog W).pullback (y_gen W) =
      (2 : KE) * (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) from by ring]
  refine ord_two_mul_ge W ?_
  rw [ord_y_gen_mul_negFrob_pi_y_eq W hq]
  exact le_refl _

/-- Helper: `ord_∞(a₁ · (x_gen · negFrob.pb y + negFrob.pb x · y_gen)) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_a1_mul_negFrob_cross_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₁ *
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
           (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) := by
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -2 - 3 * (Fintype.card K : ℤ) := by linarith
  refine ord_algebraMap_mul_ge W W.toAffine.a₁ ?_
  refine le_trans ?_ (ord_x_negFrob_pi_y_plus_negFrob_pi_x_y_ge W hq)
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(x_gen² · negFrob.pb x) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_x_sq_mul_negFrob_pi_x_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -4 - 2 * (Fintype.card K : ℤ) := by linarith
  rw [ord_x_gen_sq_mul_negFrob_pi_x_eq W]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: `ord_∞(2 · a₂ · x_gen · negFrob.pb x) ≥ -3 - 3q` for `q ≥ 2`. -/
private lemma ord_two_mul_a2_mul_x_mul_negFrob_pi_x_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((2 : KE) * algebraMap K KE W.toAffine.a₂ * x_gen W *
          (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int : (-3 - 3 * (Fintype.card K : ℤ) : ℤ) ≤ -2 - 2 * (Fintype.card K : ℤ) := by linarith
  rw [show (2 : KE) * algebraMap K KE W.toAffine.a₂ * x_gen W *
      (negFrobeniusIsog W).pullback (x_gen W) =
      (2 : KE) * (algebraMap K KE W.toAffine.a₂ *
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W))) from by ring]
  refine ord_two_mul_ge W ?_
  refine ord_algebraMap_mul_ge W W.toAffine.a₂ ?_
  rw [ord_x_gen_mul_negFrob_pi_x_eq W]
  exact WithTop.coe_le_coe.mpr h_int

/-- Helper: the six non-dominant "rest" terms of the reduced negFrobenius numerator together
have `ord_∞ ≥ -3 - 3q` for `q ≥ 2` (chains the seven term bounds). -/
private lemma ord_addPullbackNumerator_reduced_negFrob_rest_ge (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (
        algebraMap K KE W.toAffine.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : KE) * y_gen W * (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h12 := ord_add_ge_of_both_ge W (ord_a4_mul_x_add_negFrob_pi_x_ge W hq)
    (ord_two_mul_a6_ge W hq)
  have h123 := ord_sub_ge_of_both_ge W h12 (ord_a3_mul_y_add_negFrob_pi_y_ge W hq)
  have h1234 := ord_sub_ge_of_both_ge W h123 (ord_two_mul_y_mul_negFrob_pi_y_ge W hq)
  have h12345 := ord_sub_ge_of_both_ge W h1234 (ord_a1_mul_negFrob_cross_ge W hq)
  have h123456 := ord_add_ge_of_both_ge W h12345 (ord_x_sq_mul_negFrob_pi_x_ge W hq)
  exact ord_add_ge_of_both_ge W h123456 (ord_two_mul_a2_mul_x_mul_negFrob_pi_x_ge W hq)

/-- Helper: the Weierstrass reduction splits the reduced negFrobenius numerator as the
dominant term `x_gen · (negFrob.pb x)²` plus the rest sum. -/
private lemma addPullbackNumerator_reduced_negFrobenius_eq_dom_add_rest :
    addPullbackNumerator_reduced_negFrobenius W =
      x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2 +
      (algebraMap K KE W.toAffine.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : KE) * y_gen W * (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  unfold addPullbackNumerator_reduced_negFrobenius
  ring

/-- Helper: the dominant term has strictly smaller `ord_∞` than the rest sum
(`-2 - 4q < -3 - 3q` for `q ≥ 2`). -/
private lemma ord_dom_lt_negFrob_rest (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) <
      (W_smooth W).ordAtInfty (
        algebraMap K KE W.toAffine.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : KE) * y_gen W * (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_int_dom : (-2 - 4 * (Fintype.card K : ℤ) : ℤ) <
      -3 - 3 * (Fintype.card K : ℤ) := by linarith
  rw [ord_x_gen_mul_negFrob_pi_x_sq_eq W]
  refine lt_of_lt_of_le ?_ (ord_addPullbackNumerator_reduced_negFrob_rest_ge W hq)
  exact WithTop.coe_lt_coe.mpr h_int_dom

/-- **`ord_∞(addPullbackNumerator_reduced_negFrobenius) = -2 - 4q`** for `q ≥ 2`.

Mirror of the Frobenius proof with `negFrobeniusIsog` substituted. The dominant
term `x_gen · (negFrob.pb x_gen)²` has `ord = -2 - 4q` (same as Frobenius via
the pullback equality). Every other term has `ord ≥ -3 - 3q`, and `-2 - 4q
< -3 - 3q` for `q ≥ 2`. -/
theorem ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (addPullbackNumerator_reduced_negFrobenius W) =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  have h_eq := addPullbackNumerator_reduced_negFrobenius_eq_dom_add_rest W
  exact h_eq.symm ▸
    ((W_smooth W).ordAtInfty_add_eq_of_lt (ord_dom_lt_negFrob_rest W hq)).trans
      (ord_x_gen_mul_negFrob_pi_x_sq_eq W)

/-! ### Sorry 1 closure for the negFrobenius case (Day 2 final)

`ord(addPullback_x W (-π)) = -2` follows by dividing the reduced numerator
(ord = -2 - 4q) through `(x_gen − negFrob.pb x_gen)²` (ord = -4q). Then
`addPullback_x W (negFrobeniusIsog W) ≠ algebraMap K _ c` via the existing
`addPullback_x_ne_const_of_pole`. -/

/-- `x_gen W ≠ (negFrobeniusIsog W).pullback (x_gen W)`. Reuses Frobenius via
the pullback equality. -/
private lemma x_gen_ne_negFrobeniusIsog_pullback_x_gen :
    x_gen W ≠ (negFrobeniusIsog W).pullback (x_gen W) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact x_gen_ne_frobeniusIsog_pullback_x_gen W

/-- `(x_gen − negFrob.pb x_gen) ≠ 0`. -/
lemma x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero :
    x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W

/-- `ord(x_gen − negFrob.pb x_gen) = -2q`. -/
private lemma ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen :
    (W_smooth W).ordAtInfty
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen W

/-- The slope formula for `α = negFrobeniusIsog W`. -/
theorem addSlope_negFrobeniusIsog_eq :
    addSlope W (negFrobeniusIsog W) =
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) /
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) := by
  unfold addSlope
  exact Affine.slope_of_X_ne (x_gen_ne_negFrobeniusIsog_pullback_x_gen W)

/-- The numerator equation: `addPullbackNumerator_negFrobenius = (x_gen
− negFrob.pb x_gen)² · addPullback_x W (negFrobeniusIsog W)`. Mirror of the
Frobenius version. -/
theorem addPullbackNumerator_negFrobenius_eq :
    addPullbackNumerator_negFrobenius W =
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 *
        addPullback_x W (negFrobeniusIsog W) := by
  set d := x_gen W - (negFrobeniusIsog W).pullback (x_gen W) with hd_def
  set n := y_gen W - (negFrobeniusIsog W).pullback (y_gen W) with hn_def
  have hd_ne : d ≠ 0 := x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  have hL : addSlope W (negFrobeniusIsog W) = n / d := addSlope_negFrobeniusIsog_eq W
  unfold addPullbackNumerator_negFrobenius addPullback_x
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ + x_gen W +
            (negFrobeniusIsog W).pullback (x_gen W)) =
      d ^ 2 * (W_KE W).toAffine.addX (x_gen W)
        ((negFrobeniusIsog W).pullback (x_gen W)) (addSlope W (negFrobeniusIsog W))
  unfold WeierstrassCurve.Affine.addX
  rw [hL]
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ + x_gen W +
            (negFrobeniusIsog W).pullback (x_gen W)) =
      d ^ 2 * ((n / d) ^ 2 + (W_KE W).toAffine.a₁ * (n / d) -
        (W_KE W).toAffine.a₂ - x_gen W - (negFrobeniusIsog W).pullback (x_gen W))
  have h_a1_lift : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2_lift : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  rw [h_a1_lift, h_a2_lift]
  field_simp
  ring

/-- **`ord_∞(addPullback_x W (-π)) = -2`** for `q ≥ 2` (any characteristic).

Combines `addPullbackNumerator_negFrobenius_eq_reduced` (Weierstrass reduction)
with `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq` (`ord = -2 - 4q`),
then divides through by `(x_gen − negFrob.pb x_gen)²` (`ord = -4q`). -/
theorem ord_addPullback_x_negFrobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  have h_pix_ne : x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  have h_pix_sq_ne : (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 h_pix_ne
  have h_den_ord : (W_smooth W).ordAtInfty
      ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) =
      (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ord_pow_concrete h_pix_ne
      (-2 * (Fintype.card K : ℤ)) 2
      (ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen W)).trans ?_
    congr 1; push_cast; ring
  have h_num_ord : (W_smooth W).ordAtInfty (addPullbackNumerator_negFrobenius W) =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) :=
    (addPullbackNumerator_negFrobenius_eq_reduced W).symm ▸
      ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq W hq
  have h_div_eq : addPullback_x W (negFrobeniusIsog W) =
      addPullbackNumerator_negFrobenius W /
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    rw [addPullbackNumerator_negFrobenius_eq W, mul_div_cancel_left₀ _ h_pix_sq_ne]
  rw [h_div_eq]
  refine ((W_smooth W).ord_div_concrete h_pix_sq_ne
    (-2 - 4 * (Fintype.card K : ℤ))
    (-4 * (Fintype.card K : ℤ)) h_num_ord h_den_ord).trans ?_
  congr 1
  ring

/-- **Sorry 1 closure for the negFrobenius case** (`q ≥ 2`, any characteristic):
`addPullback_x W (negFrobeniusIsog W)` is not the image of any constant `c ∈ K`.

Direct from `ord_addPullback_x_negFrobenius` (which gives `ord = -2 < 0`,
a pole) plus `addPullback_x_ne_const_of_pole`. This is the closure needed
for HOLE D's `1 − π` use case (since `1 − π = id + (-π)`). -/
theorem addPullback_x_ne_const_negFrobenius
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) (c : K)
    (hc : addPullback_x W (negFrobeniusIsog W) = algebraMap K KE c) : False := by
  refine addPullback_x_ne_const_of_pole hxy c ?_ hc
  rw [ord_addPullback_x_negFrobenius W hq]
  exact_mod_cast (by norm_num : (-2 : ℤ) < 0)

/-- **Inequality wrapper** for `ord_addPullback_x_negFrobenius`.

Companion to `ordAtInfty_addPullback_x_frobenius_le_neg_two` for the
`−π` (negFrobenius) case — the load-bearing case for HOLE D's `1 − π`
analysis. Trivial corollary of the equality form. -/
theorem ordAtInfty_addPullback_x_negFrobenius_le_neg_two
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)) ≤
      ((-2 : ℤ) : WithTop ℤ) :=
  (ord_addPullback_x_negFrobenius W hq).le

/-! ### `ord_addPullback_y_negFrobenius = -3` via the curve equation

Strategy paralleling Silverman III.3 (rather than the x-side numerator
chain): use `addPullback_equation` (the curve equation for the addition
formula outputs) plus `ord_addPullback_x_negFrobenius = -2` to deduce
`ord_addPullback_y_negFrobenius = -3`. The argument: with
`X = addPullback_x` and `Y = addPullback_y`, the equation
`Y² + a₁·X·Y + a₃·Y = X³ + a₂·X² + a₄·X + a₆` has RHS ord `= -6` (since
`ord(X³) = -6` strictly dominates the lower terms which have ord `≥ -4`).
So ord(LHS) `= -6`. Case analysis on `ord(Y)`:
* If `ord(Y) ≥ -2` or `Y = 0`, every term in LHS has ord `≥ -4`, so
  ord(LHS) `≥ -4 > -6`. Contradiction.
* If `ord(Y) ≤ -3`, then `Y²` strictly dominates LHS (since `2m < m - 2`
  for `m ≤ -3`), giving ord(LHS) `= 2 · ord(Y)`. So `2 · ord(Y) = -6`,
  hence `ord(Y) = -3`. -/

/-- Helper: `addPullback_x W (negFrobeniusIsog W) ≠ 0`. -/
private theorem addPullback_x_negFrobenius_ne_zero (hq : 2 ≤ Fintype.card K) :
    addPullback_x W (negFrobeniusIsog W) ≠ 0 := by
  intro h
  have ht : (W_smooth W).ordAtInfty
      (addPullback_x W (negFrobeniusIsog W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ord_addPullback_x_negFrobenius W hq] at ht
  exact WithTop.coe_ne_top ht

/-- Helper: `ord(X²) = -4`. -/
private theorem ord_addPullback_x_sq_negFrobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (addPullback_x W (negFrobeniusIsog W) ^ 2) =
      ((-4 : ℤ) : WithTop ℤ) :=
  ((W_smooth W).ord_pow_concrete (addPullback_x_negFrobenius_ne_zero W hq) (-2) 2
    (ord_addPullback_x_negFrobenius W hq)).trans rfl

/-- Helper: `ord(X³) = -6`. -/
private theorem ord_addPullback_x_cube_negFrobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (addPullback_x W (negFrobeniusIsog W) ^ 3) =
      ((-6 : ℤ) : WithTop ℤ) :=
  ((W_smooth W).ord_pow_concrete (addPullback_x_negFrobenius_ne_zero W hq) (-2) 3
    (ord_addPullback_x_negFrobenius W hq)).trans rfl

/-- Helper: `ord(a₂·X² + a₄·X + a₆) ≥ -4`. -/
private theorem ord_RHS_lower_ge_neg_four_negFrobenius
    (hq : 2 ≤ Fintype.card K) :
    ((-4 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₂ *
          addPullback_x W (negFrobeniusIsog W) ^ 2 +
         algebraMap K KE W.toAffine.a₄ *
           addPullback_x W (negFrobeniusIsog W) +
         algebraMap K KE W.toAffine.a₆) := by
  have h_a₂_term : ((-4 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
      (algebraMap K KE W.toAffine.a₂ *
        addPullback_x W (negFrobeniusIsog W) ^ 2) :=
    ord_algebraMap_mul_ge W W.toAffine.a₂
      (ord_addPullback_x_sq_negFrobenius W hq).symm.le
  have h_a₄_term : ((-4 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
      (algebraMap K KE W.toAffine.a₄ *
        addPullback_x W (negFrobeniusIsog W)) := by
    refine ord_algebraMap_mul_ge W W.toAffine.a₄ ?_
    rw [ord_addPullback_x_negFrobenius W hq]
    exact_mod_cast (by norm_num : (-4 : ℤ) ≤ -2)
  have h_a₆_term : ((-4 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
      (algebraMap K KE W.toAffine.a₆) := by
    by_cases ha₆ : W.toAffine.a₆ = 0
    · rw [ha₆, map_zero]
      exact (W_smooth W).ordAtInfty_zero.symm ▸
        (le_top : ((-4 : ℤ) : WithTop ℤ) ≤ ⊤)
    · rw [ordAtInfty_algebraMap_F_nonzero W ha₆]
      exact_mod_cast (by norm_num : (-4 : ℤ) ≤ 0)
  exact ord_add_ge_of_both_ge W
    (ord_add_ge_of_both_ge W h_a₂_term h_a₄_term) h_a₆_term

/-- Helper: `ord(a₆) ≥ 0` (where `a₆` is a constant in K, viewed in KE). -/
private theorem ord_a₆_ge_zero :
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap K KE W.toAffine.a₆) := by
  by_cases ha₆ : W.toAffine.a₆ = 0
  · rw [ha₆, map_zero]
    exact (W_smooth W).ordAtInfty_zero.symm ▸ le_top
  · rw [ordAtInfty_algebraMap_F_nonzero W ha₆]

/-- Helper: `ord(X³ + a₂·X² + a₄·X + a₆) = -6`. Step-by-step strict
non-arch on the left-associated sum. -/
private theorem ord_RHS_negFrobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
        (addPullback_x W (negFrobeniusIsog W) ^ 3 +
         algebraMap K KE W.toAffine.a₂ *
           addPullback_x W (negFrobeniusIsog W) ^ 2 +
         algebraMap K KE W.toAffine.a₄ *
           addPullback_x W (negFrobeniusIsog W) +
         algebraMap K KE W.toAffine.a₆) =
      ((-6 : ℤ) : WithTop ℤ) := by
  set X := addPullback_x W (negFrobeniusIsog W)
  have h_X3 : (W_smooth W).ordAtInfty (X ^ 3) = ((-6 : ℤ) : WithTop ℤ) :=
    ord_addPullback_x_cube_negFrobenius W hq
  have h_a2X2 : ((-4 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₂ * X ^ 2) :=
    ord_algebraMap_mul_ge W W.toAffine.a₂
      (ord_addPullback_x_sq_negFrobenius W hq).symm.le
  have h_a4X : ((-2 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₄ * X) :=
    ord_algebraMap_mul_ge W W.toAffine.a₄
      (ord_addPullback_x_negFrobenius W hq).symm.le
  -- Step 1: ord(X³ + a₂X²) = -6.
  have step1 : (W_smooth W).ordAtInfty
      (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2) =
      ((-6 : ℤ) : WithTop ℤ) := by
    have h_lt : (W_smooth W).ordAtInfty (X ^ 3) <
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₂ * X ^ 2) := by
      rw [h_X3]
      refine lt_of_lt_of_le ?_ h_a2X2
      exact_mod_cast (by norm_num : (-6 : ℤ) < -4)
    exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans h_X3
  -- Step 2: ord((X³ + a₂X²) + a₄X) = -6.
  have step2 : (W_smooth W).ordAtInfty
      (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2 +
       algebraMap K KE W.toAffine.a₄ * X) =
      ((-6 : ℤ) : WithTop ℤ) := by
    have h_lt : (W_smooth W).ordAtInfty
        (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2) <
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₄ * X) := by
      rw [step1]
      refine lt_of_lt_of_le ?_ h_a4X
      exact_mod_cast (by norm_num : (-6 : ℤ) < -2)
    exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans step1
  -- Step 3: ord(((X³ + a₂X²) + a₄X) + a₆) = -6.
  have h_lt : (W_smooth W).ordAtInfty
      (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2 +
       algebraMap K KE W.toAffine.a₄ * X) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₆) := by
    rw [step2]
    refine lt_of_lt_of_le ?_ (ord_a₆_ge_zero W)
    show ((-6 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
    have : ((0 : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) := rfl
    rw [← this]
    exact_mod_cast (by norm_num : (-6 : ℤ) < 0)
  exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans step2

/-- `AddNonInverse W (negFrobeniusIsog W)` (inlined here to avoid forward
reference to `negFrobeniusIsog_addNonInverse`, which is defined later). -/
private theorem negFrobeniusIsog_addNonInverse_for_y_ord :
    AddNonInverse W (negFrobeniusIsog W) := by
  rintro ⟨h_x, _⟩
  rw [negFrobeniusIsog_pullback_x_gen] at h_x
  exact x_gen_ne_frobeniusIsog_pullback_x_gen W h_x

/-- **`ord_∞(addPullback_y W (-π)) = -3`** for `q ≥ 2` (any characteristic).

Mirror of `ord_addPullback_x_negFrobenius` for the y-coordinate. Strategy:
the curve equation `Y² + a₁·X·Y + a₃·Y = X³ + a₂·X² + a₄·X + a₆` (from
`addPullback_equation`) has RHS ord `= -6` (since `ord(X) = -2`); case
analysis on `ord(Y)` rules out `ord(Y) ≥ -2` (would give ord(LHS) `≥ -4 >
-6`) and `ord(Y) ≤ -4` (would give ord(LHS) `= 2 · ord(Y) ≤ -8 < -6`),
leaving `ord(Y) = -3`. -/
theorem ord_addPullback_y_negFrobenius (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty (addPullback_y W (negFrobeniusIsog W)) =
      ((-3 : ℤ) : WithTop ℤ) := by
  have hX_ord : (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)) =
      ((-2 : ℤ) : WithTop ℤ) := ord_addPullback_x_negFrobenius W hq
  have hX_ne : addPullback_x W (negFrobeniusIsog W) ≠ 0 :=
    addPullback_x_negFrobenius_ne_zero W hq
  -- Curve equation in standard form.
  have h_eq : addPullback_y W (negFrobeniusIsog W) ^ 2 +
              algebraMap K KE W.toAffine.a₁ *
                addPullback_x W (negFrobeniusIsog W) *
                addPullback_y W (negFrobeniusIsog W) +
              algebraMap K KE W.toAffine.a₃ *
                addPullback_y W (negFrobeniusIsog W) =
              addPullback_x W (negFrobeniusIsog W) ^ 3 +
              algebraMap K KE W.toAffine.a₂ *
                addPullback_x W (negFrobeniusIsog W) ^ 2 +
              algebraMap K KE W.toAffine.a₄ *
                addPullback_x W (negFrobeniusIsog W) +
              algebraMap K KE W.toAffine.a₆ := by
    have h := addPullback_equation (negFrobeniusIsog_addNonInverse_for_y_ord W)
    rw [WeierstrassCurve.Affine.equation_iff] at h
    exact h
  -- ord(LHS) = ord(RHS) = -6.
  have h_lhs_ord : (W_smooth W).ordAtInfty
        (addPullback_y W (negFrobeniusIsog W) ^ 2 +
         algebraMap K KE W.toAffine.a₁ *
           addPullback_x W (negFrobeniusIsog W) *
           addPullback_y W (negFrobeniusIsog W) +
         algebraMap K KE W.toAffine.a₃ *
           addPullback_y W (negFrobeniusIsog W)) =
      ((-6 : ℤ) : WithTop ℤ) :=
    h_eq ▸ ord_RHS_negFrobenius W hq
  -- Case 1: rule out Y = 0.
  have hY_ne : addPullback_y W (negFrobeniusIsog W) ≠ 0 := by
    intro h
    have h_zero : addPullback_y W (negFrobeniusIsog W) ^ 2 +
        algebraMap K KE W.toAffine.a₁ *
          addPullback_x W (negFrobeniusIsog W) *
          addPullback_y W (negFrobeniusIsog W) +
        algebraMap K KE W.toAffine.a₃ *
          addPullback_y W (negFrobeniusIsog W) = 0 := by rw [h]; ring
    have h_ord_eq : (W_smooth W).ordAtInfty
        (addPullback_y W (negFrobeniusIsog W) ^ 2 +
         algebraMap K KE W.toAffine.a₁ *
           addPullback_x W (negFrobeniusIsog W) *
           addPullback_y W (negFrobeniusIsog W) +
         algebraMap K KE W.toAffine.a₃ *
           addPullback_y W (negFrobeniusIsog W)) = ⊤ :=
      (congrArg (W_smooth W).ordAtInfty h_zero).trans (W_smooth W).ordAtInfty_zero
    exact WithTop.top_ne_coe (h_ord_eq.symm.trans h_lhs_ord)
  -- Extract m = ord(Y) as integer.
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (W_smooth W).ordAtInfty (addPullback_y W (negFrobeniusIsog W)) =
        ((m : ℤ) : WithTop ℤ) := by
    have h_ne_top : (W_smooth W).ordAtInfty
        (addPullback_y W (negFrobeniusIsog W)) ≠ ⊤ :=
      ((W_smooth W).ordAtInfty_eq_top_iff _).not.mpr hY_ne
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h_ne_top
    exact ⟨m, hm.symm⟩
  -- Y² has ord 2m.
  have hY_sq_ord : (W_smooth W).ordAtInfty
      (addPullback_y W (negFrobeniusIsog W) ^ 2) =
      ((2 * m : ℤ) : WithTop ℤ) :=
    (W_smooth W).ord_pow_concrete hY_ne m 2 hm
  -- ord(X·Y) = -2 + m.
  have h_xy_ord : (W_smooth W).ordAtInfty
      (addPullback_x W (negFrobeniusIsog W) *
        addPullback_y W (negFrobeniusIsog W)) =
      (((-2 + m : ℤ)) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul hX_ne hY_ne).trans ?_
    rw [hX_ord, hm]
    push_cast; rfl
  -- Step (a): show m ≤ -3 by contradiction.
  have h_m_le : m ≤ -3 := by
    by_contra h_not_le
    push Not at h_not_le
    have h_m_ge : -2 ≤ m := by omega
    have h_y_sq_ge : ((-4 : ℤ) : WithTop ℤ) ≤
        (W_smooth W).ordAtInfty
          (addPullback_y W (negFrobeniusIsog W) ^ 2) := by
      rw [hY_sq_ord]
      exact_mod_cast (by linarith : (-4 : ℤ) ≤ 2 * m)
    have h_a1xy_ge : ((-4 : ℤ) : WithTop ℤ) ≤
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁ *
          addPullback_x W (negFrobeniusIsog W) *
          addPullback_y W (negFrobeniusIsog W)) := by
      have h_assoc : algebraMap K KE W.toAffine.a₁ *
          addPullback_x W (negFrobeniusIsog W) *
          addPullback_y W (negFrobeniusIsog W) =
          algebraMap K KE W.toAffine.a₁ *
          (addPullback_x W (negFrobeniusIsog W) *
            addPullback_y W (negFrobeniusIsog W)) := by ring
      rw [h_assoc]
      refine ord_algebraMap_mul_ge W W.toAffine.a₁ ?_
      rw [h_xy_ord]
      exact_mod_cast (by linarith : (-4 : ℤ) ≤ -2 + m)
    have h_a3y_ge : ((-4 : ℤ) : WithTop ℤ) ≤
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ *
          addPullback_y W (negFrobeniusIsog W)) := by
      refine ord_algebraMap_mul_ge W W.toAffine.a₃ ?_
      rw [hm]
      exact_mod_cast (by linarith : (-4 : ℤ) ≤ m)
    have h_lhs_ge : ((-4 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (addPullback_y W (negFrobeniusIsog W) ^ 2 +
         algebraMap K KE W.toAffine.a₁ *
           addPullback_x W (negFrobeniusIsog W) *
           addPullback_y W (negFrobeniusIsog W) +
         algebraMap K KE W.toAffine.a₃ *
           addPullback_y W (negFrobeniusIsog W)) :=
      ord_add_ge_of_both_ge W
        (ord_add_ge_of_both_ge W h_y_sq_ge h_a1xy_ge) h_a3y_ge
    rw [h_lhs_ord] at h_lhs_ge
    have h46 : (-4 : ℤ) ≤ -6 := by exact_mod_cast h_lhs_ge
    omega
  -- Step (b): from m ≤ -3, Y² strictly dominates LHS, so ord(LHS) = 2m.
  have h_a1xy_gt : (W_smooth W).ordAtInfty
      (addPullback_y W (negFrobeniusIsog W) ^ 2) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁ *
        addPullback_x W (negFrobeniusIsog W) *
        addPullback_y W (negFrobeniusIsog W)) := by
    have h_assoc : algebraMap K KE W.toAffine.a₁ *
        addPullback_x W (negFrobeniusIsog W) *
        addPullback_y W (negFrobeniusIsog W) =
        algebraMap K KE W.toAffine.a₁ *
        (addPullback_x W (negFrobeniusIsog W) *
          addPullback_y W (negFrobeniusIsog W)) := by ring
    rw [hY_sq_ord, h_assoc]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge W W.toAffine.a₁
      (n := (((-2 + m : ℤ)) : WithTop ℤ)) (le_of_eq h_xy_ord.symm))
    exact_mod_cast (by linarith : (2 * m : ℤ) < -2 + m)
  have h_a3y_gt : (W_smooth W).ordAtInfty
      (addPullback_y W (negFrobeniusIsog W) ^ 2) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ *
        addPullback_y W (negFrobeniusIsog W)) := by
    rw [hY_sq_ord]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge W W.toAffine.a₃
      (n := ((m : ℤ) : WithTop ℤ)) (le_of_eq hm.symm))
    exact_mod_cast (by linarith : (2 * m : ℤ) < m)
  have h_inner_eq : (W_smooth W).ordAtInfty
      (addPullback_y W (negFrobeniusIsog W) ^ 2 +
       algebraMap K KE W.toAffine.a₁ *
         addPullback_x W (negFrobeniusIsog W) *
         addPullback_y W (negFrobeniusIsog W)) =
      (W_smooth W).ordAtInfty (addPullback_y W (negFrobeniusIsog W) ^ 2) :=
    (W_smooth W).ordAtInfty_add_eq_of_lt h_a1xy_gt
  have h_a3y_gt' : (W_smooth W).ordAtInfty
      (addPullback_y W (negFrobeniusIsog W) ^ 2 +
       algebraMap K KE W.toAffine.a₁ *
         addPullback_x W (negFrobeniusIsog W) *
         addPullback_y W (negFrobeniusIsog W)) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ *
        addPullback_y W (negFrobeniusIsog W)) := h_inner_eq ▸ h_a3y_gt
  have h_outer_eq : (W_smooth W).ordAtInfty
      (addPullback_y W (negFrobeniusIsog W) ^ 2 +
       algebraMap K KE W.toAffine.a₁ *
         addPullback_x W (negFrobeniusIsog W) *
         addPullback_y W (negFrobeniusIsog W) +
       algebraMap K KE W.toAffine.a₃ *
         addPullback_y W (negFrobeniusIsog W)) =
      (W_smooth W).ordAtInfty (addPullback_y W (negFrobeniusIsog W) ^ 2) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt h_a3y_gt').trans h_inner_eq
  rw [h_outer_eq, hY_sq_ord] at h_lhs_ord
  -- Conclude m = -3.
  have h_2m : (2 * m : ℤ) = -6 := by exact_mod_cast h_lhs_ord
  rw [hm]
  have h_m_eq : m = -3 := by omega
  exact_mod_cast h_m_eq

/-! ### Day 3a: addPullbackAlgHom for the negFrobenius case

The existing `addPullbackAlgHom W α hxy hinj` construction
(`HasseWeil.AdditionPullback`) is generic over `α`. For HOLE D we want
this for `α = negFrobeniusIsog W`. The injectivity input
`hinj : Function.Injective (addCoordAlgHom hxy)` was generically
provided by a sorry-bearing `addCoordAlgHom_injective` chain (general-`α`
transcendence of `addPullback_x` resting on an open III.3.6 pole witness) —
that chain has since been **removed**; only the witness-parametric and
negFrobenius forms remain.

We ship `addPullbackAlgHom_negFrobenius_of_inj` as a **witness-parametric
form** taking the (axiom-clean) injectivity proof as a hypothesis.
Discharging this hypothesis axiom-clean for `α = negFrobeniusIsog W`
requires one of:

1. Closing Sorry 2 + Sorry 3 generically (~350 LOC, mathlib `minpoly`
   machinery).

2. A negFrobenius-specific σ-invariance argument: prove
   `(mulByInt W (-1)).pullback (addPullback_x W (negFrobeniusIsog W))
   = addPullback_x W (negFrobeniusIsog W)`. This says addPullback_x is
   fixed by the curve-negation involution `σ : K(E) → K(E)`. By Galois
   theory (K(E) over K(x) is degree-2, σ generates the Galois group),
   σ-fixed elements lie in `K(x) = F(x_gen)`, which discharges the
   `px ∉ F(x_gen)` case of the transcendence argument for the
   negFrobenius case. Then `addPullback_x_ne_const_negFrobenius`
   closes Case 1, completing the chain.

Path 2 is more focused (~100-200 LOC) and closes only what HOLE D
needs. The σ-invariance lemma proof structure: apply
`(mulByInt W (-1)).pullback` to the addX formula
`addPullback_x = L² + a₁L − a₂ − x_gen − π·x`, distribute the AlgHom
over operations, substitute known values:
* `(mulByInt W (-1)).pullback x_gen = x_gen` (`mulByInt_pullback_x_neg_one`).
* `(mulByInt W (-1)).pullback y_gen = −y_gen − a₁·x_gen − a₃`
  (`mulByInt_pullback_y_neg_one`).
* `(mulByInt W (-1)).pullback (π·x_gen) = π·x_gen` (since `π·x_gen
  = x_gen^q` and AlgHom preserves powers and fixes `x_gen`).
* `(mulByInt W (-1)).pullback (π·y_gen) = -π·y - a₁·π·x - a₃` (via
  Frobenius distributing over `−y − a₁·x − a₃` in char p, with
  `a^q = a` in `K = F_q`).

Substituting and using `(σ(L_neg)+L_neg) = -a₁` (a curve-arithmetic
identity, computable via `field_simp; ring` after the algebra-hom
rewrites), we get `σ(L_neg² + a₁·L_neg) = L_neg² + a₁·L_neg`. The
remaining terms in addPullback_x (`a₂`, `x_gen`, `π·x_gen`) are all
σ-fixed. So addPullback_x is σ-invariant. ∎ -/

/-- Witness-parametric `addPullbackAlgHom` for `α = negFrobeniusIsog W`,
parametric on the `addCoordAlgHom hxy`-injectivity hypothesis. Once
that hypothesis is dischargeable axiom-clean (via Path 2 above or
Sorry 2 + Sorry 3 closure), the resulting algebra-hom feeds the
`isogOneSub` placeholder replacement and closes HOLE D. -/
noncomputable def addPullbackAlgHom_negFrobenius_of_inj
    (hxy : AddNonInverse W (negFrobeniusIsog W))
    (hinj : Function.Injective (addCoordAlgHom hxy)) : KE →ₐ[K] KE :=
  addPullbackAlgHom hxy hinj

/-! ### σ-invariance lemmas (Path 2 to discharge `hinj` axiom-clean) -/

/-- **σ-invariance Step 1**:
`σ(π·y_gen) = (negFrobeniusIsog W).pullback (y_gen W)` where
`σ = (mulByInt W (-1)).pullback`.

Algebraic content: applying the `[-1]`-pullback to `π·y_gen = y_gen^q`
gives `((-y_gen − a₁·x_gen − a₃))^q`. Frobenius is a ring hom, so
distributes over `+`, `−`, `*`, and fixes K-image (so `a^q = a` for
`a ∈ K`). The result equals `−y_gen^q − a₁·x_gen^q − a₃`, which by
`negFrobeniusIsog_pullback_y_gen` is exactly `(negFrobeniusIsog W).pullback
(y_gen W)`. -/
theorem sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y :
    (mulByInt W.toAffine (-1)).pullback ((frobeniusIsog W).pullback (y_gen W)) =
      (negFrobeniusIsog W).pullback (y_gen W) := by
  rw [frobeniusIsog_pullback_apply, map_pow, mulByInt_pullback_y_neg_one,
      negFrobeniusIsog_pullback_y_gen]
  -- Goal: (-y - a₁·x - a₃)^q = -frob.pb y - a₁·frob.pb x - a₃
  -- Convert LHS via ← frobeniusIsog_pullback_apply to `frob.pb(...)`, then
  -- distribute the AlgHom and the algebraMap K KE coefficients fix.
  rw [← frobeniusIsog_pullback_apply W
        (-y_gen W - algebraMap K KE W.toAffine.a₁ * x_gen W -
         algebraMap K KE W.toAffine.a₃)]
  simp only [map_sub, map_neg, map_mul,
    AlgHom.commutes (frobeniusIsog W).pullback]

/-- **σ-invariance helper**: `σ(π·x_gen) = π·x_gen`. Since `π·x_gen = x_gen^q`
and `σ` is an AlgHom that fixes `x_gen` (`mulByInt_pullback_x_neg_one`),
σ preserves `x_gen^q = π·x_gen`. -/
theorem sigma_frobenius_pullback_x_eq :
    (mulByInt W.toAffine (-1)).pullback ((frobeniusIsog W).pullback (x_gen W)) =
      (frobeniusIsog W).pullback (x_gen W) := by
  rw [frobeniusIsog_pullback_apply, map_pow, mulByInt_pullback_x_neg_one,
      ← frobeniusIsog_pullback_apply W (x_gen W)]

/-- **σ-invariance Step 1' (symmetric companion)**: `σ(negFrob.pb y_gen) =
π·y_gen = (frobeniusIsog W).pullback (y_gen W)`.

Direct from Step 1 by applying σ as an involution: distribute σ over the
explicit form of `negFrob.pb y_gen = -π·y - a₁·π·x - a₃`, use Step 1 to
substitute `σ(π·y) = negFrob.pb y` and the x-helper for `σ(π·x) = π·x`,
then expand `negFrob.pb y` again and `ring`-cancel. -/
theorem sigma_negFrobenius_pullback_y_eq_frobenius_pullback_y :
    (mulByInt W.toAffine (-1)).pullback ((negFrobeniusIsog W).pullback (y_gen W)) =
      (frobeniusIsog W).pullback (y_gen W) := by
  rw [negFrobeniusIsog_pullback_y_gen]
  simp only [map_sub, map_neg, map_mul,
    AlgHom.commutes (mulByInt W.toAffine (-1)).pullback]
  rw [sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y,
      sigma_frobenius_pullback_x_eq, negFrobeniusIsog_pullback_y_gen]
  ring

/-- **σ-invariance Step 2**: `σ(L_neg) + L_neg = -a₁` where
`L_neg = addSlope W (negFrobeniusIsog W)`. The curve-arithmetic identity
that drives σ-invariance of `addPullback_x`.

Proof: `L_neg = (y - negFrob.pb y) / (x - negFrob.pb x)` (slope formula).
Apply σ via `map_div₀` (σ is an AlgHom on the field). σ acts on each
piece via the four σ-pullback identities (`mulByInt_pullback_y_neg_one`,
`mulByInt_pullback_x_neg_one`, Step 1', x-helper). After substitution
and using `negFrob.pb x_gen = (frobeniusIsog W).pullback (x_gen W)` from
`negFrobeniusIsog_pullback_x_gen`, the numerator collapses via
`field_simp + ring` to `-a₁ · (x - π·x) / (x - π·x) = -a₁`. -/
theorem addSlope_negFrobenius_sigma_sum_eq_neg_a1 :
    (mulByInt W.toAffine (-1)).pullback (addSlope W (negFrobeniusIsog W)) +
      addSlope W (negFrobeniusIsog W) =
      -algebraMap K KE W.toAffine.a₁ := by
  have h_pix_eq : x_gen W - (frobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero W
  rw [addSlope_negFrobeniusIsog_eq, map_div₀]
  -- Distribute σ via simp + reduce all `negFrob.pb` and `σ(...)` to
  -- `frob.pb` form via the σ-invariance pair lemmas + the pullback
  -- equalities + AlgHom distribution.
  simp only [map_sub, map_neg, map_mul,
    mulByInt_pullback_x_neg_one, mulByInt_pullback_y_neg_one,
    AlgHom.commutes (mulByInt W.toAffine (-1)).pullback,
    sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y,
    sigma_frobenius_pullback_x_eq,
    negFrobeniusIsog_pullback_x_gen,
    negFrobeniusIsog_pullback_y_gen]
  -- Now all expressions are in terms of `frob.pb x_gen` and `frob.pb y_gen`,
  -- with a common denominator `x - π·x`.
  field_simp
  ring

/-- **σ-invariance Step 3 (final)**: `σ(addPullback_x W (negFrobeniusIsog W))
= addPullback_x W (negFrobeniusIsog W)`. The full σ-invariance of the
addition-pullback for `α = -π`.

Proof: `addPullback_x = L² + a₁·L − a₂ − x_gen − negFrob.pb x_gen` (the
addX formula). Apply σ:
* `σ(a₂) = a₂`, `σ(x_gen) = x_gen` (AlgHom commutes with K, fixes x_gen).
* `σ(negFrob.pb x_gen) = negFrob.pb x_gen` (since `negFrob.pb x_gen
  = π·x_gen` and σ fixes π·x_gen by `sigma_frobenius_pullback_x_eq`).
* `σ(L)² + a₁·σ(L) = L² + a₁·L`: from Step 2, `σ(L) = -L - a₁`, so
  `σ(L)² = (L + a₁)²` and the expression collapses by `ring` after
  substitution. -/
theorem addPullback_x_negFrobenius_sigma_invariant :
    (mulByInt W.toAffine (-1)).pullback (addPullback_x W (negFrobeniusIsog W)) =
      addPullback_x W (negFrobeniusIsog W) := by
  unfold addPullback_x WeierstrassCurve.Affine.addX
  -- Lift `(W_KE W).toAffine.a_i` to `algebraMap K KE W.toAffine.a_i` form
  -- so AlgHom.commutes fires consistently in the simp set below.
  have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  rw [h_a1, h_a2]
  simp only [map_sub, map_add, map_mul, map_pow,
    AlgHom.commutes (mulByInt W.toAffine (-1)).pullback,
    mulByInt_pullback_x_neg_one,
    negFrobeniusIsog_pullback_x_gen,
    sigma_frobenius_pullback_x_eq]
  -- After simp, goal reduces to σ(L)² + a₁·σ(L) = L² + a₁·L (the addX core).
  -- Use Step 2's σ(L) + L = -a₁ to substitute σ(L) = -L - a₁ and `ring` closes.
  have h := addSlope_negFrobenius_sigma_sum_eq_neg_a1 W
  linear_combination
    ((mulByInt W.toAffine (-1)).pullback (addSlope W (negFrobeniusIsog W)) -
      addSlope W (negFrobeniusIsog W)) * h

/-! ### Galois group identification: {1, σ} on K(E)/K(x)

Day 3a-final opener. To deduce that σ-fixed elements lie in K(x), we
need to know that {1, σ} is the full Galois group of K(E)/K(x).

The two structural facts:
* σ has order 2: `σ ∘ σ = id` (since `[-1] ∘ [-1] = [1]` as isogenies).
* σ fixes K(x): the algebraMap `FractionRing F[X] → KE` factors
  through `x_gen`, which σ fixes.

Combined with `[K(E) : K(x)] = 2`, this is the full Galois group. -/

/-- **σ has order 2**: `(mulByInt W (-1)).pullback.comp (mulByInt W (-1)).pullback
= AlgHom.id`. The Galois-group order-2 statement, derived from the isogeny
identity `[-1] ∘ [-1] = [1]` (`mulByInt_comp_eq_mul`) plus
`mulByInt_one_pullback_eq_id`. -/
theorem mulByInt_neg_one_pullback_comp_self :
    (mulByInt W.toAffine (-1)).pullback.comp (mulByInt W.toAffine (-1)).pullback =
      AlgHom.id K KE := by
  -- Step A: at the isogeny level, `[-1] ∘ [-1] = [1]`.
  have h_comp : (mulByInt W.toAffine (-1)).comp (mulByInt W.toAffine (-1)) =
      mulByInt W.toAffine 1 := by
    have := mulByInt_comp_eq_mul W (-1) (-1)
      (by norm_num : (-1 : ℤ) ≠ 0) (by norm_num : (-1 : ℤ) ≠ 0)
      (by norm_num : (-1 : ℤ) * (-1) ≠ 0)
    rw [this]
    norm_num
  -- Step B: take pullbacks of both sides. `Isogeny.comp`'s pullback
  -- is `φ.pullback.comp ψ.pullback` (contravariant), and `mulByInt 1`'s
  -- pullback is `AlgHom.id` by `mulByInt_one_pullback_eq_id`.
  have h_pb : ((mulByInt W.toAffine (-1)).comp (mulByInt W.toAffine (-1))).pullback =
      (mulByInt W.toAffine 1).pullback := congrArg Isogeny.pullback h_comp
  rw [show ((mulByInt W.toAffine (-1)).comp (mulByInt W.toAffine (-1))).pullback =
        (mulByInt W.toAffine (-1)).pullback.comp (mulByInt W.toAffine (-1)).pullback
        from rfl] at h_pb
  rw [h_pb, mulByInt_one_pullback_eq_id]

/-- **σ ∘ σ = id pointwise**: for any `z ∈ KE`,
`(mulByInt W (-1)).pullback ((mulByInt W (-1)).pullback z) = z`. -/
theorem mulByInt_neg_one_pullback_pow_two_apply (z : KE) :
    (mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine (-1)).pullback z) =
      z := by
  have h := mulByInt_neg_one_pullback_comp_self W
  exact congrArg (· z) h

/-! ### Galois-fixed-field consequence

To deduce that σ-fixed elements live in `K(x_gen)`, we need σ to be the
non-trivial element of `Gal(K(E)/K(x_gen))`. The key fact: σ ≠ id.

In characteristic ≠ 2 this is immediate from `σ(y) = -y - a₁·x - a₃` (the `-y`
forces non-triviality). In characteristic 2 we need the discriminant: a curve
with `a₁ = a₃ = 0` would have `Δ = 0` (by `Δ_of_char_two`), contradicting
`[IsElliptic]`. -/

/-- **σ ≠ id in characteristic 2**: the curve-negation involution
`σ = (mulByInt W (-1)).pullback` does not fix `y_gen`.

Proof: `σ(y) = -y - a₁·x - a₃`. If `σ(y) = y` then `2y + a₁·x + a₃ = 0`,
which in char 2 reduces to `a₁·x + a₃ = 0`. Transcendence of `x_gen`
over `K` forces `a₁ = 0` and `a₃ = 0`. But then `Δ_of_char_two` gives
`Δ = 0`, contradicting `[IsElliptic]`. -/
theorem mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_two
    [CharP K 2] :
    (mulByInt W.toAffine (-1)).pullback (y_gen W) ≠ y_gen W := by
  intro h_eq
  rw [mulByInt_pullback_y_neg_one] at h_eq
  -- In char 2: `(2 : KE) = 0` via the algebra map `K → KE`.
  have h_two_K : (2 : K) = 0 := by
    have h := CharP.cast_eq_zero (R := K) 2
    exact_mod_cast h
  have h_two_KE : (2 : KE) = 0 := by
    have h : algebraMap K KE 2 = algebraMap K KE 0 := by rw [h_two_K]
    rw [map_ofNat, map_zero] at h
    exact h
  -- σ(y) = y → -y - a₁x - a₃ = y → 2y + a₁x + a₃ = 0 → in char 2: a₁x + a₃ = 0.
  have h_lin : algebraMap K KE W.toAffine.a₁ * x_gen W +
      algebraMap K KE W.toAffine.a₃ = 0 := by
    linear_combination -h_eq - y_gen W * h_two_KE
  -- Use `x_gen` transcendental to extract `a₁ = 0` and `a₃ = 0`.
  have h_aeval : Polynomial.aeval (x_gen W)
      (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) = 0 := by
    rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
    exact h_lin
  have h_poly_zero :
      (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃ :
        Polynomial K) = 0 :=
    transcendental_iff.mp (x_gen_transcendental W) _ h_aeval
  have h_a1 : W.toAffine.a₁ = 0 := by
    have h := congr_arg (Polynomial.coeff · 1) h_poly_zero
    simpa using h
  have h_a3 : W.toAffine.a₃ = 0 := by
    have h := congr_arg (Polynomial.coeff · 0) h_poly_zero
    simpa using h
  -- `[IsElliptic]` in char 2 with `a₁ = a₃ = 0` forces `Δ = 0`. Contradiction.
  have h_delta : W.toAffine.Δ = 0 := by
    rw [WeierstrassCurve.Δ_of_char_two, h_a1, h_a3]; ring
  exact W.toAffine.isUnit_Δ.ne_zero h_delta

/-- The image of `C a₁ * X + C a₃` under `K[X] → KE` is `a₁ · x_gen + a₃`. -/
private lemma algebraMap_C_a1_X_plus_C_a3 :
    algebraMap (Polynomial K) KE
        (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) =
      algebraMap K KE W.toAffine.a₁ * x_gen W + algebraMap K KE W.toAffine.a₃ := by
  have h_x_alg : x_gen W = algebraMap (Polynomial K) KE Polynomial.X := by
    show algebraMap W.toAffine.CoordinateRing KE
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) = _
    exact (IsScalarTower.algebraMap_apply (Polynomial K) W.toAffine.CoordinateRing KE
      Polynomial.X).symm
  have h_C : ∀ a : K, algebraMap (Polynomial K) KE (Polynomial.C a) = algebraMap K KE a := by
    intro a; rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [map_add, map_mul, ← h_x_alg, h_C, h_C]

/-- Injectivity of `K → Frac(K[X])` on `2`: if `(2 : Frac(K[X])) = 0` then `(2 : K) = 0`. -/
private lemma two_K_eq_zero_of_two_fractionRing
    (h : (2 : FractionRing (Polynomial K)) = 0) : (2 : K) = 0 := by
  have h_alg_inj : Function.Injective (algebraMap K (FractionRing (Polynomial K))) :=
    FaithfulSMul.algebraMap_injective K (FractionRing (Polynomial K))
  apply h_alg_inj
  rw [map_zero, map_ofNat]
  exact h

/-- **σ ≠ id in characteristic ≠ 2**: in char ≠ 2, the curve-negation involution
σ does not fix `y_gen`.

Proof: If `σ(y) = y`, then `2y + a₁·x + a₃ = 0` in `KE`. View this as a basis
decomposition `(a₁·x + a₃) • 1 + 2 • y_gen = 0` in the `Frac(K[X])`-basis
`{1, y_gen}` of `KE`. By `decomp_zero_iff`, both coefficients vanish. The
`y_gen`-coefficient is `2`, so `(2 : Frac(K[X])) = 0`, which forces `(2 : K) = 0`
by injectivity of `K → Frac(K[X])`, contradicting char ≠ 2. -/
theorem mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_ne_two
    (h2 : (2 : K) ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback (y_gen W) ≠ y_gen W := by
  intro h_eq
  rw [mulByInt_pullback_y_neg_one] at h_eq
  have h_y_eq : (W_smooth W).coordYInFunctionField = y_gen W := by
    rw [← (W_smooth W).coordY_eq_coordYInFunctionField, coordY_W_smooth_eq_y_gen]
  -- View `2 y_gen + (a₁·x + a₃) = 0` as a vanishing decomposition in the
  -- `Frac(K[X])`-basis `{1, y_gen}` of KE; `decomp_zero_iff` then forces the
  -- `y_gen`-coefficient `(2 : Frac(K[X]))` to vanish.
  set p : FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K))
      (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) with hp_def
  set q : FractionRing (Polynomial K) := (2 : FractionRing (Polynomial K)) with hq_def
  have h_zero_smul :
      p • (1 : (W_smooth W).FunctionField) +
        q • (W_smooth W).coordYInFunctionField = 0 := by
    show p • (1 : KE) + q • y_gen W = (0 : KE)
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [hp_def, ← IsScalarTower.algebraMap_apply (Polynomial K)
        (FractionRing (Polynomial K)) KE, algebraMap_C_a1_X_plus_C_a3 W]
    rw [hq_def, map_ofNat]
    linear_combination -h_eq
  obtain ⟨_, hq_zero⟩ := (W_smooth W).decomp_zero_iff h_zero_smul
  exact h2 (two_K_eq_zero_of_two_fractionRing hq_zero)

/-- **σ ≠ id (unified)**: in any characteristic, the curve-negation involution
`σ = (mulByInt W (-1)).pullback` does not fix `y_gen`.

Combines the char-2 case (`mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_two`)
and the char ≠ 2 case (`mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_ne_two`)
via case-split on `(2 : K) = 0`. -/
theorem mulByInt_neg_one_pullback_y_gen_ne_y_gen :
    (mulByInt W.toAffine (-1)).pullback (y_gen W) ≠ y_gen W := by
  by_cases h2 : (2 : K) = 0
  · -- Char 2 case via `[CharP K 2]` derived from `h2`.
    haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_two W
  · -- Char ≠ 2 case directly.
    exact mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_ne_two W h2

/-! ### Path 2 Step 3 helper: σ fixes K-image

A small first piece toward σ-fixed → K(x): σ commutes with the constant
embedding `K → K(E)`. -/

/-- σ fixes the image of `K → K(E)`: for any `c : K`,
`σ(algebraMap c) = algebraMap c`. Immediate from σ being a `K`-algebra hom. -/
@[simp] theorem mulByInt_neg_one_pullback_algebraMap_K (c : K) :
    (mulByInt W.toAffine (-1)).pullback (algebraMap K KE c) =
      algebraMap K KE c :=
  AlgHom.commutes (mulByInt W.toAffine (-1)).pullback c

/-- σ fixes `algebraMap (Polynomial K) KE p` for any polynomial `p`.
Using `algebraMap p = aeval x_gen p` (via algebra-hom uniqueness on the
generator `X ↦ x_gen`) plus σ commutes with `aeval` and σ fixes `x_gen`. -/
theorem mulByInt_neg_one_pullback_algebraMap_polyK (p : Polynomial K) :
    (mulByInt W.toAffine (-1)).pullback
        (algebraMap (Polynomial K) KE p) =
      algebraMap (Polynomial K) KE p := by
  have h_x_alg : algebraMap (Polynomial K) KE Polynomial.X = x_gen W := by
    show algebraMap (Polynomial K) KE Polynomial.X =
      algebraMap W.toAffine.CoordinateRing KE
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)
    exact IsScalarTower.algebraMap_apply (Polynomial K) W.toAffine.CoordinateRing KE
      Polynomial.X
  -- Two K-algebra homs K[X] →ₐ[K] KE that agree on X are equal.
  have h_alg_eq : (IsScalarTower.toAlgHom K (Polynomial K) KE) =
      Polynomial.aeval (x_gen W) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    exact h_x_alg
  have h_eval : algebraMap (Polynomial K) KE p = Polynomial.aeval (x_gen W) p := by
    have := congrArg (fun (φ : Polynomial K →ₐ[K] KE) ↦ φ p) h_alg_eq
    simpa using this
  rw [h_eval, ← Polynomial.aeval_algHom_apply, mulByInt_pullback_x_neg_one]

/-- σ fixes the image of `Frac(K[X]) → K(E)`: for any `r ∈ Frac(K[X])`,
`σ(algebraMap r) = algebraMap r`. Lifts `mulByInt_neg_one_pullback_algebraMap_polyK`
via `IsLocalization.surj` denominator clearing. -/
theorem mulByInt_neg_one_pullback_algebraMap_kx
    (r : FractionRing (Polynomial K)) :
    (mulByInt W.toAffine (-1)).pullback
        (algebraMap (FractionRing (Polynomial K)) KE r) =
      algebraMap (FractionRing (Polynomial K)) KE r := by
  -- r = num/den via IsLocalization.surj.
  obtain ⟨⟨num, ⟨den, hden_mem⟩⟩, h_pd⟩ :=
    IsLocalization.surj (nonZeroDivisors (Polynomial K)) r
  have hden_ne : den ≠ 0 := nonZeroDivisors.ne_zero hden_mem
  have hden_alg_ne : algebraMap (Polynomial K) (FractionRing (Polynomial K)) den ≠ 0 :=
    fun h ↦ hden_ne (FaithfulSMul.algebraMap_injective _ _ (h.trans (map_zero _).symm))
  have h_r_eq : r = algebraMap (Polynomial K) (FractionRing (Polynomial K)) num *
      (algebraMap (Polynomial K) (FractionRing (Polynomial K)) den)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hden_alg_ne]; exact h_pd
  -- Push through algebraMap, then use the polynomial helper twice.
  have h_num_lift : algebraMap (FractionRing (Polynomial K)) KE
      (algebraMap (Polynomial K) (FractionRing (Polynomial K)) num) =
      algebraMap (Polynomial K) KE num :=
    (IsScalarTower.algebraMap_apply (Polynomial K) (FractionRing (Polynomial K)) KE num).symm
  have h_den_lift : algebraMap (FractionRing (Polynomial K)) KE
      (algebraMap (Polynomial K) (FractionRing (Polynomial K)) den) =
      algebraMap (Polynomial K) KE den :=
    (IsScalarTower.algebraMap_apply (Polynomial K) (FractionRing (Polynomial K)) KE den).symm
  rw [h_r_eq, map_mul, map_inv₀, h_num_lift, h_den_lift, map_mul, map_inv₀,
    mulByInt_neg_one_pullback_algebraMap_polyK W num,
    mulByInt_neg_one_pullback_algebraMap_polyK W den]

/-! ### Path 2 Step 3 Piece 3b: σ acts on coordY -/

/-- σ acts on `y_gen` as `-y_gen - a₁·x - a₃`. (Re-statement of
`mulByInt_pullback_y_neg_one` for use with the basis decomposition machinery.) -/
theorem mulByInt_neg_one_pullback_y_gen_eq :
    (mulByInt W.toAffine (-1)).pullback (y_gen W) =
      -y_gen W - algebraMap K KE W.toAffine.a₁ * x_gen W -
      algebraMap K KE W.toAffine.a₃ :=
  mulByInt_pullback_y_neg_one W

/-! ### Path 2 Step 3 Piece 3c helpers -/

/-- The polynomial `a₁ X + a₃` is nonzero in characteristic 2 for an elliptic
curve. If it were zero, then `a₁ = a₃ = 0`, and `Δ_of_char_two` would give
`Δ = 0`, contradicting `[IsElliptic]`. -/
theorem a₁X_plus_a₃_ne_zero_char_two [CharP K 2] :
    (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃ :
      Polynomial K) ≠ 0 := by
  intro h
  have h_a1 : W.toAffine.a₁ = 0 := by
    have := congr_arg (Polynomial.coeff · 1) h
    simpa using this
  have h_a3 : W.toAffine.a₃ = 0 := by
    have := congr_arg (Polynomial.coeff · 0) h
    simpa using this
  have h_delta : W.toAffine.Δ = 0 := by
    rw [WeierstrassCurve.Δ_of_char_two, h_a1, h_a3]; ring
  exact W.toAffine.isUnit_Δ.ne_zero h_delta

/-- Image of the polynomial `a₁ X + a₃` under `K[X] → KE`: equals
`a₁ · x_gen + a₃` in `KE`. -/
theorem algebraMap_a₁X_plus_a₃ :
    algebraMap (Polynomial K) KE
        (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) =
      algebraMap K KE W.toAffine.a₁ * x_gen W + algebraMap K KE W.toAffine.a₃ := by
  have h_x_alg : algebraMap (Polynomial K) KE Polynomial.X = x_gen W := by
    show algebraMap (Polynomial K) KE Polynomial.X =
      algebraMap W.toAffine.CoordinateRing KE
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)
    exact IsScalarTower.algebraMap_apply (Polynomial K) W.toAffine.CoordinateRing KE
      Polynomial.X
  have h_C : ∀ c : K,
      algebraMap (Polynomial K) KE (Polynomial.C c) = algebraMap K KE c := by
    intro c; rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [map_add, map_mul, h_C, h_C, h_x_alg]

/-- Helper for Piece 3c: the σ-equation as a vanishing `{1, Y}`-decomposition.

If `f = a • 1 + b • Y` is fixed by `σ = (mulByInt W (-1)).pullback`, then applying
σ (which fixes `algebraMap` images and sends `Y ↦ -Y - a₁·x - a₃`) and rearranging
against the original decomposition yields
`(b·(a₁X+a₃)) • 1 + (2b) • Y = 0` in the `Frac(K[X])`-basis `{1, Y}` of `KE`. -/
private lemma sigma_fixed_decomp_coeffs_vanish {a b : FractionRing (Polynomial K)}
    {f : KE} (h_fixed : (mulByInt W.toAffine (-1)).pullback f = f)
    (h_decomp : f = a • (1 : KE) + b • y_gen W) :
    (b * algebraMap (Polynomial K) (FractionRing (Polynomial K))
        (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃)) •
        (1 : (W_smooth W).FunctionField) +
      (2 * b) • (W_smooth W).coordYInFunctionField = 0 := by
  -- `bXf` is the image of `a₁ X + a₃` in `Frac(K[X])`.
  set bXf : FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K))
      (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃)
    with hbXf
  have h_bXf_image_KE : algebraMap (FractionRing (Polynomial K)) KE bXf =
      algebraMap K KE W.toAffine.a₁ * x_gen W + algebraMap K KE W.toAffine.a₃ := by
    rw [hbXf, ← IsScalarTower.algebraMap_apply (Polynomial K)
      (FractionRing (Polynomial K)) KE]
    exact algebraMap_a₁X_plus_a₃ W
  -- Rewrite the decomposition and σ(f) into `y_gen`/`algebraMap` form.
  have h_decomp' : f =
      algebraMap (FractionRing (Polynomial K)) KE a +
      algebraMap (FractionRing (Polynomial K)) KE b * y_gen W := by
    rw [h_decomp]
    change a • (1 : KE) + b • y_gen W =
      algebraMap _ KE a + algebraMap _ KE b * y_gen W
    simp only [Algebra.smul_def, mul_one]
  have h_σf : (mulByInt W.toAffine (-1)).pullback f =
      algebraMap (FractionRing (Polynomial K)) KE a +
      algebraMap (FractionRing (Polynomial K)) KE b *
        (-y_gen W - algebraMap K KE W.toAffine.a₁ * x_gen W -
         algebraMap K KE W.toAffine.a₃) := by
    conv_lhs => rw [h_decomp']
    rw [map_add, map_mul,
      mulByInt_neg_one_pullback_algebraMap_kx,
      mulByInt_neg_one_pullback_algebraMap_kx,
      mulByInt_neg_one_pullback_y_gen_eq]
  -- Combine σ(f) = f into the vanishing basis decomposition.
  change (b * bXf) • (1 : KE) + (2 * b) • y_gen W = (0 : KE)
  rw [Algebra.smul_def, Algebra.smul_def, mul_one,
    map_mul, map_mul, h_bXf_image_KE, map_ofNat]
  have h_combine :
      algebraMap (FractionRing (Polynomial K)) KE a +
        algebraMap (FractionRing (Polynomial K)) KE b *
          (-y_gen W - algebraMap K KE W.toAffine.a₁ * x_gen W -
           algebraMap K KE W.toAffine.a₃) =
        algebraMap (FractionRing (Polynomial K)) KE a +
        algebraMap (FractionRing (Polynomial K)) KE b * y_gen W :=
    h_σf.symm.trans (h_fixed.trans h_decomp')
  linear_combination -h_combine

/-- Helper for Piece 3c: char-split forcing `b = 0`.

From the two vanishing coefficients of `sigma_fixed_decomp_coeffs_vanish`,
namely `b·(a₁X+a₃) = 0` and `2·b = 0` in `Frac(K[X])`, conclude `b = 0`.
In char 2, `a₁X + a₃ ≠ 0` (from `[IsElliptic]`, via `a₁X_plus_a₃_ne_zero_char_two`),
so the first equation gives `b = 0`; in char ≠ 2, `2 ≠ 0` in `Frac(K[X])`, so the
second does. -/
private lemma eq_zero_of_mul_a₁X_plus_a₃_and_two_mul_eq_zero
    {b : FractionRing (Polynomial K)}
    (hpb : b * algebraMap (Polynomial K) (FractionRing (Polynomial K))
        (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) = 0)
    (hqb : 2 * b = 0) : b = 0 := by
  by_cases h2 : (2 : K) = 0
  · -- Char 2: `a₁ X + a₃ ≠ 0`, so `b · (a₁X+a₃) = 0` forces `b = 0`.
    haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have h_bXf_ne : algebraMap (Polynomial K) (FractionRing (Polynomial K))
        (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) ≠ 0 :=
      fun h_eq ↦ a₁X_plus_a₃_ne_zero_char_two W
        (FaithfulSMul.algebraMap_injective (Polynomial K)
          (FractionRing (Polynomial K)) (h_eq.trans (map_zero _).symm))
    rcases mul_eq_zero.mp hpb with h | h
    · exact h
    · exact absurd h h_bXf_ne
  · -- Char ≠ 2: `2 ≠ 0` in `Frac(K[X])`, so `2 * b = 0` forces `b = 0`.
    have h_two_ne : (2 : FractionRing (Polynomial K)) ≠ 0 :=
      fun h_eq ↦ h2 (two_K_eq_zero_of_two_fractionRing h_eq)
    rcases mul_eq_zero.mp hqb with h | h
    · exact absurd h h_two_ne
    · exact h

/-! ### Path 2 Step 3 Piece 3c: σ-fixed implies in K(x) image

If `f ∈ K(E)` is fixed by the curve-negation involution `σ`, then `f` lies in
the image of `Frac(K[X]) → K(E)`. Combines the σ-action on the basis
decomposition `{1, Y}` (Pieces 0/1/2/3b) with `decomp_zero_iff` and a
char-split. -/

/-- **Path 2 Step 3 Piece 3c**: If `f ∈ KE` is fixed by `σ`, then
`f` is in the image of `algebraMap (Frac K[X]) KE`.

Proof: write `f = a • 1 + b • Y` via `exists_decomp`. Apply σ — it fixes
`algebraMap` images (Pieces 0/1/2) and sends `Y ↦ -Y - a₁·x - a₃`
(Piece 3b). The σ-equation rearranges to `(b·(a₁X+a₃)) • 1 + (2b) • Y = 0`,
and `decomp_zero_iff` gives `b·(a₁X+a₃) = 0` and `2b = 0`. Char-split:
in char ≠ 2, `2 ≠ 0` in `Frac(K[X])` so `b = 0`; in char 2,
`a₁X + a₃ ≠ 0` (from `[IsElliptic]`) so `b = 0`. Then `f = a • 1 = algebraMap a`. -/
theorem sigma_fixed_implies_in_KX_image
    (f : KE) (h_fixed : (mulByInt W.toAffine (-1)).pullback f = f) :
    ∃ a : FractionRing (Polynomial K),
      f = algebraMap (FractionRing (Polynomial K)) KE a := by
  obtain ⟨a, b, h_decomp⟩ := (W_smooth W).exists_decomp f
  -- It suffices to show b = 0; then f = a • 1 = algebraMap a.
  suffices h_b : b = 0 by
    refine ⟨a, ?_⟩
    rw [h_decomp, h_b, zero_smul, add_zero]
    change a • (1 : KE) = algebraMap (FractionRing (Polynomial K)) KE a
    rw [Algebra.smul_def, mul_one]
  -- σ-fixedness turns the decomposition into a vanishing `{1, Y}`-decomposition
  -- `(b·(a₁X+a₃)) • 1 + (2b) • Y = 0`; basis-independence then gives both
  -- coefficients zero, and a char-split forces `b = 0`.
  obtain ⟨hpb, hqb⟩ :=
    (W_smooth W).decomp_zero_iff (sigma_fixed_decomp_coeffs_vanish W h_fixed h_decomp)
  exact eq_zero_of_mul_a₁X_plus_a₃_and_two_mul_eq_zero W hpb hqb

/-! ### Path 2 Step 3 Piece 3d: addPullback_x_negFrobenius lies in K(x) -/

/-- **Path 2 Step 3 Piece 3d**: `addPullback_x W (negFrobeniusIsog W)` lies
in the image of `Frac(K[X]) → K(E)`. One-line consequence of
`sigma_fixed_implies_in_KX_image` applied to
`addPullback_x_negFrobenius_sigma_invariant`. -/
theorem addPullback_x_negFrobenius_in_KX_image :
    ∃ a : FractionRing (Polynomial K),
      addPullback_x W (negFrobeniusIsog W) =
        algebraMap (FractionRing (Polynomial K)) KE a :=
  sigma_fixed_implies_in_KX_image W _
    (addPullback_x_negFrobenius_sigma_invariant W)

/-! ### Path 2 Steps 4+5: addPullback_x_negFrobenius is transcendental

The consumer of `addPullback_x_negFrobenius_in_KX_image`. Combines that
witness with `algebraic_in_fracRing_eq_const` (algebraic-closure-of-K-in-K(x))
and `addPullback_x_ne_const_negFrobenius` (the non-constancy lemma) to
discharge transcendence axiom-clean for the `α = -π` case. -/

/-- **Path 2 Step 4+5 (axiom-clean closure of Sorry 2 for α = -π)**:
`addPullback_x W (negFrobeniusIsog W)` is transcendental over `K`.

Proof outline:
* By `addPullback_x_negFrobenius_in_KX_image` (Piece 3d): there exists
  `r : Frac(K[X])` with `addPullback_x = algebraMap _ KE r`.
* If `addPullback_x` were algebraic over `K`, so would `r` be (since
  `algebraMap _ KE` is injective and pulls back transcendence).
* By `algebraic_in_fracRing_eq_const`: an element of `Frac(K[X])` algebraic
  over `K` is the image of some `c ∈ K`, i.e., `r = algebraMap K _ c`.
* So `addPullback_x = algebraMap K KE c` (via the algebraMap tower
  `K → Frac(K[X]) → KE`).
* But `addPullback_x_ne_const_negFrobenius` (from `ord = -2 < 0`, the pole
  argument) rules this out. Contradiction. ∎ -/
theorem addPullback_x_transcendental_negFrobenius
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    Transcendental K (addPullback_x W (negFrobeniusIsog W)) := by
  intro h_alg
  obtain ⟨r, hr⟩ := addPullback_x_negFrobenius_in_KX_image W
  have h_inj : Function.Injective (algebraMap (FractionRing (Polynomial K)) KE) :=
    (algebraMap (FractionRing (Polynomial K)) KE).injective
  have hr_alg : IsAlgebraic K r := by
    by_contra h_trans
    have h_px_trans : Transcendental K (addPullback_x W (negFrobeniusIsog W)) := by
      rw [hr]
      exact (transcendental_algebraMap_iff h_inj).mpr h_trans
    exact h_px_trans h_alg
  obtain ⟨c, hc⟩ := algebraic_in_fracRing_eq_const r hr_alg
  have hc' : addPullback_x W (negFrobeniusIsog W) = algebraMap K KE c := by
    rw [hr, hc, ← IsScalarTower.algebraMap_apply K (FractionRing (Polynomial K)) KE]
  exact addPullback_x_ne_const_negFrobenius W hq hxy c hc'

/-! ### Day 3b: addCoordAlgHom injectivity for the negFrobenius case

Consumer of `addPullback_x_transcendental_negFrobenius` (Steps 4+5). Uses the
witness-parametric `addCoordAlgHom_injective_of_baseHom_inj` with the
unconditional base-hom injectivity below (the sorry-bearing generic
`addBaseHom_injective` has been removed). -/

/-- **Day 3b helper**: `addBaseHom W (negFrobeniusIsog W)` is injective.
Axiom-clean negFrobenius base-hom injectivity: rewrites the base-hom as
`Polynomial.aeval (addPullback_x W (negFrob W))` (`addBaseHom_eq_aeval`)
and applies `transcendental_iff_injective` to the unconditional
`addPullback_x_transcendental_negFrobenius`. -/
theorem addBaseHom_injective_negFrobenius
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    Function.Injective (addBaseHom W (negFrobeniusIsog W)) := by
  rw [addBaseHom_eq_aeval]
  exact transcendental_iff_injective.mp
    (addPullback_x_transcendental_negFrobenius W hq hxy)

/-- **Day 3b**: `addCoordAlgHom` for `α = negFrobeniusIsog W` is injective.
One-line consumer of `addCoordAlgHom_injective_of_baseHom_inj` and
`addBaseHom_injective_negFrobenius`. Closes one of the three sorries in HOLE D's
downstream chain axiom-clean.

Together with `addPullback_x_transcendental_negFrobenius` and Path 2 Step 3,
the negFrobenius `addCoordAlgHom`-injectivity is now fully
unconditional — the input needed by `addPullbackAlgHom_negFrobenius_of_inj`
to build a non-witness-parametric `addPullbackAlgHom_negFrobenius`. -/
theorem addCoordAlgHom_injective_negFrobenius
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    Function.Injective (addCoordAlgHom hxy) :=
  addCoordAlgHom_injective_of_baseHom_inj hxy
    (addBaseHom_injective_negFrobenius W hq hxy)

/-! ### Day 3c Piece A: AddNonInverse witness + specialized addPullbackAlgHom

The negFrobenius variant of `addPullbackAlgHom` requires both
`AddNonInverse W (negFrobeniusIsog W)` and the corresponding injectivity
of `addCoordAlgHom`. Both are dischargeable axiom-clean: the non-inverse
condition reduces to `x_gen ≠ π·x_gen` (different orders at infinity),
and injectivity is `addCoordAlgHom_injective_negFrobenius` (c8b4b66). -/

/-- **Day 3c Piece A.1**: `AddNonInverse W (negFrobeniusIsog W)` holds
unconditionally. The negation hypothesis would require `x_gen W = π·x_gen`
(the first conjunct), which contradicts
`x_gen_ne_frobeniusIsog_pullback_x_gen` (their orders at infinity differ). -/
theorem negFrobeniusIsog_addNonInverse :
    AddNonInverse W (negFrobeniusIsog W) := by
  rintro ⟨h_x, _⟩
  rw [negFrobeniusIsog_pullback_x_gen] at h_x
  exact x_gen_ne_frobeniusIsog_pullback_x_gen W h_x

/-- **Day 3c Piece A.2**: Specialized `addPullbackAlgHom` for `α = negFrobenius`,
discharging both `AddNonInverse` (via `negFrobeniusIsog_addNonInverse`) and
`addCoordAlgHom`-injectivity (via `addCoordAlgHom_injective_negFrobenius`)
axiom-clean. The unconditional algebra hom corresponding to the rational
map `P ↦ P + (-π)(P) = P - π(P)` (i.e., `1 - π` on rational points). -/
noncomputable def addPullbackAlgHom_negFrobenius
    (hq : 2 ≤ Fintype.card K) : KE →ₐ[K] KE :=
  addPullbackAlgHom_negFrobenius_of_inj W
    (negFrobeniusIsog_addNonInverse W)
    (addCoordAlgHom_injective_negFrobenius W hq
      (negFrobeniusIsog_addNonInverse W))

/-! ### Day 3c Piece B: isogOneSub_negFrobenius (replacement for the placeholder)

The unconditional `1 − π` isogeny: pullback from `addPullbackAlgHom_negFrobenius`
(real addition pullback for `id + (-π)`), rational-point map from
`(AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom`. Replaces the
`isogOneSub (frobeniusIsog W)` placeholder (whose pullback was `AlgHom.id`)
with the mathematically correct pullback. -/

/-- **Day 3c Piece B**: The isogeny `1 − π` with the unconditional addition-formula
pullback. Built from `addPullbackAlgHom_negFrobenius` (the pullback for
`id + (−π) = 1 − π`) and the standard rational-point map
`(AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom`.

Mathematically this is `1 − π` with the correct pullback that the placeholder
`isogOneSub (frobeniusIsog W)` lacks (it uses `AlgHom.id` as a stub). HOLE D
wire-up consumes this directly via `Isogeny.toAlgebra`/`degree`. -/
noncomputable def isogOneSub_negFrobenius
    (hq : 2 ≤ Fintype.card K) : Isogeny W.toAffine W.toAffine where
  pullback := addPullbackAlgHom_negFrobenius W hq
  toAddMonoidHom := (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom

@[simp] theorem isogOneSub_negFrobenius_pullback (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).pullback =
      addPullbackAlgHom_negFrobenius W hq := rfl

@[simp] theorem isogOneSub_negFrobenius_toAddMonoidHom
    (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom := rfl

/-! ### Day 3c Piece C — REMOVED (2026-05-28 placeholder grind)

The bridge lemma `isogOneSub_negFrobenius_toAddMonoidHom_eq_oneSubFrobeniusIsog`
(genuine `1−π` and the placeholder agree on `toAddMonoidHom`) existed only to
transfer the placeholder's rational-point API to the genuine isogeny. All
consumers now prove their kernel/point-map facts directly on
`isogOneSub_negFrobenius` (its `toAddMonoidHom = id − frob`, frob's point map
is the identity), so the bridge is no longer needed and has been deleted as
part of removing the placeholder `oneSubFrobeniusIsog`. -/

/-! ### D3b base: `AddNonInversePair` for `(zsmul 1 π, mulByInt (-1))`

The `(r, s) = (1, 1)` specialisation of the genuine `(zsmul r π, mulByInt (-s))`
family that D3b/D4 will assemble into `genuineIsogSmulSub r s`. Both pullbacks
reduce on x-coord to `x_gen W` and `x_gen W ^ q` respectively via
`mulByInt_x_one` / `mulByInt_x_neg` / `frobeniusIsog_pullback_apply`; the
mismatch is `x_gen_ne_frobeniusIsog_pullback_x_gen`. -/

/-- The pair `((frobeniusIsog W).zsmul 1, mulByInt W (-1))` is non-inverse: the
x-coord pullbacks differ (`x_gen^q` vs `x_gen`, by Frobenius non-fixedness over
F_q). -/
theorem AddNonInversePair_zsmul_one_frobenius_mulByInt_neg_one :
    AddNonInversePair ((frobeniusIsog W).zsmul 1) (mulByInt W.toAffine (-1)) := by
  apply AddNonInversePair_of_x_ne
  have h_lhs : ((frobeniusIsog W).zsmul 1).pullback (x_gen W) =
      (x_gen W) ^ Fintype.card K := by
    show ((mulByInt W.toAffine 1).comp (frobeniusIsog W)).pullback (x_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    have h : (mulByInt W.toAffine 1).pullback (x_gen W) = x_gen W := by
      show (mulByInt W.toAffine 1).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
      rw [mulByInt_pullback_x W 1 one_ne_zero, mulByInt_x_one]
    rw [h, frobeniusIsog_pullback_apply]
  have h_rhs : (mulByInt W.toAffine (-1)).pullback (x_gen W) = x_gen W := by
    show (mulByInt W.toAffine (-1)).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
    rw [mulByInt_pullback_x W (-1) (by norm_num), mulByInt_x_neg, mulByInt_x_one]
  rw [h_lhs, h_rhs]
  intro h
  have hne := x_gen_ne_frobeniusIsog_pullback_x_gen W
  rw [frobeniusIsog_pullback_apply] at hne
  exact hne h.symm

/-! ### D3b general consumer: AddNonInversePair for `(zsmul r π, mulByInt -s)`

Generalises the (1, 1) base case to arbitrary `(r, s) ≠ 0` (with `(r : K) ≠ 0`
and `(s : K) ≠ 0`). The x-coord pullbacks are `(mulByInt_x r)^q` (LHS) and
`mulByInt_x (-s)` (RHS); their orders at infinity are `-2q` and `-2` respectively
(via `ordAtInfty_mulByInt_x` from `OrdAtInftyBridge.lean:207` and
`ordAtInfty_pow`). For `q ≥ 2`, these are unequal, so the pullbacks are
unequal — Silverman III.6 reflection of Frobenius pole-multiplication. -/

/-- The `x_gen` pullback of `(frobeniusIsog W).zsmul r` is `(mulByInt_x W r) ^ |K|`
(Frobenius is the `|K|`-power map on the `[r]`-pullback). -/
private theorem zsmul_frobenius_pullback_x_gen (r : ℤ) (hr : r ≠ 0) :
    ((frobeniusIsog W).zsmul r).pullback (x_gen W) = (mulByInt_x W r) ^ Fintype.card K := by
  show ((mulByInt W.toAffine r).comp (frobeniusIsog W)).pullback (x_gen W) = _
  rw [Isogeny.comp_algebraMap_eq]
  have h_inner : (mulByInt W.toAffine r).pullback (x_gen W) = mulByInt_x W r := by
    show (mulByInt W.toAffine r).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
    exact mulByInt_pullback_x W r hr
  rw [h_inner, frobeniusIsog_pullback_apply]

/-- The `x_gen` pullback of `mulByInt W (-s)` is `mulByInt_x W (-s)`. -/
private theorem mulByInt_neg_pullback_x_gen (s : ℤ) (hs : s ≠ 0) :
    (mulByInt W.toAffine (-s)).pullback (x_gen W) = mulByInt_x W (-s) := by
  show (mulByInt W.toAffine (-s)).pullback
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
  exact mulByInt_pullback_x W (-s) (neg_ne_zero.mpr hs)

/-- The pair `((frobeniusIsog W).zsmul r, mulByInt W (-s))` is non-inverse for
`r, s ≠ 0` with `(r : K) ≠ 0`, `(s : K) ≠ 0`. The x-coord pullbacks differ at
`ord_∞`: LHS is `-2q`, RHS is `-2`. -/
theorem AddNonInversePair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    AddNonInversePair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) := by
  apply AddNonInversePair_of_x_ne
  rw [zsmul_frobenius_pullback_x_gen W r hr, mulByInt_neg_pullback_x_gen W s hs]
  intro h_eq
  -- Apply ordAtInfty and derive contradiction.
  have h_ord := congrArg (W_smooth W).ordAtInfty h_eq
  have h_pow_ord :
      (W_smooth W).ordAtInfty (mulByInt_x W r ^ Fintype.card K) =
        Fintype.card K • (W_smooth W).ordAtInfty (mulByInt_x W r) :=
    (W_smooth W).ordAtInfty_pow (mulByInt_x_ne_zero W r hr) (Fintype.card K)
  have h_neg_sK : ((-s : ℤ) : K) ≠ 0 := by push_cast; exact neg_ne_zero.mpr hsK
  rw [h_pow_ord, ordAtInfty_mulByInt_x W r hr hrK,
      ordAtInfty_mulByInt_x W (-s) (neg_ne_zero.mpr hs) h_neg_sK] at h_ord
  -- h_ord : (Fintype.card K) • ((-2 : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ).
  have h_smul_eq : (Fintype.card K : ℕ) • ((-2 : ℤ) : WithTop ℤ) =
      (((Fintype.card K : ℤ) * (-2) : ℤ) : WithTop ℤ) := by
    induction Fintype.card K with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, ih]
      rw [show (((k + 1 : ℕ) : ℤ) * -2 : ℤ) = ((k : ℤ) * -2) + (-2) from by push_cast; ring]
      push_cast
      rfl
  rw [h_smul_eq] at h_ord
  have h_int : (Fintype.card K : ℤ) * (-2) = (-2 : ℤ) := WithTop.coe_inj.mp h_ord
  have h_ge : (2 : ℤ) ≤ Fintype.card K := by
    exact_mod_cast Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  linarith

/-! ### D3c step 1: σ-action on `(mulByInt n)` pullbacks (generic in `n ≠ 0`)

For any nonzero `n`, σ commutes with `(mulByInt n).pullback`: their composition
on `x_gen` is `(mulByInt (-n)).pullback x_gen = mulByInt_x W (-n) = mulByInt_x W n`,
and on `y_gen` is the negY of the original.

Combines `mulByInt_comp_eq_mul` (commutativity at isogeny level) with the
explicit `mulByInt_x_neg` / `mulByInt_y_neg` symmetries. -/

/-- **[n] ∘ σ = [-n]** at the isogeny level for `n ≠ 0`. The composition
ordering needed for `σ.pullback ∘ [n].pullback` (since
`(ψ.comp φ).pullback = φ.pullback.comp ψ.pullback`). -/
private theorem mulByInt_comp_mulByInt_neg_one
    (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine n).comp (mulByInt W.toAffine (-1)) =
      mulByInt W.toAffine (-n) := by
  have h := mulByInt_comp_eq_mul W n (-1) hn (by norm_num : (-1 : ℤ) ≠ 0)
    (by simpa using neg_ne_zero.mpr hn)
  rw [h]; congr 1; ring

/-- **σ.pb fixes `(mulByInt n).pb x_gen`** for `n ≠ 0`. By `mulByInt`
commutativity, `σ.pb ([n].pb x_gen) = ([n].comp σ).pb x_gen
= (mulByInt (-n)).pb x_gen = mulByInt_x W (-n) = mulByInt_x W n` (the last by
`mulByInt_x_neg`). -/
theorem sigma_mulByInt_pullback_x_eq (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine n).pullback (x_gen W)) =
      (mulByInt W.toAffine n).pullback (x_gen W) := by
  have h_comp : (mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine n).pullback (x_gen W)) =
      ((mulByInt W.toAffine n).comp (mulByInt W.toAffine (-1))).pullback (x_gen W) := rfl
  rw [h_comp, mulByInt_comp_mulByInt_neg_one W n hn]
  show (mulByInt W.toAffine (-n)).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
  rw [mulByInt_pullback_x W (-n) (neg_ne_zero.mpr hn), mulByInt_x_neg]
  exact (mulByInt_pullback_x W n hn).symm

/-- **σ.pb on `(mulByInt n).pb y_gen`** for `n ≠ 0`. Same composition path
as the x-version but using `mulByInt_y_neg`: the σ-image is
`negY (mulByInt_x n) (mulByInt_y n) = -mulByInt_y n - a₁·mulByInt_x n - a₃`. -/
theorem sigma_mulByInt_pullback_y_eq (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine n).pullback (y_gen W)) =
      -(mulByInt W.toAffine n).pullback (y_gen W) -
      algebraMap K KE W.toAffine.a₁ * (mulByInt W.toAffine n).pullback (x_gen W) -
      algebraMap K KE W.toAffine.a₃ := by
  have h_inner_x := mulByInt_pullback_x W n hn
  have h_inner_y := mulByInt_pullback_y W n hn
  have h_xeq : (mulByInt W.toAffine n).pullback (x_gen W) = mulByInt_x W n := by
    show (mulByInt W.toAffine n).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
    exact h_inner_x
  have h_yeq : (mulByInt W.toAffine n).pullback (y_gen W) = mulByInt_y W n := by
    show (mulByInt W.toAffine n).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial)) = _
    exact h_inner_y
  rw [h_xeq, h_yeq]
  have h_comp : (mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine n).pullback (y_gen W)) =
      ((mulByInt W.toAffine n).comp (mulByInt W.toAffine (-1))).pullback (y_gen W) := rfl
  rw [show (mulByInt W.toAffine (-1)).pullback (mulByInt_y W n) =
      ((mulByInt W.toAffine n).comp (mulByInt W.toAffine (-1))).pullback (y_gen W) from
    h_yeq ▸ h_comp]
  rw [mulByInt_comp_mulByInt_neg_one W n hn]
  rw [show (mulByInt W.toAffine (-n)).pullback (y_gen W) = mulByInt_y W (-n) from by
    show (mulByInt W.toAffine (-n)).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial)) = _
    exact mulByInt_pullback_y W (-n) (neg_ne_zero.mpr hn)]
  rw [mulByInt_y_neg W n hn]
  show (W_KE W).toAffine.negY (mulByInt_x W n) (mulByInt_y W n) = _
  unfold WeierstrassCurve.Affine.negY
  rfl

/-! ### D3c step 2: σ-action on `(zsmul r π).pb`

For `α₁ = (frobeniusIsog W).zsmul r = (mulByInt r).comp π`, the σ-action
follows from `sigma_mulByInt_pullback_x_eq` / `_y_eq` plus σ commuting
through π via `frobeniusIsog_pullback_universal_commute`. -/

/-- **σ.pb fixes `((zsmul r π).pb x_gen)`** for `r ≠ 0`. Reduces via
`(zsmul r π).pb = π.pb ∘ (mulByInt r).pb` (comp), σ-π commutation
(`frobeniusIsog_pullback_universal_commute`), and
`sigma_mulByInt_pullback_x_eq`. -/
theorem sigma_zsmul_frobenius_pullback_x_eq (r : ℤ) (hr : r ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback
        (((frobeniusIsog W).zsmul r).pullback (x_gen W)) =
      ((frobeniusIsog W).zsmul r).pullback (x_gen W) := by
  -- (zsmul r π).pb x_gen = π.pb ((mulByInt r).pb x_gen) via comp_algebraMap_eq.
  show (mulByInt W.toAffine (-1)).pullback
      ((frobeniusIsog W).pullback ((mulByInt W.toAffine r).pullback (x_gen W))) = _
  -- σ.pb (π.pb z) = π.pb (σ.pb z) via universal commute.
  rw [show (mulByInt W.toAffine (-1)).pullback
      ((frobeniusIsog W).pullback ((mulByInt W.toAffine r).pullback (x_gen W))) =
      (frobeniusIsog W).pullback ((mulByInt W.toAffine (-1)).pullback
        ((mulByInt W.toAffine r).pullback (x_gen W))) from by
    have h := frobeniusIsog_pullback_universal_commute W
      (mulByInt W.toAffine (-1)).pullback
    exact (DFunLike.congr_fun h.symm
      ((mulByInt W.toAffine r).pullback (x_gen W)) : _)]
  rw [sigma_mulByInt_pullback_x_eq W r hr]
  rfl

/-- **σ.pb on `((zsmul r π).pb y_gen)`** for `r ≠ 0`. Same reduction path
as the x-version: comp + σ-π commutation + `sigma_mulByInt_pullback_y_eq`,
then push the linear combination back through `π.pb` (which is a `K`-algebra
hom, so distributes over `+`, `*`, and fixes `K`-image). -/
theorem sigma_zsmul_frobenius_pullback_y_eq (r : ℤ) (hr : r ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback
        (((frobeniusIsog W).zsmul r).pullback (y_gen W)) =
      -((frobeniusIsog W).zsmul r).pullback (y_gen W) -
      algebraMap K KE W.toAffine.a₁ *
        ((frobeniusIsog W).zsmul r).pullback (x_gen W) -
      algebraMap K KE W.toAffine.a₃ := by
  show (mulByInt W.toAffine (-1)).pullback
      ((frobeniusIsog W).pullback ((mulByInt W.toAffine r).pullback (y_gen W))) =
    -(frobeniusIsog W).pullback ((mulByInt W.toAffine r).pullback (y_gen W)) -
    algebraMap K KE W.toAffine.a₁ *
      (frobeniusIsog W).pullback ((mulByInt W.toAffine r).pullback (x_gen W)) -
    algebraMap K KE W.toAffine.a₃
  rw [show (mulByInt W.toAffine (-1)).pullback
      ((frobeniusIsog W).pullback ((mulByInt W.toAffine r).pullback (y_gen W))) =
      (frobeniusIsog W).pullback ((mulByInt W.toAffine (-1)).pullback
        ((mulByInt W.toAffine r).pullback (y_gen W))) from by
    have h := frobeniusIsog_pullback_universal_commute W
      (mulByInt W.toAffine (-1)).pullback
    exact (DFunLike.congr_fun h.symm
      ((mulByInt W.toAffine r).pullback (y_gen W)) : _)]
  rw [sigma_mulByInt_pullback_y_eq W r hr]
  -- Push π.pb over the linear combination.
  simp only [map_sub, map_neg, map_mul,
    AlgHom.commutes (frobeniusIsog W).pullback]

/-! ### D3c step 3: x-ne mismatch witness for `(zsmul r π, mulByInt -s)`

Extracted from `AddNonInversePair_zsmul_frobenius_mulByInt_neg`'s internal
proof: the x-coord pullbacks differ at `ord_∞` (`-2q` vs `-2`). Used
directly as the `h_x_ne` argument to the generic
`addPullback_x_pair_sigma_invariant`. -/

/-- The `ord_∞` contradiction behind the `x`-coord mismatch: `(mulByInt_x W r)^|K|`
(order `-2q`) cannot equal `mulByInt_x W (-s)` (order `-2`), since `|K|·(-2) = -2`
would force `|K| ≤ 1`. -/
private lemma mulByInt_x_pow_card_ne_mulByInt_x_neg (r s : ℤ) (hr : r ≠ 0)
    (hrK : (r : K) ≠ 0) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) :
    (mulByInt_x W r) ^ Fintype.card K ≠ mulByInt_x W (-s) := by
  intro h_eq
  have h_ord := congrArg (W_smooth W).ordAtInfty h_eq
  have h_pow_ord :
      (W_smooth W).ordAtInfty (mulByInt_x W r ^ Fintype.card K) =
        Fintype.card K • (W_smooth W).ordAtInfty (mulByInt_x W r) :=
    (W_smooth W).ordAtInfty_pow (mulByInt_x_ne_zero W r hr) (Fintype.card K)
  have h_neg_sK : ((-s : ℤ) : K) ≠ 0 := by push_cast; exact neg_ne_zero.mpr hsK
  rw [h_pow_ord, ordAtInfty_mulByInt_x W r hr hrK,
      ordAtInfty_mulByInt_x W (-s) (neg_ne_zero.mpr hs) h_neg_sK] at h_ord
  have h_smul_eq : (Fintype.card K : ℕ) • ((-2 : ℤ) : WithTop ℤ) =
      (((Fintype.card K : ℤ) * (-2) : ℤ) : WithTop ℤ) := by
    induction Fintype.card K with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, ih]
      rw [show (((k + 1 : ℕ) : ℤ) * -2 : ℤ) = ((k : ℤ) * -2) + (-2) from by push_cast; ring]
      push_cast
      rfl
  rw [h_smul_eq] at h_ord
  have h_int : (Fintype.card K : ℤ) * (-2) = (-2 : ℤ) := WithTop.coe_inj.mp h_ord
  have h_ge : (2 : ℤ) ≤ Fintype.card K := by
    exact_mod_cast Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  linarith

/-- **x-coord mismatch**: `((frobeniusIsog W).zsmul r).pb x_gen ≠
(mulByInt W (-s)).pb x_gen` for `r, s ≠ 0` with `(r : K) ≠ 0`, `(s : K) ≠ 0`
and `q ≥ 2`. The two have `ord_∞` `-2q` and `-2` respectively. -/
theorem zsmul_frobenius_pullback_x_ne_mulByInt_neg_pullback_x
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    ((frobeniusIsog W).zsmul r).pullback (x_gen W) ≠
      (mulByInt W.toAffine (-s)).pullback (x_gen W) := by
  rw [zsmul_frobenius_pullback_x_gen W r hr, mulByInt_neg_pullback_x_gen W s hs]
  exact mulByInt_x_pow_card_ne_mulByInt_x_neg W r s hr hrK hs hsK

/-! ### D3c step 4: σ-invariance specialised + K(x) image

Specialise `addPullback_x_pair_sigma_invariant` to
`(α₁, α₂) = (zsmul r π, mulByInt -s)` using the four σ-symmetry helpers
shipped above, then chain with `sigma_fixed_implies_in_KX_image` to extract
the K(x) image. -/

/-- **σ-invariance of `addPullback_x_pair (zsmul r π, mulByInt -s)`**.
Specialisation of the generic `addPullback_x_pair_sigma_invariant` for
the family used by D3c/D4. -/
theorem addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback
        (addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) =
      addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) :=
  addPullback_x_pair_sigma_invariant
    (zsmul_frobenius_pullback_x_ne_mulByInt_neg_pullback_x W r s hr hs hrK hsK)
    (sigma_zsmul_frobenius_pullback_x_eq W r hr)
    (sigma_mulByInt_pullback_x_eq W (-s) (neg_ne_zero.mpr hs))
    (sigma_zsmul_frobenius_pullback_y_eq W r hr)
    (sigma_mulByInt_pullback_y_eq W (-s) (neg_ne_zero.mpr hs))

/-- **`addPullback_x_pair (zsmul r π, mulByInt -s) ∈ K(x_gen)`**: the σ-fixed
expression lies in the image of `Frac(K[X]) → K(E)`. One-line consequence
of `sigma_fixed_implies_in_KX_image` applied to the σ-invariance above. -/
theorem addPullback_x_pair_zsmul_frobenius_mulByInt_neg_in_KX_image
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    ∃ a : FractionRing (Polynomial K),
      addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s)) =
        algebraMap (FractionRing (Polynomial K)) KE a :=
  sigma_fixed_implies_in_KX_image W _
    (addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant
      W r s hr hs hrK hsK)

/-! ### D3c step 5: ord helpers for `(zsmul r π).pb x_gen` and
`(mulByInt -s).pb x_gen`

Concrete ord values needed by the pole-bound argument: `(zsmul r π).pb x_gen
= (mulByInt_x r)^q` has `ord = -2q`, and `(mulByInt -s).pb x_gen
= mulByInt_x (-s)` has `ord = -2`. -/

/-- `ord_∞((zsmul r π).pb x_gen) = -2q` for `r ≠ 0` with `(r : K) ≠ 0`.
Combines `(zsmul r π).pb x_gen = (mulByInt_x r)^q`,
`(W_smooth W).ordAtInfty_pow`, and `ordAtInfty_mulByInt_x`. -/
theorem ordAtInfty_zsmul_frobenius_pullback_x_gen
    (r : ℤ) (hr : r ≠ 0) (hrK : (r : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
  have h_eq : ((frobeniusIsog W).zsmul r).pullback (x_gen W) =
      (mulByInt_x W r) ^ Fintype.card K := by
    show ((mulByInt W.toAffine r).comp (frobeniusIsog W)).pullback (x_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    rw [show (mulByInt W.toAffine r).pullback (x_gen W) = mulByInt_x W r from by
      show (mulByInt W.toAffine r).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W r hr]
    exact frobeniusIsog_pullback_apply W (mulByInt_x W r)
  rw [h_eq]
  have h_pow_ord :
      (W_smooth W).ordAtInfty (mulByInt_x W r ^ Fintype.card K) =
        Fintype.card K • (W_smooth W).ordAtInfty (mulByInt_x W r) :=
    (W_smooth W).ordAtInfty_pow (mulByInt_x_ne_zero W r hr) (Fintype.card K)
  rw [h_pow_ord, ordAtInfty_mulByInt_x W r hr hrK]
  -- Goal: Fintype.card K • ((-2 : ℤ) : WithTop ℤ) = ((-2 * Fintype.card K : ℤ) : WithTop ℤ).
  induction Fintype.card K with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ih]
    rw [show (-2 * ((k + 1 : ℕ) : ℤ) : ℤ) = (-2 * (k : ℤ)) + (-2) from by push_cast; ring]
    push_cast
    rfl

/-- `ord_∞((mulByInt (-s)).pb x_gen) = -2` for `s ≠ 0` with `(s : K) ≠ 0`.
Direct from `(mulByInt -s).pb x_gen = mulByInt_x W (-s)` plus
`ordAtInfty_mulByInt_x`. -/
theorem ordAtInfty_mulByInt_neg_pullback_x_gen
    (s : ℤ) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((mulByInt W.toAffine (-s)).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  rw [show (mulByInt W.toAffine (-s)).pullback (x_gen W) = mulByInt_x W (-s) from by
    show (mulByInt W.toAffine (-s)).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
    exact mulByInt_pullback_x W (-s) (neg_ne_zero.mpr hs)]
  exact ordAtInfty_mulByInt_x W (-s) (neg_ne_zero.mpr hs)
    (by push_cast; exact neg_ne_zero.mpr hsK)

/-! ### Inseparable `mulByInt_y` order (`p ∣ r` pencil case)

For the inseparable summand `r·π` of the pencil `r·π − s` when `p ∣ r` (so `(r : K) = 0`), the
`x`-order `ord_∞(mulByInt_x W r) = M` is an even value `≤ -2` (not the separable `-2`), and the
curve-equation halving gives `ord_∞(mulByInt_y W r) = 3M/2`.  These mirror
`ordAtInfty_mulByInt_y_eq_neg_three` but parametric in `M`, with **no** `(r : K) ≠ 0` hypothesis. -/

/-- The curve point `(mulByInt_x W r, mulByInt_y W r)` satisfies the (expanded) Weierstrass
equation `Y² + a₁·X·Y + a₃·Y = X³ + a₂·X² + a₄·X + a₆` over `K(E)`.  Obtained by pulling back the
generic Weierstrass equation along `[r]` and rewriting the `x`/`y` pullbacks (`mulByInt_pullback_x`,
`mulByInt_pullback_y`). -/
private lemma mulByInt_weierstrass_equation (r : ℤ) (hr : r ≠ 0) :
    mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r =
      mulByInt_x W r ^ 3 +
        algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2 +
        algebraMap K KE W.toAffine.a₄ * mulByInt_x W r +
        algebraMap K KE W.toAffine.a₆ := by
  have h_alg := pullback_equation W (mulByInt W.toAffine r)
  have hx_pb : (mulByInt W.toAffine r).pullback (x_gen W) = mulByInt_x W r := by
    show (mulByInt W.toAffine r).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
    exact mulByInt_pullback_x W r hr
  have hy_pb : (mulByInt W.toAffine r).pullback (y_gen W) = mulByInt_y W r := by
    show (mulByInt W.toAffine r).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial)) = _
    exact mulByInt_pullback_y W r hr
  rw [hx_pb, hy_pb] at h_alg
  rw [WeierstrassCurve.Affine.equation_iff] at h_alg
  exact h_alg

/-- `ord_∞(mulByInt_x W r · mulByInt_y W r) = M + m` from the orders `M, m` of the two factors. -/
private lemma ordAtInfty_mulByInt_x_mul_y (r : ℤ) {M m : ℤ}
    (hX_ne : mulByInt_x W r ≠ 0) (hY_ne : mulByInt_y W r ≠ 0)
    (hX_ord : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ))
    (hm : (W_smooth W).ordAtInfty (mulByInt_y W r) = ((m : ℤ) : WithTop ℤ)) :
    (W_smooth W).ordAtInfty (mulByInt_x W r * mulByInt_y W r) = (((M + m : ℤ)) : WithTop ℤ) := by
  refine ((W_smooth W).ordAtInfty_mul hX_ne hY_ne).trans ?_
  rw [hX_ord, hm]; push_cast; rfl

/-- For `M < 0` the right-hand side of the Weierstrass equation is dominated by `X³`, so
`ord_∞(X³ + a₂·X² + a₄·X + a₆) = 3M` where `M = ord_∞(mulByInt_x W r)`.  Repeated strict
non-archimedean additivity: `3M < 2M < M < 0`, so each successive `aᵢ·Xⁱ` term has strictly larger
order than the running `X³`-dominated sum. -/
private lemma ordAtInfty_mulByInt_weierstrass_rhs_eq (r : ℤ) {M : ℤ}
    (hX_ne : mulByInt_x W r ≠ 0) (hM_neg : M < 0)
    (hX_ord : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ)) :
    (W_smooth W).ordAtInfty
      (mulByInt_x W r ^ 3 +
        algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2 +
        algebraMap K KE W.toAffine.a₄ * mulByInt_x W r +
        algebraMap K KE W.toAffine.a₆) = ((3 * M : ℤ) : WithTop ℤ) := by
  have hX_sq : (W_smooth W).ordAtInfty (mulByInt_x W r ^ 2) = ((2 * M : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hX_ne M 2 hX_ord).trans (by push_cast; ring_nf)
  have hX_cube : (W_smooth W).ordAtInfty (mulByInt_x W r ^ 3) = ((3 * M : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hX_ne M 3 hX_ord).trans (by push_cast; ring_nf)
  have h_a2X2 : ((2 * M : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2) :=
    ord_algebraMap_mul_ge W W.toAffine.a₂ hX_sq.symm.le
  have h_a4X : ((M : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₄ * mulByInt_x W r) :=
    ord_algebraMap_mul_ge W W.toAffine.a₄ hX_ord.symm.le
  have h_a6 : (0 : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₆) := by
    by_cases ha₆ : W.toAffine.a₆ = 0
    · rw [ha₆, map_zero]; exact (W_smooth W).ordAtInfty_zero.symm ▸ le_top
    · rw [ordAtInfty_algebraMap_F_nonzero W ha₆]
  have step1 : (W_smooth W).ordAtInfty
      (mulByInt_x W r ^ 3 + algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2) =
      ((3 * M : ℤ) : WithTop ℤ) := by
    have h_lt : (W_smooth W).ordAtInfty (mulByInt_x W r ^ 3) <
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2) := by
      rw [hX_cube]; refine lt_of_lt_of_le ?_ h_a2X2
      exact_mod_cast (by linarith : (3 * M : ℤ) < 2 * M)
    exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans hX_cube
  have step2 : (W_smooth W).ordAtInfty
      (mulByInt_x W r ^ 3 + algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2 +
        algebraMap K KE W.toAffine.a₄ * mulByInt_x W r) = ((3 * M : ℤ) : WithTop ℤ) := by
    have h_lt : (W_smooth W).ordAtInfty
        (mulByInt_x W r ^ 3 + algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2) <
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₄ * mulByInt_x W r) := by
      rw [step1]; refine lt_of_lt_of_le ?_ h_a4X
      exact_mod_cast (by linarith : (3 * M : ℤ) < M)
    exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans step1
  have h_lt : (W_smooth W).ordAtInfty
      (mulByInt_x W r ^ 3 + algebraMap K KE W.toAffine.a₂ * mulByInt_x W r ^ 2 +
        algebraMap K KE W.toAffine.a₄ * mulByInt_x W r) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₆) := by
    rw [step2]; refine lt_of_lt_of_le ?_ h_a6
    exact_mod_cast (by linarith : (3 * M : ℤ) < 0)
  exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans step2

/-- `mulByInt_y W r ≠ 0`: were `Y = 0` the Weierstrass LHS would vanish (order `⊤`), but the LHS
order equals the finite value `3M`. -/
private lemma mulByInt_y_ne_zero_of_weierstrass_lhs_ord (r : ℤ) {M : ℤ}
    (h_lhs_ord : (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) = ((3 * M : ℤ) : WithTop ℤ)) :
    mulByInt_y W r ≠ 0 := by
  intro h
  have h_zero : mulByInt_y W r ^ 2 +
      algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
      algebraMap K KE W.toAffine.a₃ * mulByInt_y W r = 0 := by rw [h]; ring
  have h_ord_eq : (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) = ⊤ :=
    (congrArg (W_smooth W).ordAtInfty h_zero).trans (W_smooth W).ordAtInfty_zero
  exact WithTop.top_ne_coe (h_ord_eq.symm.trans h_lhs_ord)

/-- The halving lower bound `2m ≤ 3M`, where `m = ord_∞(mulByInt_y W r)` and `M = ord_∞(mulByInt_x W
r)`.  If instead `2m ≥ 3M + 1`, every Weierstrass LHS term (`Y²`, `a₁·X·Y`, `a₃·Y`) would have order
`≥ 3M + 1`, so the LHS order would be `≥ 3M + 1`, contradicting `ord(LHS) = 3M`. -/
private lemma two_mul_ordAtInfty_mulByInt_y_le (r : ℤ) {M m : ℤ} (hM_neg : M < 0)
    (hX_ne : mulByInt_x W r ≠ 0) (hY_ne : mulByInt_y W r ≠ 0)
    (hX_ord : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ))
    (hm : (W_smooth W).ordAtInfty (mulByInt_y W r) = ((m : ℤ) : WithTop ℤ))
    (h_lhs_ord : (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) = ((3 * M : ℤ) : WithTop ℤ)) :
    2 * m ≤ 3 * M := by
  by_contra h_not_le
  push Not at h_not_le
  have hY_sq_ord : (W_smooth W).ordAtInfty (mulByInt_y W r ^ 2) = ((2 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hY_ne m 2 hm).trans (by push_cast; ring_nf)
  have h_xy_ord := ordAtInfty_mulByInt_x_mul_y W r hX_ne hY_ne hX_ord hm
  -- All three LHS terms have ord ≥ 3M + 1.
  have h_y_sq_ge : (((3 * M + 1 : ℤ)) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (mulByInt_y W r ^ 2) := by
    rw [hY_sq_ord]; exact_mod_cast (by omega : (3 * M + 1 : ℤ) ≤ 2 * m)
  have h_a1xy_ge : (((3 * M + 1 : ℤ)) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁ *
        mulByInt_x W r * mulByInt_y W r) := by
    rw [show algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r =
        algebraMap K KE W.toAffine.a₁ * (mulByInt_x W r * mulByInt_y W r) from by ring]
    refine ord_algebraMap_mul_ge W W.toAffine.a₁ ?_
    rw [h_xy_ord]; exact_mod_cast (by omega : (3 * M + 1 : ℤ) ≤ M + m)
  have h_a3y_ge : (((3 * M + 1 : ℤ)) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) := by
    refine ord_algebraMap_mul_ge W W.toAffine.a₃ ?_
    rw [hm]; exact_mod_cast (by omega : (3 * M + 1 : ℤ) ≤ m)
  have h_lhs_ge : (((3 * M + 1 : ℤ)) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) :=
    ord_add_ge_of_both_ge W
      (ord_add_ge_of_both_ge W h_y_sq_ge h_a1xy_ge) h_a3y_ge
  rw [h_lhs_ord] at h_lhs_ge
  have : (3 * M + 1 : ℤ) ≤ 3 * M := by exact_mod_cast h_lhs_ge
  omega

/-- When `m < M` and `m < 0` (which hold once `2m ≤ 3M` with `M < 0`), the term `Y²` strictly
dominates the other two Weierstrass LHS terms, so `ord_∞(Y² + a₁·X·Y + a₃·Y) = 2m`, where `m =
ord_∞(mulByInt_y W r)`. -/
private lemma ordAtInfty_mulByInt_weierstrass_lhs_eq (r : ℤ) {M m : ℤ}
    (hX_ne : mulByInt_x W r ≠ 0) (hY_ne : mulByInt_y W r ≠ 0)
    (hX_ord : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ))
    (hm : (W_smooth W).ordAtInfty (mulByInt_y W r) = ((m : ℤ) : WithTop ℤ))
    (hm_lt_M : m < M) (hm_neg : m < 0) :
    (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) = ((2 * m : ℤ) : WithTop ℤ) := by
  have hY_sq_ord : (W_smooth W).ordAtInfty (mulByInt_y W r ^ 2) = ((2 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hY_ne m 2 hm).trans (by push_cast; ring_nf)
  have h_xy_ord := ordAtInfty_mulByInt_x_mul_y W r hX_ne hY_ne hX_ord hm
  have h_a1xy_gt : (W_smooth W).ordAtInfty (mulByInt_y W r ^ 2) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁ *
        mulByInt_x W r * mulByInt_y W r) := by
    rw [hY_sq_ord, show algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r =
        algebraMap K KE W.toAffine.a₁ * (mulByInt_x W r * mulByInt_y W r) from by ring]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge W W.toAffine.a₁
      (n := (((M + m : ℤ)) : WithTop ℤ)) (le_of_eq h_xy_ord.symm))
    exact_mod_cast (by omega : (2 * m : ℤ) < M + m)
  have h_a3y_gt : (W_smooth W).ordAtInfty (mulByInt_y W r ^ 2) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) := by
    rw [hY_sq_ord]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge W W.toAffine.a₃
      (n := ((m : ℤ) : WithTop ℤ)) (le_of_eq hm.symm))
    exact_mod_cast (by omega : (2 * m : ℤ) < m)
  have h_inner_eq : (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r) =
      (W_smooth W).ordAtInfty (mulByInt_y W r ^ 2) :=
    (W_smooth W).ordAtInfty_add_eq_of_lt h_a1xy_gt
  have h_a3y_gt' : (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) :=
    h_inner_eq ▸ h_a3y_gt
  refine (((W_smooth W).ordAtInfty_add_eq_of_lt h_a3y_gt').trans h_inner_eq).trans ?_
  exact hY_sq_ord

/-- **`ord_∞(mulByInt_y W r) = 3M/2`** for `r ≠ 0`, where `M = ord_∞(mulByInt_x W r)` is the
(even, `≤ -2`) `x`-order — **no** `(r : K) ≠ 0` hypothesis.  The curve point
`(mulByInt_x W r, mulByInt_y W r)` satisfies the Weierstrass equation
`Y² + a₁·X·Y + a₃·Y = X³ + a₂·X² + a₄·X + a₆`; with `ord(X) = M < 0` the RHS is dominated by `ord(X³) =
3M`, and the LHS by `ord(Y²) = 2·ord(Y)` (once `ord(Y) ≤ 3M/2`), forcing `2·ord(Y) = 3M`.  Generalises
`ordAtInfty_mulByInt_y_eq_neg_three` (the `M = -2` case) to the inseparable regime. -/
theorem ordAtInfty_mulByInt_y_eq_of_x
    (r : ℤ) (hr : r ≠ 0) {M : ℤ} (hM : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ))
    (hM_le : M ≤ -2) (hM_even : Even M) :
    (W_smooth W).ordAtInfty (mulByInt_y W r) = (((3 * M) / 2 : ℤ) : WithTop ℤ) := by
  obtain ⟨M₂, hM₂⟩ := hM_even
  -- `M = 2·M₂`, so the target `3M/2 = 3·M₂`; throughout `M < 0`.
  have h_target : (3 * M) / 2 = 3 * M₂ := by omega
  have hM_neg : M < 0 := by omega
  have hX_ne : mulByInt_x W r ≠ 0 := mulByInt_x_ne_zero W r hr
  -- ord(LHS) = ord(RHS) = 3M, via the Weierstrass equation with `X³` dominating the RHS.
  have h_lhs_ord : (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) = ((3 * M : ℤ) : WithTop ℤ) :=
    (mulByInt_weierstrass_equation W r hr) ▸ ordAtInfty_mulByInt_weierstrass_rhs_eq W r hX_ne hM_neg hM
  -- Extract `m = ord(Y)` as an integer (`Y ≠ 0` since the finite-order LHS would otherwise vanish).
  have hY_ne : mulByInt_y W r ≠ 0 := mulByInt_y_ne_zero_of_weierstrass_lhs_ord W r h_lhs_ord
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (W_smooth W).ordAtInfty (mulByInt_y W r) = ((m : ℤ) : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((W_smooth W).ordAtInfty_eq_top_iff _).not.mpr hY_ne)
    exact ⟨m, hm.symm⟩
  -- Halving: `2m ≤ 3M` (lower bound), and then `Y²` dominates the LHS, forcing `2m = 3M`.
  have h_m_le : 2 * m ≤ 3 * M :=
    two_mul_ordAtInfty_mulByInt_y_le W r hM_neg hX_ne hY_ne hM hm h_lhs_ord
  have h_lhs_eq : (W_smooth W).ordAtInfty
      (mulByInt_y W r ^ 2 +
        algebraMap K KE W.toAffine.a₁ * mulByInt_x W r * mulByInt_y W r +
        algebraMap K KE W.toAffine.a₃ * mulByInt_y W r) = ((2 * m : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_weierstrass_lhs_eq W r hX_ne hY_ne hM hm (by omega) (by omega)
  have h_2m : (2 * m : ℤ) = 3 * M := by exact_mod_cast h_lhs_eq.symm.trans h_lhs_ord
  rw [hm, h_target]
  exact_mod_cast (by omega : m = 3 * M₂)

/-! ### D3c step 6: ord helpers for `mulByInt_y` and the y-pullbacks

To compute `ord_∞` of the pair `addPullback_x`, we need ord values for
the y-coordinate pullbacks: `ord((zsmul r π).pb y_gen) = -3q` and
`ord((mulByInt -s).pb y_gen) = -3`. These chain through
`ord(mulByInt_y W r) = -3` (curve-equation argument with x-ord = -2). -/

/-- **`ord_∞(mulByInt_y W r) = -3`** for `r ≠ 0` with `(r : K) ≠ 0`.
The `(mulByInt_x W r, mulByInt_y W r)` curve point has `ord(mulByInt_x) = -2`,
so the curve equation `Y² + a₁·X·Y + a₃·Y = X³ + ...` forces
`ord(Y) = -3` (the `2 ord(Y) = 3 ord(X)` halving).

This is the separable `M = -2` instance of the general halving lemma
`ordAtInfty_mulByInt_y_eq_of_x`: with `(r : K) ≠ 0` the `x`-order is `-2`
(via `ordAtInfty_mulByInt_x`), and `3·(-2)/2 = -3`. -/
theorem ordAtInfty_mulByInt_y_eq_neg_three
    (r : ℤ) (hr : r ≠ 0) (hrK : (r : K) ≠ 0) :
    (W_smooth W).ordAtInfty (mulByInt_y W r) =
      ((-3 : ℤ) : WithTop ℤ) := by
  have hX_ord : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((-2 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_x W r hr hrK
  -- Specialise the general halving lemma at `M = -2`; `3 · (-2) / 2 = -3`.
  have h := ordAtInfty_mulByInt_y_eq_of_x W r hr hX_ord (by norm_num) (by decide)
  rwa [show (3 * (-2) / 2 : ℤ) = -3 from by norm_num] at h

/-- `ord_∞((zsmul r π).pb y_gen) = -3q` for `r ≠ 0` with `(r : K) ≠ 0`.
Reduces to `ord_∞(mulByInt_y W r ^ q) = q · ord(mulByInt_y r) = q · -3 = -3q`. -/
theorem ordAtInfty_zsmul_frobenius_pullback_y_gen
    (r : ℤ) (hr : r ≠ 0) (hrK : (r : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
  have h_eq : ((frobeniusIsog W).zsmul r).pullback (y_gen W) =
      (mulByInt_y W r) ^ Fintype.card K := by
    show ((mulByInt W.toAffine r).comp (frobeniusIsog W)).pullback (y_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    rw [show (mulByInt W.toAffine r).pullback (y_gen W) = mulByInt_y W r from by
      show (mulByInt W.toAffine r).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.root W.toAffine.polynomial)) = _
      exact mulByInt_pullback_y W r hr]
    exact frobeniusIsog_pullback_apply W (mulByInt_y W r)
  rw [h_eq]
  have hY_ne : mulByInt_y W r ≠ 0 := by
    intro h
    have h_top : (W_smooth W).ordAtInfty (mulByInt_y W r) = ⊤ := by
      rw [h]; exact (W_smooth W).ordAtInfty_zero
    rw [ordAtInfty_mulByInt_y_eq_neg_three W r hr hrK] at h_top
    exact WithTop.coe_ne_top h_top
  have h_pow_ord : (W_smooth W).ordAtInfty (mulByInt_y W r ^ Fintype.card K) =
      Fintype.card K • (W_smooth W).ordAtInfty (mulByInt_y W r) :=
    (W_smooth W).ordAtInfty_pow hY_ne (Fintype.card K)
  rw [h_pow_ord, ordAtInfty_mulByInt_y_eq_neg_three W r hr hrK]
  induction Fintype.card K with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ih]
    rw [show (-3 * ((k + 1 : ℕ) : ℤ) : ℤ) = (-3 * (k : ℤ)) + (-3) from by push_cast; ring]
    push_cast
    rfl

/-- `ord_∞((mulByInt -s).pb y_gen) = -3` for `s ≠ 0` with `(s : K) ≠ 0`.
Direct from `(mulByInt -s).pb y_gen = mulByInt_y W (-s)` plus
`ordAtInfty_mulByInt_y_eq_neg_three`. -/
theorem ordAtInfty_mulByInt_neg_pullback_y_gen
    (s : ℤ) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((mulByInt W.toAffine (-s)).pullback (y_gen W)) =
      ((-3 : ℤ) : WithTop ℤ) := by
  rw [show (mulByInt W.toAffine (-s)).pullback (y_gen W) = mulByInt_y W (-s) from by
    show (mulByInt W.toAffine (-s)).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial)) = _
    exact mulByInt_pullback_y W (-s) (neg_ne_zero.mpr hs)]
  exact ordAtInfty_mulByInt_y_eq_neg_three W (-s) (neg_ne_zero.mpr hs)
    (by push_cast; exact neg_ne_zero.mpr hsK)

/-! ### Inseparable summand `x`/`y`-pullback orders (`p ∣ r` pencil case)

For `p ∣ r` (so `(r : K) = 0`, no separable `-2q`/`-3q`), the `r·π` summand pullbacks are
`((frobeniusIsog).zsmul r)^* x_gen = (mulByInt_x r)^q` and `^* y_gen = (mulByInt_y r)^q`, with orders
`q·M` and `q·(3M/2)` where `M = ord_∞(mulByInt_x r) ≤ -2` is the inseparable `x`-order
(`exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`).  These mirror
`ordAtInfty_zsmul_frobenius_pullback_x_gen`/`_y_gen` but parametric in `M`. -/

/-- **`ord_∞(((frobeniusIsog).zsmul r)^* x_gen) = q·M`** for `r ≠ 0` (no `(r : K) ≠ 0`), where
`M = ord_∞(mulByInt_x W r)` is the inseparable `x`-order.  As `(mulByInt_x r)^q`, the order is
`q·ord_∞(mulByInt_x r) = q·M`. -/
theorem ordAtInfty_zsmul_frobenius_pullback_x_gen_of_x
    (r : ℤ) (hr : r ≠ 0) {M : ℤ}
    (hM : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ)) :
    (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (x_gen W)) =
      (((Fintype.card K : ℤ) * M : ℤ) : WithTop ℤ) := by
  have h_eq : ((frobeniusIsog W).zsmul r).pullback (x_gen W) =
      (mulByInt_x W r) ^ Fintype.card K := by
    show ((mulByInt W.toAffine r).comp (frobeniusIsog W)).pullback (x_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    rw [show (mulByInt W.toAffine r).pullback (x_gen W) = mulByInt_x W r from by
      show (mulByInt W.toAffine r).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W r hr]
    exact frobeniusIsog_pullback_apply W (mulByInt_x W r)
  rw [h_eq]
  exact ((W_smooth W).ord_pow_concrete (mulByInt_x_ne_zero W r hr) M (Fintype.card K) hM)

/-- **`ord_∞(((frobeniusIsog).zsmul r)^* y_gen) = q·(3M/2)`** for `r ≠ 0` (no `(r : K) ≠ 0`), where
`M = ord_∞(mulByInt_x W r) ≤ -2` is the inseparable `x`-order and `3M/2 = ord_∞(mulByInt_y W r)`
(`ordAtInfty_mulByInt_y_eq_of_x`).  As `(mulByInt_y r)^q`, the order is `q·(3M/2)`. -/
theorem ordAtInfty_zsmul_frobenius_pullback_y_gen_of_x
    (r : ℤ) (hr : r ≠ 0) {M : ℤ}
    (hM : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ))
    (hM_le : M ≤ -2) (hM_even : Even M) :
    (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (y_gen W)) =
      (((Fintype.card K : ℤ) * ((3 * M) / 2) : ℤ) : WithTop ℤ) := by
  have hY_ord : (W_smooth W).ordAtInfty (mulByInt_y W r) = (((3 * M) / 2 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_y_eq_of_x W r hr hM hM_le hM_even
  have hY_ne : mulByInt_y W r ≠ 0 := by
    intro h
    have h_top : (W_smooth W).ordAtInfty (mulByInt_y W r) = ⊤ := by
      rw [h]; exact (W_smooth W).ordAtInfty_zero
    rw [hY_ord] at h_top; exact WithTop.coe_ne_top h_top
  have h_eq : ((frobeniusIsog W).zsmul r).pullback (y_gen W) =
      (mulByInt_y W r) ^ Fintype.card K := by
    show ((mulByInt W.toAffine r).comp (frobeniusIsog W)).pullback (y_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    rw [show (mulByInt W.toAffine r).pullback (y_gen W) = mulByInt_y W r from by
      show (mulByInt W.toAffine r).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.root W.toAffine.polynomial)) = _
      exact mulByInt_pullback_y W r hr]
    exact frobeniusIsog_pullback_apply W (mulByInt_y W r)
  rw [h_eq]
  exact ((W_smooth W).ord_pow_concrete hY_ne ((3 * M) / 2) (Fintype.card K) hY_ord)

/-! ### D3c step 7: ord helpers for the pair differences

The slope `L = (Y₁ - Y₂) / (X₁ - X₂)` requires ord of the differences:
`ord(α₁(x) - α₂(x)) = -2q` (α₁(x) dominates, ord = -2q < -2 = ord(α₂(x))),
and similarly `ord(α₁(y) - α₂(y)) = -3q`. -/

/-- `ord_∞((zsmul r π).pb x_gen - (mulByInt -s).pb x_gen) = -2q`. The
α₁ side dominates strictly: `-2q < -2` for `q ≥ 2`. -/
theorem ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((((frobeniusIsog W).zsmul r).pullback (x_gen W) -
          (mulByInt W.toAffine (-s)).pullback (x_gen W)) : KE) =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
  have h_lt : (-2 * (Fintype.card K : ℤ) : ℤ) < -2 := by linarith
  exact (W_smooth W).ord_sub_lt_concrete (-2 * (Fintype.card K : ℤ)) (-2) h_lt
    (ordAtInfty_zsmul_frobenius_pullback_x_gen W r hr hrK)
    (ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK)

/-- `ord_∞((zsmul r π).pb y_gen - (mulByInt -s).pb y_gen) = -3q`. The
α₁ side dominates strictly: `-3q < -3` for `q ≥ 2`. -/
theorem ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_y
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((((frobeniusIsog W).zsmul r).pullback (y_gen W) -
          (mulByInt W.toAffine (-s)).pullback (y_gen W)) : KE) =
      ((-3 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
  have h_lt : (-3 * (Fintype.card K : ℤ) : ℤ) < -3 := by linarith
  exact (W_smooth W).ord_sub_lt_concrete (-3 * (Fintype.card K : ℤ)) (-3) h_lt
    (ordAtInfty_zsmul_frobenius_pullback_y_gen W r hr hrK)
    (ordAtInfty_mulByInt_neg_pullback_y_gen W s hs hsK)

/-- `(zsmul r π).pb x_gen - (mulByInt -s).pb x_gen ≠ 0`: from
the ord-mismatch witness. -/
theorem zsmul_frobenius_sub_mulByInt_neg_x_ne_zero
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (((frobeniusIsog W).zsmul r).pullback (x_gen W) -
      (mulByInt W.toAffine (-s)).pullback (x_gen W)) ≠ (0 : KE) := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      ((((frobeniusIsog W).zsmul r).pullback (x_gen W) -
        (mulByInt W.toAffine (-s)).pullback (x_gen W)) : KE) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x W r s hr hs hrK hsK] at h_top
  exact WithTop.coe_ne_top h_top

/-! ### D3c step 8: numerator + reduced form for the pair (zsmul r π, mulByInt -s)

Mirror of `addPullbackNumerator_negFrobenius` and `_reduced` for the pair
version. The numerator is `(X₁-X₂)² · addPullback_x_pair` (cleared of the
denominator), and the reduced form expands the `Y_i^2` terms via
Weierstrass equations for both `(X_i, Y_i)` points. -/

/-- The numerator obtained by clearing the `(α₁(x) - α₂(x))²` denominator
from `addPullback_x_pair α₁ α₂` for `α₁ = (zsmul r π)`, `α₂ = (mulByInt -s)`. -/
noncomputable def addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) : KE :=
  (((frobeniusIsog W).zsmul r).pullback (y_gen W) -
    (mulByInt W.toAffine (-s)).pullback (y_gen W)) ^ 2 +
  algebraMap K KE W.toAffine.a₁ *
    (((frobeniusIsog W).zsmul r).pullback (x_gen W) -
      (mulByInt W.toAffine (-s)).pullback (x_gen W)) *
    (((frobeniusIsog W).zsmul r).pullback (y_gen W) -
      (mulByInt W.toAffine (-s)).pullback (y_gen W)) -
  (((frobeniusIsog W).zsmul r).pullback (x_gen W) -
    (mulByInt W.toAffine (-s)).pullback (x_gen W)) ^ 2 *
    (algebraMap K KE W.toAffine.a₂ +
      ((frobeniusIsog W).zsmul r).pullback (x_gen W) +
      (mulByInt W.toAffine (-s)).pullback (x_gen W))

/-- The Weierstrass-reduced 8-term form of the pair numerator. The dominant
term for `q ≥ 2` (with `α₁(x)` having the deeper pole) is `α₁(x)² · α₂(x)`,
with `ord_∞ = -4q - 2`. -/
noncomputable def addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) : KE :=
  algebraMap K KE W.toAffine.a₄ *
      (((frobeniusIsog W).zsmul r).pullback (x_gen W) +
        (mulByInt W.toAffine (-s)).pullback (x_gen W))
    + 2 * algebraMap K KE W.toAffine.a₆
    - algebraMap K KE W.toAffine.a₃ *
        (((frobeniusIsog W).zsmul r).pullback (y_gen W) +
          (mulByInt W.toAffine (-s)).pullback (y_gen W))
    - 2 * ((frobeniusIsog W).zsmul r).pullback (y_gen W) *
        (mulByInt W.toAffine (-s)).pullback (y_gen W)
    - algebraMap K KE W.toAffine.a₁ *
        (((frobeniusIsog W).zsmul r).pullback (x_gen W) *
          (mulByInt W.toAffine (-s)).pullback (y_gen W) +
         (mulByInt W.toAffine (-s)).pullback (x_gen W) *
          ((frobeniusIsog W).zsmul r).pullback (y_gen W))
    + ((frobeniusIsog W).zsmul r).pullback (x_gen W) ^ 2 *
        (mulByInt W.toAffine (-s)).pullback (x_gen W)
    + ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
        (mulByInt W.toAffine (-s)).pullback (x_gen W) ^ 2
    + 2 * algebraMap K KE W.toAffine.a₂ *
        ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
        (mulByInt W.toAffine (-s)).pullback (x_gen W)

/-- Weierstrass relation at the pullback of an arbitrary isogeny `α`, in
`algebraMap K KE`-coefficient form (via `pullback_equation`). -/
private theorem weierstrass_relation_pullback (α : Isogeny W.toAffine W.toAffine) :
    α.pullback (y_gen W) ^ 2 +
        algebraMap K KE W.toAffine.a₁ * α.pullback (x_gen W) * α.pullback (y_gen W) +
        algebraMap K KE W.toAffine.a₃ * α.pullback (y_gen W) -
        (α.pullback (x_gen W) ^ 3 +
         algebraMap K KE W.toAffine.a₂ * α.pullback (x_gen W) ^ 2 +
         algebraMap K KE W.toAffine.a₄ * α.pullback (x_gen W) +
         algebraMap K KE W.toAffine.a₆) = 0 := by
  have h := pullback_equation W α
  rw [WeierstrassCurve.Affine.equation_iff'] at h
  have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  have h_a3 : (W_KE W).toAffine.a₃ = algebraMap K KE W.toAffine.a₃ := rfl
  have h_a4 : (W_KE W).toAffine.a₄ = algebraMap K KE W.toAffine.a₄ := rfl
  have h_a6 : (W_KE W).toAffine.a₆ = algebraMap K KE W.toAffine.a₆ := rfl
  rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h
  exact h

/-- **Weierstrass reduction for the pair**:
`addPullbackNumerator_pair = addPullbackNumerator_reduced_pair`. Mirror of
`addPullbackNumerator_negFrobenius_eq_reduced`, with both Weierstrass
equations applied via `linear_combination h_α₁ + h_α₂`. -/
theorem addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_reduced
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) :
    addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg W r s =
      addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg W r s := by
  have h_α₁ := weierstrass_relation_pullback W ((frobeniusIsog W).zsmul r)
  have h_α₂ := weierstrass_relation_pullback W (mulByInt W.toAffine (-s))
  unfold addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg
    addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg
  linear_combination h_α₁ + h_α₂

/-- **Numerator clears the denominator**:
`addPullbackNumerator_pair = (X₁-X₂)² · addPullback_x_pair`. Direct from
the slope formula `addX = L² + a₁L - a₂ - X₁ - X₂` with
`L = (Y₁-Y₂)/(X₁-X₂)` and clearing `(X₁-X₂)²`. -/
theorem addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg W r s =
      (((frobeniusIsog W).zsmul r).pullback (x_gen W) -
        (mulByInt W.toAffine (-s)).pullback (x_gen W)) ^ 2 *
      addPullback_x_pair ((frobeniusIsog W).zsmul r)
        (mulByInt W.toAffine (-s)) := by
  set d := ((frobeniusIsog W).zsmul r).pullback (x_gen W) -
    (mulByInt W.toAffine (-s)).pullback (x_gen W) with hd_def
  set n := ((frobeniusIsog W).zsmul r).pullback (y_gen W) -
    (mulByInt W.toAffine (-s)).pullback (y_gen W) with hn_def
  have hd_ne : d ≠ 0 :=
    zsmul_frobenius_sub_mulByInt_neg_x_ne_zero W r s hr hs hrK hsK
  have hL : addSlopePair ((frobeniusIsog W).zsmul r)
        (mulByInt W.toAffine (-s)) = n / d := by
    unfold addSlopePair
    exact Affine.slope_of_X_ne (sub_ne_zero.mp hd_ne)
  unfold addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg addPullback_x_pair
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ +
            ((frobeniusIsog W).zsmul r).pullback (x_gen W) +
            (mulByInt W.toAffine (-s)).pullback (x_gen W)) =
      d ^ 2 * (W_KE W).toAffine.addX (((frobeniusIsog W).zsmul r).pullback (x_gen W))
        ((mulByInt W.toAffine (-s)).pullback (x_gen W))
        (addSlopePair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)))
  unfold WeierstrassCurve.Affine.addX
  rw [hL]
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ +
            ((frobeniusIsog W).zsmul r).pullback (x_gen W) +
            (mulByInt W.toAffine (-s)).pullback (x_gen W)) =
      d ^ 2 * ((n / d) ^ 2 + (W_KE W).toAffine.a₁ * (n / d) -
        (W_KE W).toAffine.a₂ -
        ((frobeniusIsog W).zsmul r).pullback (x_gen W) -
        (mulByInt W.toAffine (-s)).pullback (x_gen W))
  have h_a1_lift : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2_lift : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  rw [h_a1_lift, h_a2_lift]
  field_simp
  ring

/-! ### D3c step 9: `ord(reduced_pair) = -4q - 2`

Mirror of `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq` for
the pair version. Dominant term: `α₁(x)² · α₂(x)` (ord = -4q-2). All
other 7 terms have ord strictly larger (≥ -3q-3 + small) for q ≥ 2. -/

/-- `((zsmul r π).pb y_gen ≠ 0)` for `r ≠ 0` with `(r : K) ≠ 0`. From
`ord = -3q ≠ ⊤`. -/
private lemma zsmul_frobenius_pullback_y_gen_ne_zero
    (r : ℤ) (hr : r ≠ 0) (hrK : (r : K) ≠ 0) :
    ((frobeniusIsog W).zsmul r).pullback (y_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      (((frobeniusIsog W).zsmul r).pullback (y_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_zsmul_frobenius_pullback_y_gen W r hr hrK] at h_top
  exact WithTop.coe_ne_top h_top

/-- `((zsmul r π).pb x_gen ≠ 0)` for `r ≠ 0` with `(r : K) ≠ 0`. -/
private lemma zsmul_frobenius_pullback_x_gen_ne_zero
    (r : ℤ) (hr : r ≠ 0) (hrK : (r : K) ≠ 0) :
    ((frobeniusIsog W).zsmul r).pullback (x_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      (((frobeniusIsog W).zsmul r).pullback (x_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_zsmul_frobenius_pullback_x_gen W r hr hrK] at h_top
  exact WithTop.coe_ne_top h_top

/-- `(mulByInt -s).pb y_gen ≠ 0` for `s ≠ 0` with `(s : K) ≠ 0`. -/
private lemma mulByInt_neg_pullback_y_gen_ne_zero
    (s : ℤ) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) :
    (mulByInt W.toAffine (-s)).pullback (y_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      ((mulByInt W.toAffine (-s)).pullback (y_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_mulByInt_neg_pullback_y_gen W s hs hsK] at h_top
  exact WithTop.coe_ne_top h_top

/-- `(mulByInt -s).pb x_gen ≠ 0` for `s ≠ 0` with `(s : K) ≠ 0`. -/
private lemma mulByInt_neg_pullback_x_gen_ne_zero
    (s : ℤ) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) :
    (mulByInt W.toAffine (-s)).pullback (x_gen W) ≠ 0 := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      ((mulByInt W.toAffine (-s)).pullback (x_gen W)) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK] at h_top
  exact WithTop.coe_ne_top h_top

/-! ### Decomposition of `ord_∞(addPullbackNumerator_reduced_pair)`

The reduced numerator for the pair `(zsmul r π, mulByInt -s)` splits as a dominant
term `X₁² · X₂` (order `-4q - 2`) plus seven "rest" terms each of order `≥ -3q - 3`,
where `X₁ = (zsmul r π)^* x`, `X₂ = (mulByInt -s)^* x`, `Y₁ = (zsmul r π)^* y`,
`Y₂ = (mulByInt -s)^* y` have orders `-2q, -2, -3q, -3` respectively.  This mirrors the
`(1,1)`-analogue `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq` and reuses the
generic order helpers (`ord_algebraMap_mul_ge`, `ord_two_mul_ge`, `ord_add_ge_of_both_ge`,
`ord_sub_ge_of_both_ge`).  The helpers below carve out the independent sub-arguments. -/

/-- `ord(X₁ + X₂) = -2q` for the pair: `X₁ = (zsmul r π)^* x` (order `-2q`) dominates
`X₂ = (mulByInt -s)^* x` (order `-2`) strictly, since `-2q < -2` for `q ≥ 2`. -/
private lemma ord_zsmul_frobenius_mulByInt_neg_x_add_eq
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (x_gen W) +
          (mulByInt W.toAffine (-s)).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
  refine (W_smooth W).ord_add_lt_concrete (-2 * (Fintype.card K : ℤ)) (-2) ?_
    (ordAtInfty_zsmul_frobenius_pullback_x_gen W r hr hrK)
    (ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK)
  exact_mod_cast (by linarith : (-2 * (Fintype.card K : ℤ) : ℤ) < -2)

/-- `ord(Y₁ + Y₂) = -3q` for the pair: `Y₁ = (zsmul r π)^* y` (order `-3q`) dominates
`Y₂ = (mulByInt -s)^* y` (order `-3`) strictly, since `-3q < -3` for `q ≥ 2`. -/
private lemma ord_zsmul_frobenius_mulByInt_neg_y_add_eq
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (y_gen W) +
          (mulByInt W.toAffine (-s)).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
  refine (W_smooth W).ord_add_lt_concrete (-3 * (Fintype.card K : ℤ)) (-3) ?_
    (ordAtInfty_zsmul_frobenius_pullback_y_gen W r hr hrK)
    (ordAtInfty_mulByInt_neg_pullback_y_gen W s hs hsK)
  exact_mod_cast (by linarith : (-3 * (Fintype.card K : ℤ) : ℤ) < -3)

/-- The dominant term: `ord(X₁² · X₂) = 2·(-2q) + (-2) = -4q - 2`. -/
private lemma ord_zsmul_frobenius_mulByInt_neg_x_sq_mul_eq
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((((frobeniusIsog W).zsmul r).pullback (x_gen W)) ^ 2 *
          (mulByInt W.toAffine (-s)).pullback (x_gen W)) =
      ((-4 * (Fintype.card K : ℤ) - 2 : ℤ) : WithTop ℤ) := by
  set X₁ := ((frobeniusIsog W).zsmul r).pullback (x_gen W) with hX₁_def
  set X₂ := (mulByInt W.toAffine (-s)).pullback (x_gen W) with hX₂_def
  have hX₁_ne : X₁ ≠ 0 := zsmul_frobenius_pullback_x_gen_ne_zero W r hr hrK
  have hX₂_ne : X₂ ≠ 0 := mulByInt_neg_pullback_x_gen_ne_zero W s hs hsK
  have hX₁_ord : (W_smooth W).ordAtInfty X₁ =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ordAtInfty_zsmul_frobenius_pullback_x_gen W r hr hrK
  have hX₂_ord : (W_smooth W).ordAtInfty X₂ = ((-2 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK
  have h_pow_X1 : (W_smooth W).ordAtInfty (X₁ ^ 2) =
      ((-4 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ord_pow_concrete hX₁_ne
      (-2 * (Fintype.card K : ℤ)) 2 hX₁_ord).trans ?_
    rw [WithTop.coe_inj]; ring
  have h_combined : (W_smooth W).ordAtInfty (X₁ ^ 2) +
      (W_smooth W).ordAtInfty X₂ =
      ((-4 * (Fintype.card K : ℤ) - 2 : ℤ) : WithTop ℤ) := by
    rw [h_pow_X1, hX₂_ord, ← WithTop.coe_add, WithTop.coe_inj]; ring
  exact ((W_smooth W).ordAtInfty_mul (pow_ne_zero 2 hX₁_ne) hX₂_ne).trans h_combined

/-- A non-dominant term: `ord(X₁ · X₂²) = -2q + 2·(-2) = -2q - 4`. -/
private lemma ord_zsmul_frobenius_mulByInt_neg_x_mul_x_sq_eq
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (x_gen W) *
          ((mulByInt W.toAffine (-s)).pullback (x_gen W)) ^ 2) =
      ((-2 * (Fintype.card K : ℤ) - 4 : ℤ) : WithTop ℤ) := by
  set X₁ := ((frobeniusIsog W).zsmul r).pullback (x_gen W) with hX₁_def
  set X₂ := (mulByInt W.toAffine (-s)).pullback (x_gen W) with hX₂_def
  have hX₁_ne : X₁ ≠ 0 := zsmul_frobenius_pullback_x_gen_ne_zero W r hr hrK
  have hX₂_ne : X₂ ≠ 0 := mulByInt_neg_pullback_x_gen_ne_zero W s hs hsK
  have hX₁_ord : (W_smooth W).ordAtInfty X₁ =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ordAtInfty_zsmul_frobenius_pullback_x_gen W r hr hrK
  have hX₂_ord : (W_smooth W).ordAtInfty X₂ = ((-2 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK
  have h_pow_X2 : (W_smooth W).ordAtInfty (X₂ ^ 2) = ((-4 : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ord_pow_concrete hX₂_ne (-2) 2 hX₂_ord).trans ?_
    rw [WithTop.coe_inj]; ring
  have h_combined : (W_smooth W).ordAtInfty X₁ +
      (W_smooth W).ordAtInfty (X₂ ^ 2) =
      ((-2 * (Fintype.card K : ℤ) - 4 : ℤ) : WithTop ℤ) := by
    rw [hX₁_ord, h_pow_X2, ← WithTop.coe_add, WithTop.coe_inj]; ring
  exact ((W_smooth W).ordAtInfty_mul hX₁_ne (pow_ne_zero 2 hX₂_ne)).trans h_combined

/-- The cross term `ord(X₁ · Y₂ + X₂ · Y₁) ≥ -2 - 3q`: the two summands have orders
`-2q - 3` and `-2 - 3q`, and for `q ≥ 2` the second is the smaller, giving the bound. -/
private lemma ord_zsmul_frobenius_mulByInt_neg_cross_ge
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        (((frobeniusIsog W).zsmul r).pullback (x_gen W) *
            (mulByInt W.toAffine (-s)).pullback (y_gen W) +
          (mulByInt W.toAffine (-s)).pullback (x_gen W) *
            ((frobeniusIsog W).zsmul r).pullback (y_gen W)) := by
  set X₁ := ((frobeniusIsog W).zsmul r).pullback (x_gen W) with hX₁_def
  set X₂ := (mulByInt W.toAffine (-s)).pullback (x_gen W) with hX₂_def
  set Y₁ := ((frobeniusIsog W).zsmul r).pullback (y_gen W) with hY₁_def
  set Y₂ := (mulByInt W.toAffine (-s)).pullback (y_gen W) with hY₂_def
  have hX₁_ne : X₁ ≠ 0 := zsmul_frobenius_pullback_x_gen_ne_zero W r hr hrK
  have hX₂_ne : X₂ ≠ 0 := mulByInt_neg_pullback_x_gen_ne_zero W s hs hsK
  have hY₁_ne : Y₁ ≠ 0 := zsmul_frobenius_pullback_y_gen_ne_zero W r hr hrK
  have hY₂_ne : Y₂ ≠ 0 := mulByInt_neg_pullback_y_gen_ne_zero W s hs hsK
  have hX₁_ord : (W_smooth W).ordAtInfty X₁ =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ordAtInfty_zsmul_frobenius_pullback_x_gen W r hr hrK
  have hX₂_ord : (W_smooth W).ordAtInfty X₂ = ((-2 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK
  have hY₁_ord : (W_smooth W).ordAtInfty Y₁ =
      ((-3 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ordAtInfty_zsmul_frobenius_pullback_y_gen W r hr hrK
  have hY₂_ord : (W_smooth W).ordAtInfty Y₂ = ((-3 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_neg_pullback_y_gen W s hs hsK
  have h_X1_Y2 : (W_smooth W).ordAtInfty (X₁ * Y₂) =
      ((-2 * (Fintype.card K : ℤ) - 3 : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul hX₁_ne hY₂_ne).trans ?_
    rw [hX₁_ord, hY₂_ord, ← WithTop.coe_add, WithTop.coe_inj]; ring
  have h_X2_Y1 : (W_smooth W).ordAtInfty (X₂ * Y₁) =
      ((-2 - 3 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul hX₂_ne hY₁_ne).trans ?_
    rw [hX₂_ord, hY₁_ord, ← WithTop.coe_add, WithTop.coe_inj]; ring
  have h_min_le := (W_smooth W).ordAtInfty_add_ge_min (X₁ * Y₂) (X₂ * Y₁)
  rw [h_X1_Y2, h_X2_Y1] at h_min_le
  refine le_trans ?_ h_min_le
  have h_ineq : (-2 - 3 * (Fintype.card K : ℤ) : ℤ) ≤
      min (-2 * (Fintype.card K : ℤ) - 3) (-2 - 3 * (Fintype.card K : ℤ)) := by
    apply le_min ?_ (le_refl _)
    have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
      exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
    linarith
  exact_mod_cast h_ineq

/-- The seven non-dominant "rest" terms of the reduced pair numerator together have
`ord_∞ ≥ -3q - 3`.  Each term clears the uniform bound (`-3q - 3` is the second-deepest
pole) — even in characteristic 2, where the `2·a₆`, `2·Y₁·Y₂`, `2·a₂·X₁·X₂` terms vanish —
and the bound is closed under the additions/subtractions via the generic `ord_*_ge`
helpers. -/
private lemma ord_zsmul_frobenius_mulByInt_neg_rest_ge
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (
        algebraMap K KE W.toAffine.a₄ *
            (((frobeniusIsog W).zsmul r).pullback (x_gen W) +
              (mulByInt W.toAffine (-s)).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (((frobeniusIsog W).zsmul r).pullback (y_gen W) +
                (mulByInt W.toAffine (-s)).pullback (y_gen W))
          - (2 : KE) * ((frobeniusIsog W).zsmul r).pullback (y_gen W) *
              (mulByInt W.toAffine (-s)).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (((frobeniusIsog W).zsmul r).pullback (x_gen W) *
                  (mulByInt W.toAffine (-s)).pullback (y_gen W) +
                (mulByInt W.toAffine (-s)).pullback (x_gen W) *
                  ((frobeniusIsog W).zsmul r).pullback (y_gen W))
          + ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
              ((mulByInt W.toAffine (-s)).pullback (x_gen W)) ^ 2
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
              (mulByInt W.toAffine (-s)).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
  set X₁ := ((frobeniusIsog W).zsmul r).pullback (x_gen W) with hX₁_def
  set X₂ := (mulByInt W.toAffine (-s)).pullback (x_gen W) with hX₂_def
  set Y₁ := ((frobeniusIsog W).zsmul r).pullback (y_gen W) with hY₁_def
  set Y₂ := (mulByInt W.toAffine (-s)).pullback (y_gen W) with hY₂_def
  have hX₁_ne : X₁ ≠ 0 := zsmul_frobenius_pullback_x_gen_ne_zero W r hr hrK
  have hX₂_ne : X₂ ≠ 0 := mulByInt_neg_pullback_x_gen_ne_zero W s hs hsK
  have hY₁_ne : Y₁ ≠ 0 := zsmul_frobenius_pullback_y_gen_ne_zero W r hr hrK
  have hY₂_ne : Y₂ ≠ 0 := mulByInt_neg_pullback_y_gen_ne_zero W s hs hsK
  have hX₁_ord : (W_smooth W).ordAtInfty X₁ =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ordAtInfty_zsmul_frobenius_pullback_x_gen W r hr hrK
  have hX₂_ord : (W_smooth W).ordAtInfty X₂ = ((-2 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK
  have hY₁_ord : (W_smooth W).ordAtInfty Y₁ =
      ((-3 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ordAtInfty_zsmul_frobenius_pullback_y_gen W r hr hrK
  have hY₂_ord : (W_smooth W).ordAtInfty Y₂ = ((-3 : ℤ) : WithTop ℤ) :=
    ordAtInfty_mulByInt_neg_pullback_y_gen W s hs hsK
  -- ord(X₁ + X₂) = -2q, ord(Y₁ + Y₂) = -3q.
  have h_X_sum : (W_smooth W).ordAtInfty (X₁ + X₂) =
      ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ord_zsmul_frobenius_mulByInt_neg_x_add_eq W r s hr hs hrK hsK
  have h_Y_sum : (W_smooth W).ordAtInfty (Y₁ + Y₂) =
      ((-3 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) :=
    ord_zsmul_frobenius_mulByInt_neg_y_add_eq W r s hr hs hrK hsK
  -- ord(Y₁ · Y₂) = -3q - 3, ord(X₁ · X₂) = -2q - 2.
  have h_Y_prod : (W_smooth W).ordAtInfty (Y₁ * Y₂) =
      ((-3 * (Fintype.card K : ℤ) - 3 : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul hY₁_ne hY₂_ne).trans ?_
    rw [hY₁_ord, hY₂_ord, ← WithTop.coe_add, WithTop.coe_inj]; ring
  have h_X_prod : (W_smooth W).ordAtInfty (X₁ * X₂) =
      ((-2 * (Fintype.card K : ℤ) - 2 : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul hX₁_ne hX₂_ne).trans ?_
    rw [hX₁_ord, hX₂_ord, ← WithTop.coe_add, WithTop.coe_inj]; ring
  have h_X1_X2_sq : (W_smooth W).ordAtInfty (X₁ * X₂ ^ 2) =
      ((-2 * (Fintype.card K : ℤ) - 4 : ℤ) : WithTop ℤ) :=
    ord_zsmul_frobenius_mulByInt_neg_x_mul_x_sq_eq W r s hr hs hrK hsK
  have h_cross : (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (X₁ * Y₂ + X₂ * Y₁) :=
    ord_zsmul_frobenius_mulByInt_neg_cross_ge W r s hr hs hrK hsK
  -- Term 1: a₄ · (X₁ + X₂). ord ≥ -3q-3.
  have h_t1 : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₄ * (X₁ + X₂)) := by
    refine ord_algebraMap_mul_ge W W.toAffine.a₄ ?_
    rw [h_X_sum]; exact_mod_cast (by linarith :
      (-3 * (Fintype.card K : ℤ) - 3 : ℤ) ≤ -2 * (Fintype.card K : ℤ))
  -- Term 2: 2 · a₆. ord ≥ -3q-3.
  have h_t2 : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty ((2 : KE) * algebraMap K KE W.toAffine.a₆) := by
    refine ord_two_mul_ge W ?_
    by_cases ha₆ : W.toAffine.a₆ = 0
    · rw [ha₆, map_zero]
      exact (W_smooth W).ordAtInfty_zero.symm ▸
        (le_top : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤ ⊤)
    · rw [ordAtInfty_algebraMap_F_nonzero W ha₆]
      exact_mod_cast (by linarith : (-3 * (Fintype.card K : ℤ) - 3 : ℤ) ≤ (0 : ℤ))
  -- Term 3: a₃ · (Y₁ + Y₂). ord ≥ -3q-3.
  have h_t3 : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ * (Y₁ + Y₂)) := by
    refine ord_algebraMap_mul_ge W W.toAffine.a₃ ?_
    rw [h_Y_sum]; exact_mod_cast (by linarith :
      (-3 * (Fintype.card K : ℤ) - 3 : ℤ) ≤ -3 * (Fintype.card K : ℤ))
  -- Term 4: 2 · Y₁ · Y₂. ord = -3q-3.
  have h_t4 : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty ((2 : KE) * Y₁ * Y₂) := by
    rw [show (2 : KE) * Y₁ * Y₂ = (2 : KE) * (Y₁ * Y₂) from by ring]
    refine ord_two_mul_ge W ?_
    rw [h_Y_prod]
  -- Term 5: a₁ · (X₁ · Y₂ + X₂ · Y₁). ord ≥ -3q-3.
  have h_t5 : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁ * (X₁ * Y₂ + X₂ * Y₁)) := by
    refine ord_algebraMap_mul_ge W W.toAffine.a₁ ?_
    refine le_trans ?_ h_cross
    exact_mod_cast (by linarith :
      (-3 * (Fintype.card K : ℤ) - 3 : ℤ) ≤ -2 - 3 * (Fintype.card K : ℤ))
  -- Term 6: X₁ · X₂². ord = -2q-4 ≥ -3q-3.
  have h_t6 : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (X₁ * X₂ ^ 2) := by
    rw [h_X1_X2_sq]; exact_mod_cast (by linarith :
      (-3 * (Fintype.card K : ℤ) - 3 : ℤ) ≤ -2 * (Fintype.card K : ℤ) - 4)
  -- Term 7: 2 · a₂ · X₁ · X₂. ord ≥ -3q-3.
  have h_t7 : (((-3 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((2 : KE) * algebraMap K KE W.toAffine.a₂ * X₁ * X₂) := by
    rw [show (2 : KE) * algebraMap K KE W.toAffine.a₂ * X₁ * X₂ =
        (2 : KE) * (algebraMap K KE W.toAffine.a₂ * (X₁ * X₂)) from by ring]
    refine ord_two_mul_ge W ?_
    refine ord_algebraMap_mul_ge W W.toAffine.a₂ ?_
    rw [h_X_prod]; exact_mod_cast (by linarith :
      (-3 * (Fintype.card K : ℤ) - 3 : ℤ) ≤ -2 * (Fintype.card K : ℤ) - 2)
  -- Chain the seven bounds.
  have h12 := ord_add_ge_of_both_ge W h_t1 h_t2
  have h123 := ord_sub_ge_of_both_ge W h12 h_t3
  have h1234 := ord_sub_ge_of_both_ge W h123 h_t4
  have h12345 := ord_sub_ge_of_both_ge W h1234 h_t5
  have h123456 := ord_add_ge_of_both_ge W h12345 h_t6
  exact ord_add_ge_of_both_ge W h123456 h_t7

/-- The Weierstrass reduction splits the reduced pair numerator as the dominant term
`X₁² · X₂` plus the seven-term rest sum. -/
private lemma addPullbackNumerator_reduced_pair_eq_dom_add_rest (r s : ℤ) :
    addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg W r s =
      (((frobeniusIsog W).zsmul r).pullback (x_gen W)) ^ 2 *
        (mulByInt W.toAffine (-s)).pullback (x_gen W) +
      (algebraMap K KE W.toAffine.a₄ *
            (((frobeniusIsog W).zsmul r).pullback (x_gen W) +
              (mulByInt W.toAffine (-s)).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (((frobeniusIsog W).zsmul r).pullback (y_gen W) +
                (mulByInt W.toAffine (-s)).pullback (y_gen W))
          - (2 : KE) * ((frobeniusIsog W).zsmul r).pullback (y_gen W) *
              (mulByInt W.toAffine (-s)).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (((frobeniusIsog W).zsmul r).pullback (x_gen W) *
                  (mulByInt W.toAffine (-s)).pullback (y_gen W) +
                (mulByInt W.toAffine (-s)).pullback (x_gen W) *
                  ((frobeniusIsog W).zsmul r).pullback (y_gen W))
          + ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
              ((mulByInt W.toAffine (-s)).pullback (x_gen W)) ^ 2
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
              (mulByInt W.toAffine (-s)).pullback (x_gen W)) := by
  unfold addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg
  ring

/-- The dominant term `X₁² · X₂` has strictly smaller `ord_∞` than the rest sum
(`-4q - 2 < -3q - 3` for `q ≥ 2`). -/
private lemma ord_zsmul_frobenius_mulByInt_neg_dom_lt_rest
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((((frobeniusIsog W).zsmul r).pullback (x_gen W)) ^ 2 *
          (mulByInt W.toAffine (-s)).pullback (x_gen W)) <
      (W_smooth W).ordAtInfty (
        algebraMap K KE W.toAffine.a₄ *
            (((frobeniusIsog W).zsmul r).pullback (x_gen W) +
              (mulByInt W.toAffine (-s)).pullback (x_gen W))
          + (2 : KE) * algebraMap K KE W.toAffine.a₆
          - algebraMap K KE W.toAffine.a₃ *
              (((frobeniusIsog W).zsmul r).pullback (y_gen W) +
                (mulByInt W.toAffine (-s)).pullback (y_gen W))
          - (2 : KE) * ((frobeniusIsog W).zsmul r).pullback (y_gen W) *
              (mulByInt W.toAffine (-s)).pullback (y_gen W)
          - algebraMap K KE W.toAffine.a₁ *
              (((frobeniusIsog W).zsmul r).pullback (x_gen W) *
                  (mulByInt W.toAffine (-s)).pullback (y_gen W) +
                (mulByInt W.toAffine (-s)).pullback (x_gen W) *
                  ((frobeniusIsog W).zsmul r).pullback (y_gen W))
          + ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
              ((mulByInt W.toAffine (-s)).pullback (x_gen W)) ^ 2
          + (2 : KE) * algebraMap K KE W.toAffine.a₂ *
              ((frobeniusIsog W).zsmul r).pullback (x_gen W) *
              (mulByInt W.toAffine (-s)).pullback (x_gen W)) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
  rw [ord_zsmul_frobenius_mulByInt_neg_x_sq_mul_eq W r s hr hs hrK hsK]
  refine lt_of_lt_of_le ?_ (ord_zsmul_frobenius_mulByInt_neg_rest_ge W r s hr hs hrK hsK)
  exact_mod_cast (by linarith :
    (-4 * (Fintype.card K : ℤ) - 2 : ℤ) < -3 * (Fintype.card K : ℤ) - 3)

/-- **`ord_∞(addPullbackNumerator_reduced_pair) = -4q - 2`** for `q ≥ 2`.
Dominant term: `α₁(x)² · α₂(x)` with `ord = 2·(-2q) + (-2) = -4q - 2`.
All other 7 terms have `ord ≥ -3q - 3` (strictly larger than -4q-2 for
q ≥ 2). -/
theorem ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg W r s) =
      (((-4 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) := by
  -- The reduced numerator splits as the dominant term `X₁² · X₂` (order `-4q - 2`)
  -- plus a seven-term rest sum of strictly larger order (`≥ -3q - 3`); strict
  -- non-archimedean additivity then picks out the dominant term.
  rw [addPullbackNumerator_reduced_pair_eq_dom_add_rest W r s]
  refine ((W_smooth W).ordAtInfty_add_eq_of_lt
    (ord_zsmul_frobenius_mulByInt_neg_dom_lt_rest W r s hr hs hrK hsK)).trans ?_
  exact ord_zsmul_frobenius_mulByInt_neg_x_sq_mul_eq W r s hr hs hrK hsK

/-- **`ord_∞(addPullback_x_pair (zsmul r π) (mulByInt -s)) = -2`** for
`q ≥ 2` and `r, s ≠ 0` with `(r : K), (s : K) ≠ 0`.

Combines `addPullbackNumerator_pair_eq` (numerator = `(X₁-X₂)² · addPullback_x_pair`)
with `ordAtInfty_addPullbackNumerator_reduced_pair_eq` (`ord(reduced) = -4q-2`)
and `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x` (`ord(X₁-X₂) = -2q`,
so `ord((X₁-X₂)²) = -4q`). The division `-4q-2 - (-4q) = -2` matches the
(1,1) value `ord_addPullback_x_negFrobenius = -2`. -/
theorem ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) =
      ((-2 : ℤ) : WithTop ℤ) := by
  set d := ((frobeniusIsog W).zsmul r).pullback (x_gen W) -
    (mulByInt W.toAffine (-s)).pullback (x_gen W) with hd_def
  have h_d_ne : d ≠ 0 :=
    zsmul_frobenius_sub_mulByInt_neg_x_ne_zero W r s hr hs hrK hsK
  have h_d_sq_ne : d ^ 2 ≠ 0 := pow_ne_zero 2 h_d_ne
  have h_den_ord : (W_smooth W).ordAtInfty (d ^ 2) =
      (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    refine ((W_smooth W).ord_pow_concrete h_d_ne
      (-2 * (Fintype.card K : ℤ)) 2
      (ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x W r s hr hs hrK hsK)).trans ?_
    congr 1; ring
  have h_num_ord : (W_smooth W).ordAtInfty
      (addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg W r s) =
      (((-4 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) :=
    (addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_reduced W r s hr hs).symm ▸
      ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq
        W r s hr hs hrK hsK
  have h_div_eq : addPullback_x_pair ((frobeniusIsog W).zsmul r)
      (mulByInt W.toAffine (-s)) =
      addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg W r s / d ^ 2 := by
    rw [addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq W r s hr hs hrK hsK,
      mul_div_cancel_left₀ _ h_d_sq_ne]
  rw [h_div_eq]
  refine ((W_smooth W).ord_div_concrete h_d_sq_ne
    (-4 * (Fintype.card K : ℤ) - 2)
    (-4 * (Fintype.card K : ℤ)) h_num_ord h_den_ord).trans ?_
  congr 1; ring

/-! ### D3c: the `y`-coordinate `∞`-order for the pair `(zsmul r π, mulByInt -s)`

The pair analogue of `ord_addPullback_y_negFrobenius = -3`.  The proof is the *same*
Weierstrass-equation argument: from `ord_∞(addPullback_x_pair) = -2` and the curve equation
`Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` (`addPullback_pair_equation`), the RHS has dominant pole
`ord(X³) = -6`, so the LHS — dominated by `ord(Y²) = 2·ord(Y)` once `ord(Y) ≤ -3` — forces
`ord(Y) = -3`.  This is the `y`-version `ord_∞ y_gen = -3` for the base-changed pencil's infinity
field (transported to `K̄` by `ordAtInftyBaseChange_holds`). -/

/-- Helper: `ord(X²) = -4` for the pair. -/
private theorem ord_addPullback_x_sq_pair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) ^ 2) =
      ((-4 : ℤ) : WithTop ℤ) := by
  haveI : (W_smooth W).toAffine.IsElliptic := inferInstanceAs W.toAffine.IsElliptic
  have hX_ne : addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) ≠ 0 :=
    fun h ↦ WithTop.coe_ne_top
      (((W_smooth W).ordAtInfty_eq_top_iff _).mpr h ▸
        ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK).symm
  refine ((W_smooth W).ord_pow_concrete hX_ne (-2) 2
    (ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK)).trans ?_
  rfl

/-- Helper: `ord(X³) = -6` for the pair. -/
private theorem ord_addPullback_x_cube_pair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) ^ 3) =
      ((-6 : ℤ) : WithTop ℤ) := by
  haveI : (W_smooth W).toAffine.IsElliptic := inferInstanceAs W.toAffine.IsElliptic
  have hX_ne : addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) ≠ 0 :=
    fun h ↦ WithTop.coe_ne_top
      (((W_smooth W).ordAtInfty_eq_top_iff _).mpr h ▸
        ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK).symm
  refine ((W_smooth W).ord_pow_concrete hX_ne (-2) 3
    (ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK)).trans ?_
  rfl

/-- Helper: `ord(X³ + a₂·X² + a₄·X + a₆) = -6` for the pair (the Weierstrass RHS). -/
private theorem ord_RHS_pair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        (addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) ^ 3 +
         algebraMap K KE W.toAffine.a₂ *
           addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) ^ 2 +
         algebraMap K KE W.toAffine.a₄ *
           addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) +
         algebraMap K KE W.toAffine.a₆) =
      ((-6 : ℤ) : WithTop ℤ) := by
  haveI : (W_smooth W).toAffine.IsElliptic := inferInstanceAs W.toAffine.IsElliptic
  set X := addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) with hX
  have h_X3 : (W_smooth W).ordAtInfty (X ^ 3) = ((-6 : ℤ) : WithTop ℤ) :=
    ord_addPullback_x_cube_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK
  have h_a2X2 : ((-4 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₂ * X ^ 2) :=
    ord_algebraMap_mul_ge W W.toAffine.a₂
      (ord_addPullback_x_sq_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK).symm.le
  have h_a4X : ((-2 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₄ * X) :=
    ord_algebraMap_mul_ge W W.toAffine.a₄
      (ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK).symm.le
  have step1 : (W_smooth W).ordAtInfty
      (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2) = ((-6 : ℤ) : WithTop ℤ) := by
    have h_lt : (W_smooth W).ordAtInfty (X ^ 3) <
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₂ * X ^ 2) := by
      rw [h_X3]; refine lt_of_lt_of_le ?_ h_a2X2
      exact_mod_cast (by norm_num : (-6 : ℤ) < -4)
    exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans h_X3
  have step2 : (W_smooth W).ordAtInfty
      (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2 + algebraMap K KE W.toAffine.a₄ * X) =
      ((-6 : ℤ) : WithTop ℤ) := by
    have h_lt : (W_smooth W).ordAtInfty
        (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2) <
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₄ * X) := by
      rw [step1]; refine lt_of_lt_of_le ?_ h_a4X
      exact_mod_cast (by norm_num : (-6 : ℤ) < -2)
    exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans step1
  have h_lt : (W_smooth W).ordAtInfty
      (X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2 + algebraMap K KE W.toAffine.a₄ * X) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₆) := by
    rw [step2]; refine lt_of_lt_of_le ?_ (ord_a₆_ge_zero W)
    show ((-6 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl]
    exact_mod_cast (by norm_num : (-6 : ℤ) < 0)
  exact ((W_smooth W).ordAtInfty_add_eq_of_lt h_lt).trans step2

/-- **`ord_∞(addPullback_y_pair (zsmul r π) (mulByInt -s)) = -3`** — the pole of order `3` at `O`
for the genuine pencil `rπ − s`.  Pair analogue of `ord_addPullback_y_negFrobenius`.  From the curve
equation (`addPullback_pair_equation`), `ord_∞ X = -2`, and the dominant `ord(X³) = -6`: writing
`m = ord(Y)`, the equation gives `ord(Y² + a₁XY + a₃Y) = -6`; one shows `m ≤ -3` (else `Y²` would not
reach `-6`), then `Y²` strictly dominates, forcing `2m = -6`, i.e. `m = -3`. -/
theorem ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((addPullback_y_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s))) : KE) =
      ((-3 : ℤ) : WithTop ℤ) := by
  haveI : (W_smooth W).toAffine.IsElliptic := inferInstanceAs W.toAffine.IsElliptic
  set X := addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) with hX
  set Y := addPullback_y_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) with hY
  have hX_ord : (W_smooth W).ordAtInfty X = ((-2 : ℤ) : WithTop ℤ) :=
    ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK
  have hX_ne : X ≠ 0 := by
    intro h
    have ht : (W_smooth W).ordAtInfty X = ⊤ := by rw [h]; exact (W_smooth W).ordAtInfty_zero
    rw [hX_ord] at ht; exact WithTop.coe_ne_top ht
  -- Curve equation in standard form (from the pair `AddNonInversePair`).
  have h_eq : Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y + algebraMap K KE W.toAffine.a₃ * Y =
      X ^ 3 + algebraMap K KE W.toAffine.a₂ * X ^ 2 + algebraMap K KE W.toAffine.a₄ * X +
        algebraMap K KE W.toAffine.a₆ := by
    have h := addPullback_pair_equation
      (AddNonInversePair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK)
    rw [WeierstrassCurve.Affine.equation_iff] at h
    exact h
  have h_lhs_ord : (W_smooth W).ordAtInfty
        (Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y + algebraMap K KE W.toAffine.a₃ * Y) =
      ((-6 : ℤ) : WithTop ℤ) :=
    h_eq ▸ ord_RHS_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK
  -- Y ≠ 0.
  have hY_ne : Y ≠ 0 := by
    intro h
    have h_zero : Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y +
        algebraMap K KE W.toAffine.a₃ * Y = 0 := by rw [h]; ring
    have h_ord_eq : (W_smooth W).ordAtInfty
        (Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y + algebraMap K KE W.toAffine.a₃ * Y) = ⊤ :=
      (congrArg (W_smooth W).ordAtInfty h_zero).trans (W_smooth W).ordAtInfty_zero
    exact WithTop.top_ne_coe (h_ord_eq.symm.trans h_lhs_ord)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ordAtInfty Y = ((m : ℤ) : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((W_smooth W).ordAtInfty_eq_top_iff _).not.mpr hY_ne)
    exact ⟨m, hm.symm⟩
  have hY_sq_ord : (W_smooth W).ordAtInfty (Y ^ 2) = ((2 * m : ℤ) : WithTop ℤ) :=
    (W_smooth W).ord_pow_concrete hY_ne m 2 hm
  have h_xy_ord : (W_smooth W).ordAtInfty (X * Y) = (((-2 + m : ℤ)) : WithTop ℤ) := by
    refine ((W_smooth W).ordAtInfty_mul hX_ne hY_ne).trans ?_
    rw [hX_ord, hm]; push_cast; rfl
  -- Step (a): m ≤ -3.
  have h_m_le : m ≤ -3 := by
    by_contra h_not_le
    push Not at h_not_le
    have h_y_sq_ge : ((-4 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (Y ^ 2) := by
      rw [hY_sq_ord]; exact_mod_cast (by linarith : (-4 : ℤ) ≤ 2 * m)
    have h_a1xy_ge : ((-4 : ℤ) : WithTop ℤ) ≤
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁ * X * Y) := by
      rw [show algebraMap K KE W.toAffine.a₁ * X * Y =
          algebraMap K KE W.toAffine.a₁ * (X * Y) from by ring]
      refine ord_algebraMap_mul_ge W W.toAffine.a₁ ?_
      rw [h_xy_ord]; exact_mod_cast (by linarith : (-4 : ℤ) ≤ -2 + m)
    have h_a3y_ge : ((-4 : ℤ) : WithTop ℤ) ≤
        (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ * Y) := by
      refine ord_algebraMap_mul_ge W W.toAffine.a₃ ?_
      rw [hm]; exact_mod_cast (by linarith : (-4 : ℤ) ≤ m)
    have h_lhs_ge : ((-4 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y + algebraMap K KE W.toAffine.a₃ * Y) :=
      ord_add_ge_of_both_ge W (ord_add_ge_of_both_ge W h_y_sq_ge h_a1xy_ge) h_a3y_ge
    rw [h_lhs_ord] at h_lhs_ge
    have h46 : (-4 : ℤ) ≤ -6 := by exact_mod_cast h_lhs_ge
    omega
  -- Step (b): Y² strictly dominates ⟹ ord(LHS) = 2m.
  have h_a1xy_gt : (W_smooth W).ordAtInfty (Y ^ 2) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₁ * X * Y) := by
    rw [hY_sq_ord, show algebraMap K KE W.toAffine.a₁ * X * Y =
        algebraMap K KE W.toAffine.a₁ * (X * Y) from by ring]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge W W.toAffine.a₁
      (n := (((-2 + m : ℤ)) : WithTop ℤ)) (le_of_eq h_xy_ord.symm))
    exact_mod_cast (by linarith : (2 * m : ℤ) < -2 + m)
  have h_a3y_gt : (W_smooth W).ordAtInfty (Y ^ 2) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ * Y) := by
    rw [hY_sq_ord]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge W W.toAffine.a₃
      (n := ((m : ℤ) : WithTop ℤ)) (le_of_eq hm.symm))
    exact_mod_cast (by linarith : (2 * m : ℤ) < m)
  have h_inner_eq : (W_smooth W).ordAtInfty
      (Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y) =
      (W_smooth W).ordAtInfty (Y ^ 2) :=
    (W_smooth W).ordAtInfty_add_eq_of_lt h_a1xy_gt
  have h_a3y_gt' : (W_smooth W).ordAtInfty
      (Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y) <
      (W_smooth W).ordAtInfty (algebraMap K KE W.toAffine.a₃ * Y) := h_inner_eq ▸ h_a3y_gt
  have h_outer_eq : (W_smooth W).ordAtInfty
      (Y ^ 2 + algebraMap K KE W.toAffine.a₁ * X * Y + algebraMap K KE W.toAffine.a₃ * Y) =
      (W_smooth W).ordAtInfty (Y ^ 2) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt h_a3y_gt').trans h_inner_eq
  rw [h_outer_eq, hY_sq_ord] at h_lhs_ord
  have h_2m : (2 * m : ℤ) = -6 := by exact_mod_cast h_lhs_ord
  rw [hm]; exact_mod_cast (by omega : m = -3)

/-! ### D4: pole-bound-parametric `genuineIsogSmulSub`

Worker D consumes `genuineIsogSmulSub r s` for the genuine `r·π - s·id`
isogeny. The constructor needs:
1. The `AddNonInversePair` witness — shipped axiom-clean as
   `AddNonInversePair_zsmul_frobenius_mulByInt_neg`.
2. `addCoordAlgHomPair`-injectivity — reducible (via base-hom + transcendence
   chain) to a pole bound `ord_∞ < 0` on the pair pullback x-coord.

We ship the **pole-bound-parametric** form. The pole bound discharges
axiom-clean via the same numerator/denominator/Weierstrass-reduction
chain as `ord_addPullback_x_negFrobenius` (the (1,1) base case here),
mirrored to the pair version with α₁(x)²·α₂(x) as the dominant term
(ord = -4q-2). Worker D supplies the pole bound (or waits for the
follow-up axiom-clean discharge). -/

/-- **Witness-parametric base-hom injectivity** for the
`(zsmul r π, mulByInt -s)` family: takes the pole bound hypothesis
(`ord_∞ < 0`) and discharges base-hom injectivity via the
σ-invariance + K(x) image + algebraic_in_fracRing_eq_const chain. -/
theorem addBaseHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) < 0) :
    Function.Injective
      (addBaseHomPair ((frobeniusIsog W).zsmul r)
        (mulByInt W.toAffine (-s))) := by
  rw [addBaseHomPair_eq_aeval]
  apply transcendental_iff_injective.mp
  intro h_alg
  obtain ⟨a, ha⟩ := addPullback_x_pair_zsmul_frobenius_mulByInt_neg_in_KX_image
    W r s hr hs hrK hsK
  have h_inj : Function.Injective (algebraMap (FractionRing (Polynomial K)) KE) :=
    (algebraMap (FractionRing (Polynomial K)) KE).injective
  have ha_alg : IsAlgebraic K a := by
    by_contra h_trans
    have h_px_trans : Transcendental K
        (addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) := by
      rw [ha]
      exact (transcendental_algebraMap_iff h_inj).mpr h_trans
    exact h_px_trans h_alg
  obtain ⟨c, hc⟩ := algebraic_in_fracRing_eq_const a ha_alg
  have hc' : addPullback_x_pair ((frobeniusIsog W).zsmul r)
      (mulByInt W.toAffine (-s)) = algebraMap K KE c := by
    rw [ha, hc, ← IsScalarTower.algebraMap_apply K (FractionRing (Polynomial K)) KE]
  by_cases hc_zero : c = 0
  · have h0 : addPullback_x_pair ((frobeniusIsog W).zsmul r)
        (mulByInt W.toAffine (-s)) = 0 := by rw [hc', hc_zero, map_zero]
    have h_top : (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) = ⊤ := by
      rw [h0]; exact (W_smooth W).ordAtInfty_zero
    rw [h_top] at h_pole
    exact absurd h_pole (not_lt_of_ge le_top)
  · have h_ord_c : (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) = 0 := by
      rw [hc']; exact ordAtInfty_algebraMap_F_nonzero W hc_zero
    rw [h_ord_c] at h_pole
    exact absurd h_pole (lt_irrefl _)

/-- **Witness-parametric `addCoordAlgHomPair` injectivity** for the
`(zsmul r π, mulByInt -s)` family, taking the pole bound as a
hypothesis. -/
theorem addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) < 0) :
    Function.Injective
      (addCoordAlgHomPair
        (AddNonInversePair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK)) :=
  addCoordAlgHomPair_injective_of_baseHom_inj _
    (addBaseHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole
      W r s hr hs hrK hsK h_pole)

/-- **D4: genuine `r·π - s·id` isogeny constructor (pole-bound-parametric)**.

The genuine `r·π - s·id` isogeny with the *real* function-field pullback
(replacing the `AlgHom.id` placeholder of `Endomorphism.lean`'s
`isogSmulSub`). On rational points equals
`(zsmul r π).toAddMonoidHom + (mulByInt -s).toAddMonoidHom`.

Worker D in `DegreeQuadraticForm.lean` consumes this as the `r·π - s·id`
isogeny family. The pole bound discharges axiom-clean via the same
numerator chain as `ord_addPullback_x_negFrobenius` (the (1,1) base
case), mirrored to the pair version. -/
noncomputable def genuineIsogSmulSub_of_pole
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) < 0) :
    Isogeny W.toAffine W.toAffine :=
  addIsog
    (AddNonInversePair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK)
    (addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole
      W r s hr hs hrK hsK h_pole)

@[simp] theorem genuineIsogSmulSub_of_pole_toAddMonoidHom
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) < 0) :
    (genuineIsogSmulSub_of_pole W r s hr hs hrK hsK h_pole).toAddMonoidHom =
      ((frobeniusIsog W).zsmul r).toAddMonoidHom +
        (mulByInt W.toAffine (-s)).toAddMonoidHom :=
  rfl

/-! ### D4 unconditional: `genuineIsogSmulSub`

With `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg = -2 < 0`
discharged axiom-clean, the witness-parametric `genuineIsogSmulSub_of_pole`
becomes unconditional. The unconditional form is what Worker D consumes
in `DegreeQuadraticForm.lean` for the polarisation. -/

/-- The pole bound `ord_∞ < 0` discharges from
`ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg = -2`. -/
private theorem h_pole_discharge
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((frobeniusIsog W).zsmul r)
          (mulByInt W.toAffine (-s))) : KE) < 0 := by
  rw [ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK]
  exact_mod_cast (by norm_num : (-2 : ℤ) < 0)

/-- **D4 (unconditional)**: the genuine `r·π - s·id` isogeny for
`r, s ≠ 0` with `(r : K), (s : K) ≠ 0`. Pullback is the *real*
function-field pullback; on rational points equals
`r · π + (-s) · id = r · π - s · id`. Worker D in
`DegreeQuadraticForm.lean` consumes this directly. -/
noncomputable def genuineIsogSmulSub
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    Isogeny W.toAffine W.toAffine :=
  genuineIsogSmulSub_of_pole W r s hr hs hrK hsK
    (h_pole_discharge W r s hr hs hrK hsK)

@[simp] theorem genuineIsogSmulSub_toAddMonoidHom
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom =
      ((frobeniusIsog W).zsmul r).toAddMonoidHom +
        (mulByInt W.toAffine (-s)).toAddMonoidHom :=
  rfl

/-! ### D4 inseparable: the `p ∣ r` pole bound `ord_∞(addPullback_x_pair) = -2`

For the **inseparable** pencil summand `r·π` (when `p ∣ r`, so `(r : K) = 0`), the `x`-pole of
`α₁ = (frobeniusIsog).zsmul r` is `ord_∞(α₁^* x_gen) = q·M` with `M = ord_∞(mulByInt_x r) ≤ -2` (even),
which is **strictly deeper** than the `x`-pole `ord_∞(α₂^* x_gen) = -2` of `α₂ = mulByInt (-s)`
(`p ∤ s`).  This *asymmetry* — `q·M ≤ -4 < -2` — makes the Weierstrass-reduced addition numerator have a
**unique strictly-dominant** term `X₁²·X₂` (order `2qM − 2`), avoiding the symmetric 3-way tie of
`addPullback_x_pair_x_ord_neg` (which needs the formal group).  The result `ord_∞(addPullback_x_pair) =
(2qM − 2) − 2qM = −2` is **independent** of the exact `M`.  This is the genuine new content for the
`p ∣ r` member of the pencil; the value `−2` matches the separable
`ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`. -/

/-- **`ord_∞(α₁^* x_gen − α₂^* x_gen) = q·M`** (inseparable): `α₁^* x_gen` (order `qM ≤ -4`) strictly
dominates `α₂^* x_gen` (order `-2`).  Mirror of `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x` with the
inseparable `qM` in place of `-2q`. -/
theorem ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x_of_x
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) {M : ℤ}
    (hM : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ)) (hM_le : M ≤ -2) :
    (W_smooth W).ordAtInfty
        ((((frobeniusIsog W).zsmul r).pullback (x_gen W) -
          (mulByInt W.toAffine (-s)).pullback (x_gen W)) : KE) =
      (((Fintype.card K : ℤ) * M : ℤ) : WithTop ℤ) := by
  have h_q : (1 : ℤ) < (Fintype.card K : ℤ) := by
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K))
  have h_lt : ((Fintype.card K : ℤ) * M : ℤ) < -2 := by nlinarith
  exact (W_smooth W).ord_sub_lt_concrete ((Fintype.card K : ℤ) * M) (-2) h_lt
    (ordAtInfty_zsmul_frobenius_pullback_x_gen_of_x W r hr hM)
    (ordAtInfty_mulByInt_neg_pullback_x_gen W s hs hsK)

/-- **`α₁^* x_gen − α₂^* x_gen ≠ 0`** (inseparable), from the order `qM ≠ ⊤`. -/
theorem zsmul_frobenius_sub_mulByInt_neg_x_ne_zero_of_x
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) {M : ℤ}
    (hM : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ)) (hM_le : M ≤ -2) :
    (((frobeniusIsog W).zsmul r).pullback (x_gen W) -
      (mulByInt W.toAffine (-s)).pullback (x_gen W)) ≠ (0 : KE) := by
  intro h
  have h_top : (W_smooth W).ordAtInfty
      ((((frobeniusIsog W).zsmul r).pullback (x_gen W) -
        (mulByInt W.toAffine (-s)).pullback (x_gen W)) : KE) = ⊤ := by
    rw [h]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x_of_x W r s hr hs hsK hM hM_le] at h_top
  exact WithTop.coe_ne_top h_top

/-- **`AddNonInversePair (α₁ := (frobeniusIsog).zsmul r) (α₂ := mulByInt (-s))`** (inseparable case):
the two `x`-pullbacks differ (different `∞`-orders `qM ≠ -2`).  Mirror of
`AddNonInversePair_zsmul_frobenius_mulByInt_neg` valid for `(r : K) = 0`. -/
theorem AddNonInversePair_zsmul_frobenius_mulByInt_neg_of_x
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hsK : (s : K) ≠ 0) {M : ℤ}
    (hM : (W_smooth W).ordAtInfty (mulByInt_x W r) = ((M : ℤ) : WithTop ℤ)) (hM_le : M ≤ -2) :
    AddNonInversePair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) :=
  AddNonInversePair_of_x_ne (sub_ne_zero.mp
    (zsmul_frobenius_sub_mulByInt_neg_x_ne_zero_of_x W r s hr hs hsK hM hM_le))

/-- **Numerator clearing** (parametric on `d := α₁^* x_gen − α₂^* x_gen ≠ 0`):
`addPullbackNumerator_pair = d² · addPullback_x_pair`.  Body-identical to
`addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq` but taking `hd_ne` directly (so it also
serves the inseparable `(r : K) = 0` case). -/
theorem addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_of_hd_ne
    (r s : ℤ)
    (hd_ne : (((frobeniusIsog W).zsmul r).pullback (x_gen W) -
      (mulByInt W.toAffine (-s)).pullback (x_gen W)) ≠ (0 : KE)) :
    addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg W r s =
      (((frobeniusIsog W).zsmul r).pullback (x_gen W) -
        (mulByInt W.toAffine (-s)).pullback (x_gen W)) ^ 2 *
      addPullback_x_pair ((frobeniusIsog W).zsmul r)
        (mulByInt W.toAffine (-s)) := by
  set d := ((frobeniusIsog W).zsmul r).pullback (x_gen W) -
    (mulByInt W.toAffine (-s)).pullback (x_gen W) with hd_def
  set n := ((frobeniusIsog W).zsmul r).pullback (y_gen W) -
    (mulByInt W.toAffine (-s)).pullback (y_gen W) with hn_def
  have hL : addSlopePair ((frobeniusIsog W).zsmul r)
        (mulByInt W.toAffine (-s)) = n / d := by
    unfold addSlopePair
    exact Affine.slope_of_X_ne (sub_ne_zero.mp hd_ne)
  unfold addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg addPullback_x_pair
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ +
            ((frobeniusIsog W).zsmul r).pullback (x_gen W) +
            (mulByInt W.toAffine (-s)).pullback (x_gen W)) =
      d ^ 2 * (W_KE W).toAffine.addX (((frobeniusIsog W).zsmul r).pullback (x_gen W))
        ((mulByInt W.toAffine (-s)).pullback (x_gen W))
        (addSlopePair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)))
  unfold WeierstrassCurve.Affine.addX
  rw [hL]
  show n ^ 2 + algebraMap K KE W.toAffine.a₁ * d * n
        - d ^ 2 * (algebraMap K KE W.toAffine.a₂ +
            ((frobeniusIsog W).zsmul r).pullback (x_gen W) +
            (mulByInt W.toAffine (-s)).pullback (x_gen W)) =
      d ^ 2 * ((n / d) ^ 2 + (W_KE W).toAffine.a₁ * (n / d) -
        (W_KE W).toAffine.a₂ -
        ((frobeniusIsog W).zsmul r).pullback (x_gen W) -
        (mulByInt W.toAffine (-s)).pullback (x_gen W))
  have h_a1_lift : (W_KE W).toAffine.a₁ = algebraMap K KE W.toAffine.a₁ := rfl
  have h_a2_lift : (W_KE W).toAffine.a₂ = algebraMap K KE W.toAffine.a₂ := rfl
  rw [h_a1_lift, h_a2_lift]
  field_simp
  ring

end HasseWeil
