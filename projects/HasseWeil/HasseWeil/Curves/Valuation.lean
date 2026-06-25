import HasseWeil.Curves.DVR
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The discrete valuation at a smooth point

For a smooth plane curve `C` over a field `F` and a smooth point `P ∈ C`, the
local ring at `P` is a discrete valuation ring (Silverman II.1.1, closed by
`T-II-1-001`). This file extracts the associated additive valuation on the
function field,

```
ord_P : F(C) → WithTop ℤ.
```

The construction proceeds via mathlib's adic-valuation machinery: the local
ring is a DVR, which gives a `HeightOneSpectrum` element, and the induced
valuation on its fraction field — which is precisely `F(C)` — has values in
`ℤᵐ⁰ := WithZero (Multiplicative ℤ)`. We translate this multiplicative
formulation to the additive `WithTop ℤ` convention used by Silverman.

This closes ticket `T-II-1-002`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.1 (definition after
  II.1.1)
-/

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F]

instance maximalIdealAt_isPrime (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    (C.maximalIdealAt P).IsPrime :=
  (C.maximalIdealAt_isMaximal P).isPrime

/-- The local ring of a smooth plane curve at a smooth point. -/
noncomputable abbrev localRingAt (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    Type _ :=
  Localization.AtPrime (C.maximalIdealAt P)

noncomputable instance localRingAt.instIsDVR
    (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    IsDiscreteValuationRing (C.localRingAt P) :=
  C.localRing_isDVR_of_smooth P

/-- The function field of a smooth plane curve is the fraction field of its
local ring at any smooth point. Both rings are localizations of the same
coordinate ring. -/
noncomputable instance localRingAt.instIsFractionRing
    (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    IsFractionRing (C.localRingAt P) C.FunctionField :=
  inferInstanceAs <| IsFractionRing
    (Localization.AtPrime (C.maximalIdealAt P))
    (FractionRing C.CoordinateRing)

/-- The multiplicative `v`-adic valuation on the function field associated with
a smooth point `P` of `C`, with values in `ℤᵐ⁰ := WithZero (Multiplicative ℤ)`.
Reference: Silverman II.1. -/
noncomputable def pointValuation (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    Valuation C.FunctionField (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal (C.localRingAt P)).valuation C.FunctionField

/-- The order of a function at a smooth point of the curve.
Returns `↑n : WithTop ℤ` for a nonzero function, and `⊤` for the zero
function.
Reference: Silverman II.1 (definition after II.1.1). -/
noncomputable def ord_P (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    (f : C.FunctionField) : WithTop ℤ :=
  if h : C.pointValuation P f = 0 then ⊤
  else (- (WithZero.unzero h).toAdd : ℤ)

variable {C : SmoothPlaneCurve F} {P : C.SmoothPoint}

theorem pointValuation_eq_zero_iff (f : C.FunctionField) :
    C.pointValuation P f = 0 ↔ f = 0 :=
  (C.pointValuation P).zero_iff

private theorem pointValuation_ne_zero {f : C.FunctionField} (hf : f ≠ 0) :
    C.pointValuation P f ≠ 0 :=
  (C.pointValuation P).ne_zero_iff.mpr hf

@[simp] theorem ord_P_zero : C.ord_P P 0 = ⊤ := by
  simp [ord_P]

theorem ord_P_eq_top_iff (f : C.FunctionField) : C.ord_P P f = ⊤ ↔ f = 0 := by
  unfold ord_P
  split_ifs with h
  · simp [(pointValuation_eq_zero_iff f).mp h]
  · simp only [WithTop.coe_ne_top, false_iff]
    intro hf; exact h ((pointValuation_eq_zero_iff f).mpr hf)

private lemma ord_P_of_ne (f : C.FunctionField)
    (h : C.pointValuation P f ≠ 0) :
    C.ord_P P f = (- (WithZero.unzero h).toAdd : ℤ) := dif_neg h

/-- **Order-positivity bridge**: for a nonzero `f ∈ F(C)`,
`ord_P(f) ≥ 1 ↔ pointValuation(f) < 1`. The forward direction is the defining
property of the maximal ideal; the reverse is by strict inequality on the
value group. -/
theorem one_le_ord_P_iff_pointValuation_lt_one {f : C.FunctionField}
    (hf : f ≠ 0) :
    (1 : WithTop ℤ) ≤ C.ord_P P f ↔ C.pointValuation P f < 1 := by
  have hv : C.pointValuation P f ≠ 0 := pointValuation_ne_zero hf
  rw [ord_P_of_ne _ hv, show (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) from rfl,
    WithTop.coe_le_coe]
  constructor
  · intro h
    have h_toAdd : (WithZero.unzero hv).toAdd ≤ -1 := by omega
    have : WithZero.unzero hv < 1 := by
      rw [← Multiplicative.toAdd_lt]; exact lt_of_le_of_lt h_toAdd (by norm_num)
    rwa [← WithZero.coe_unzero hv, ← WithZero.coe_one, WithZero.coe_lt_coe]
  · intro h
    rw [← WithZero.coe_unzero hv, ← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [← Multiplicative.toAdd_lt, toAdd_one] at h
    omega

theorem ord_P_mul (f g : C.FunctionField) :
    C.ord_P P (f * g) = C.ord_P P f + C.ord_P P g := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hvf : C.pointValuation P f ≠ 0 := pointValuation_ne_zero hf
  have hvg : C.pointValuation P g ≠ 0 := pointValuation_ne_zero hg
  have hvfg : C.pointValuation P (f * g) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hvf hvg
  rw [ord_P_of_ne _ hvf, ord_P_of_ne _ hvg, ord_P_of_ne _ hvfg]
  have key : (WithZero.unzero hvfg).toAdd =
      (WithZero.unzero hvf).toAdd + (WithZero.unzero hvg).toAdd := by
    rw [← toAdd_mul]
    congr 1
    rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero,
        WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [key, neg_add, ← WithTop.coe_add]

theorem ord_P_add_le (f g : C.FunctionField) :
    min (C.ord_P P f) (C.ord_P P g) ≤ C.ord_P P (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  rcases eq_or_ne (f + g) 0 with hfg0 | hfg0
  · rw [hfg0, ord_P_zero]; exact le_top
  have hvf : C.pointValuation P f ≠ 0 := pointValuation_ne_zero hf
  have hvg : C.pointValuation P g ≠ 0 := pointValuation_ne_zero hg
  have hvfg : C.pointValuation P (f + g) ≠ 0 := pointValuation_ne_zero hfg0
  have hadd : C.pointValuation P (f + g) ≤
      max (C.pointValuation P f) (C.pointValuation P g) :=
    Valuation.map_add _ _ _
  rw [ord_P_of_ne _ hvf, ord_P_of_ne _ hvg, ord_P_of_ne _ hvfg]
  rcases le_max_iff.mp hadd with hle | hle
  · apply (min_le_left _ _).trans
    rw [WithTop.coe_le_coe, neg_le_neg_iff]
    rwa [← WithZero.coe_unzero hvfg, ← WithZero.coe_unzero hvf,
      WithZero.coe_le_coe] at hle
  · apply (min_le_right _ _).trans
    rw [WithTop.coe_le_coe, neg_le_neg_iff]
    rwa [← WithZero.coe_unzero hvfg, ← WithZero.coe_unzero hvg,
      WithZero.coe_le_coe] at hle

theorem ord_P_inv (f : C.FunctionField) (hf : f ≠ 0) :
    C.ord_P P f⁻¹ = -(C.ord_P P f) := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hvf : C.pointValuation P f ≠ 0 := pointValuation_ne_zero hf
  have hvfi : C.pointValuation P f⁻¹ ≠ 0 := pointValuation_ne_zero hfi
  rw [ord_P_of_ne _ hvf, ord_P_of_ne _ hvfi]
  have key : (WithZero.unzero hvfi).toAdd = -(WithZero.unzero hvf).toAdd := by
    rw [show -(WithZero.unzero hvf).toAdd = (WithZero.unzero hvf)⁻¹.toAdd from
      (toAdd_inv _).symm]
    congr 1
    rw [← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_inv,
      WithZero.coe_unzero, map_inv₀]
  rw [key]
  push_cast
  rfl

@[simp] theorem ord_P_one : C.ord_P P (1 : C.FunctionField) = 0 := by
  have hv : C.pointValuation P 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  rw [ord_P_of_ne _ hv]
  have : WithZero.unzero hv = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero]; exact map_one _
  rw [this]; rfl

theorem ord_P_pow (f : C.FunctionField) (n : ℕ) :
    C.ord_P P (f ^ n) = n • C.ord_P P f := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ord_P_mul, ih, succ_nsmul]

@[simp] theorem ord_P_neg (f : C.FunctionField) :
    C.ord_P P (-f) = C.ord_P P f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero]
  have hvf : C.pointValuation P f ≠ 0 := pointValuation_ne_zero hf
  have hvneg : C.pointValuation P (-f) ≠ 0 := by
    rw [Valuation.map_neg]; exact hvf
  rw [ord_P_of_ne _ hvneg, ord_P_of_ne _ hvf]
  congr 3
  apply WithZero.coe_injective
  rw [WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_neg]

/-- **Strict non-archimedean for `ord_P`**: when `ord_P f < ord_P g`, the
dominant term wins: `ord_P (f + g) = ord_P f`. Parallels
`ordAtInfty_add_eq_of_lt`. -/
theorem ord_P_add_eq_of_lt {f g : C.FunctionField}
    (h : C.ord_P P f < C.ord_P P g) :
    C.ord_P P (f + g) = C.ord_P P f := by
  have h_ge : C.ord_P P f ≤ C.ord_P P (f + g) := by
    have := ord_P_add_le (P := P) f g
    rwa [min_eq_left h.le] at this
  have h_step : (f + g) + (-g) = f := by ring
  have h_le_step := ord_P_add_le (P := P) (f + g) (-g)
  rw [h_step, ord_P_neg (P := P) g] at h_le_step
  rcases le_total (C.ord_P P (f + g)) (C.ord_P P g) with h_case | h_case
  · rw [min_eq_left h_case] at h_le_step
    exact le_antisymm h_le_step h_ge
  · rw [min_eq_right h_case] at h_le_step
    exact absurd (lt_of_lt_of_le h h_le_step) (lt_irrefl _)

/-- Subtraction variant of `ord_P_add_eq_of_lt`: when `ord_P f < ord_P g`,
`ord_P (f − g) = ord_P f`. -/
theorem ord_P_sub_eq_of_lt {f g : C.FunctionField}
    (h : C.ord_P P f < C.ord_P P g) :
    C.ord_P P (f - g) = C.ord_P P f := by
  rw [sub_eq_add_neg]
  apply ord_P_add_eq_of_lt
  rwa [ord_P_neg (P := P)]

end SmoothPlaneCurve

/-! ### Uniformizers (T-II-1-003) -/

namespace SmoothPlaneCurve

variable {F : Type*} [Field F]

/-- A uniformizer at a smooth point `P` of a smooth curve is any function
`t ∈ K̄(C)` with `ord_P(t) = 1`. Equivalently, `t` generates the maximal ideal
of `K̄[C]_P`.
Reference: Silverman II.1 (definition after II.1.1). -/
def Uniformizer (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    (t : C.FunctionField) : Prop :=
  C.ord_P P t = 1

variable {C : SmoothPlaneCurve F} {P : C.SmoothPoint}

/-- Existence of a uniformizer at any smooth point: the DVR structure of the
local ring guarantees one. Reference: Silverman II.1.1. -/
theorem exists_uniformizer (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    ∃ t : C.FunctionField, Uniformizer C P t := by
  obtain ⟨π, hπ⟩ :=
    (IsDiscreteValuationRing.maximalIdeal
      (C.localRingAt P)).valuation_exists_uniformizer C.FunctionField
  refine ⟨π, ?_⟩
  have hvπ : C.pointValuation P π ≠ 0 := by
    change (IsDedekindDomain.HeightOneSpectrum.valuation _ _) π ≠ 0
    rw [hπ]; exact WithZero.exp_ne_zero
  unfold Uniformizer
  rw [ord_P_of_ne _ hvπ]
  have hunz : WithZero.unzero hvπ = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero]
    exact hπ
  rw [hunz]
  rfl

/-- An `F`-rational smooth point of a curve: in our formulation every
`SmoothPoint C` already has coordinates in the base field `F`, so the notion
of "rational point" over `F` coincides with `SmoothPoint`. This alias is
provided to match Silverman's notation for statements that distinguish
`C(K)` from `C(K̄)`.
Reference: Silverman II.1 (terminology). -/
abbrev RationalPoint (C : SmoothPlaneCurve F) : Type _ := C.SmoothPoint

/-- There exists a uniformizer in the function field `F(C)` itself — not only
in some algebraic closure — at every `F`-rational smooth point. For our thin
`SmoothPlaneCurve F` wrapper this is the same statement as
`exists_uniformizer`, since every smooth point is by construction
`F`-rational.
Reference: Silverman II.1.1.1 / Exercise 2.16. -/
theorem exists_K_uniformizer (C : SmoothPlaneCurve F) (P : C.RationalPoint) :
    ∃ t : C.FunctionField, Uniformizer C P t :=
  C.exists_uniformizer P

/-- A uniformizer is nonzero. -/
theorem Uniformizer.ne_zero {t : C.FunctionField} (ht : Uniformizer C P t) :
    t ≠ 0 := by
  intro h; rw [h] at ht; simp [Uniformizer] at ht

/-- Two uniformizers have order difference zero: if `t` and `s` are both
uniformizers, then `ord_P(t/s) = 0`. Equivalently, `t/s` is a unit in the
local ring at `P`. Reference: Silverman II.1. -/
theorem Uniformizer.unit_quotient {t s : C.FunctionField}
    (ht : Uniformizer C P t) (hs : Uniformizer C P s) :
    C.ord_P P (t / s) = 0 := by
  rw [div_eq_mul_inv, ord_P_mul, ord_P_inv _ hs.ne_zero, ht, hs]
  rfl

/-- For a uniformizer `t` at `P` and any integer `n`, there is an element
`s ∈ K(C)ˣ` with `ord_P s = n`. Constructed via `t^n.toNat` for `n ≥ 0` and
`(t^(-n).toNat)⁻¹` for `n < 0`. -/
theorem Uniformizer.exists_ord_P_eq {t : C.FunctionField}
    (ht : Uniformizer C P t) (n : ℤ) :
    ∃ s : C.FunctionField, s ≠ 0 ∧ C.ord_P P s = (n : ℤ) := by
  have ht_ne : t ≠ 0 := ht.ne_zero
  rcases lt_or_ge n 0 with hneg | hpos
  · refine ⟨(t ^ (-n).toNat)⁻¹, inv_ne_zero (pow_ne_zero _ ht_ne), ?_⟩
    rw [ord_P_inv _ (pow_ne_zero _ ht_ne), ord_P_pow, ht, nsmul_one]
    have hn : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have h1 : ((-n).toNat : WithTop ℤ) = ((-n : ℤ) : WithTop ℤ) := by
      exact_mod_cast hn
    rw [h1]
    norm_cast
    omega
  · refine ⟨t ^ n.toNat, pow_ne_zero _ ht_ne, ?_⟩
    rw [ord_P_pow, ht, nsmul_one]
    exact_mod_cast Int.toNat_of_nonneg hpos

end SmoothPlaneCurve

end HasseWeil.Curves
