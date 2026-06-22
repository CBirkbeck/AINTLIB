/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.MvPowerSeries.Substitution
import HasseWeil.AdditionPullback
import HasseWeil.Curves.WithTopArith
import HasseWeil.EC.MulByIntBaseCase
import HasseWeil.LocalExpansion
import HasseWeil.OmegaPullbackCoeff
import HasseWeil.OrdAtInftyBridge

/-!
# Formal isogeny series and the bridge to `omegaPullbackCoeff`

For an isogeny `α : E → E` over a field `F`, its **formal isogeny series**
`formalIsogenySeries W α : PowerSeries F` records the expansion of
`α.pullback t ∈ K(E)` in the local parameter `t = −x/y` at the identity `O`.

## Main definitions

* `formalIsogenySeries W α` — the power series whose `n`-th coefficient is
  the coefficient of `t^n` in the Laurent expansion `localExpand (α.pullback (localParam W))`.
  For a "genuine" isogeny (one sending `O` to `O`), this Laurent series has
  non-negative order, so the `PowerSeries` representation is faithful.

## Main theorems (BRIDGE chain)

* `T-IV-BRIDGE-001` / `omegaPullbackCoeff_eq_formalIsogenyLeading` —
  `omegaPullbackCoeff W α = coeff 1 (formalIsogenySeries W α)` (Silverman
  IV.4.3, "a_φ = φ′(0)"), under the genuineness hypothesis
  `0 < orderTop (localExpand (α.pullback t))` (the t-adic form of `α(O) = O`).

* `T-IV-BRIDGE-003` / `formalIsogenySeries_add` — Silverman IV.1.4: the local
  expansion of the `z = −x/y` coordinate of the genuine pair sum
  `α(P) + β(P)` (the chord-tangent `addPullback_x_pair`/`addPullback_y_pair`)
  equals the formal group law applied to
  `(formalIsogenySeries α, formalIsogenySeries β)`, for summands that reduce
  to `O` and are not mutual inverses. Its conclusion is verbatim the `h_iv14`
  hypothesis of `addPullback_x_pair_sum_reduces_of_iv14_witness`
  (`Verschiebung/Genuine.lean`), so it discharges that Wall-A witness by
  `exact`. **PROVEN** — the statement and proof live in
  `HasseWeil.ChordExpansion` (FG-B5; the proof needs the
  `FormalGroupLawSpec`/`ChordExpansion` chord apparatus, which imports this
  file).

BRIDGE-001 remains `sorry` at the substantive mathematical step. Both
bridges were **restated 2026-06-11** into guarded true forms: the original
unguarded statements were refutable because the project's `Isogeny.pullback`
is an unconstrained `AlgHom`, decoupled from the point map (B2 log
`BRIDGE-003-B2` in `.mathlib-quality/b2_log.jsonl`; the individual
docstrings record the counterexamples).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.1, IV.2, IV.4.
-/

open WeierstrassCurve PowerSeries LaurentSeries

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- The **formal isogeny series** of `α : Isogeny E E`. This is the power
    series whose `n`-th coefficient is the coefficient of `t^n` in the
    Laurent-series expansion of `α.pullback (localParam W)` (which is
    `α` pulling back the local parameter `t = −x/y` at `O`).

    For a "genuine" isogeny (whose pullback is compatible with `O ↦ O`), the
    Laurent series has non-negative order, so coefficients at negative
    indices vanish and this `PowerSeries` representation is faithful.
    Pathological isogenies (where `pullback` and `toAddMonoidHom` are
    inconsistent, which the `Isogeny` structure does not forbid) have
    their negative-order terms silently dropped. -/
noncomputable def formalIsogenySeries (α : Isogeny W.toAffine W.toAffine) : PowerSeries F :=
  PowerSeries.mk fun n ↦
    (localExpand W (α.pullback (localParam W))).coeff (n : ℤ)

/-- The `n`-th coefficient of `formalIsogenySeries W α` equals the `n`-th
    Laurent-series coefficient of the local expansion of `α.pullback t`. -/
@[simp] theorem formalIsogenySeries_coeff (α : Isogeny W.toAffine W.toAffine) (n : ℕ) :
    PowerSeries.coeff n (formalIsogenySeries W α) =
      (localExpand W (α.pullback (localParam W))).coeff (n : ℤ) := by
  rw [formalIsogenySeries]
  exact PowerSeries.coeff_mk n _

/-! ### Constant coefficient / positive order (QF Layer-1 brick 4)

The local parameter `t = −x/y` vanishes at `O` (`ord_O(t) = 1`). A *genuine*
isogeny `α` satisfies `α(O) = O`, so `α.pullback t` also vanishes at `O`; hence
its `t`-adic expansion `localExpand (α.pullback t)` has order `≥ 1` and the
formal isogeny series has **zero constant term** (equivalently, positive
`PowerSeries.order`).

The `HasseWeil.Isogeny` structure (`Basic.lean`) carries only an unconstrained
algebra-hom `pullback` and an additive hom `toAddMonoidHom`, with **no field
forcing `pullback` to fix `O`** (and no compatibility between the two
components). So this brick is gated on the genuine-isogeny hypothesis, stated
here in the form already used for `[n]`/Frobenius in `SilvermanIV14.lean`:
`0 < orderTop (localExpand (α.pullback t))`. Every concrete isogeny in the
development supplies this (e.g.
`orderTop_localExpand_mulByInt_neg_one_pullback_localParam = 1`). -/

/-- **`constantCoeff (formalIsogenySeries W α) = 0` for a genuine isogeny**:
    if the local expansion of `α.pullback t` has positive `orderTop` (i.e.
    `α.pullback t` vanishes at `O`, which is the t-adic form of `α(O) = O`),
    then the formal isogeny series has zero constant term. -/
theorem constantCoeff_formalIsogenySeries_of_orderTop_pos (α : Isogeny W.toAffine W.toAffine)
    (h_orderTop : (0 : WithTop ℤ) < (localExpand W (α.pullback (localParam W))).orderTop) :
    PowerSeries.constantCoeff (formalIsogenySeries W α) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalIsogenySeries_coeff]
  refine HahnSeries.coeff_eq_zero_of_lt_orderTop ?_
  rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) from rfl]
  exact_mod_cast h_orderTop

/-- **Positive order of `formalIsogenySeries W α` for a genuine isogeny**
    (QF Layer-1 brick 4): the form that composes directly with
    `HasseWeil.FG.formalGroup_preserves_positive_order` (which takes
    `0 < order`). Equivalent to `constantCoeff = 0` via
    `PowerSeries.order_ne_zero_iff_constCoeff_eq_zero`. -/
theorem order_formalIsogenySeries_pos_of_orderTop_pos (α : Isogeny W.toAffine W.toAffine)
    (h_orderTop : (0 : WithTop ℤ) < (localExpand W (α.pullback (localParam W))).orderTop) :
    0 < (formalIsogenySeries W α).order := by
  rw [pos_iff_ne_zero, PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]
  exact constantCoeff_formalIsogenySeries_of_orderTop_pos W α h_orderTop

/-! ### Coefficients of `formalGroupLaw W` at (1,0) and (0,1)

These are the axiomatic coefficients of a formal group law (from `lunit` +
`runit`), specialised to the concrete `formalGroupLaw W` built from the
Weierstrass curve addition formula. They equal `1` by direct computation
on `formalGroupLaw_coeff`. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The `(1, 0)` coefficient of `(formalGroupLaw W).toMvPowerSeries` is `1`. -/
theorem formalGroupLaw_coeff_single_zero_one :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (formalGroupLaw W).toMvPowerSeries = 1 := by
  change formalGroupLaw_coeff W (Finsupp.single (0 : Fin 2) 1) = 1
  simp [formalGroupLaw_coeff]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The `(0, 1)` coefficient of `(formalGroupLaw W).toMvPowerSeries` is `1`. -/
theorem formalGroupLaw_coeff_single_one_one :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (formalGroupLaw W).toMvPowerSeries = 1 := by
  change formalGroupLaw_coeff W (Finsupp.single (1 : Fin 2) 1) = 1
  simp [formalGroupLaw_coeff]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The constant coefficient of `(formalGroupLaw W).toMvPowerSeries` is `0`. -/
theorem constantCoeff_formalGroupLaw :
    MvPowerSeries.constantCoeff (σ := Fin 2) (R := F) (formalGroupLaw W).toMvPowerSeries = 0 := by
  change formalGroupLaw_coeff W 0 = 0
  simp [formalGroupLaw_coeff]

/-! ### Generic coefficient-1 substitution lemma

The following is a reformulation of `coeff_one_fAdd` (in
`FormalGroup/Definition.lean`) that does NOT require a `FormalGroup`
structure — it takes the three essential coefficient values as
hypotheses. This makes it applicable to `formalGroupLaw W` (via the
facts proved above) without needing to construct a full `FormalGroup F`
from the Weierstrass curve. -/

omit [DecidableEq F] in
/-- **Generic coefficient-1-of-subst identity**: for any bivariate series `S`
    with `S(1,0) = 1`, `S(0,1) = 1`, `S(0,0) = 0`, and univariate `f, g`
    with constant coefficient zero, the coefficient of `T^1` in
    `S(f(T), g(T))` equals `coeff 1 f + coeff 1 g`.

    This is the generic form of `coeff_one_fAdd`: the FormalGroup axioms
    there are used only to derive the three coefficient values, which are
    taken as hypotheses here. -/
theorem coeff_one_subst_bivariate (S : MvPowerSeries (Fin 2) F)
    (hS10 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) S = 1)
    (hS01 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) S = 1)
    (hS00 : MvPowerSeries.constantCoeff (σ := Fin 2) (R := F) S = 0) (f g : PowerSeries F)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1
        (MvPowerSeries.subst (![f, g] : Fin 2 → PowerSeries F) S) =
      PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  have coeff_one_high : ∀ (a b : ℕ), 2 ≤ a + b →
      PowerSeries.coeff 1 (f ^ a * g ^ b) = 0 := by
    intro a b hab
    have : PowerSeries.X ^ (a + b) ∣ f ^ a * g ^ b := by
      rw [pow_add]
      exact mul_dvd_mul
        (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hf) _)
        (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hg) _)
    exact (PowerSeries.X_pow_dvd_iff.mp this) 1 (by omega)
  change MvPowerSeries.coeff (Finsupp.single () 1)
    (MvPowerSeries.subst _ S) = _
  have ha : MvPowerSeries.HasSubst
      (show Fin 2 → MvPowerSeries Unit F from ![f, g]) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    fin_cases s <;> simpa
  rw [MvPowerSeries.coeff_subst ha]
  conv_lhs =>
    arg 1; ext d; rw [smul_eq_mul]; arg 2
    change MvPowerSeries.coeff (Finsupp.single () 1)
      (d.prod fun s e ↦ (![f, g]) s ^ e)
    rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> exact pow_zero _),
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero]
  change (∑ᶠ d, MvPowerSeries.coeff d S *
    PowerSeries.coeff 1 (f ^ (d 0) * g ^ (d 1))) = _
  have vanish : ∀ d : Fin 2 →₀ ℕ, d ≠ Finsupp.single 0 1 →
      d ≠ Finsupp.single 1 1 →
      MvPowerSeries.coeff d S *
        PowerSeries.coeff 1 (f ^ (d 0) * g ^ (d 1)) = 0 := by
    intro d hd0 hd1
    by_cases hsum : 2 ≤ d 0 + d 1
    · rw [coeff_one_high (d 0) (d 1) hsum, mul_zero]
    · push Not at hsum
      have hd : d = 0 := by
        ext i; fin_cases i <;> simp_all [Finsupp.ext_iff, Fin.forall_fin_two] <;> omega
      subst hd
      simp only [Finsupp.coe_zero, Pi.zero_apply, pow_zero]
      norm_num [PowerSeries.coeff_one, hS00]
  have hsub : Function.support (fun d : Fin 2 →₀ ℕ ↦
      MvPowerSeries.coeff d S *
        PowerSeries.coeff 1 (f ^ (d 0) * g ^ (d 1))) ⊆
      ({Finsupp.single 0 1, Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_contra h
    simp only [Fin.isValue, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at h
    exact hd (vanish d h.1 h.2)
  rw [finsum_eq_finsetSum_of_support_subset _ hsub]
  have hne : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro h
    exact absurd (DFunLike.congr_fun h 0) (by simp [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide)])
  rw [Finset.sum_pair hne]
  simp only [Finsupp.single_eq_same, pow_one, pow_zero,
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide),
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide),
    hS10, hS01, one_mul, mul_one]

/-! ### (a) The formal group law preserves positive order (the subgroup property)

This is the pure power-series content of Silverman VII.2.2 / IV.1: the formal
group law `F̂(u, v) = u + v + (higher cross terms)` has zero constant coefficient,
so substituting two power series `f, g` of *positive* order yields a power series
of positive order. Concretely `F̂(f, g)` has zero constant coefficient because
`F̂` has zero constant coefficient and `f, g` have zero constant coefficient
(every monomial `u^i v^j` with `i + j ≥ 1` then contributes `0` to the constant
term, and the `i = j = 0` term is excluded by `constantCoeff F̂ = 0`).

This is the "kernel of reduction at `O` is closed under addition" fact at the
formal-group level: positive order of `z` ⟺ the point reduces to `O`, and
`z(P₁ + P₂) = F̂(z(P₁), z(P₂))` preserves that. The statement is given generically
(taking only `constantCoeff S = 0` as the hypothesis on the bivariate series, so
it applies to `formalGroupLaw W` via `constantCoeff_formalGroupLaw`) and is
reusable for any pair of positive-order summand series. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **Generic constant-coefficient-of-subst vanishing**: for any bivariate series
    `S` with `constantCoeff S = 0` and univariate `f, g` with zero constant
    coefficient, `S(f, g)` has zero constant coefficient. Thin specialisation of
    `MvPowerSeries.constantCoeff_subst_eq_zero` to the `Fin 2 → PowerSeries`
    substitution shape used throughout this file. -/
theorem constantCoeff_subst_bivariate_eq_zero (S : MvPowerSeries (Fin 2) F)
    (hS00 : MvPowerSeries.constantCoeff (σ := Fin 2) (R := F) S = 0) (f g : PowerSeries F)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff
        (MvPowerSeries.subst (![f, g] : Fin 2 → PowerSeries F) S) = 0 := by
  have ha : MvPowerSeries.HasSubst
      (show Fin 2 → MvPowerSeries Unit F from ![f, g]) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    fin_cases s <;> simpa
  have ha' : ∀ i, ((show Fin 2 → MvPowerSeries Unit F from ![f, g]) i).constantCoeff = 0 := by
    intro i
    fin_cases i <;> simpa
  exact MvPowerSeries.constantCoeff_subst_eq_zero ha ha' hS00

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **(a) The formal group law preserves positive order (subgroup property).**

    For any bivariate series `S` with `constantCoeff S = 0` (in particular
    `formalGroupLaw W` via `constantCoeff_formalGroupLaw`), if `f, g : PowerSeries F`
    have positive `PowerSeries.order` (i.e. vanish at `O`), then the substitution
    `S(f, g)` has positive order. This is the formal-power-series form of "the
    kernel of reduction at `O` is a subgroup" (Silverman VII.2.2). -/
theorem order_subst_bivariate_pos (S : MvPowerSeries (Fin 2) F)
    (hS00 : MvPowerSeries.constantCoeff (σ := Fin 2) (R := F) S = 0) (f g : PowerSeries F)
    (hf : 0 < PowerSeries.order f) (hg : 0 < PowerSeries.order g) :
    0 < PowerSeries.order
        (MvPowerSeries.subst (![f, g] : Fin 2 → PowerSeries F) S) := by
  have hf' : PowerSeries.constantCoeff f = 0 :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp (Order.one_le_iff_pos.mpr hf)
  have hg' : PowerSeries.constantCoeff g = 0 :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp (Order.one_le_iff_pos.mpr hg)
  exact pos_iff_ne_zero.mpr <| PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr <|
    constantCoeff_subst_bivariate_eq_zero S hS00 f g hf' hg'

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **(a), specialised to `formalGroupLaw W`**: substituting two positive-order
    power series into the elliptic curve's formal group law yields a positive-order
    power series. The reusable form of the formal-group subgroup property for the
    concrete `formalGroupLaw W`. -/
theorem order_formalGroupLaw_subst_pos (f g : PowerSeries F)
    (hf : 0 < PowerSeries.order f) (hg : 0 < PowerSeries.order g) :
    0 < PowerSeries.order (MvPowerSeries.subst (![f, g] : Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries) :=
  order_subst_bivariate_pos (formalGroupLaw W).toMvPowerSeries
    (constantCoeff_formalGroupLaw W) f g hf hg

/-- **T-IV-BRIDGE-001** (Silverman IV.4.3, "a_φ = φ′(0)"): for a *genuine*
    isogeny, the linear coefficient of `formalIsogenySeries W α` equals the
    invariant-differential pullback coefficient `omegaPullbackCoeff W α`.

    Mathematical content: the expansion `α.pullback(t) = a_α · t + O(t²)`
    in `K(E)` has its linear coefficient equal to the coefficient by which
    `α*` scales the invariant differential `ω = dx/(2y + a₁x + a₃)` in the
    Kähler differential module. This is the bridge between the III.5
    invariant-differential definition and the IV.4 formal-series
    definition of `a_α`.

    **Why the `h_orderTop` genuineness hypothesis is REQUIRED** (restated
    2026-06-11; the unguarded form was refutable): the project `Isogeny`
    structure (`Basic.lean`) carries `pullback` as an *unconstrained*
    `AlgHom`, so translation pullbacks `τ_S^*` qualify as isogenies. For
    those, `ω` is translation-invariant (Silverman III.5.1), hence
    `omegaPullbackCoeff = 1`; but `localExpand (τ_S^* t)` is the expansion
    at `O` of `t ∘ τ_S`, whose linear coefficient is a derivative value at
    `S` (`≠ 1` generically — its constant term `t(S)` is even nonzero). The
    hypothesis is the brick-4 shape used throughout this file
    (`constantCoeff_formalIsogenySeries_of_orderTop_pos` above): the t-adic
    form of `α(O) = O`, which excludes the translation pathology.

    Per-α instances discharge the bridge directly, sorry-free:
    `omegaPullbackCoeff_eq_formalIsogenyLeading_id` (below),
    `omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog` and the
    char-2 `bridge_001_γ_isogOneSub_negFrobenius_char_two`
    (`AdditionPullback/SilvermanIV14.lean`). Matching `orderTop` witnesses:
    `localExpand_localParam` (id),
    `orderTop_localExpand_mulByInt_neg_one_pullback_localParam`,
    `orderTop_localExpand_isogOneSub_negFrobenius_pullback_localParam`, and
    the generic pole bridge
    `orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg` (below).

    **Discharge route** (kept open): prove the chain-rule leaf
    `pullback_invariantDiff_coeff_zero` (P, `GapQfKernel.lean`); then this
    statement follows via
    `omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization` (ibid.,
    identical signature). -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading (α : Isogeny W.toAffine W.toAffine)
    (h_orderTop : (0 : WithTop ℤ) < (localExpand W (α.pullback (localParam W))).orderTop) :
    omegaPullbackCoeff W α =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α)) := by
  sorry

/-! #### Witness-parametric factorization of BRIDGE-001

The sorry above has TWO mathematical components, which we factor here so each
can be discharged independently:

1. **III.1.5 content** (`a_α ∈ F`): the omega pullback coefficient lies in the
   image of `algebraMap F KE`. Mathematically, this is "the invariant
   differential has no zeros or poles, so `α* ω / ω` is a global rational
   function with no zeros/poles, hence constant".

2. **IV.4.3 substance** (Kähler ↔ Laurent bridge): the constant value matches
   the linear coefficient of the formal series — the formal series literally
   records the local expansion.

The witness form below takes (1) as a hypothesis (a witness `c : F` with the
range identification) plus (2) the explicit identification with the formal
coefficient. Either chain — Silverman III.1.5 or formal-group correspondence
— produces both witnesses, then this lemma closes the sorry above by `rfl`. -/

/-- **Witness-parametric BRIDGE-001**: given that `omegaPullbackCoeff W α =
    algebraMap F KE c` for some `c : F` (Silverman III.1.5: invariant
    differential is a generator), and that `c` matches the linear formal
    coefficient (Silverman IV.4.3), the BRIDGE-001 identity holds. -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading_of_witness
    (α : Isogeny W.toAffine W.toAffine) (c : F)
    (h_const : omegaPullbackCoeff W α = algebraMap F KE c)
    (h_match : c = PowerSeries.coeff 1 (formalIsogenySeries W α)) :
    omegaPullbackCoeff W α =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α)) := by
  rw [h_const, h_match]

/-! ### BRIDGE-001 general α scaffold (closer with III.5.5 + addition-pullback)

The general-α extension of BRIDGE-001 proceeds via two routes that compose:
* **Frobenius branch**: `omegaPullbackCoeff_frobenius = 0` (existing
  axiom-clean) combined with `formalIsogenySeries_frobenius = T^q` (existing
  axiom-clean) gives BRIDGE-001 for `α = π` directly via constant 0.
* **Identity branch**: `omegaPullbackCoeff_id = 1` and `formalIsogenySeries_id`
  give the constant 1 case.
* **Composite branch via III.5.2 additivity**: for `γ = m·id + n·π`, the
  omega-coefficient is `m·1 + n·0 = m` (linear combination), matching the
  formal series's linear coefficient via `formalIsogenySeries_add` (the formal
  group law's degree-1 expansion). -/

/-- **BRIDGE-001 closer for general α via III.5.5 + linearity (witness-parametric)**:
takes a constant-coefficient witness `c : F` for both sides and an additivity
witness for the formal series, then closes BRIDGE-001 by `rfl`-shape.

This composer is the ENTRY POINT for the general-α discharge: once `c` is
identified (either by direct computation for [n], frobenius, identity, or via
III.5.2 for combinations), the closure fires axiom-clean. -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading_of_constant_witness
    (α : Isogeny W.toAffine W.toAffine) (c : F)
    (h_omega_const : omegaPullbackCoeff W α = algebraMap F KE c)
    (h_formal_const : (PowerSeries.coeff 1 (formalIsogenySeries W α) : F) = c) :
    omegaPullbackCoeff W α =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α)) := by
  rw [h_omega_const, h_formal_const]

/-- **BRIDGE-001 helper: linearity from additivity witnesses**.
For `γ = α + β` with omega-coefficient `c_γ = c_α + c_β` (Silverman III.5.2)
and formal series `f_γ` with `coeff 1 f_γ = coeff 1 f_α + coeff 1 f_β` (the
formal group law's leading-term linearity), if BRIDGE-001 holds for `α` and `β`
with constants in `F`, then it holds for `γ` with the sum constant.

Witness-parametric on the additivity facts. When the formal-group-law leading
linearity (`formalIsogenySeries_add` reduced to `coeff 1`) discharges, this
chains BRIDGE-001 closure for any signed-sum γ from BRIDGE-001 closure for the
summands. -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading_add_witness
    (α β γ : Isogeny W.toAffine W.toAffine) (c_α c_β : F)
    (h_α : omegaPullbackCoeff W α = algebraMap F KE c_α)
    (h_β : omegaPullbackCoeff W β = algebraMap F KE c_β)
    (h_omega_add : omegaPullbackCoeff W γ = omegaPullbackCoeff W α + omegaPullbackCoeff W β)
    (h_formal_add : PowerSeries.coeff 1 (formalIsogenySeries W γ) =
      PowerSeries.coeff 1 (formalIsogenySeries W α) + PowerSeries.coeff 1 (formalIsogenySeries W β))
    (h_α_match : c_α = PowerSeries.coeff 1 (formalIsogenySeries W α))
    (h_β_match : c_β = PowerSeries.coeff 1 (formalIsogenySeries W β)) :
    omegaPullbackCoeff W γ =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W γ)) := by
  rw [h_omega_add, h_α, h_β, h_formal_add, map_add, h_α_match, h_β_match]

/-! ### T-IV-BRIDGE-003: proven in `HasseWeil.ChordExpansion`

The Silverman IV.1.4 chord-addition identity `formalIsogenySeries_add` — the
local `z = −x/y` expansion of the genuine pair sum `α(P) + β(P)` equals the
formal group law substituted at the two formal isogeny series — was stated
here as a `sorry` through 2026-06-11 and is now **proven** in
`HasseWeil.ChordExpansion` (which imports this file; the proof needs the
`FormalGroupLawSpec` chord apparatus, so the statement moved there).

**Statement-shape history.** The original BRIDGE-003 quantified over a third
isogeny `γ` with the *point-map* hypothesis `γ.toAddMonoidHom =
α.toAddMonoidHom + β.toAddMonoidHom` and concluded a `PowerSeries`-level
identity for `formalIsogenySeries W γ`. That is refutable: the project
`Isogeny` carries `pullback` and `toAddMonoidHom` as *independent* fields, so
the placeholder `γ := ⟨AlgHom.id, [2].toAddMonoidHom⟩` with `α = β = [1]`
satisfies the hypothesis while the two sides have different linear
coefficients (B2 log `BRIDGE-003-B2`, `.mathlib-quality/b2_log.jsonl`). The
proven form states the identity at the *pullback* level, where the sum is the
genuine group-law addition (`AdditionPullback.lean`), with no `γ` at all,
under the summand-reduces-to-`O` pole hypotheses and `AddNonInversePair`. -/

/-! #### Witness-parametric lemmas for the PowerSeries-level series identity

The lemmas in this section are stated for the *PowerSeries-level* identity
`formalIsogenySeries W γ = subst ![f_α, f_β] (formalGroupLaw W)` — the shape
of the pre-2026-06-11 BRIDGE-003.  As an unconditional statement from the
point-map hypothesis alone that shape is refutable (see the BRIDGE-003
docstring above), but as *hypothesis-driven* lemmas these remain true and
useful: a caller who has the identity for a specific genuine `γ` (e.g. for
`γ = [k+1]` with `(α, β) = ([k], [1])`, where `γ.pullback` IS the group-law
addition pullback) can break it into coefficient ladders here, and the
`n = 0` / `n = 1` rungs are discharged below from the formal-group-law
coefficient facts. The `[n]`-induction consumer is
`constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003` at the end of
this file (which takes the `[k+1] = F([k], [1])` family as a hypothesis,
matching `formalIsogenySeries_FGL_additivity` in `GapQfKernel.lean`). -/

/-- **Witness-parametric BRIDGE-003**: given the pointwise series equality
    (for each `n : ℕ`) between `formalIsogenySeries W γ` and the formal-group
    substitution, the BRIDGE-003 conclusion holds.

    Useful when downstream callers can produce coefficient-by-coefficient
    identifications (e.g. via `coeff_one_subst_bivariate` for n = 1) without
    needing the full power-series equality. -/
theorem formalIsogenySeries_add_of_coeff_witness (α β γ : Isogeny W.toAffine W.toAffine)
    (h_coeff : ∀ n : ℕ, PowerSeries.coeff n (formalIsogenySeries W γ) =
      PowerSeries.coeff n
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries)) :
    formalIsogenySeries W γ =
      MvPowerSeries.subst
        (![formalIsogenySeries W α, formalIsogenySeries W β] :
          Fin 2 → PowerSeries F)
        (formalGroupLaw W).toMvPowerSeries :=
  PowerSeries.ext h_coeff

/-- **Fresh-angle factorization of BRIDGE-003**: split the
    coefficient-ladder into n=0, n=1, n≥2 pieces.

    `n=0` (`h_zero`) is the constant-coefficient identity. For "genuine"
    isogenies (sending O to O), both sides have constant coefficient 0,
    so this reduces to `0 = 0`. The substantive content is the genuine-
    isogeny hypothesis itself (which BRIDGE-003 implicitly assumes).

    `n=1` (`h_one`) is the leading-linear-term identity. Both sides
    equal `coeff 1 fα + coeff 1 fβ`: the LHS via the formal-group-law's
    leading-term linearity (Silverman III.5.2), the RHS via
    `coeff_one_subst_bivariate` applied to `formalGroupLaw W` with
    `formalGroupLaw_coeff_single_zero_one` and `_single_one_one`.

    `n≥2` (`h_higher`) is the substantive arc — the formal group law's
    behavior at higher orders.

    This factorization isolates the substantive content (h_higher) from
    the foundational identities (h_zero, h_one), enabling downstream
    consumers to discharge the easy parts directly while leaving the
    hard part as a single named witness. -/
theorem formalIsogenySeries_add_of_split_coeff_witness (α β γ : Isogeny W.toAffine W.toAffine)
    (h_zero : PowerSeries.coeff 0 (formalIsogenySeries W γ) =
      PowerSeries.coeff 0
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries))
    (h_one : PowerSeries.coeff 1 (formalIsogenySeries W γ) =
      PowerSeries.coeff 1
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries))
    (h_higher : ∀ n : ℕ, 2 ≤ n →
      PowerSeries.coeff n (formalIsogenySeries W γ) =
      PowerSeries.coeff n
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries)) :
    formalIsogenySeries W γ =
      MvPowerSeries.subst
        (![formalIsogenySeries W α, formalIsogenySeries W β] :
          Fin 2 → PowerSeries F)
        (formalGroupLaw W).toMvPowerSeries := by
  refine formalIsogenySeries_add_of_coeff_witness W α β γ (fun n ↦ ?_)
  match n with
  | 0 => exact h_zero
  | 1 => exact h_one
  | n + 2 => exact h_higher (n + 2) (by lia)

/-- **Coefficient-0 BRIDGE-003 discharge**: under the genuine-isogeny
    hypothesis (formal series have constant coefficient 0 for α, β, γ),
    both sides of the BRIDGE-003 equality have coefficient 0 at index 0.

    Direct from `MvPowerSeries.constantCoeff_subst_eq_zero` (mathlib)
    + `constantCoeff_formalGroupLaw` (zero constant coefficient of FGL)
    + the genuine-isogeny constant-zero hypotheses for α, β. -/
theorem formalIsogenySeries_add_coeff_zero_via_genuine (α β γ : Isogeny W.toAffine W.toAffine)
    (h_γ_const : PowerSeries.constantCoeff (formalIsogenySeries W γ) = 0)
    (h_α_const : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0)
    (h_β_const : PowerSeries.constantCoeff (formalIsogenySeries W β) = 0) :
    PowerSeries.coeff 0 (formalIsogenySeries W γ) =
      PowerSeries.coeff 0
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries) := by
  have ha : MvPowerSeries.HasSubst
      (show Fin 2 → MvPowerSeries Unit F from
        ![formalIsogenySeries W α, formalIsogenySeries W β]) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    fin_cases s
    · simpa [PowerSeries.constantCoeff_eq] using h_α_const
    · simpa [PowerSeries.constantCoeff_eq] using h_β_const
  have ha' : ∀ i, ((show Fin 2 → MvPowerSeries Unit F from
      ![formalIsogenySeries W α, formalIsogenySeries W β]) i).constantCoeff = 0 := by
    intro i
    fin_cases i
    · simpa [PowerSeries.constantCoeff_eq] using h_α_const
    · simpa [PowerSeries.constantCoeff_eq] using h_β_const
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h_γ_const,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact (MvPowerSeries.constantCoeff_subst_eq_zero ha ha' (constantCoeff_formalGroupLaw W)).symm

/-- **Coefficient-1 BRIDGE-003 discharge via formal group law axioms**:
    given the leading-linear-term linearity (Silverman III.5.2 LHS) and
    the constant-coefficient-zero hypotheses for the formal isogeny
    series, the n=1 identity follows from `coeff_one_subst_bivariate`
    plus `formalGroupLaw_coeff_single_*_one`.

    This discharges the `h_one` slot of `formalIsogenySeries_add_of_split_coeff_witness`
    given the LHS-side leading linearity (a Silverman III.5.2 fact). -/
theorem formalIsogenySeries_add_coeff_one_via_FGL (α β γ : Isogeny W.toAffine W.toAffine)
    (h_lhs_linearity : PowerSeries.coeff 1 (formalIsogenySeries W γ) =
      PowerSeries.coeff 1 (formalIsogenySeries W α) + PowerSeries.coeff 1 (formalIsogenySeries W β))
    (h_α_const : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0)
    (h_β_const : PowerSeries.constantCoeff (formalIsogenySeries W β) = 0) :
    PowerSeries.coeff 1 (formalIsogenySeries W γ) =
      PowerSeries.coeff 1
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries) := by
  rw [h_lhs_linearity, coeff_one_subst_bivariate _
    (formalGroupLaw_coeff_single_zero_one W) (formalGroupLaw_coeff_single_one_one W)
    (constantCoeff_formalGroupLaw W) _ _ h_α_const h_β_const]

/-! ### Consequence: additivity of `omegaPullbackCoeff` via the bridge

The supported route is **witness-parametric and axiom-clean**:
`omegaPullbackCoeff_add_of_bridge_witnesses` (and its specialisation
`omegaPullbackCoeff_add_of_leading_witness`) takes the three BRIDGE-001
instances and the coefficient-1 additivity for the specific formal series
as hypotheses. No BRIDGE sorry is touched; per-α BRIDGE-001 instances (id,
negFrobeniusIsog, isogOneSub char-2 — see the BRIDGE-001 docstring) feed it
directly.

A former *unconditional* form (`omegaPullbackCoeff_add_via_bridge_of_constCoeff`)
was **deleted 2026-06-11**: it chained the two pre-restatement BRIDGE sorries
from the bare point-map hypothesis `γ.toAddMonoidHom = α.toAddMonoidHom +
β.toAddMonoidHom`, and was itself refutable for the same placeholder-`γ`
reason as the old BRIDGE-003 (B2 log `BRIDGE-003-B2`): with
`γ := ⟨AlgHom.id, [2].toAddMonoidHom⟩` and `α = β = [1]` its hypotheses hold
while the conclusion reads `1 = 1 + 1` in `K(E)` — false over every field.
After the BRIDGE-003 restatement (pullback-level, no `γ`) it was also no
longer derivable in that shape. It had zero consumers (re-verified by grep
2026-06-11). Pointwise III.5.2 additivity for *genuine* sums is shipped
independently (`omegaPullbackCoeff_addIsog_pair`, `RouteBInduction.lean`). -/

/-- **Witness-parametric T-III-5-002**: the omega pullback coefficient is
    additive given the three BRIDGE-001 instances and coefficient-1
    additivity of the series.

    This form is **axiom-clean**: downstream workers who have produced
    the BRIDGE-001 instances and the specific coefficient-1 identity
    (e.g. via `coeff_one_fAdd` on a constructed `FormalGroup F`, or
    directly from `formalGroupLaw_coeff` at indices (1,0) and (0,1))
    can invoke this without touching any BRIDGE sorry. -/
theorem omegaPullbackCoeff_add_of_bridge_witnesses (α β γ : Isogeny W.toAffine W.toAffine)
    (f_α f_β f_γ : PowerSeries F)
    (h_bridge_α : omegaPullbackCoeff W α = algebraMap F KE (PowerSeries.coeff 1 f_α))
    (h_bridge_β : omegaPullbackCoeff W β = algebraMap F KE (PowerSeries.coeff 1 f_β))
    (h_bridge_γ : omegaPullbackCoeff W γ = algebraMap F KE (PowerSeries.coeff 1 f_γ))
    (h_coeff1_add : PowerSeries.coeff 1 f_γ = PowerSeries.coeff 1 f_α + PowerSeries.coeff 1 f_β) :
    omegaPullbackCoeff W γ =
      omegaPullbackCoeff W α + omegaPullbackCoeff W β := by
  rw [h_bridge_γ, h_bridge_α, h_bridge_β, ← map_add]
  exact congrArg _ h_coeff1_add

/-- **Leading-coefficient BRIDGE-003 specialization (witness-parametric,
axiom-clean)**: given BRIDGE-001 for α, β, γ + leading-coefficient additivity
(= what BRIDGE-003 reduces to at coeff 1), conclude omega-pullback coefficient
additivity. Specializes `omegaPullbackCoeff_add_of_bridge_witnesses` to the
case where the formal series are the canonical `formalIsogenySeries`. -/
theorem omegaPullbackCoeff_add_of_leading_witness (α β γ : Isogeny W.toAffine W.toAffine)
    (h_bridge_α : omegaPullbackCoeff W α =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α)))
    (h_bridge_β : omegaPullbackCoeff W β =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W β)))
    (h_bridge_γ : omegaPullbackCoeff W γ =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W γ)))
    (h_leading_add : PowerSeries.coeff 1 (formalIsogenySeries W γ) =
      PowerSeries.coeff 1 (formalIsogenySeries W α) +
      PowerSeries.coeff 1 (formalIsogenySeries W β)) :
    omegaPullbackCoeff W γ =
      omegaPullbackCoeff W α + omegaPullbackCoeff W β :=
  omegaPullbackCoeff_add_of_bridge_witnesses W α β γ
    (formalIsogenySeries W α) (formalIsogenySeries W β) (formalIsogenySeries W γ)
    h_bridge_α h_bridge_β h_bridge_γ h_leading_add

/-! ### Unconditional: `formalIsogenySeries [1] = X`

The identity isogeny `[1]`'s pullback is the identity AlgHom on `K(E)`
(`mulByInt_one_pullback_eq_id`), so its formal series is just the local
expansion of `localParam W`, which equals `PowerSeries.X`. -/

/-- `formalIsogenySeries W (Isogeny.id) = X` (unconditional). The identity
    isogeny has identity pullback, so the formal series is just the local
    expansion of `localParam W`, which is `PowerSeries.X`. -/
theorem formalIsogenySeries_id :
    formalIsogenySeries W (Isogeny.id W.toAffine) = PowerSeries.X := by
  ext n
  rw [formalIsogenySeries_coeff]
  change ((localExpand W) ((AlgHom.id F W.toAffine.FunctionField) (localParam W))).coeff
      ((n : ℕ) : ℤ) = _
  rw [AlgHom.id_apply, localExpand_localParam, PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst hn
    rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from rfl,
      HahnSeries.coeff_single_same, if_pos rfl]
  · have hn' : (n : ℤ) ≠ (1 : ℤ) := by exact_mod_cast hn
    rw [HahnSeries.coeff_single_of_ne hn', if_neg hn]

/-- **`coeff 1 (formal id) = 1` (axiom-clean)**: extract the leading coefficient
from `formalIsogenySeries_id = X`. -/
@[simp] theorem coeff_one_formalIsogenySeries_id :
    PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) = 1 := by
  rw [formalIsogenySeries_id, PowerSeries.coeff_X, if_pos rfl]

/-- **omegaPullbackCoeff of `Isogeny.id` is 1 (axiom-clean, inlined)**.
Mirrors `omegaPullbackCoeff_of_pullback_eq_id` from `Hasse/PointFix.lean`,
inlined here to avoid a forward-import. -/
theorem omegaPullbackCoeff_id : omegaPullbackCoeff W (Isogeny.id W.toAffine) = 1 := by
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, alpha_star_u_eq]
  simp only [Isogeny.id_pullback, AlgHom.id_apply, one_smul]
  rfl

/-- **BRIDGE-001 for `Isogeny.id` (axiom-clean)**: the bridge identity
holds for the identity isogeny — both sides equal `1`.

Direct from `formalIsogenySeries_id = X` (so `coeff 1 = 1`) +
`omegaPullbackCoeff_id` (= 1). -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading_id :
    omegaPullbackCoeff W (Isogeny.id W.toAffine) =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine))) := by
  rw [formalIsogenySeries_id W, PowerSeries.coeff_X, if_pos rfl, map_one]
  exact omegaPullbackCoeff_id W

/-- `formalIsogenySeries W [1] = X` (unconditional). The pullback of `[1]`
    is the identity, so the formal series is the local expansion of
    `localParam W` (which is `t = -x_gen/y_gen`), equal to the formal
    variable `X`. -/
theorem formalIsogenySeries_mulByInt_one :
    formalIsogenySeries W (mulByInt W.toAffine 1) = PowerSeries.X := by
  ext n
  rw [formalIsogenySeries_coeff]
  have h_pb : (mulByInt W.toAffine 1).pullback (localParam W) = localParam W := by
    rw [mulByInt_one_pullback_eq_id]
    rfl
  rw [h_pb, localExpand_localParam, PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst hn
    rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from rfl,
      HahnSeries.coeff_single_same, if_pos rfl]
  · have hn' : (n : ℤ) ≠ (1 : ℤ) := by exact_mod_cast hn
    rw [HahnSeries.coeff_single_of_ne hn', if_neg hn]

/-! ### Alternative path: `coeff 1 [n] = n` via BRIDGE-003 induction

`BridgeMulByInt.lean` ships `coeff_one_formalIsogenySeries_mulByInt`
(the BRIDGE-001 result for `[n]`) via the **Wronskian-derived** path,
which depends on `wronskian_Φ_ΨSq_nat` for `m ≥ 5`
(`OmegaPullbackCoeff.lean:477` sorry).

We give an **alternative witness-parametric path** via BRIDGE-003
(formal additivity) plus the `[1] = X` and `constantCoeff [n] = 0`
hypotheses. This proves `coeff 1 (formalIsogenySeries [n]) = n` by
induction on positive `n`, decomposing via `[n+1] = [n] + [1]` and
the bivariate substitution coefficient identity.

If BRIDGE-003 closes first (e.g. via formal-group infrastructure
for the addition-pullback), the Wronskian dependency is bypassed.
This entry point matches the natural Silverman IV.2.3(a) proof
(addition formula → induction). -/

/-- **Inductive constantCoeff witness via BRIDGE-003**: given BRIDGE-003 in
    its specialised `[k+1] = [k] + [1]` form, `constantCoeff` of
    `formalIsogenySeries [n]` is `0` for every positive natural `n`.

    The base `[1] = X` has `constantCoeff X = 0`. The step
    `[k+1] = F([k], [1])` preserves constantCoeff = 0 via
    `MvPowerSeries.constantCoeff_subst_eq_zero` together with the fact that
    `formalGroupLaw W` itself has vanishing constant term. -/
theorem constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003 (h_bridge_003 : ∀ k : ℕ, 1 ≤ k →
      formalIsogenySeries W (mulByInt W.toAffine ((k : ℤ) + 1)) =
        MvPowerSeries.subst
          (![formalIsogenySeries W (mulByInt W.toAffine (k : ℤ)),
             formalIsogenySeries W (mulByInt W.toAffine 1)] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries) :
    ∀ n : ℕ, 1 ≤ n →
      PowerSeries.constantCoeff
        (formalIsogenySeries W (mulByInt W.toAffine (n : ℤ))) = 0 := by
  intro n hn
  induction n with
  | zero => lia
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      rw [show ((0 : ℕ).succ : ℤ) = 1 from rfl, formalIsogenySeries_mulByInt_one]
      exact PowerSeries.constantCoeff_X
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have ih' := ih hk_pos
      rw [show ((k.succ : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring]
      rw [h_bridge_003 k hk_pos]
      have ha_const : ∀ i : Fin 2, PowerSeries.constantCoeff
          ((![formalIsogenySeries W (mulByInt W.toAffine (k : ℤ)),
              formalIsogenySeries W (mulByInt W.toAffine 1)] :
            Fin 2 → PowerSeries F) i) = 0 := by
        intro i
        fin_cases i
        · simpa using ih'
        · simp [formalIsogenySeries_mulByInt_one, PowerSeries.constantCoeff_X]
      have ha_subst : MvPowerSeries.HasSubst
          (![formalIsogenySeries W (mulByInt W.toAffine (k : ℤ)),
              formalIsogenySeries W (mulByInt W.toAffine 1)] :
            Fin 2 → PowerSeries F) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero ha_const
      exact MvPowerSeries.constantCoeff_subst_eq_zero ha_subst ha_const
        (constantCoeff_formalGroupLaw W)

/-- **Inductive coefficient formula via BRIDGE-003**: given BRIDGE-003 in its
    specialised `[k+1] = [k] + [1]` form, conclude
    `coeff 1 (formalIsogenySeries [n]) = n` for all positive natural `n`.

    The base case `[1] = X` is shipped unconditionally as
    `formalIsogenySeries_mulByInt_one`. The constantCoeff witnesses are
    derived from `h_bridge_003` via
    `constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003`.

    Proof: induction on `n`. Step `n → n+1` via `coeff_one_subst_bivariate`
    applied to the BRIDGE-003 decomposition. -/
theorem coeff_one_formalIsogenySeries_mulByInt_via_bridge_003 (h_bridge_003 : ∀ k : ℕ, 1 ≤ k →
      formalIsogenySeries W (mulByInt W.toAffine ((k : ℤ) + 1)) =
        MvPowerSeries.subst
          (![formalIsogenySeries W (mulByInt W.toAffine (k : ℤ)),
             formalIsogenySeries W (mulByInt W.toAffine 1)] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries) :
    ∀ n : ℕ, 1 ≤ n →
      PowerSeries.coeff 1
        (formalIsogenySeries W (mulByInt W.toAffine (n : ℤ))) = (n : F) := by
  have h_const := constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003 W h_bridge_003
  intro n hn
  induction n with
  | zero => lia
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      rw [show ((0 : ℕ).succ : ℤ) = 1 from rfl, formalIsogenySeries_mulByInt_one]
      simp [PowerSeries.coeff_one_X]
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have ih' := ih hk_pos
      rw [show ((k.succ : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring, h_bridge_003 k hk_pos]
      rw [coeff_one_subst_bivariate (formalGroupLaw W).toMvPowerSeries
        (formalGroupLaw_coeff_single_zero_one W)
        (formalGroupLaw_coeff_single_one_one W)
        (constantCoeff_formalGroupLaw W)
        (formalIsogenySeries W (mulByInt W.toAffine (k : ℤ)))
        (formalIsogenySeries W (mulByInt W.toAffine 1))
        (h_const k hk_pos)
        (by rw [formalIsogenySeries_mulByInt_one]; exact PowerSeries.constantCoeff_X)]
      rw [ih', formalIsogenySeries_mulByInt_one, PowerSeries.coeff_one_X]
      push_cast
      ring

/-! ### QF Layer-1 brick 5: positive formal order of `α*t` ⟹ pole of `α*x`

This is the bridge from a *positive-order formal parameter pullback* to a
*pole of `x`* at the point at infinity `O`. Concretely: at `O` the local
parameter is `t = -x/y` with `ord_O(x) = -2`, `ord_O(t) = 1`, and
`x = t⁻² · u` for a unit `u` (with `ord_O(u) = 0`); this is the shipped
formal identity `localExpand_x_gen : localExpand W (x_gen W) = formalX W`
together with `formalX = single(-2,1) · u⁻¹` (`LocalExpansion.formalX`,
`formalX_orderTop = -2`).

For an isogeny `α`, if `α*t = α.pullback (localParam W)` vanishes at `O`
(`0 < orderTop (localExpand (α*t))` — the genuine-isogeny / `α(O) = O`
hypothesis, the same shape as brick 4's
`constantCoeff_formalIsogenySeries_of_orderTop_pos`), then `α*x` has a pole:
`ordAtInfty (α*x) < 0`.

#### Why this is the substantive Layer-1 bridge (two genuine gaps)

The hypothesis lives in the **`localExpand` / `LaurentSeries.orderTop`**
world (the formal `t`-adic expansion at `O`); the conclusion lives in the
**norm-based `ordAtInfty`** world (`Curves/Infinity.lean`, `OrdAtInftyBridge`).
These are two *independently constructed* discrete valuations on `K(E)`. The
two facts originally flagged as residuals are now resolved as follows:

1. **R5a is FALSE as originally stated** (no substitution lemma is needed; the
   gap is a *missing basepoint hypothesis*, not missing chain-rule
   infrastructure). With R5b the statement transports to the `ordAtInfty`
   world, where the genuine Weierstrass relation between `α*x` and `α*y`
   (`pullback_equation`, valid for an abstract `α.pullback` since it is an
   `F`-algebra hom) drives a discrete-valuation argument
   (`ord_pullback_x_neg_of_localParam_pos`). That argument **requires**
   `ordAtInfty (α*x) ≤ 0` ("`α` defined at `O`"), which the `Isogeny` structure
   of this file does not carry — so the unconditional R5a fails (counterexample
   in the R5a note). The conditional, basepoint-hypothesis form is fully proved.

2. **R5b is DONE** (`orderTop_localExpand_eq_ordAtInfty`): the two valuations
   coincide on all of `K(E)`. Both are discrete valuations agreeing on the
   generators (`ordAtInfty (x_gen) = -2 = orderTop formalX`, `y_gen ↦ -3`); the
   proof matches the basis-decomposition `min` formulas
   (`orderTop_localExpand_basis_eq_min`, `ordAtInfty_basis_eq_min`).

So brick 5 reduces to a *true, axiom-clean* basepoint-hypothesis theorem
(`ordAtInfty_pullback_x_gen_neg_of_orderTop_pos_of_base`); only the over-strong
unconditional signatures (R5a and `ordAtInfty_pullback_x_gen_gen_neg_of_orderTop_pos`)
retain a `sorry`, pending a redraft that adds the basepoint hypothesis. See the
ticket in `.mathlib-quality/qf-layer1-brick5-ordAtInfty-bridge-ticket.md`. -/

/-! #### R5a infrastructure: the valuation route (replaces the substitution gap)

The docstring originally flagged R5a as needing the general `localExpand ∘
α.pullback = substitution` development. That framing is unnecessary: with R5b
(`orderTop_localExpand_eq_ordAtInfty`) the whole statement transports into the
norm-based `ordAtInfty` world, where it becomes a *discrete-valuation* argument
that needs **no** substitution lemma. The mechanism is the genuine Weierstrass
relation between `α*x` and `α*y` (`pullback_equation`, which holds for an
abstract `α` because `α.pullback` is an `F`-algebra hom) combined with the
shipped `ordAtInfty` valuation API (`Curves/Infinity.lean`,
`Curves/WithTopArith.lean`).

The lemmas below carry out that argument. The catch — and the reason R5a as
literally stated keeps its `sorry` — is exposed precisely by this route: see
`ord_pullback_x_neg_of_localParam_pos` and the note on R5a. -/

/-- `pullback_equation` (`AdditionPullback.lean`) inlined, since that module is
not in this file's import chain: the image of the generic point under `α.pullback`
satisfies the Weierstrass equation, because `α.pullback` is an `F`-algebra hom and
so fixes the Weierstrass coefficients. -/
theorem pullback_equation_inl (α : Isogeny W.toAffine W.toAffine) :
    (W_KE W).toAffine.Equation (α.pullback (x_gen W)) (α.pullback (y_gen W)) := by
  have hmapped := Affine.Equation.map α.pullback.toRingHom (generic_equation W)
  rwa [show (W_KE W).toAffine.map α.pullback.toRingHom = (W_KE W).toAffine from by
    unfold W_KE; rw [Affine.map, WeierstrassCurve.map_map]
    congr 1; ext x; exact α.pullback.commutes x] at hmapped

/-- `0 ≤ ordAtInfty (algebraMap F KE c)`: a constant from the base field is
regular at `O` (`ord = 0` when `c ≠ 0`, `⊤` when `c = 0`). -/
theorem ord_algebraMap_F_nonneg (c : F) :
    0 ≤ (W_smooth W).ordAtInfty (algebraMap F KE c) := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero]
    exact (W_smooth W).ordAtInfty_zero ▸ le_top
  · rw [ordAtInfty_algebraMap_F_nonzero W hc]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Multiplying by a factor `c` with `0 ≤ ord c` cannot decrease the order:
`ord z ≤ ord (c * z)`. (Used with `c` a Weierstrass coefficient.) -/
theorem ord_coeff_mul_ge (c z : KE) (hc : 0 ≤ (W_smooth W).ordAtInfty c) :
    (W_smooth W).ordAtInfty z ≤ (W_smooth W).ordAtInfty (c * z) := by
  by_cases hz : z = 0
  · subst hz
    rw [mul_zero]
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul]
    exact (W_smooth W).ordAtInfty_zero ▸ le_top
  · calc (W_smooth W).ordAtInfty z = 0 + (W_smooth W).ordAtInfty z := (zero_add _).symm
      _ ≤ (W_smooth W).ordAtInfty c + (W_smooth W).ordAtInfty z := by gcongr
      _ = (W_smooth W).ordAtInfty (c * z) := ((W_smooth W).ordAtInfty_mul hc0 hz).symm

/-- **The genuine R5a content, with the basepoint hypothesis made explicit.**

Set `X = α*x`, `Y = α*y`, `m = ord_O X`, `n = ord_O Y` (both finite, as
`α.pullback` is injective). Since `localParam = -x/y`, `ord_O(α*localParam)
= m − n`, so the hypothesis `h_pos` says `m > n`. The Weierstrass equation for
`(X, Y)` (`pullback_equation_inl`) then forces a pole of `X`:

* `h_base : m ≤ 0` rules out `α(O)` being a *finite* point where `X` is a unit.
  Combined with `m > n` it gives either `m < 0` (done) or `m = 0`.
* If `m = 0` then `n < 0`, and in the Weierstrass identity
  `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` the term `Y²` has order `2n`, which
  is *strictly* smaller than every other term (orders `≥ n > 2n` on the left,
  `≥ 0` on the right). Strict non-archimedean additivity
  (`ordAtInfty_add_eq_of_lt`) makes the left side have order `2n`, while the
  right side has order `≥ 0`; equality forces `2n ≥ 0`, contradicting `n < 0`.

This is exactly the discrete-valuation form of Silverman II.2 / IV.1 (a function
on an elliptic curve has order `−2k`/`−3k` at a pole of `x`). **No substitution
lemma is used.** The hypothesis `h_base` is the valuation form of "`α` is
defined at `O`" (basepoint preservation), which the `Isogeny` structure of this
file does *not* carry — see the note on R5a. -/
theorem ord_pullback_x_neg_of_localParam_pos (α : Isogeny W.toAffine W.toAffine)
    (h_base : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) ≤ 0)
    (h_pos : 0 < (W_smooth W).ordAtInfty (α.pullback (localParam W))) :
    (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0 := by
  have hX_ne : α.pullback (x_gen W) ≠ 0 := fun h ↦
    x_gen_ne_zero W (α.pullback_injective (h.trans (map_zero _).symm))
  have hY_ne : α.pullback (y_gen W) ≠ 0 := fun h ↦
    y_gen_ne_zero W (α.pullback_injective (h.trans (map_zero _).symm))
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ordAtInfty (α.pullback (x_gen W)) = (m : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hX_ne
    | coe k => exact ⟨k, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (W_smooth W).ordAtInfty (α.pullback (y_gen W)) = (n : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty (α.pullback (y_gen W)) with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hY_ne
    | coe k => exact ⟨k, rfl⟩
  -- `ord_O(α*localParam) = m − n` via `localParam = -x/y`.
  have h_lp : (W_smooth W).ordAtInfty (α.pullback (localParam W)) = ((m - n : ℤ) : WithTop ℤ) := by
    have h_eq : α.pullback (localParam W) =
        -(α.pullback (x_gen W)) / (α.pullback (y_gen W)) := by
      unfold localParam
      rw [map_div₀, map_neg]
    rw [h_eq]
    have h_neg_x : (W_smooth W).ordAtInfty (-(α.pullback (x_gen W))) = (m : WithTop ℤ) :=
      ((W_smooth W).ordAtInfty_neg _).trans hm
    exact (W_smooth W).ord_div_concrete hY_ne m n h_neg_x hn
  rw [h_lp] at h_pos
  have h_nm : n < m := by
    have h0 : (0 : ℤ) < m - n := by exact_mod_cast h_pos
    omega
  rw [hm] at h_base ⊢
  rw [WithTop.coe_le_zero] at h_base
  rw [WithTop.coe_lt_zero]
  rcases lt_or_eq_of_le h_base with h_lt | h_eq0
  · exact h_lt
  · -- `m = 0` ⟹ `n < 0`; the Weierstrass equation contradicts this.
    exfalso
    have hn_neg : n < 0 := h_eq0 ▸ h_nm
    have h_weier := pullback_equation_inl W α
    rw [Affine.equation_iff'] at h_weier
    set X := α.pullback (x_gen W) with hXdef
    set Y := α.pullback (y_gen W) with hYdef
    have h_eq2 : Y ^ 2 + ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y) =
        X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
          + (W_KE W).toAffine.a₆ := by linear_combination h_weier
    have hca1 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₁)
    have hca2 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₂)
    have hca3 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₃) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₃)
    have hca4 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₄)
    have hca6 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₆) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₆)
    have hX0 : (W_smooth W).ordAtInfty X = ((0 : ℤ) : WithTop ℤ) := by rw [hXdef, hm, ← h_eq0]
    have hYn : (W_smooth W).ordAtInfty Y = ((n : ℤ) : WithTop ℤ) := by rw [hYdef, hn]
    have hY2 : (W_smooth W).ordAtInfty (Y ^ 2) = ((2 * n : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ord_pow_concrete hY_ne n 2 hYn).trans (by norm_num)
    have hX3 : (W_smooth W).ordAtInfty (X ^ 3) = ((0 : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ord_pow_concrete hX_ne 0 3 hX0).trans (by norm_num)
    have hX2 : (W_smooth W).ordAtInfty (X ^ 2) = ((0 : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ord_pow_concrete hX_ne 0 2 hX0).trans (by norm_num)
    have hord_a1X : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X) :=
      calc (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_num
        _ = (W_smooth W).ordAtInfty X := hX0.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₁) X hca1
    have hterm2_ge : (n : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X * Y) :=
      calc (n : WithTop ℤ) = (W_smooth W).ordAtInfty Y := hYn.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₁ * X) Y hord_a1X
    have hterm3_ge : (n : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₃ * Y) :=
      calc (n : WithTop ℤ) = (W_smooth W).ordAtInfty Y := hYn.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₃) Y hca3
    have hterm23_ge : (n : WithTop ℤ) ≤
        (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y) :=
      le_trans (le_min hterm2_ge hterm3_ge) ((W_smooth W).ordAtInfty_add_ge_min _ _)
    have h2n_lt_n : ((2 * n : ℤ) : WithTop ℤ) < (n : WithTop ℤ) := by rw [WithTop.coe_lt_coe]; omega
    have hLHS : (W_smooth W).ordAtInfty
        (Y ^ 2 + ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y))
        = ((2 * n : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ordAtInfty_add_eq_of_lt
        (hY2 ▸ lt_of_lt_of_le h2n_lt_n hterm23_ge)).trans hY2
    have hb1 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂ * X ^ 2) :=
      calc (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_num
        _ = (W_smooth W).ordAtInfty (X ^ 2) := hX2.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₂) (X ^ 2) hca2
    have hb2 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄ * X) :=
      calc (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_num
        _ = (W_smooth W).ordAtInfty X := hX0.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₄) X hca4
    have hRHS_ge : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
          + (W_KE W).toAffine.a₆) := by
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      refine le_min ?_ hca6
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      refine le_min ?_ hb2
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      exact le_min (hX3 ▸ le_refl _) hb1
    have hRHS_ord : (W_smooth W).ordAtInfty
        (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
          + (W_KE W).toAffine.a₆) = ((2 * n : ℤ) : WithTop ℤ) :=
      (congrArg (W_smooth W).ordAtInfty h_eq2).symm.trans hLHS
    rw [hRHS_ord, WithTop.coe_nonneg] at hRHS_ge
    omega

/-! ### Generic Weierstrass-point pole brick (the `x`-pole ⟹ `z` reduces direction)

The companion to `ord_pullback_x_neg_of_localParam_pos`: that lemma runs the
discrete-valuation argument "`z` vanishes at `O` ⟹ `x` has a pole at `O`". For
the formal-group subgroup closure we need the **converse, generic** direction:
for *any* point `(X, Y)` on `W_KE W` (the curve over `K(E)`) — not necessarily a
single-isogeny pullback — whose `x`-coordinate `X` has a pole at `O`
(`ord_∞ X < 0`), the local parameter `z = −X/Y` *reduces to `O`*
(`ord_∞ (−X/Y) > 0`).

The mechanism is the standard valuation balance in the Weierstrass equation
`Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆`: when `X` has a pole of order `m < 0`,
the right-hand side has order exactly `3m` (the `X³` term strictly dominates the
constant-bounded lower terms), so the left-hand side does too; that forces
`ord Y < ord X` (a pole of `Y` strictly deeper than `X`), whence
`ord(−X/Y) = ord X − ord Y > 0`. This is the **`z`-coordinate / IV.1.4 order
conversion** half, generic in `(X, Y)` so it applies to the addition-formula
output `(addPullback_x_pair, addPullback_y_pair)` exactly as to a single pullback.
No formal-group law is used here — only the curve equation and the shipped
`ordAtInfty` valuation API. -/

/-- **Generic: a pole of `X` forces `Y ≠ 0`.** For `(X, Y)` on `W_KE W` satisfying
the Weierstrass equation, if the `x`-coordinate `X` has a pole at `O`
(`ord_∞ X < 0`) then `Y ≠ 0`.

**Why this is axiom-clean (no formal-group law).**  If `Y = 0`, the Weierstrass
equation `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` degenerates to
`X³ + a₂X² + a₄X + a₆ = 0`, i.e. `X` is a root of a *monic cubic with
constant (base-field) coefficients*, hence `X` is algebraic over `K` — but an
element with a pole at `O` (`ord_∞ X = m < 0`) cannot be algebraic over `K`.
Concretely we run the valuation balance directly: `X³` has order `3m`, while
`−(a₂X² + a₄X + a₆)` has order `≥ 2m > 3m` (the lower-degree terms in `X` strictly
dominate because the coefficients are regular at `O`), so the two sides cannot be
equal.  No `addPullback_y_pair`-specific or formal-group input is used — only the
curve equation and the shipped `ordAtInfty` valuation API; so it applies to the
addition-formula output `(addPullback_x_pair, addPullback_y_pair)` exactly as to a
single pullback. -/
theorem ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg {X Y : KE} (hX_ne : X ≠ 0)
    (h_weier : (W_KE W).toAffine.Equation X Y)
    (hX_neg : (W_smooth W).ordAtInfty X < 0) :
    Y ≠ 0 := by
  intro hY0
  subst hY0
  -- Integer order of `X`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ordAtInfty X = (m : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty X with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hX_ne
    | coe k => exact ⟨k, rfl⟩
  have hm_neg : m < 0 := by rw [hm] at hX_neg; exact_mod_cast hX_neg
  -- Weierstrass equation at `Y = 0`: `X³ + a₂X² + a₄X + a₆ = 0`.
  rw [Affine.equation_iff'] at h_weier
  have h_cubic : X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
      + (W_KE W).toAffine.a₆ = 0 := by linear_combination -h_weier
  -- Coefficient orders are `≥ 0`.
  have hca2 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₂)
  have hca4 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₄)
  have hca6 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₆) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₆)
  -- Closed-form term orders: `ord(X³) = 3m`, lower terms `≥ 2m, m, 0`.
  have hX3 : (W_smooth W).ordAtInfty (X ^ 3) = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hX_ne m 3 hm).trans (by norm_num)
  have hX2 : (W_smooth W).ordAtInfty (X ^ 2) = ((2 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hX_ne m 2 hm).trans (by norm_num)
  have hb_a2X2 : ((2 * m : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂ * X ^ 2) :=
    calc ((2 * m : ℤ) : WithTop ℤ) = (W_smooth W).ordAtInfty (X ^ 2) := hX2.symm
      _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₂) (X ^ 2) hca2
  have hb_a4X : (m : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄ * X) :=
    calc (m : WithTop ℤ) = (W_smooth W).ordAtInfty X := hm.symm
      _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₄) X hca4
  -- `3m < 2m < m < 0` since `m < 0`.
  have h3m_lt_2m : ((3 * m : ℤ) : WithTop ℤ) < ((2 * m : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have h3m_lt_m : ((3 * m : ℤ) : WithTop ℤ) < (m : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have h3m_lt_0 : ((3 * m : ℤ) : WithTop ℤ) < (0 : WithTop ℤ) := by
    rw [WithTop.coe_lt_zero]; omega
  -- Build `ord(X³ + a₂X² + a₄X + a₆) = 3m` by peeling outside-in (`X³` dominates).
  have hRHS1 : (W_smooth W).ordAtInfty (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2)
      = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt
      (hX3 ▸ lt_of_lt_of_le h3m_lt_2m hb_a2X2)).trans hX3
  have hRHS2 : (W_smooth W).ordAtInfty
      (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X)
      = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt
      (hRHS1 ▸ lt_of_lt_of_le h3m_lt_m hb_a4X)).trans hRHS1
  have hRHS' : (W_smooth W).ordAtInfty
      (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
        + (W_KE W).toAffine.a₆) = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt
      (hRHS2 ▸ lt_of_lt_of_le h3m_lt_0 hca6)).trans hRHS2
  -- But the sum is `0`, with order `⊤ ≠ 3m`. Contradiction.
  have hsum_top : (W_smooth W).ordAtInfty
      (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
        + (W_KE W).toAffine.a₆) = ⊤ :=
    (congrArg (W_smooth W).ordAtInfty h_cubic).trans (W_smooth W).ordAtInfty_zero
  rw [hsum_top] at hRHS'
  exact absurd hRHS'.symm (WithTop.coe_ne_top)

/-- **Generic: a pole of `X` forces a strictly deeper pole of `Y`.** For `(X, Y)`
on `W_KE W` satisfying the Weierstrass equation with `X, Y ≠ 0` and `ord_∞ X < 0`,
the order of `Y` is strictly below that of `X`: `ord_∞ Y < ord_∞ X`. -/
theorem ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg
    {X Y : KE} (hX_ne : X ≠ 0) (hY_ne : Y ≠ 0)
    (h_weier : (W_KE W).toAffine.Equation X Y)
    (hX_neg : (W_smooth W).ordAtInfty X < 0) :
    (W_smooth W).ordAtInfty Y < (W_smooth W).ordAtInfty X := by
  -- Integer ords.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ordAtInfty X = (m : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty X with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hX_ne
    | coe k => exact ⟨k, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (W_smooth W).ordAtInfty Y = (n : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty Y with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hY_ne
    | coe k => exact ⟨k, rfl⟩
  -- `m < 0`.
  have hm_neg : m < 0 := by rw [hm] at hX_neg; exact_mod_cast hX_neg
  -- Suppose, for contradiction, `m ≤ n`. We will derive `ord(LHS) > 3m = ord(RHS)`.
  rw [hm, hn, WithTop.coe_lt_coe]
  by_contra! h_not
  -- Weierstrass equation rearranged.
  rw [Affine.equation_iff'] at h_weier
  have h_eq2 : Y ^ 2 + ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y) =
      X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
        + (W_KE W).toAffine.a₆ := by linear_combination h_weier
  -- Coefficient orders are `≥ 0`.
  have hca1 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₁)
  have hca2 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₂)
  have hca3 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₃) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₃)
  have hca4 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₄)
  have hca6 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₆) :=
    ord_algebraMap_F_nonneg W (W.toAffine.a₆)
  -- Closed-form term orders.
  have hX3 : (W_smooth W).ordAtInfty (X ^ 3) = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hX_ne m 3 hm).trans (by norm_num)
  have hX2 : (W_smooth W).ordAtInfty (X ^ 2) = ((2 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hX_ne m 2 hm).trans (by norm_num)
  have hY2 : (W_smooth W).ordAtInfty (Y ^ 2) = ((2 * n : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ord_pow_concrete hY_ne n 2 hn).trans (by norm_num)
  -- RHS: `X³` is the unique strict dominant term, so `ord(RHS) = 3m`.
  have hb_a2X2 : ((2 * m : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂ * X ^ 2) :=
    calc ((2 * m : ℤ) : WithTop ℤ) = (W_smooth W).ordAtInfty (X ^ 2) := hX2.symm
      _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₂) (X ^ 2) hca2
  have hb_a4X : (m : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄ * X) :=
    calc (m : WithTop ℤ) = (W_smooth W).ordAtInfty X := hm.symm
      _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₄) X hca4
  -- `3m < 2m < m < 0` since `m < 0`; so the three lower RHS terms beat `X³` strictly.
  have h3m_lt_2m : ((3 * m : ℤ) : WithTop ℤ) < ((2 * m : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have h3m_lt_m : ((3 * m : ℤ) : WithTop ℤ) < (m : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have h3m_lt_0 : ((3 * m : ℤ) : WithTop ℤ) < (0 : WithTop ℤ) := by
    rw [WithTop.coe_lt_zero]; omega
  -- Build `ord(RHS) = 3m` by peeling the (left-associated) sum from the outside in,
  -- keeping the exact associativity that appears in `h_eq2` (no reassociation `rw`).
  -- `ord(X³ + a₂X²) = 3m` (X³ strictly dominates a₂X²).
  have hRHS1 : (W_smooth W).ordAtInfty (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2)
      = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt
      (hX3 ▸ lt_of_lt_of_le h3m_lt_2m hb_a2X2)).trans hX3
  -- `ord((X³ + a₂X²) + a₄X) = 3m`.
  have hRHS2 : (W_smooth W).ordAtInfty
      (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X)
      = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt
      (hRHS1 ▸ lt_of_lt_of_le h3m_lt_m hb_a4X)).trans hRHS1
  -- `ord(((X³ + a₂X²) + a₄X) + a₆) = 3m`.
  have hRHS' : (W_smooth W).ordAtInfty
      (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
        + (W_KE W).toAffine.a₆) = ((3 * m : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_add_eq_of_lt
      (hRHS2 ▸ lt_of_lt_of_le h3m_lt_0 hca6)).trans hRHS2
  -- LHS: under `m ≤ n` every LHS term has order `> 3m`, so `ord(LHS) > 3m`.
  have hord_a1X : (m : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X) :=
    calc (m : WithTop ℤ) = (W_smooth W).ordAtInfty X := hm.symm
      _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₁) X hca1
  -- `ord(a₁ X Y) ≥ m + n`.
  have hterm_a1XY : ((m + n : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X * Y) := by
    by_cases haX0 : (W_KE W).toAffine.a₁ * X = 0
    · rw [haX0, zero_mul]; exact (W_smooth W).ordAtInfty_zero ▸ le_top
    · calc ((m + n : ℤ) : WithTop ℤ) = (m : WithTop ℤ) + (n : WithTop ℤ) := by
            rw [WithTop.coe_add]
        _ ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X) +
              (W_smooth W).ordAtInfty Y := by rw [hn]; gcongr
        _ = (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X * Y) :=
            ((W_smooth W).ordAtInfty_mul haX0 hY_ne).symm
  -- `ord(a₃ Y) ≥ n`.
  have hterm_a3Y : (n : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₃ * Y) :=
    calc (n : WithTop ℤ) = (W_smooth W).ordAtInfty Y := hn.symm
      _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₃) Y hca3
  -- Each LHS term order `> 3m`: `2n > 3m`, `m+n > 3m`, `n > 3m` (all from `m ≤ n`, `m < 0`).
  have h3m_lt_2n : ((3 * m : ℤ) : WithTop ℤ) < ((2 * n : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have h3m_lt_mn : ((3 * m : ℤ) : WithTop ℤ) < ((m + n : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have h3m_lt_n : ((3 * m : ℤ) : WithTop ℤ) < (n : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have hLHS_gt : ((3 * m : ℤ) : WithTop ℤ) <
      (W_smooth W).ordAtInfty
        (Y ^ 2 + ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y)) := by
    refine lt_of_lt_of_le ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
    refine lt_min (hY2 ▸ h3m_lt_2n) ?_
    refine lt_of_lt_of_le ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
    exact lt_min (lt_of_lt_of_le h3m_lt_mn hterm_a1XY) (lt_of_lt_of_le h3m_lt_n hterm_a3Y)
  -- Contradiction: `ord(LHS) = ord(RHS) = 3m` but `ord(LHS) > 3m`.
  have hLHS_eq_RHS : (W_smooth W).ordAtInfty
      (Y ^ 2 + ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y)) =
      ((3 * m : ℤ) : WithTop ℤ) := (congrArg (W_smooth W).ordAtInfty h_eq2).trans hRHS'
  rw [hLHS_eq_RHS] at hLHS_gt
  exact absurd hLHS_gt (lt_irrefl _)

/-- **Generic `z`-reduction brick (the `x`-pole ⟹ `z` reduces direction).** For
`(X, Y)` on `W_KE W` satisfying the Weierstrass equation with `X, Y ≠ 0`, if the
`x`-coordinate `X` has a pole at `O` (`ord_∞ X < 0`), then the local parameter
`z = −X/Y` *reduces to `O`*: `ord_∞ (−X/Y) > 0`. Immediate from
`ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg` and `ord(−X/Y) = ord X − ord Y`. -/
theorem ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg
    {X Y : KE} (hX_ne : X ≠ 0) (hY_ne : Y ≠ 0)
    (h_weier : (W_KE W).toAffine.Equation X Y)
    (hX_neg : (W_smooth W).ordAtInfty X < 0) :
    0 < (W_smooth W).ordAtInfty (-X / Y) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ordAtInfty X = (m : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty X with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hX_ne
    | coe k => exact ⟨k, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (W_smooth W).ordAtInfty Y = (n : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty Y with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hY_ne
    | coe k => exact ⟨k, rfl⟩
  have hn_lt_m : n < m := by
    have h := ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg W hX_ne hY_ne h_weier hX_neg
    rw [hm, hn] at h; exact_mod_cast h
  have h_neg_x : (W_smooth W).ordAtInfty (-X) = (m : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_neg _).trans hm
  have h_div : (W_smooth W).ordAtInfty (-X / Y) = (((m - n : ℤ)) : WithTop ℤ) :=
    (W_smooth W).ord_div_concrete hY_ne m n h_neg_x hn
  rw [h_div, WithTop.coe_pos]
  omega

/-- **Generic converse: `z` reduces ⟹ `x` has a pole.** For `(X, Y)` on `W_KE W`
satisfying the Weierstrass equation with `X, Y ≠ 0`, if the local parameter
`z = −X/Y` *reduces to `O`* (`ord_∞ (−X/Y) > 0`) **and** `X` is not a unit at `O`
(`ord_∞ X ≤ 0`, the basepoint hypothesis), then `X` has a pole at `O`:
`ord_∞ X < 0`.

This is the generic form of `ord_pullback_x_neg_of_localParam_pos` (which is the
special case `(X, Y) = (α.pullback x_gen, α.pullback y_gen)`); the proof is the
same discrete-valuation argument on the Weierstrass equation. Generic in `(X, Y)`
so it applies to `(addPullback_x_pair, addPullback_y_pair)`. This is the
**back-conversion** step 4 of the formal-group route: once the formal-group
subgroup property gives `ord_∞(z_sum) > 0`, this brick (with the basepoint
hypothesis) returns `ord_∞(addPullback_x_pair) < 0`, the Wall-A goal. -/
theorem ordAtInfty_x_neg_of_equation_of_neg_div_pos {X Y : KE} (hX_ne : X ≠ 0) (hY_ne : Y ≠ 0)
    (h_weier : (W_KE W).toAffine.Equation X Y)
    (h_base : (W_smooth W).ordAtInfty X ≤ 0)
    (h_pos : 0 < (W_smooth W).ordAtInfty (-X / Y)) :
    (W_smooth W).ordAtInfty X < 0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ordAtInfty X = (m : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty X with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hX_ne
    | coe k => exact ⟨k, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (W_smooth W).ordAtInfty Y = (n : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty Y with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hY_ne
    | coe k => exact ⟨k, rfl⟩
  -- `ord(−X/Y) = m − n`, so `h_pos` says `n < m`.
  have h_neg_x : (W_smooth W).ordAtInfty (-X) = (m : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_neg _).trans hm
  have h_lp : (W_smooth W).ordAtInfty (-X / Y) = ((m - n : ℤ) : WithTop ℤ) :=
    (W_smooth W).ord_div_concrete hY_ne m n h_neg_x hn
  rw [h_lp] at h_pos
  have h_nm : n < m := by
    have h0 : (0 : ℤ) < m - n := by exact_mod_cast h_pos
    omega
  rw [hm] at h_base ⊢
  rw [WithTop.coe_le_zero] at h_base
  rw [WithTop.coe_lt_zero]
  rcases lt_or_eq_of_le h_base with h_lt | h_eq0
  · exact h_lt
  · -- `m = 0` ⟹ `n < 0`; the Weierstrass equation contradicts this (`Y²` dominant at `2n`).
    exfalso
    have hn_neg : n < 0 := h_eq0 ▸ h_nm
    rw [Affine.equation_iff'] at h_weier
    have h_eq2 : Y ^ 2 + ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y) =
        X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
          + (W_KE W).toAffine.a₆ := by linear_combination h_weier
    have hca1 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₁)
    have hca2 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₂)
    have hca3 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₃) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₃)
    have hca4 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₄)
    have hca6 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₆) :=
      ord_algebraMap_F_nonneg W (W.toAffine.a₆)
    have hX0 : (W_smooth W).ordAtInfty X = ((0 : ℤ) : WithTop ℤ) := by rw [hm, ← h_eq0]
    have hY2 : (W_smooth W).ordAtInfty (Y ^ 2) = ((2 * n : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ord_pow_concrete hY_ne n 2 hn).trans (by norm_num)
    have hX3 : (W_smooth W).ordAtInfty (X ^ 3) = ((0 : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ord_pow_concrete hX_ne 0 3 hX0).trans (by norm_num)
    have hX2 : (W_smooth W).ordAtInfty (X ^ 2) = ((0 : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ord_pow_concrete hX_ne 0 2 hX0).trans (by norm_num)
    have hord_a1X : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X) :=
      calc (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_num
        _ = (W_smooth W).ordAtInfty X := hX0.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₁) X hca1
    have hterm2_ge : (n : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X * Y) :=
      calc (n : WithTop ℤ) = (W_smooth W).ordAtInfty Y := hn.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₁ * X) Y hord_a1X
    have hterm3_ge : (n : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₃ * Y) :=
      calc (n : WithTop ℤ) = (W_smooth W).ordAtInfty Y := hn.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₃) Y hca3
    have hterm23_ge : (n : WithTop ℤ) ≤
        (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y) :=
      le_trans (le_min hterm2_ge hterm3_ge) ((W_smooth W).ordAtInfty_add_ge_min _ _)
    have h2n_lt_n : ((2 * n : ℤ) : WithTop ℤ) < (n : WithTop ℤ) := by rw [WithTop.coe_lt_coe]; omega
    have hLHS : (W_smooth W).ordAtInfty
        (Y ^ 2 + ((W_KE W).toAffine.a₁ * X * Y + (W_KE W).toAffine.a₃ * Y))
        = ((2 * n : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ordAtInfty_add_eq_of_lt
        (hY2 ▸ lt_of_lt_of_le h2n_lt_n hterm23_ge)).trans hY2
    have hb1 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₂ * X ^ 2) :=
      calc (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_num
        _ = (W_smooth W).ordAtInfty (X ^ 2) := hX2.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₂) (X ^ 2) hca2
    have hb2 : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty ((W_KE W).toAffine.a₄ * X) :=
      calc (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_num
        _ = (W_smooth W).ordAtInfty X := hX0.symm
        _ ≤ _ := ord_coeff_mul_ge W ((W_KE W).toAffine.a₄) X hca4
    have hRHS_ge : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
          + (W_KE W).toAffine.a₆) := by
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      refine le_min ?_ hca6
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      refine le_min ?_ hb2
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      exact le_min (hX3 ▸ le_refl _) hb1
    have hRHS_ord : (W_smooth W).ordAtInfty
        (X ^ 3 + (W_KE W).toAffine.a₂ * X ^ 2 + (W_KE W).toAffine.a₄ * X
          + (W_KE W).toAffine.a₆) = ((2 * n : ℤ) : WithTop ℤ) :=
      (congrArg (W_smooth W).ordAtInfty h_eq2).symm.trans hLHS
    rw [hRHS_ord, WithTop.coe_nonneg] at hRHS_ge
    omega

/-! **[2026-05-29 B2 — false residuals deleted]** The residuals R5a
(`orderTop_localExpand_pullback_x_gen_neg_of_orderTop_localParam_pos`) and its
composite (`ordAtInfty_pullback_x_gen_gen_neg_of_orderTop_pos`) were DELETED:
both were FALSE as stated for the unconstrained `HasseWeil.Isogeny` (whose
`pullback` is an arbitrary `F`-algebra hom with no basepoint preservation).
Counterexample: over `E : y² = x³ + 1`, the translation-by-`(0,1)` comorphism is
a legal `pullback` with `ord_O(α*localParam) > 0` yet `ord_O(α*x) ≥ 0`,
contradicting the conclusion. The TRUE statements — with the basepoint
hypothesis `ord_O(α*x) ≤ 0` made explicit — are
`ord_pullback_x_neg_of_localParam_pos` and
`ordAtInfty_pullback_x_gen_neg_of_orderTop_pos_of_base` above (both axiom-clean).
Logged in `.mathlib-quality/b2_log.jsonl`. -/

/-! ### R5b: the formal valuation `orderTop ∘ localExpand` equals `ordAtInfty`

We prove the full identity `(localExpand f).orderTop = (W_smooth W).ordAtInfty f`
for all `f : KE`, of which R5b is the `< 0` direction. The proof matches the two
valuations on the `F(X)`-subfield (both `= -2 · intDegree`) and on the generator
`y_gen` (both `= -3`), then uses the order-parity / non-cancellation argument on
the basis decomposition `f = α + β · y_gen` (`F(X)`-images have even formal/norm
order, the `β · y_gen` term has odd order). The `ordAtInfty` side of this min
formula is `Curves/Infinity.lean`'s `ordAtInfty_basis_eq_min`; the `localExpand`
side reuses the parity structure already shipped in `LocalExpansion.lean`
(`localExpand_inner_orderTop_eq`, `formalY_orderTop`). -/

/-- `localExpand` of a nonzero `F(X)`-image has formal order `-2 · intDegree`,
matching `ordAtInfty` on `F(X)` (`ordAtInfty_algebraMap_fracPolyX_of_ne_zero`).

Write `r₀ = p / d` (`IsLocalization.surj`); then `localExpand (algebraMap r₀) ·
localExpand_inner d = localExpand_inner p`, and the order arithmetic gives
`orderTop = -2 (natDeg p - natDeg d) = -2 · intDegree r₀`. -/
theorem orderTop_localExpand_algebraMap_fracPolyX
    {r₀ : FractionRing (Polynomial F)} (hr₀ : r₀ ≠ 0) :
    (localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₀)).orderTop =
      ((-2 * (RatFunc.ofFractionRing r₀ : RatFunc F).intDegree : ℤ) : WithTop ℤ) := by
  obtain ⟨⟨p, ⟨d, hd_mem⟩⟩, hpd⟩ :=
    IsLocalization.surj (nonZeroDivisors (Polynomial F)) r₀
  have hd_ne : d ≠ 0 := nonZeroDivisors.ne_zero hd_mem
  have hd_alg_ne : algebraMap (Polynomial F) (FractionRing (Polynomial F)) d ≠ 0 :=
    fun h ↦ hd_ne (FaithfulSMul.algebraMap_injective _ _ (h.trans (map_zero _).symm))
  -- `p ≠ 0` since `r₀ ≠ 0` and `r₀ * algebraMap d = algebraMap p`.
  have hp_ne : p ≠ 0 := by
    intro hp
    apply hr₀
    have h_zero : r₀ * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d = 0 := by
      rw [hpd, hp, map_zero]
    exact (mul_eq_zero.mp h_zero).resolve_right hd_alg_ne
  -- `r₀ * algebraMap d = algebraMap p` in `F(X)`, then mapped into `KE`.
  have hpd' : r₀ * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d =
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) p := hpd
  -- Map `r₀ * algebraMap d = algebraMap p` into `KE` and apply `localExpand`.
  set a : LaurentSeries F :=
    localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₀) with ha_def
  have h_mul : a * localExpand W (algebraMap (Polynomial F) KE d) =
      localExpand W (algebraMap (Polynomial F) KE p) := by
    rw [ha_def,
      show (algebraMap (Polynomial F) KE d) =
          algebraMap (FractionRing (Polynomial F)) KE
            (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d) from
        IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE d,
      show (algebraMap (Polynomial F) KE p) =
          algebraMap (FractionRing (Polynomial F)) KE
            (algebraMap (Polynomial F) (FractionRing (Polynomial F)) p) from
        IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE p,
      ← map_mul, ← map_mul, hpd']
  -- Take `orderTop` of both sides; both `localExpand_inner` factors are known.
  have h_ord := congrArg HahnSeries.orderTop h_mul
  rw [HahnSeries.orderTop_mul, orderTop_localExpand_algebraMap_polynomial W hd_ne,
    orderTop_localExpand_algebraMap_polynomial W hp_ne] at h_ord
  -- `a.orderTop + (-2 natDeg d) = -2 natDeg p`; `a ≠ 0`, so `a.orderTop` is a coe.
  have ha_ne : a ≠ 0 := by
    rw [ha_def]
    intro h
    apply hr₀
    have hz := (RingHom.injective (localExpand W)) (h.trans (map_zero _).symm)
    exact FaithfulSMul.algebraMap_injective (FractionRing (Polynomial F)) KE
      (hz.trans (map_zero _).symm)
  -- `intDegree (ofFractionRing r₀) = natDeg p - natDeg d`.
  have h_intDeg : (RatFunc.ofFractionRing r₀ : RatFunc F).intDegree =
      (p.natDegree : ℤ) - (d.natDegree : ℤ) := by
    have hr_eq : r₀ = algebraMap (Polynomial F) (FractionRing (Polynomial F)) p *
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hd_alg_ne).mpr hpd'
    have hofD_ne : (RatFunc.ofFractionRing (algebraMap (Polynomial F)
        (FractionRing (Polynomial F)) d) : RatFunc F) ≠ 0 := by
      rw [RatFunc.ofFractionRing_algebraMap]
      exact fun heq ↦ hd_ne (FaithfulSMul.algebraMap_injective (Polynomial F) (RatFunc F)
        (heq.trans (map_zero _).symm))
    have hofP_ne : (RatFunc.ofFractionRing (algebraMap (Polynomial F)
        (FractionRing (Polynomial F)) p) : RatFunc F) ≠ 0 := by
      rw [RatFunc.ofFractionRing_algebraMap]
      exact fun heq ↦ hp_ne (FaithfulSMul.algebraMap_injective (Polynomial F) (RatFunc F)
        (heq.trans (map_zero _).symm))
    rw [hr_eq, RatFunc.ofFractionRing_mul, RatFunc.ofFractionRing_inv,
      RatFunc.intDegree_mul hofP_ne (inv_ne_zero hofD_ne), RatFunc.intDegree_inv,
      RatFunc.ofFractionRing_algebraMap, RatFunc.ofFractionRing_algebraMap,
      RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
    ring
  -- Solve for `a.orderTop` in `WithTop ℤ`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, a.orderTop = (k : WithTop ℤ) := by
    cases hao : a.orderTop with
    | top => exact absurd (HahnSeries.orderTop_eq_top.mp hao) ha_ne
    | coe k => exact ⟨k, rfl⟩
  rw [hk, ← WithTop.coe_add, WithTop.coe_inj] at h_ord
  rw [hk, h_intDeg, WithTop.coe_inj]
  linarith [h_ord]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `y_gen W` and `(W_smooth W).coordYInFunctionField` are the same element of
`KE`: both are `algebraMap R KE (AdjoinRoot.root W.polynomial)` (the curve of
`W_smooth W` is `W.toAffine` definitionally). -/
theorem y_gen_eq_coordYInFunctionField :
    y_gen W = (W_smooth W).coordYInFunctionField := rfl

/-- `orderTop (localExpand (y_gen W)) = -3`, matching `ordAtInfty (y_gen W) = -3`. -/
theorem orderTop_localExpand_y_gen :
    (localExpand W (y_gen W)).orderTop = ((-3 : ℤ) : WithTop ℤ) := by
  rw [localExpand_y_gen]
  exact formalY_orderTop W

/-- **Parity / min formula for `orderTop ∘ localExpand`** on the basis
decomposition `f = algebraMap r₁ + algebraMap r₂ · y_gen` (`r₁, r₂ ∈ F(X)`),
the exact analogue of `Curves/Infinity.lean`'s `ordAtInfty_basis_eq_min`:
`orderTop (localExpand f) = min (orderTop (localExpand (algebraMap r₁)))
  (orderTop (localExpand (algebraMap r₂)) + orderTop (localExpand (y_gen)))`.

The `F(X)`-image `algebraMap r₁` has *even* formal order `-2 intDeg r₁`
(`orderTop_localExpand_algebraMap_fracPolyX`), while `algebraMap r₂ · y_gen` has
*odd* order `-2 intDeg r₂ - 3`. Even and odd never coincide, so the formal order
of the sum is the smaller of the two (`HahnSeries.orderTop_add_eq_left/right`). -/
theorem orderTop_localExpand_basis_eq_min (r₁ r₂ : FractionRing (Polynomial F)) :
    (localExpand W
      (algebraMap (FractionRing (Polynomial F)) KE r₁ +
       algebraMap (FractionRing (Polynomial F)) KE r₂ * y_gen W)).orderTop =
      min (localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₁)).orderTop
          ((localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₂)).orderTop +
           (localExpand W (y_gen W)).orderTop) := by
  rw [map_add, map_mul]
  set A := localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₁) with hA_def
  set B := localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₂) with hB_def
  set Y := localExpand W (y_gen W) with hY_def
  -- Rewrite the RHS min's second summand `B.orderTop + Y.orderTop = (B*Y).orderTop`.
  rw [← HahnSeries.orderTop_mul B Y]
  by_cases hr₁ : r₁ = 0
  · -- `A = 0`: the sum is `B * Y`, and `A.orderTop = ⊤`, so min picks the right term.
    have hA0 : A = 0 := by rw [hA_def, hr₁, map_zero, map_zero]
    rw [hA0, zero_add, HahnSeries.orderTop_zero]
    exact (min_eq_right le_top).symm
  · by_cases hr₂ : r₂ = 0
    · -- `B = 0`: the sum is `A`, and `(B*Y).orderTop = ⊤`.
      have hB0 : B = 0 := by rw [hB_def, hr₂, map_zero, map_zero]
      rw [hB0, zero_mul, add_zero, HahnSeries.orderTop_zero]
      exact (min_eq_left le_top).symm
    · -- Both nonzero: parity argument on `A.orderTop` (even) vs `(B*Y).orderTop` (odd).
      have hA_ord : A.orderTop =
          ((-2 * (RatFunc.ofFractionRing r₁ : RatFunc F).intDegree : ℤ) : WithTop ℤ) :=
        orderTop_localExpand_algebraMap_fracPolyX W hr₁
      have hB_ord : B.orderTop =
          ((-2 * (RatFunc.ofFractionRing r₂ : RatFunc F).intDegree : ℤ) : WithTop ℤ) :=
        orderTop_localExpand_algebraMap_fracPolyX W hr₂
      have hBY_ord : (B * Y).orderTop =
          (((-2 * (RatFunc.ofFractionRing r₂ : RatFunc F).intDegree - 3 : ℤ)) : WithTop ℤ) := by
        rw [HahnSeries.orderTop_mul, hB_ord, hY_def, orderTop_localExpand_y_gen,
          ← WithTop.coe_add, WithTop.coe_inj]
        ring
      -- Orders differ: one even, one odd.
      have h_ne : A.orderTop ≠ (B * Y).orderTop := by
        rw [hA_ord, hBY_ord, Ne, WithTop.coe_inj]; omega
      rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
      · rw [HahnSeries.orderTop_add_eq_left h_lt]
        exact (min_eq_left h_lt.le).symm
      · rw [HahnSeries.orderTop_add_eq_right h_lt]
        exact (min_eq_right h_lt.le).symm

/-- The two valuations agree on every `F(X)`-image (including `0`):
`orderTop (localExpand (algebraMap r)) = ordAtInfty (algebraMap r)`. For `r ≠ 0`
both are `-2 · intDegree r`; for `r = 0` both are `⊤`. -/
theorem orderTop_localExpand_algebraMap_fracPolyX_eq_ordAtInfty (r : FractionRing (Polynomial F)) :
    (localExpand W (algebraMap (FractionRing (Polynomial F)) KE r)).orderTop =
      (W_smooth W).ordAtInfty (algebraMap (FractionRing (Polynomial F)) KE r) := by
  by_cases hr : r = 0
  · subst hr
    rw [map_zero, map_zero, HahnSeries.orderTop_zero]
    exact ((W_smooth W).ordAtInfty_zero).symm
  · rw [orderTop_localExpand_algebraMap_fracPolyX W hr]
    exact ((W_smooth W).ordAtInfty_algebraMap_fracPolyX_of_ne_zero hr).symm

/-- **The formal valuation `orderTop ∘ localExpand` equals `ordAtInfty`**
on all of `K(E)`. Decompose `f = algebraMap r₁ + algebraMap r₂ · y_gen`
(`exists_decomp`); both valuations equal the same `min` of the two summand
orders (`orderTop_localExpand_basis_eq_min` and `ordAtInfty_basis_eq_min`),
and the summand orders agree on `F(X)`-images and on `y_gen = coordY`. -/
theorem orderTop_localExpand_eq_ordAtInfty (f : KE) :
    (localExpand W f).orderTop = (W_smooth W).ordAtInfty f := by
  obtain ⟨r₁, r₂, hf⟩ := (W_smooth W).exists_decomp f
  -- `f = algebraMap r₁ + algebraMap r₂ · y_gen` (additive form of the smul basis;
  -- `y_gen W = (W_smooth W).coordYInFunctionField` definitionally).
  have h_eq : f = algebraMap (FractionRing (Polynomial F)) KE r₁ +
      algebraMap (FractionRing (Polynomial F)) KE r₂ * y_gen W := by
    rw [hf, y_gen_eq_coordYInFunctionField, Algebra.smul_def, mul_one, Algebra.smul_def]; rfl
  -- LHS: formal-order min formula.
  have h_LHS : (localExpand W f).orderTop =
      min (localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₁)).orderTop
          ((localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₂)).orderTop +
           (localExpand W (y_gen W)).orderTop) := by
    rw [h_eq]; exact orderTop_localExpand_basis_eq_min W r₁ r₂
  -- RHS: ord-at-infinity min formula (`ordAtInfty_basis_eq_min` is stated with
  -- `coordYInFunctionField`, defeq to `y_gen W`).
  have h_RHS : (W_smooth W).ordAtInfty f =
      min ((W_smooth W).ordAtInfty (algebraMap (FractionRing (Polynomial F)) KE r₁))
          ((W_smooth W).ordAtInfty (algebraMap (FractionRing (Polynomial F)) KE r₂) +
           (W_smooth W).ordAtInfty (y_gen W)) := by
    rw [h_eq]; exact (W_smooth W).ordAtInfty_basis_eq_min r₁ r₂
  rw [h_LHS, h_RHS]
  -- Match the two `min`s componentwise.
  refine congr_arg₂ min
    (orderTop_localExpand_algebraMap_fracPolyX_eq_ordAtInfty W r₁) ?_
  rw [orderTop_localExpand_algebraMap_fracPolyX_eq_ordAtInfty W r₂]
  congr 1
  rw [orderTop_localExpand_y_gen, y_gen_eq_coordYInFunctionField,
    (W_smooth W).ordAtInfty_coordYInFunctionField]

/-- **Residual R5b (`<0`-direction valuation bridge `orderTop ∘ localExpand
→ ordAtInfty`)**: if the formal `t`-adic expansion of `f` at `O` has a pole
(`orderTop (localExpand f) < 0`), then so does `f` in the norm-based order:
`ordAtInfty f < 0`. Immediate from the full identity
`orderTop_localExpand_eq_ordAtInfty`. -/
theorem ordAtInfty_neg_of_orderTop_localExpand_neg
    {f : KE} (h : (localExpand W f).orderTop < (0 : WithTop ℤ)) :
    (W_smooth W).ordAtInfty f < 0 := by
  rwa [orderTop_localExpand_eq_ordAtInfty W f] at h

/-- **QF Layer-1 brick 5, basepoint-hypothesis form (TRUE, axiom-clean).**

If `α*t` vanishes at `O` (`0 < orderTop (localExpand (α*t))`) **and** `α*x` is
not a unit there (`ordAtInfty (α*x) ≤ 0`, the basepoint hypothesis), then `α*x`
has a pole at `O`: `ordAtInfty (α*x) < 0`.

`R5b` (`orderTop_localExpand_eq_ordAtInfty`) converts the formal-order hypothesis
to the norm-based `0 < ordAtInfty (α*t)`; then `ord_pullback_x_neg_of_localParam_pos`
runs the discrete-valuation argument on the Weierstrass equation. This is the
honest, fully-proved version of brick 5; the unconditional form below is false
without `h_base`. -/
theorem ordAtInfty_pullback_x_gen_neg_of_orderTop_pos_of_base (α : Isogeny W.toAffine W.toAffine)
    (h_base : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) ≤ 0)
    (h_orderTop : (0 : WithTop ℤ) < (localExpand W (α.pullback (localParam W))).orderTop) :
    (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0 :=
  ord_pullback_x_neg_of_localParam_pos W α h_base
    (by rwa [orderTop_localExpand_eq_ordAtInfty W] at h_orderTop)

/-! ### z-order of a summand that reduces to `O` (Silverman IV.1.4 input brick)

The IV.1.4 formal-group argument for the pair `(α₁, α₂)` needs, for each
summand, the positivity `0 < orderTop (localExpand (αᵢ.pullback (localParam W)))`,
i.e. that the local parameter `z_i = αᵢ.pullback (localParam W) = −αᵢ(x)/αᵢ(y)`
*reduces to `O`* (positive order). This is the genuine `x`-pole ⟹ `z`-reduces
direction, specialised to the summand image `(αᵢ(x), αᵢ(y))` on the curve.

These bricks are axiom-clean: they compose `pullback_equation_inl` (the summand
image is on the curve), `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg` (the
generic `x`-pole ⟹ `z`-reduces brick), the chain rule
`αᵢ.pullback (localParam W) = −αᵢ(x)/αᵢ(y)`, and R5b
(`orderTop_localExpand_eq_ordAtInfty`). -/

/-- **`x`-pole ⟹ `z`-reduces, summand form (`ordAtInfty`)**: if the `x`-pullback
of `α` has a pole at `O` (`ord_∞(α.pullback x_gen) < 0`), then the local-parameter
pullback `α.pullback (localParam W) = −α(x)/α(y)` reduces to `O`:
`0 < ord_∞(α.pullback (localParam W))`.

Axiom-clean: `pullback_equation_inl` puts `(α(x), α(y))` on the curve, then the
generic brick `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg` applies. -/
theorem ordAtInfty_pullback_localParam_pos_of_ord_x_neg (α : Isogeny W.toAffine W.toAffine)
    (h_x_neg : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    0 < (W_smooth W).ordAtInfty (α.pullback (localParam W)) := by
  have hX_ne : α.pullback (x_gen W) ≠ 0 := fun h ↦
    x_gen_ne_zero W (α.pullback_injective (h.trans (map_zero _).symm))
  have hY_ne : α.pullback (y_gen W) ≠ 0 := fun h ↦
    y_gen_ne_zero W (α.pullback_injective (h.trans (map_zero _).symm))
  have h_eq : α.pullback (localParam W) =
      -(α.pullback (x_gen W)) / (α.pullback (y_gen W)) := by
    unfold localParam
    rw [map_div₀, map_neg]
  rw [h_eq]
  exact ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg W hX_ne hY_ne
    (pullback_equation_inl W α) h_x_neg

/-- **`x`-pole ⟹ `z`-reduces, summand form (`orderTop ∘ localExpand`)**: the formal
`t`-adic statement. If `ord_∞(α.pullback x_gen) < 0`, then the local expansion of
`α.pullback (localParam W)` has positive `orderTop`:
`0 < orderTop (localExpand (α.pullback (localParam W)))`.

Equivalently `0 < (formalIsogenySeries W α).order`. This is the exact
`hf`/`hg` input for the formal-group subgroup brick `order_formalGroupLaw_subst_pos`
(sub-piece (a)). Axiom-clean: `ordAtInfty_pullback_localParam_pos_of_ord_x_neg`
+ R5b (`orderTop_localExpand_eq_ordAtInfty`). -/
theorem orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg
    (α : Isogeny W.toAffine W.toAffine)
    (h_x_neg : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    0 < (localExpand W (α.pullback (localParam W))).orderTop := by
  rw [orderTop_localExpand_eq_ordAtInfty W]
  exact ordAtInfty_pullback_localParam_pos_of_ord_x_neg W α h_x_neg

/-- **Positive `PowerSeries.order` of the formal isogeny series for a summand that
reduces to `O`**: if `ord_∞(α.pullback x_gen) < 0`, then
`0 < (formalIsogenySeries W α).order`. This is the `order`-form of the previous
brick, in the exact shape consumed by `order_formalGroupLaw_subst_pos`. -/
theorem order_formalIsogenySeries_pos_of_ord_x_neg (α : Isogeny W.toAffine W.toAffine)
    (h_x_neg : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    0 < (formalIsogenySeries W α).order :=
  order_formalIsogenySeries_pos_of_orderTop_pos W α
    (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_x_neg)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`PowerSeries.order > 0` ⟹ `orderTop` of the `LaurentSeries` image is `> 0`.**
A power series `P` with positive `PowerSeries.order` (vanishing constant term)
lifts to a `LaurentSeries` with positive `orderTop`: all coefficients at integer
indices `< 1` vanish (negative indices are outside the image of `ℕ`; the `0`
coefficient is the constant term, which is `0`). This is the order-direction
bridge needed to transport the formal-group subgroup conclusion (stated on
`PowerSeries.order`, sub-piece (a)) back to the `LaurentSeries.orderTop` world
in which `localExpand` and R5b live. -/
theorem orderTop_ofPowerSeries_pos_of_order_pos {P : PowerSeries F} (hP : 0 < P.order) :
    (0 : WithTop ℤ) < (HahnSeries.ofPowerSeries ℤ F P).orderTop := by
  have hcc : PowerSeries.constantCoeff P = 0 :=
    PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp (pos_iff_ne_zero.mp hP)
  have h1 : ((1 : ℤ) : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ F P).orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    have hj0 : j ≤ 0 := by
      have : j < 1 := by exact_mod_cast hj
      omega
    rcases lt_or_eq_of_le hj0 with hjneg | hjeq
    · have hnr : j ∉ Set.range ((↑) : ℕ → ℤ) := by rintro ⟨n, rfl⟩; omega
      rw [HahnSeries.ofPowerSeries_apply]
      exact HahnSeries.embDomain_notin_range hnr
    · subst hjeq
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hcc
  exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1)) h1

/-! ### IV.1.4 pair-level order output (witness-parametric)

The genuine Silverman IV.1.4 content for a pair `(α₁, α₂)` reducing to `O` is the
*identity* (the chord-tangent addition formula in the `z = −x/y` coordinate,
local-expanded, equals the explicit formal group law):

```
localExpand (z_sum) = ofPowerSeries (subst ![f₁, f₂] (formalGroupLaw W))
```

where `z_sum` is the addition-formula sum's `z`-coordinate and
`fᵢ = formalIsogenySeries W αᵢ`. The brick below is the *consumer* of that
identity: given the identity (`h_iv14`) and the two summand reductions
(`ord αᵢ(x) < 0`, supplying `0 < order fᵢ` via
`order_formalIsogenySeries_pos_of_ord_x_neg`), it produces the order output
`0 < orderTop (localExpand z_sum)` by composing sub-piece (a)
(`order_formalGroupLaw_subst_pos`) with the `ofPowerSeries` order bridge.

This isolates the **single** irreducible residual to `h_iv14` (the chord-addition
match): everything else — the summand reductions, the subgroup property, the
order transport — is axiom-clean here. -/

/-- **IV.1.4 order output from the formal-group identity (witness-parametric,
axiom-clean).** Given the IV.1.4 identity `h_iv14`
(`localExpand z_sum = ofPowerSeries (F̂(f₁, f₂))`) and the two summand reductions
(`ord αᵢ(x) < 0`), the local-expanded sum `z_sum` has positive `orderTop`:
`0 < orderTop (localExpand z_sum)`.

Composes the shipped sub-pieces: (a) `order_formalGroupLaw_subst_pos` (the formal
group law preserves positive order), the Phase-1 summand bricks
`order_formalIsogenySeries_pos_of_ord_x_neg`, and the order bridge
`orderTop_ofPowerSeries_pos_of_order_pos`. The hypothesis `h_iv14` is the sole
remaining IV.1.4 content (the chord-addition coefficient match). -/
theorem orderTop_localExpand_z_sum_pos_of_iv14_identity
    (α₁ α₂ : Isogeny W.toAffine W.toAffine) (z_sum : KE)
    (h_α₁ : (W_smooth W).ordAtInfty (α₁.pullback (x_gen W)) < 0)
    (h_α₂ : (W_smooth W).ordAtInfty (α₂.pullback (x_gen W)) < 0)
    (h_iv14 : localExpand W z_sum =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α₁, formalIsogenySeries W α₂] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries)) :
    0 < (localExpand W z_sum).orderTop := by
  rw [h_iv14]
  exact orderTop_ofPowerSeries_pos_of_order_pos
    (order_formalGroupLaw_subst_pos W _ _
      (order_formalIsogenySeries_pos_of_ord_x_neg W α₁ h_α₁)
      (order_formalIsogenySeries_pos_of_ord_x_neg W α₂ h_α₂))

end HasseWeil
