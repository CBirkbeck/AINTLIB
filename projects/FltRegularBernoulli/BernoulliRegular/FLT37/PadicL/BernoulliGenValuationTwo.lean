import BernoulliRegular.FLT37.PadicL.IwasawaModSqCorrected
import BernoulliRegular.FLT37.Eichler.HerbrandBoundAnalytic

/-!
# Discharge of `bernoulliGenOmegaValuationTwo37` — the mod-`37³` Teichmüller core

This file **discharges** the sound second-digit residual
`bernoulliGenOmegaValuationTwo37` of `IwasawaModSqCorrected.lean`,

  `v₃₇(37 · B_{1,ω³¹}) = 2`,

equivalently the sharp `v₃₇(B_{1,ω³¹}) = 1`, hence — through the proved reduction
chain `valuation_bernoulliGenOmega_thirtytwo_of_valTwo` →
`IwasawaModSqCorrected37.valuation_Lp_thirtytwo` — the Washington Cor 8.23 value
`v₃₇(L_p(1, ω³²)) = 1` (the `M ≤ 1` boundary value of FLT37 Case-II II2).

## The mathematics (the mod-`37³` Teichmüller decomposition, VERIFIED)

The exact Stickelberger identity (T006) is the equality

  `37 · B_{1,ω³¹}  =  ∑_a ω(a)³¹ · a`   (`thirtyseven_mul_bernoulliGenOmega_thirtytwo_eq`,
  `thirtyseven_mul_bernoulliGen_eq_intSum`),

so the entire generalized-Bernoulli layer is peeled off and the residual is the
`37`-adic valuation of the **integral Teichmüller sum** `S = ∑_a ω(a)³¹·a ∈ ℤ_[37]`.

The mod-`37³` content is the **higher Teichmüller congruence**

  `ω(a) ≡ (a.val)^{37²} = (a.val)^{1369}   (mod 37³)`

(`teichmuller_sModEq_pow_val_pow_two`, the two-step Frobenius lift of
`ω(a) ≡ a (mod 37)`; the standard limit characterisation `ω(a) = lim_k a^{p^k}`).
Raising to the `31`-st power and multiplying by `a.val`
(`teichmullerChar_pow_mul_val_sModEq`) gives the per-term congruence

  `ω(a)³¹·a  ≡  (a.val)^{31·37²+1}  =  (a.val)^{42440}   (mod 37³)`,

hence summing (`intSum_sModEq_const`)

  `S  ≡  ∑_{a} (a.val)^{42440}  ≡  31487  =  37²·23   (mod 37³)`

(`sum_val_pow_sModEq_const`, a finite kernel computation of the `36` modular
`42440`-th powers; `sum_range_pow_mod_eq`).  Since `37 ∤ 23`, the constant `31487`
has `37`-adic valuation **exactly 2**, and the remainder lies in `37³·ℤ_[37]`
(valuation `≥ 3`); by ultrametric exactness `‖37·B_{1,ω³¹}‖ = ‖31487‖ = 37⁻²`
(`norm_thirtyseven_mul_bernoulliGen_sub_const_le` + `norm_const_eq`), which is the
target valuation `2`.

### Verified soundness of the mod-`37³` reduction

The naive `c + 31·d` reorganisation `37·B ≡ ∑a³² + 37·31·∑a³²·q(a) + 37²·E (mod 37³)`
of the task brief does **not** simplify the problem: `c = 32`, `d = 21` (first
digits of `∑a³²/37²`, `∑a³²q(a)/37`), and the genuine second-order Teichmüller term
`E ≡ 6 (mod 37)` does **not** vanish (`c + 31·d + E ≡ 32 + 31·21 + 6 ≡ 23 ≠ 0`); the
combination `c + 31d + E` is *literally* the second `37`-adic digit `23` of `37·B`.
The clean closed form is instead the single power-sum congruence above: the standard
Teichmüller iteration `ω(a) ≡ a^{37²} (mod 37³)` collapses the whole twist to the
explicit constant `37²·23`.  (A direct numerical check confirms `37·B ≡ 31487`,
`∑a^{42440} ≡ 31487`, and `37·B − ∑a^{1148}` has valuation `3` — i.e. the summed
first-order Fermat-quotient correction cancels, so even `37·B ≡ ∑a^{1148} (mod 37³)`;
the iteration form `a^{1369·31+1}=a^{42440}` is the cleanest provable handle, and is
the one already mechanised in `HerbrandBoundAnalytic.lean`.)

### Independence from Kellner (verified)

`B_{1184} = B_{32·37}` (the Kellner datum, governing the `s`-direction Iwasawa
second-order structure) does **not** appear: the constant `31487` is a finite power
sum of `37`-adic Teichmüller representatives, computed by kernel evaluation, with no
`B_{1184}` input.  This is the **`s = 0` first-order value** `v₃₇(L_p(1, ω³²)) = 1`,
a datum separate from Kellner.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Thm 5.12,
  Cor 5.13, Thm 5.18, Prop 8.12, Cor 8.23.
* Kellner, Math. Comp. 76 (2007), Prop 2.7 (the `s`-direction Iwasawa datum — NOT
  used here).
-/

namespace BernoulliRegular.FLT37.PadicL

open BernoulliRegular

/-- Local prime instance for `37`. -/
private instance instFact37BGVT : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- **`‖37 · B_{1,ω³¹}‖ = 37⁻²`** in `ℚ_[37]`, the norm form of the target valuation,
assembled from the two exposed Teichmüller-modular facts of `HerbrandBoundAnalytic`:

* `norm_thirtyseven_mul_bernoulliGen_sub_const_le`: `‖37·B − 31487‖ ≤ 37⁻³`
  (the mod-`37³` Teichmüller congruence `37·B ≡ 31487`);
* `norm_const_eq`: `‖31487‖ = 37⁻²` (since `31487 = 37²·23`, `37 ∤ 23`).

By ultrametric exactness (`Padic.norm_eq_of_norm_sub_lt_right`, `37⁻³ < 37⁻²`),
`‖37·B‖ = ‖31487‖ = 37⁻²`.  This is `hnorm_37B` from the body of
`flt37SharpHMinusValuation_proved`, re-exposed as a named theorem. -/
theorem norm_thirtyseven_mul_bernoulliGenOmega_thirtytwo :
    ‖(37 : ℚ_[37]) * bernoulliGenOmega 37 32‖ = (37 : ℝ) ^ (-2 : ℤ) := by
  rw [bernoulliGenOmega_def, show (32 - 1 : ℕ) = 31 from rfl]
  have hlt :
      ‖(37 : ℚ_[37]) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1 - (31487 : ℚ_[37])‖ <
        ‖(31487 : ℚ_[37])‖ := by
    rw [BernoulliRegular.FLT37.Eichler.norm_const_eq]
    refine lt_of_le_of_lt
      BernoulliRegular.FLT37.Eichler.norm_thirtyseven_mul_bernoulliGen_sub_const_le ?_
    apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 37)
    norm_num
  rw [Padic.norm_eq_of_norm_sub_lt_right hlt, BernoulliRegular.FLT37.Eichler.norm_const_eq]

/-- **`bernoulliGenOmegaValuationTwo37` is DISCHARGED.**

`v₃₇(37 · B_{1,ω³¹}) = 2` — the sound second-digit residual of
`IwasawaModSqCorrected.lean` — proved unconditionally from the higher Teichmüller
congruence `ω(a) ≡ a^{37²} (mod 37³)` and the finite power-sum identity
`∑_a (a.val)^{42440} ≡ 31487 = 37²·23 (mod 37³)` (`HerbrandBoundAnalytic.lean`).

From the norm equality `‖37·B‖ = 37⁻²` and `37·B ≠ 0`, `Padic.norm_eq_zpow_neg_valuation`
gives `(37:ℝ)^(-v) = (37:ℝ)^(-2)`, so `v = 2` by injectivity of `zpow` at base `37 > 1`.
**No Kellner / `B_{1184}` input.** -/
theorem bernoulliGenOmegaValuationTwo37_proved : bernoulliGenOmegaValuationTwo37 := by
  unfold bernoulliGenOmegaValuationTwo37
  -- `37·B ≠ 0`: its norm is `37⁻² ≠ 0`.
  have hnorm := norm_thirtyseven_mul_bernoulliGenOmega_thirtytwo
  have hne : (37 : ℚ_[37]) * bernoulliGenOmega 37 32 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    have : (0 : ℝ) < (37 : ℝ) ^ (-2 : ℤ) := by positivity
    rw [← hnorm] at this; exact lt_irrefl 0 this
  -- `(37:ℝ)^(-v) = ‖37·B‖ = (37:ℝ)^(-2)` ⟹ `v = 2`.
  have hval := Padic.norm_eq_zpow_neg_valuation hne
  rw [hnorm] at hval
  -- `hval : (37:ℝ)^(-2) = (37:ℝ)^(-v)`; normalise the cast `((37:ℕ):ℝ) = (37:ℝ)` then inject.
  have hcast : ((37 : ℕ) : ℝ) = (37 : ℝ) := by norm_num
  rw [hcast] at hval
  have heq : (-(2 : ℤ)) = -(Padic.valuation ((37 : ℚ_[37]) * bernoulliGenOmega 37 32)) :=
    (zpow_right_inj₀ (by norm_num : (0 : ℝ) < 37) (by norm_num : (37 : ℝ) ≠ 1)).mp hval
  omega

/-- **`v₃₇(B_{1,ω³¹}) = 1`** (the sharp `M = 1` valuation of the algebraic generalized
Bernoulli number), now **unconditional**: discharge `bernoulliGenOmegaValuationTwo37`
and feed it to the proved reduction `valuation_bernoulliGenOmega_thirtytwo_of_valTwo`. -/
theorem valuation_bernoulliGenOmega_thirtytwo :
    (bernoulliGenOmega 37 32).valuation = 1 :=
  valuation_bernoulliGenOmega_thirtytwo_of_valTwo bernoulliGenOmegaValuationTwo37_proved

/-- **`v₃₇(B_{1,ω³¹}) = v₃₇(B₃₂/32)`** (`= 1`), unconditional: the corrected Iwasawa
bridge at the algebraic value, with the second-digit residual discharged. -/
theorem valuation_bernoulliGenOmega_eq_bernoulliFactor_thirtytwo' :
    (bernoulliGenOmega 37 32).valuation = (bernoulliFactorQp 37 32).valuation :=
  valuation_bernoulliGenOmega_eq_bernoulliFactor_thirtytwo bernoulliGenOmegaValuationTwo37_proved

/-- **`v₃₇(L_p(1, ω³²)) = 1`** from any corrected Iwasawa bundle — now with the analytic
field discharged: the bundle's `valTwo_thirtytwo : bernoulliGenOmegaValuationTwo37` field
is supplied unconditionally, so the sharp `L`-value valuation follows from the
**proved** `bernoulliGenOmegaValuationTwo37_proved` together with the Euler-unit
identity carried by the bundle. -/
theorem valuation_Lp_thirtytwo_of_corrected
    (D : IwasawaModSqCorrected37) : (D.Lp 32).valuation = 1 :=
  D.valuation_Lp_thirtytwo

/-- **The corrected Iwasawa bundle from any `L_p` family with the Euler-unit identity.**

Given an `L_p` family that is nonzero on the FLT range and satisfies Washington's
Euler-unit identity `v₃₇(L_p(1, ω^i)) = v₃₇(B_{1,ω^{i-1}})`, this packages it into an
`IwasawaModSqCorrected37` with the analytic `valTwo_thirtytwo` field supplied by the
**proved** `bernoulliGenOmegaValuationTwo37_proved`.  The previously-residual
second-digit field is no longer an input. -/
def IwasawaModSqCorrected37.ofEulerUnit
    (Lp : ℕ → ℚ_[37])
    (Lp_ne_zero : ∀ i, 2 ≤ i → i ≤ 37 - 3 → Even i → Lp i ≠ 0)
    (valuation_Lp_eq_bernoulliGenOmega :
      ∀ i, 2 ≤ i → i ≤ 37 - 3 → Even i →
        (Lp i).valuation = (bernoulliGenOmega 37 i).valuation) :
    IwasawaModSqCorrected37 where
  Lp := Lp
  Lp_ne_zero := Lp_ne_zero
  valuation_Lp_eq_bernoulliGenOmega := valuation_Lp_eq_bernoulliGenOmega
  valTwo_thirtytwo := bernoulliGenOmegaValuationTwo37_proved

end BernoulliRegular.FLT37.PadicL
