import PadicLFunctions.Measure.Convolution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The measure-theoretic toolbox

RJW (arXiv:2309.15692) §3.5 (`sec:toolbox`): the standard operations on measures on
`ℤ_p` and their effect on Mahler transforms. Everything here stays over `ℤ_p`
coefficients; the two formulas requiring `p`-power roots of unity
(`EqRestrictionFormula`, `Eqphipsi`) are deferred to the §5 pass (see plan.md).

## Contents (with source labels)

* multiplication by a continuous function; by `x` — `∂ = (1+T)d/dT` (Lem. 3.24,
  `LemmaMultiplicationbyx`); evaluation `∫ xᵏ dμ = (∂ᵏ𝓐_μ)(0)` (Cor. 3.25,
  `cor:eval at x^k`).
* restriction to clopen subsets (§3.5.3).
* the `ℤ_p^×`-action `σ_a`, the operators `φ`, `ψ` (§3.5.5, `SubSectionphipsi`):
  `ψ ∘ φ = id`, `φ ∘ ψ = Res_{pℤ_p}`, `Res_{ℤ_p^×} = 1 − φψ` (Eq. `res to Zp`), and
  `μ` supported on `ℤ_p^×` ⟺ `ψ(μ) = 0` (Cor. 3.32, `CorollarySupportedZpet`).
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

section cmul

/-- Multiplication of a measure by a continuous function: `(g·μ)(f) = μ(gf)`.

Source: RJW §3.5.2 (TeX lines 1086–1089). -/
def cmul (g : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) : PadicMeasure p ℤ_[p] :=
  μ.comp (LinearMap.mulLeft ℤ_[p] g)

@[simp]
lemma cmul_apply (g f : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) :
    cmul p g μ f = μ (g * f) := rfl

/-- The operator `∂ = (1+T) d/dT` on power series. Source: RJW Lem. 3.24. -/
noncomputable def del (F : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  (1 + PowerSeries.X) * F.derivativeFun

/-- The binomial recurrence `x·binom(x,n) = (n+1)·binom(x,n+1) + n·binom(x,n)` over
`ℤ_p` (RJW TeX line 1074). -/
lemma mul_choose_eq (x : ℤ_[p]) (n : ℕ) :
    x * Ring.choose x n
      = (n + 1 : ℤ_[p]) * Ring.choose x (n + 1) + (n : ℤ_[p]) * Ring.choose x n := by
  have hnat : ∀ m : ℕ,
      (m : ℕ) * m.choose n = (n + 1) * m.choose (n + 1) + n * m.choose n := by
    intro m
    rcases Nat.lt_or_ge m n with h | h
    · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (h.trans n.lt_succ_self)]
      simp
    · have h2 := Nat.choose_succ_right_eq m n
      zify [h] at h2 ⊢
      nlinarith [h2]
  have hc : ∀ m : ℕ, ((m : ℤ_[p])) * Ring.choose (m : ℤ_[p]) n
      = (n + 1 : ℤ_[p]) * Ring.choose ((m : ℤ_[p])) (n + 1)
        + (n : ℤ_[p]) * Ring.choose ((m : ℤ_[p])) n := by
    intro m
    simp only [Ring.choose_natCast]
    exact_mod_cast hnat m
  exact congrFun
    (PadicInt.denseRange_natCast.equalizer
      (by fun_prop : Continuous fun x : ℤ_[p] => x * Ring.choose x n)
      (by fun_prop :
        Continuous fun x : ℤ_[p] =>
          (n + 1 : ℤ_[p]) * Ring.choose x (n + 1) + (n : ℤ_[p]) * Ring.choose x n)
      (funext hc)) x

private lemma coeff_del (F : PowerSeries ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (del p F)
      = (n + 1 : ℤ_[p]) * PowerSeries.coeff (n + 1) F
        + (n : ℤ_[p]) * PowerSeries.coeff n F := by
  rw [del, one_add_mul, map_add, coeff_derivativeFun]
  rcases n with - | m
  · rw [coeff_zero_X_mul]
    push_cast
    ring
  · rw [coeff_succ_X_mul, coeff_derivativeFun]
    push_cast
    ring

/-- Multiplication by `x` on measures corresponds to `∂` on Mahler transforms:
`𝓐_{xμ} = ∂ 𝓐_μ`.

Source: RJW Lem. 3.24 (`LemmaMultiplicationbyx`, TeX lines 1066–1075). -/
theorem mahlerTransform_cmul_X (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (cmul p (ContinuousMap.id ℤ_[p]) μ) = del p (mahlerTransform p μ) := by
  ext n
  rw [coeff_mahlerTransform]
  have hpt : (ContinuousMap.id ℤ_[p] * mahler n : C(ℤ_[p], ℤ_[p]))
      = (n + 1 : ℤ_[p]) • mahler (n + 1) + (n : ℤ_[p]) • mahler n := by
    ext x
    simpa only [ContinuousMap.mul_apply, ContinuousMap.id_apply, mahler_apply,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul] using mul_choose_eq p x n
  change μ (ContinuousMap.id ℤ_[p] * mahler n) = _
  rw [hpt, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, coeff_del,
    coeff_mahlerTransform, coeff_mahlerTransform]

/-- The monomial `x ↦ x^k` as a continuous map. -/
def powCM (k : ℕ) : C(ℤ_[p], ℤ_[p]) := ⟨fun x => x ^ k, by fun_prop⟩

/-- `∫_{ℤ_p} xᵏ dμ = (∂ᵏ 𝓐_μ)(0)`.

Source: RJW Cor. 3.25 (`cor:eval at x^k`, TeX lines 1079–1082). -/
theorem apply_powCM (μ : PadicMeasure p ℤ_[p]) (k : ℕ) :
    μ (powCM p k) = PowerSeries.constantCoeff ((del p)^[k] (mahlerTransform p μ)) := by
  induction k generalizing μ with
  | zero =>
    have h1 : powCM p 0 = (mahler 0 : C(ℤ_[p], ℤ_[p])) := by
      ext x
      simp [powCM, mahler_apply]
    rw [Function.iterate_zero_apply, h1, ← coeff_mahlerTransform,
      PowerSeries.coeff_zero_eq_constantCoeff]
  | succ m ih =>
    have h1 : powCM p (m + 1) = ContinuousMap.id ℤ_[p] * powCM p m := by
      ext x
      simp [powCM, pow_succ, mul_comm]
    rw [h1, ← cmul_apply, ih (cmul p (ContinuousMap.id ℤ_[p]) μ), mahlerTransform_cmul_X,
      Function.iterate_succ_apply]

end cmul

section res

/-- Restriction of a measure to a clopen subset `U ⊆ ℤ_p`:
`(Res_U μ)(f) = μ(𝟙_U · f)`, viewed as a measure on `ℤ_p`.

Source: RJW §3.5.3 (TeX lines 1100–1103). -/
noncomputable def res {U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) :
    PadicMeasure p ℤ_[p] :=
  cmul p (LocallyConstant.charFn ℤ_[p] hU : C(ℤ_[p], ℤ_[p])) μ

/-- A measure is *supported on* a clopen `U` if `Res_U μ = μ` (RJW TeX line 1108). -/
def IsSupportedOn {U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) : Prop :=
  res p hU μ = μ

/-- Restriction is additive over a disjoint clopen decomposition.

Source: RJW §3.5.4 (TeX line 1129): "we can write X ... as a disjoint union". -/
theorem res_union {U V : Set ℤ_[p]} (hU : IsClopen U) (hV : IsClopen V)
    (hUV : Disjoint U V) (μ : PadicMeasure p ℤ_[p]) :
    res p (hU.union hV) μ = res p hU μ + res p hV μ := by
  have hchar : (LocallyConstant.charFn ℤ_[p] (hU.union hV) : C(ℤ_[p], ℤ_[p]))
      = (LocallyConstant.charFn ℤ_[p] hU : C(ℤ_[p], ℤ_[p]))
        + (LocallyConstant.charFn ℤ_[p] hV : C(ℤ_[p], ℤ_[p])) := by
    ext x
    simp only [LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn,
      ContinuousMap.add_apply]
    exact congrFun (Set.indicator_union_of_disjoint hUV 1) x
  refine LinearMap.ext fun f => ?_
  change μ (_ * f) = μ (_ * f) + μ (_ * f)
  rw [← map_add, ← add_mul, hchar]

end res

section phipsi

/-- Multiplication by a fixed `a : ℤ_[p]` as a continuous self-map of `ℤ_[p]`. -/
def mulCM (a : ℤ_[p]) : C(ℤ_[p], ℤ_[p]) := ⟨fun x => a * x, by fun_prop⟩

/-- The `ℤ_p^×`-action on measures: `∫ f d(σ_a μ) = ∫ f(ax) dμ`.

Source: RJW §3.5.5 (TeX lines 1135–1136). -/
noncomputable def sigma (a : ℤ_[p]ˣ) :
    PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p] :=
  pushforward p (mulCM p (a : ℤ_[p]))

/-- The operator `φ` ("`σ_p`"): `∫ f d(φμ) = ∫ f(px) dμ`.

Source: RJW §3.5.5 (TeX lines 1141–1142). -/
noncomputable def phi : PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p] :=
  pushforward p (mulCM p (p : ℤ_[p]))

private lemma binomialSeries_mul_nat (c : ℤ_[p]) (k : ℕ) :
    binomialSeries ℤ_[p] (c * (k : ℤ_[p])) = binomialSeries ℤ_[p] c ^ k := by
  induction k with
  | zero => simp [binomialSeries_zero]
  | succ m ih =>
    have : c * ((m : ℤ_[p]) + 1) = c * (m : ℤ_[p]) + c := by ring
    rw [Nat.cast_add, Nat.cast_one, this, binomialSeries_add, ih, pow_succ]

/-- General substitution formula: pushing a measure forward along multiplication by
`c ∈ ℤ_p` substitutes `(1+T)^c − 1` into the Mahler transform.

Source: RJW §3.5.5 (TeX line 1138 for `σ_a`; Eq. (3.9) for `φ`). -/
theorem mahlerTransform_pushforward_mulCM (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (pushforward p (mulCM p c) μ)
      = PowerSeries.subst (binomialSeries ℤ_[p] c - 1) (mahlerTransform p μ) := by
  set B' : PowerSeries ℤ_[p] := binomialSeries ℤ_[p] c - 1 with hB'
  have hconst : PowerSeries.constantCoeff B' = 0 := by
    simp [hB', binomialSeries_constantCoeff]
  have hsub : PowerSeries.HasSubst B' := PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  have hvanish : ∀ {n d : ℕ}, n < d → PowerSeries.coeff n (B' ^ d) = 0 := fun {n d} hnd =>
    PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hconst) d) n hnd
  ext n
  rw [coeff_mahlerTransform, PowerSeries.coeff_subst' hsub,
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [hvanish (by lia)]; simp))]
  have key : ∀ k : ℕ, mahler n (c * (k : ℤ_[p]))
      = ∑ d ∈ Finset.range (n + 1),
          PowerSeries.coeff n (B' ^ d) * ((k.choose d : ℕ) : ℤ_[p]) := by
    intro k
    have lhs_eq : mahler n (c * (k : ℤ_[p]))
        = PowerSeries.coeff n (binomialSeries ℤ_[p] c ^ k) := by
      rw [← binomialSeries_mul_nat p c k, binomialSeries_coeff, mahler_apply, smul_eq_mul,
        mul_one]
    have expand : PowerSeries.coeff n (binomialSeries ℤ_[p] c ^ k)
        = ∑ d ∈ Finset.range (k + 1),
            PowerSeries.coeff n (B' ^ d) * ((k.choose d : ℕ) : ℤ_[p]) := by
      have hb : binomialSeries ℤ_[p] c = B' + 1 := by rw [hB', sub_add_cancel]
      rw [hb, add_pow, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [one_pow, mul_one, ← map_natCast (PowerSeries.C (R := ℤ_[p])) (k.choose d),
        PowerSeries.coeff_mul_C]
    rw [lhs_eq, expand]
    rcases le_total k n with hkn | hnk
    · refine Finset.sum_subset (by intro d hd; simp only [Finset.mem_range] at *; lia)
        (fun d hd hnd => ?_)
      simp only [Finset.mem_range, not_lt] at hnd
      simp only [Finset.mem_range] at hd
      rw [Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero, mul_zero]
    · refine (Finset.sum_subset (by intro d hd; simp only [Finset.mem_range] at *; lia)
        (fun d hd hnd => ?_)).symm
      simp only [Finset.mem_range, not_lt] at hnd
      rw [hvanish (by lia), zero_mul]
  have hfun : (mahler n).comp (mulCM p c)
      = ∑ d ∈ Finset.range (n + 1),
          (PowerSeries.coeff n (B' ^ d)) • (mahler d : C(ℤ_[p], ℤ_[p])) := by
    apply ContinuousMap.coe_injective
    refine PadicInt.denseRange_natCast.equalizer (map_continuous _) (map_continuous _)
      (funext fun k => ?_)
    change mahler n (c * (k : ℤ_[p])) = _
    rw [key k]
    simp only [Function.comp_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mahler_natCast_eq]
  change μ ((mahler n).comp (mulCM p c)) = _
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, smul_eq_mul, coeff_mahlerTransform, smul_eq_mul, mul_comm]

/-- `𝓐_{σ_a μ} = 𝓐_μ((1+T)^a − 1)`: the `ℤ_p^×`-action on power series is substitution
into the binomial series.

Source: RJW §3.5.5 (TeX line 1138). -/
theorem mahlerTransform_sigma (a : ℤ_[p]ˣ) (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (sigma p a μ) =
      PowerSeries.subst (binomialSeries ℤ_[p] (a : ℤ_[p]) - 1) (mahlerTransform p μ) :=
  mahlerTransform_pushforward_mulCM p _ μ

/-- `𝓐_{φ(μ)} = 𝓐_μ((1+T)^p − 1)` — Eq. (3.9) (`eq:varphi power series`).

Source: RJW TeX lines 1144–1146. -/
theorem mahlerTransform_phi (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (phi p μ) =
      PowerSeries.subst ((1 + PowerSeries.X) ^ p - 1) (mahlerTransform p μ) := by
  have h := mahlerTransform_pushforward_mulCM p ((p : ℕ) : ℤ_[p]) μ
  rwa [binomialSeries_nat] at h

/-- The canonical digit of `x` mod `p`, lifted back to `ℤ_p`. -/
noncomputable def digit (x : ℤ_[p]) : ℤ_[p] :=
  (((PadicInt.toZModPow 1 x).val : ℕ) : ℤ_[p])

lemma sub_digit_mem_span (x : ℤ_[p]) :
    x - digit p x ∈ (Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, digit, map_natCast,
    ZMod.natCast_rightInverse (PadicInt.toZModPow 1 x), sub_self]

private lemma shiftDiv_mem (x : ℤ_[p]) :
    ‖((x : ℚ_[p]) - (digit p x : ℚ_[p])) / (p : ℚ_[p])‖ ≤ 1 := by
  have hle : ‖x - digit p x‖ ≤ (p : ℝ) ^ (-1 : ℤ) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 (sub_digit_mem_span p x)
  have hcast : (x : ℚ_[p]) - (digit p x : ℚ_[p]) = ((x - digit p x : ℤ_[p]) : ℚ_[p]) := by
    push_cast
    ring
  have hppos : (0 : ℝ) < ‖(p : ℚ_[p])‖ := by
    rw [Padic.norm_p]
    exact inv_pos.2 (by exact_mod_cast hp.out.pos)
  rw [hcast, norm_div, ← PadicInt.norm_def, div_le_one hppos, Padic.norm_p]
  simpa [zpow_neg, zpow_one] using hle

/-- The canonical "digit shift" `x ↦ (x − [x mod p])/p` as a continuous map, where
`[x mod p]` is the canonical lift of `x mod p`. Satisfies `shiftDiv (p*x) = x`.
Auxiliary for the `ψ` operator. -/
noncomputable def shiftDiv : C(ℤ_[p], ℤ_[p]) where
  toFun x := ⟨((x : ℚ_[p]) - (digit p x : ℚ_[p])) / (p : ℚ_[p]), shiftDiv_mem p x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.sub
      (continuous_subtype_val.comp
        (isLocallyConstant_toZModPow_val p 1).continuous)).div_const _

@[simp]
lemma shiftDiv_mul (x : ℤ_[p]) : shiftDiv p ((p : ℤ_[p]) * x) = x := by
  have hdig : digit p ((p : ℤ_[p]) * x) = 0 := by
    have hpz : PadicInt.toZModPow 1 (((p : ℕ) : ℤ_[p])) = 0 := by
      rw [map_natCast, show ((p : ℕ) : ZMod (p ^ 1)) = ((p ^ 1 : ℕ) : ZMod (p ^ 1)) by norm_num,
        ZMod.natCast_self]
    have hp0 : PadicInt.toZModPow 1 ((p : ℤ_[p]) * x) = 0 := by
      rw [map_mul, hpz, zero_mul]
    rw [digit, hp0, ZMod.val_zero, Nat.cast_zero]
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  refine Subtype.ext ?_
  change ((((p : ℤ_[p]) * x : ℤ_[p]) : ℚ_[p]) - (digit p ((p : ℤ_[p]) * x) : ℚ_[p]))
      / (p : ℚ_[p]) = (x : ℚ_[p])
  rw [hdig]
  push_cast
  rw [sub_zero, mul_comm, mul_div_assoc, div_self hp0, mul_one]

/-- `pℤ_p ⊆ ℤ_p` is clopen (it is the closed ball of radius `1/p`). -/
lemma isClopen_pZp : IsClopen {x : ℤ_[p] | ‖x‖ < 1} := by
  have heq : {x : ℤ_[p] | ‖x‖ < 1} = Metric.closedBall 0 ((p : ℝ) ^ (-1 : ℤ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
    norm_num
  refine ⟨?_, isOpen_lt continuous_norm continuous_const⟩
  rw [heq]
  exact Metric.isClosed_closedBall

/-- The operator `ψ`: `∫ f d(ψμ) = ∫_{pℤ_p} f(p⁻¹x) dμ`.

Source: RJW §3.5.5 (TeX lines 1147–1148). -/
noncomputable def psi (μ : PadicMeasure p ℤ_[p]) : PadicMeasure p ℤ_[p] where
  toFun f :=
    μ ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
      f.comp (shiftDiv p))
  map_add' f g := by
    rw [ContinuousMap.add_comp, mul_add, map_add]
  map_smul' c f := by
    rw [ContinuousMap.smul_comp, mul_smul_comm, map_smul, RingHom.id_apply]

lemma mem_pZp_of_mul {x : ℤ_[p]} : ‖(p : ℤ_[p]) * x‖ < 1 :=
  lt_of_le_of_lt (by
      calc ‖(p : ℤ_[p]) * x‖ = ‖(p : ℤ_[p])‖ * ‖x‖ := norm_mul _ _
        _ ≤ ‖(p : ℤ_[p])‖ * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one x) (norm_nonneg _)
        _ = ‖(p : ℤ_[p])‖ := mul_one _)
    (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))

/-- On `pℤ_p`, multiplying the digit shift back by `p` recovers the point. -/
lemma mul_shiftDiv_of_mem {x : ℤ_[p]} (hx : ‖x‖ < 1) :
    (p : ℤ_[p]) * shiftDiv p x = x := by
  have hker : PadicInt.toZModPow 1 x = 0 := by
    have hle : ‖x‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
      rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
      simpa using hx
    have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow x 1).1 hle
    rwa [← PadicInt.ker_toZModPow, RingHom.mem_ker] at hmem
  have hdig : digit p x = 0 := by
    rw [digit, hker, ZMod.val_zero, Nat.cast_zero]
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  refine Subtype.ext ?_
  change (p : ℚ_[p]) * (((x : ℚ_[p]) - (digit p x : ℚ_[p])) / (p : ℚ_[p])) = (x : ℚ_[p])
  rw [hdig]
  push_cast
  rw [sub_zero, mul_comm, div_mul_cancel₀ _ hp0]

/-- `ψ ∘ φ = id`. Source: RJW TeX lines 1149–1150, first display. -/
@[simp]
theorem psi_phi (μ : PadicMeasure p ℤ_[p]) : psi p (phi p μ) = μ := by
  refine LinearMap.ext fun f => ?_
  change μ ((((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
      f.comp (shiftDiv p))).comp (mulCM p (p : ℤ_[p]))) = μ f
  congr 1
  ext x
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply, mulCM,
    ContinuousMap.coe_mk, LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn,
    shiftDiv_mul]
  have hmem : ((p : ℤ_[p]) * x) ∈ {y : ℤ_[p] | ‖y‖ < 1} := mem_pZp_of_mul p
  rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]

/-- `φ ∘ ψ = Res_{pℤ_p}`. Source: RJW TeX lines 1149–1151, second display. -/
theorem phi_psi (μ : PadicMeasure p ℤ_[p]) :
    phi p (psi p μ) = res p (isClopen_pZp p) μ := by
  refine LinearMap.ext fun f => ?_
  change μ ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
      (f.comp (mulCM p (p : ℤ_[p]))).comp (shiftDiv p))
    = μ ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) * f)
  congr 1
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply,
    LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn, mulCM,
    ContinuousMap.coe_mk]
  by_cases hx : ‖x‖ < 1
  · rw [mul_shiftDiv_of_mem p hx]
  · rw [Set.indicator_of_notMem (by simpa using hx) 1, zero_mul, zero_mul]

/-- `ℤ_p^× ⊆ ℤ_p` (the units, i.e. `‖x‖ = 1`) is clopen. -/
lemma isClopen_units : IsClopen {x : ℤ_[p] | IsUnit x} := by
  have heq : {x : ℤ_[p] | IsUnit x} = {x : ℤ_[p] | ‖x‖ < 1}ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, PadicInt.isUnit_iff, not_lt]
    exact ⟨fun h => h.ge, fun h => le_antisymm (PadicInt.norm_le_one x) h⟩
  rw [heq]
  exact (isClopen_pZp p).compl

/-- `Res_{ℤ_p^×} = 1 − φ∘ψ` — Eq. (3.10) (`res to Zp`).

Source: RJW TeX lines 1152–1154. -/
lemma setOf_isUnit_eq : {x : ℤ_[p] | IsUnit x} = {x : ℤ_[p] | ‖x‖ < 1}ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, PadicInt.isUnit_iff, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (PadicInt.norm_le_one x) h⟩

theorem res_units_eq (μ : PadicMeasure p ℤ_[p]) :
    res p (isClopen_units p) μ = μ - phi p (psi p μ) := by
  rw [phi_psi]
  refine LinearMap.ext fun f => ?_
  change μ (_ * f) = μ f - μ (_ * f)
  rw [eq_sub_iff_add_eq, ← map_add]
  congr 1
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply,
    LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
  rw [← add_mul]
  by_cases hx : ‖x‖ < 1
  · have hnu : x ∉ {y : ℤ_[p] | IsUnit y} := fun hu =>
      absurd (PadicInt.isUnit_iff.1 hu) hx.ne
    have hmem : x ∈ {y : ℤ_[p] | ‖y‖ < 1} := hx
    rw [Set.indicator_of_notMem hnu, Set.indicator_of_mem hmem, Pi.one_apply, zero_add,
      one_mul]
  · have hu : x ∈ {y : ℤ_[p] | IsUnit y} :=
      PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one x) (not_lt.1 hx))
    have hnm : x ∉ {y : ℤ_[p] | ‖y‖ < 1} := hx
    rw [Set.indicator_of_mem hu, Set.indicator_of_notMem hnm, Pi.one_apply, add_zero,
      one_mul]

lemma psi_sub (μ ν : PadicMeasure p ℤ_[p]) :
    psi p (μ - ν) = psi p μ - psi p ν :=
  LinearMap.ext fun _f => LinearMap.sub_apply μ ν _

/-- **RJW Cor. 3.32 (`CorollarySupportedZpet`)**: a measure is supported on `ℤ_p^×` if
and only if `ψ(μ) = 0` (TeX lines 1161–1167). -/
theorem isSupportedOn_units_iff_psi_eq_zero (μ : PadicMeasure p ℤ_[p]) :
    IsSupportedOn p (isClopen_units p) μ ↔ psi p μ = 0 := by
  rw [IsSupportedOn]
  constructor
  · intro h
    have hres := congrArg (psi p) h
    rw [res_units_eq, psi_sub, psi_phi, sub_self] at hres
    exact hres.symm
  · intro h
    rw [res_units_eq, h, map_zero, sub_zero]

end phipsi

end PadicMeasure
