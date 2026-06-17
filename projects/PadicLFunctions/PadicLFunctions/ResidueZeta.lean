/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import PadicLFunctions.Interpolation.Branches
import PadicLFunctions.ValuesAtOne

/-!
# The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)

**RJW Theorem 7.1** (`thm:residue`, TeX 2187–2194): for `i ∈ {1,…,p−1}`,
(i) if `i ≠ p−1` then `ζ_{p,i}` is analytic at `s = 1` (here: continuous —
the denominator never vanishes), and (ii) `ζ_{p,p−1}` has a simple pole at
`s = 1` with residue `1 − p⁻¹` (here: the topological limit
`lim_{s→1, s≠1} (s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹`).

Route (decomposition R7; replans recorded there): `zetaPBranch` is
literally RJW's Eqtmp2 quotient, so the work is (a) the denominator
analysis through the T523 exp/log bridge (`g(s) = ⟨a⟩^{1−s} − 1`,
`(s−1)⁻¹g(s) → −log⟨a⟩`), (b) continuity of the numerator pairing via the
`p^m`-congruence Lipschitz bound, and (c) the mass
`∫x⁻¹μ_a = −(1−p⁻¹)·log_p(a)` by the §6 c₀-design applied to the explicit
antiderivative `F̃_a = log(T/(1+T) · (1+T)^a/((1+T)^a−1))` (TeX 2268),
with the `ξ ∈ μ_p`-machinery run in a field `K ⊇ ℚ_p(μ_p)` (ℂ_p) and
descended by injectivity. RJW's Lemma 7.4 (`ℛ⁺`-membership) is not needed
on this route.
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section expTail

variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- Per-term quadratic bound: for `n ≥ 2`, the `n`-th exponential term is
`≤ p·‖w‖²` on the convergence ball (compared at the `(p−1)`-power level). -/
private lemma norm_factorial_inv_smul_pow_le_quad {w : L} (hw : InExpBall p w)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖(n.factorial : ℚ_[p])⁻¹ • w ^ n‖ ≤ (p : ℝ) * ‖w‖ ^ 2 := by
  have hp1 : 0 < p - 1 := by have := hp.out.one_lt; omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hT0 : 0 ≤ (p : ℝ) * ‖w‖ ^ (p - 1) := by positivity
  have hT1 : (p : ℝ) * ‖w‖ ^ (p - 1) < 1 :=
    calc (p : ℝ) * ‖w‖ ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hw hppos
      _ = 1 := mul_inv_cancel₀ hppos.ne'
  -- power-level comparison `‖term‖^{p−1} ≤ (p·‖w‖²)^{p−1}`
  have hpow : ‖(n.factorial : ℚ_[p])⁻¹ • w ^ n‖ ^ (p - 1)
      ≤ ((p : ℝ) * ‖w‖ ^ 2) ^ (p - 1) := by
    calc ‖(n.factorial : ℚ_[p])⁻¹ • w ^ n‖ ^ (p - 1)
        ≤ ‖w‖ ^ (p - 1) * ((p : ℝ) * ‖w‖ ^ (p - 1)) ^ (n - 1) :=
          norm_factorial_inv_smul_pow_le p w (by omega)
      _ = ‖w‖ ^ (p - 1)
            * (((p : ℝ) * ‖w‖ ^ (p - 1)) ^ (n - 2)
              * ((p : ℝ) * ‖w‖ ^ (p - 1))) := by
          rw [← pow_succ, show n - 2 + 1 = n - 1 from by omega]
      _ ≤ ‖w‖ ^ (p - 1) * (1 * ((p : ℝ) * ‖w‖ ^ (p - 1))) := by
          gcongr
          exact pow_le_one₀ hT0 hT1.le
      _ = (p : ℝ) * (‖w‖ ^ (p - 1)) ^ 2 := by ring
      _ ≤ (p : ℝ) ^ (p - 1) * (‖w‖ ^ (p - 1)) ^ 2 := by
          gcongr
          · exact le_self_pow₀ (by exact_mod_cast hp.out.one_le) (by omega)
      _ = ((p : ℝ) * ‖w‖ ^ 2) ^ (p - 1) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (p - 1)]
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow

/-- R7.1a: the quadratic tail of the exponential —
`‖exp w − 1 − w‖ ≤ p·‖w‖²` on the convergence ball (the `n ≥ 2` terms at
the `(p−1)`-power level). -/
theorem norm_padicExp_sub_one_sub_self_le {w : L} (hw : InExpBall p w) :
    ‖padicExp p w - 1 - w‖ ≤ (p : ℝ) * ‖w‖ ^ 2 := by
  have hsd := summable_padicExp_terms p hw
  -- peel the `n = 0` and `n = 1` terms
  have hdiff : padicExp p w - 1 - w
      = ∑' n : ℕ, ((n + 1 + 1 : ℕ).factorial : ℚ_[p])⁻¹ • w ^ (n + 1 + 1) := by
    rw [padicExp, hsd.tsum_eq_zero_add,
      ((summable_nat_add_iff 1).mpr hsd).tsum_eq_zero_add]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
      zero_add, Nat.factorial_one, pow_one]
    ring
  rw [hdiff]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le
    fun n => norm_factorial_inv_smul_pow_le_quad p hw (by omega)

end expTail

section character

/-- R7.1b: the character is a norm isometry in the exponent —
`‖y^t − 1‖ = ‖t‖·‖y−1‖` for `y ∈ 1+pℤ_p` (via the T523 exp/log bridge:
`y^t = exp(t·log y)` and `‖exp w − 1‖ = ‖w‖`, `‖log y‖ = ‖y−1‖`). -/
theorem norm_onePAdicPow_sub_one (hp2 : p ≠ 2) {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) :
    ‖(PadicInt.onePAdicPow p y hy t : ℤ_[p]) - 1‖ = ‖t‖ * ‖y - 1‖ := by
  set ℓ : ℤ_[p] := pZpLog p y with hℓ
  have hℓmem : ℓ ∈ Ideal.span {(p : ℤ_[p])} := pZpLog_mem p hp2 hy
  have htℓmem : t * ℓ ∈ Ideal.span {(p : ℤ_[p])} := Ideal.mul_mem_left _ _ hℓmem
  -- the bridge `y^t = exp(t·log y)`
  rw [← padicExp_smul_padicLog_eq_onePAdicPow p hp2 hy t, ← hℓ,
    PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one,
    pZpExp_coe p hp2 htℓmem,
    norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 htℓmem),
    PadicInt.coe_mul, norm_mul, ← PadicInt.norm_def, ← PadicInt.norm_def]
  -- `‖log y‖ = ‖y − 1‖`
  congr 1
  have hball : InExpBall p ((y : ℚ_[p]) - 1) := by
    rw [show ((y : ℚ_[p]) - 1) = ((y - 1 : ℤ_[p]) : ℚ_[p]) by
      rw [PadicInt.coe_sub, PadicInt.coe_one]]
    exact inExpBall_of_mem_span p hp2 hy
  rw [hℓ, PadicInt.norm_def, pZpLog_coe p hp2 hy, norm_padicLog (L := ℚ_[p]) p hball,
    ← PadicInt.coe_one, ← PadicInt.coe_sub, ← PadicInt.norm_def]

/-- R7.2a: the Teichmüller value of a topological generator is a primitive
`(p−1)`-th root of unity (its reduction generates `(ZMod p)ˣ`). -/
theorem teichmuller_isPrimitiveRoot {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u)
      = ⊤) :
    IsPrimitiveRoot (PadicInt.teichmuller p u) (p - 1) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  -- `ω(u)^{p−1} = 1`, so `orderOf ω(u) ∣ p−1`
  have hpow : (PadicInt.teichmuller p u) ^ (p - 1) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
      PadicInt.teichmullerFun_pow_card_sub_one, Units.val_one])
  have hdvd1 : orderOf (PadicInt.teichmuller p u) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  -- the level-1 reduction `g := unitsToZModPow p 1 u` generates, so `orderOf g = p−1`
  have ho1 : orderOf (PadicMeasure.unitsToZModPow p 1 u) = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers fun x => hgen 1 ▸ Subgroup.mem_top x,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one,
      Nat.totient_prime hp.out]
  -- `ω(u)` reduces to the same residue as `u` mod `p`, so `g = unitsToZModPow p 1 ω(u)`
  have hred : PadicMeasure.unitsToZModPow p 1 (PadicInt.teichmuller p u)
      = PadicMeasure.unitsToZModPow p 1 u := by
    refine Units.ext ?_
    rw [PadicMeasure.unitsToZModPow_coe, PadicMeasure.unitsToZModPow_coe,
      PadicInt.teichmuller_coe, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker,
      PadicInt.ker_toZModPow, pow_one]
    exact PadicInt.teichmullerFun_sub_self_mem p u
  -- hence `(p−1) = orderOf g ∣ orderOf ω(u)`
  have hdvd2 : p - 1 ∣ orderOf (PadicInt.teichmuller p u) := by
    rw [← ho1, ← hred]
    exact orderOf_map_dvd _ _
  exact Nat.dvd_antisymm hdvd1 hdvd2

/-- For `0 < i < p−1` the reduction `ω(u)^i ≢ 1 mod p`, so `‖ω(u)^i − 1‖ = 1`
(the Teichmüller value has exact order `p−1` by `teichmuller_isPrimitiveRoot`). -/
private lemma norm_teichmuller_pow_sub_one_eq_one {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u) = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) :
    ‖(PadicInt.teichmuller p u : ℤ_[p]) ^ i - 1‖ = 1 := by
  -- `(toZMod u)^i ≠ 1` (else `(p−1) ∣ i`, impossible for `0 < i < p−1`)
  have hred : PadicInt.toZMod ((PadicInt.teichmuller p u : ℤ_[p]) ^ i) ≠ 1 := by
    rw [map_pow, PadicInt.teichmuller_coe, PadicInt.teichmullerFun,
      PadicInt.toZMod_teichmullerZMod]
    intro h
    -- lift `(toZMod u)^i = 1` back to the units level through the section ω
    have hu1 : (PadicInt.teichmuller p u) ^ i = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
        PadicInt.teichmullerFun, ← map_pow, h, map_one, Units.val_one])
    have hdvd : p - 1 ∣ i := by
      rw [(teichmuller_isPrimitiveRoot p hgen).eq_orderOf]
      exact orderOf_dvd_of_pow_eq_one hu1
    exact absurd (Nat.le_of_dvd hi0 hdvd) (by omega)
  -- nonzero reduction ⟺ norm one
  have hnotdvd : ¬ ((p : ℤ_[p]) ∣ ((PadicInt.teichmuller p u : ℤ_[p]) ^ i - 1)) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    exact hred
  have hlt : ¬ (‖(PadicInt.teichmuller p u : ℤ_[p]) ^ i - 1‖ < 1) :=
    fun h => hnotdvd ((PadicInt.norm_lt_one_iff_dvd _).mp h)
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp hlt)

/-- R7.2b: for `0 < i < p−1` the branch denominator never vanishes —
`‖ω(u)^i − 1‖ = 1` beats `‖⟨u⟩^{1−s} − 1‖ < 1` (ultrametric isoceles);
this is RJW's Lemma 7.2(i) strengthened from `s = 1` to all `s`. -/
theorem branch_denom_ne_zero {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u)
      = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) (s : ℤ_[p]) :
    (((branchChar p i s u : ℤ_[p])) : ℚ_[p]) - 1 ≠ 0 := by
  set ω : ℤ_[p] := (PadicInt.teichmuller p u : ℤ_[p]) with hω
  set A : ℤ_[p] := PadicInt.onePAdicPow p (PadicInt.angleUnit p u : ℤ_[p])
    (PadicInt.angleUnit_sub_one_mem p u) s with hA
  -- the value `V = ω^i·A`
  have hV : (branchChar p i s u : ℤ_[p]) = ω ^ i * A := by
    rw [branchChar_apply]
  -- `‖ω^i − 1‖ = 1`
  have hωi : ‖ω ^ i - 1‖ = 1 := norm_teichmuller_pow_sub_one_eq_one p hgen hi0 hi
  -- `‖A − 1‖ < 1`
  have hAlt : ‖A - 1‖ < 1 := by
    have hmem : A - 1 ∈ Ideal.span {(p : ℤ_[p])} :=
      PadicInt.onePAdicPow_sub_one_mem p _ _ s
    exact (PadicInt.norm_lt_one_iff_dvd _).mpr (Ideal.mem_span_singleton.mp hmem)
  -- `‖ω^i‖ = 1`
  have hωnorm : ‖ω ^ i‖ = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val]
    exact PadicInt.norm_units _
  -- isoceles: `‖V − 1‖ = max ‖ω^i·A − ω^i‖ ‖ω^i − 1‖ = 1`
  have hlt : ‖ω ^ i * A - ω ^ i‖ < ‖ω ^ i - 1‖ := by
    rw [show ω ^ i * A - ω ^ i = ω ^ i * (A - 1) from by ring, norm_mul, hωnorm,
      one_mul, hωi]
    exact hAlt
  have hkey := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hlt)
  rw [show ω ^ i * A - ω ^ i + (ω ^ i - 1) = ω ^ i * A - 1 from by ring,
    max_eq_right hlt.le, hωi] at hkey
  -- `‖V − 1‖ = 1 ≠ 0`, so `V − 1 ≠ 0` in `ℤ_[p]`, hence the `ℚ_[p]`-coercion
  have hVsub : (branchChar p i s u : ℤ_[p]) - 1 ≠ 0 := by
    rw [hV]
    refine fun h => one_ne_zero (?_ : (1 : ℝ) = 0)
    rw [← hkey, h, norm_zero]
  rw [show (((branchChar p i s u : ℤ_[p])) : ℚ_[p]) - 1
      = (((branchChar p i s u : ℤ_[p]) - 1 : ℤ_[p]) : ℚ_[p]) by
    rw [PadicInt.coe_sub, PadicInt.coe_one]]
  rwa [Ne, PadicInt.coe_eq_zero]

/-- R7.2c (RJW Lemma 7.2(ii), TeX 2224–2226): the denominator has a simple
zero at `s = 1` with derivative `−log_p⟨a⟩`:
`(s−1)⁻¹·(⟨a⟩^{1−s} − 1) → −log_p⟨a⟩` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_branch_denom_div (hp2 : p ≠ 2) {u : ℤ_[p]ˣ} :
    Filter.Tendsto (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1)⁻¹
        * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1))
      (nhdsWithin 1 {s | s ≠ 1})
      (nhds (-((pZpLog p ((PadicInt.angleUnit p u : ℤ_[p]))) : ℚ_[p]))) := by
  set L : ℤ_[p] := pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) with hL
  set Lq : ℚ_[p] := (L : ℚ_[p]) with hLq
  have hLmem : L ∈ Ideal.span {(p : ℤ_[p])} :=
    pZpLog_mem p hp2 (PadicInt.angleUnit_sub_one_mem p u)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  -- the branch value `branchChar p (p−1) (1−s) u = exp((1−s)·L)`, coerced
  have hpow1 : (PadicInt.teichmuller p u : ℤ_[p]) ^ (p - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val,
      show (PadicInt.teichmuller p u) ^ (p - 1) = 1 from
        Units.ext (by rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
          PadicInt.teichmullerFun_pow_card_sub_one, Units.val_one]),
      Units.val_one]
  have hval : ∀ s : ℤ_[p], (((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p])
      = padicExp p ((((1 - s) * L : ℤ_[p])) : ℚ_[p]) := by
    intro s
    have hmem : (1 - s) * L ∈ Ideal.span {(p : ℤ_[p])} :=
      Ideal.mul_mem_left _ _ hLmem
    rw [branchChar_apply, hpow1, one_mul,
      ← padicExp_smul_padicLog_eq_onePAdicPow p hp2
        (PadicInt.angleUnit_sub_one_mem p u) (1 - s),
      pZpExp_coe p hp2 hmem]
  -- the squeezing function `a(s) = p·‖Lq‖²·‖s−1‖ → 0`
  have hcoe : Filter.Tendsto (fun s : ℤ_[p] => ‖(s : ℚ_[p]) - 1‖)
      (nhds (1 : ℤ_[p])) (nhds 0) := by
    have hc : Continuous (fun s : ℤ_[p] => ‖(s : ℚ_[p]) - 1‖) :=
      continuous_norm.comp (continuous_subtype_val.sub continuous_const)
    simpa only [PadicInt.coe_one, sub_self, norm_zero] using hc.tendsto (1 : ℤ_[p])
  have ha : Filter.Tendsto (fun s : ℤ_[p] => (p : ℝ) * ‖Lq‖ ^ 2 * ‖(s : ℚ_[p]) - 1‖)
      (nhdsWithin 1 {s | s ≠ 1}) (nhds 0) := by
    have h0 : Filter.Tendsto (fun s : ℤ_[p] => ‖(s : ℚ_[p]) - 1‖)
        (nhdsWithin (1 : ℤ_[p]) {s | s ≠ 1}) (nhds 0) :=
      hcoe.mono_left nhdsWithin_le_nhds
    simpa using h0.const_mul ((p : ℝ) * ‖Lq‖ ^ 2)
  -- pointwise bound on `{s ≠ 1}`
  have hbound : ∀ᶠ s : ℤ_[p] in nhdsWithin 1 {s | s ≠ 1},
      ‖(((s : ℚ_[p]) - 1)⁻¹
          * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1)) - (-Lq)‖
        ≤ (p : ℝ) * ‖Lq‖ ^ 2 * ‖(s : ℚ_[p]) - 1‖ := by
    refine eventually_nhdsWithin_of_forall fun s hs => ?_
    have hs1 : (s : ℚ_[p]) - 1 ≠ 0 := by
      rw [show ((s : ℚ_[p]) - 1) = ((s - 1 : ℤ_[p]) : ℚ_[p]) by
        rw [PadicInt.coe_sub, PadicInt.coe_one], Ne, PadicInt.coe_eq_zero,
        sub_eq_zero]
      exact hs
    have hsn : ‖(s : ℚ_[p]) - 1‖ ≠ 0 := norm_ne_zero_iff.mpr hs1
    set w : ℚ_[p] := ((((1 - s) * L : ℤ_[p])) : ℚ_[p]) with hw
    have hwval : w = -((s : ℚ_[p]) - 1) * Lq := by
      rw [hw, PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_one, ← hLq]; ring
    have hwnorm : ‖w‖ = ‖(s : ℚ_[p]) - 1‖ * ‖Lq‖ := by
      rw [hwval, norm_mul, norm_neg]
    have hwball : InExpBall p w :=
      inExpBall_of_mem_span p hp2 (Ideal.mul_mem_left _ _ hLmem)
    have hwinv : ((s : ℚ_[p]) - 1)⁻¹ * w = -Lq := by
      rw [hwval]; field_simp
    -- the shifted difference is `(s−1)⁻¹·(exp w − 1 − w)`
    have hid : (((s : ℚ_[p]) - 1)⁻¹
        * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1)) - (-Lq)
        = ((s : ℚ_[p]) - 1)⁻¹ * (padicExp p w - 1 - w) := by
      rw [hval s, ← hw]
      linear_combination hwinv
    rw [hid, norm_mul, norm_inv]
    calc ‖(s : ℚ_[p]) - 1‖⁻¹ * ‖padicExp p w - 1 - w‖
        ≤ ‖(s : ℚ_[p]) - 1‖⁻¹ * ((p : ℝ) * ‖w‖ ^ 2) := by
          gcongr
          exact norm_padicExp_sub_one_sub_self_le p hwball
      _ = (p : ℝ) * ‖Lq‖ ^ 2 * ‖(s : ℚ_[p]) - 1‖ := by
          rw [hwnorm, mul_pow]
          field_simp
  -- squeeze
  have hsq : Filter.Tendsto (fun s : ℤ_[p] => (((s : ℚ_[p]) - 1)⁻¹
        * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1)) - (-Lq))
      (nhdsWithin 1 {s | s ≠ 1}) (nhds 0) :=
    squeeze_zero_norm' hbound ha
  simpa using hsq.add (tendsto_const_nhds (x := -Lq))

/-- Exponent-congruence (the `p = 2`-valid analogue of `norm_onePAdicPow_sub_one`):
if `t ∈ p^k·ℤ_p` then `y^t ≡ 1 mod p^k`. Route: `t = p^k·c`, so
`y^t = (y^c)^{p^k}` and `dvd_sub_pow_of_dvd_sub` lifts `p ∣ y^c − 1` to
`p^{k+1} ∣ (y^c)^{p^k} − 1`. -/
private lemma onePAdicPow_sub_one_mem_span_pow {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (k : ℕ) {t : ℤ_[p]}
    (ht : t ∈ Ideal.span {(p : ℤ_[p]) ^ k}) :
    PadicInt.onePAdicPow p y hy t - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
  -- `t = p^k · c`
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ht
  -- `y^t = (y^c)^{p^k}` via `κ(n • a) = κ(a)^n` (`p^k·c = (p^k : ℕ) • c`)
  have hsmul : (p : ℤ_[p]) ^ k * c = (p ^ k : ℕ) • c := by
    rw [nsmul_eq_mul, Nat.cast_pow]
  have hpow : PadicInt.onePAdicPow p y hy ((p : ℤ_[p]) ^ k * c)
      = (PadicInt.onePAdicPow p y hy c) ^ (p ^ k) := by
    rw [hsmul, AddChar.map_nsmul_eq_pow]
  rw [hpow]
  -- `p ∣ y^c − 1`
  have hdvd1 : (p : ℤ_[p]) ∣ PadicInt.onePAdicPow p y hy c - 1 :=
    Ideal.mem_span_singleton.mp (PadicInt.onePAdicPow_sub_one_mem p y hy c)
  -- `p^{k+1} ∣ (y^c)^{p^k} − 1`, weaken to `p^k`
  have hsharp : ((p : ℤ_[p]) ^ (k + 1)) ∣
      (PadicInt.onePAdicPow p y hy c) ^ p ^ k - (1 : ℤ_[p]) ^ p ^ k :=
    dvd_sub_pow_of_dvd_sub hdvd1 k
  rw [one_pow] at hsharp
  exact Ideal.mem_span_singleton.mpr
    (dvd_trans (pow_dvd_pow _ (Nat.le_succ k)) hsharp)

/-- The `p = 2`-valid weak isometry: `‖y^t − 1‖ ≤ ‖t‖` for `y ∈ 1 + pℤ_p` and
every `t` (the sharp `‖y^t − 1‖ = ‖t‖·‖y − 1‖` of `norm_onePAdicPow_sub_one`
needs `p ≠ 2`; this one-sided bound holds for all `p`). -/
private lemma norm_onePAdicPow_sub_one_le {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) :
    ‖(PadicInt.onePAdicPow p y hy t : ℤ_[p]) - 1‖ ≤ ‖t‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [show PadicInt.onePAdicPow p y hy 0 = 1 from AddChar.map_zero_eq_one _,
      sub_self, norm_zero]
  -- `‖t‖ = p^{-val t}`, so `t ∈ span{p^{val t}}`
  set k : ℕ := t.valuation with hk
  have htmem : t ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_eq_zpow_neg_valuation ht]
  have hmem := onePAdicPow_sub_one_mem_span_pow p hy k htmem
  rw [PadicInt.norm_eq_zpow_neg_valuation ht]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ k).mpr hmem

/-- R7.3a: the numerator pairing is continuous in `s` (the `p^m`-congruence
route: `s ≡ s' mod p^m ⟹ ⟨x⟩^{1−s} ≡ ⟨x⟩^{1−s'} mod p^m` uniformly in
`x`, through `onePAdicPow_sub_one_mem_pow`; then the measure norm bound).
Notably `p = 2` is allowed here. -/
theorem continuous_zetaNum_branch_pairing (m i : ℕ) :
    Continuous (fun s : ℤ_[p] =>
      (((PadicMeasure.zetaNum p m (branchChar p i (1 - s)) : ℤ_[p]))
        : ℚ_[p])) := by
  -- pointwise sup-norm bound `‖branchChar (1−s) x − branchChar (1−s') x‖ ≤ ‖s − s'‖`
  have hptbound : ∀ (s s' : ℤ_[p]) (x : ℤ_[p]ˣ),
      ‖(branchChar p i (1 - s) x : ℤ_[p]) - branchChar p i (1 - s') x‖ ≤ ‖s - s'‖ := by
    intro s s' x
    set ω : ℤ_[p] := (PadicInt.teichmuller p x : ℤ_[p]) with hω
    set κ : AddChar ℤ_[p] ℤ_[p] := PadicInt.onePAdicPow p (PadicInt.angleUnit p x : ℤ_[p])
      (PadicInt.angleUnit_sub_one_mem p x) with hκ
    -- `branchChar (1−s) x = ω^i · κ(1−s)` and `κ(1−s) = κ(1−s')·κ(s'−s)`
    have hadd : κ (1 - s) = κ (1 - s') * κ (s' - s) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    have hdiff : (branchChar p i (1 - s) x : ℤ_[p]) - branchChar p i (1 - s') x
        = ω ^ i * κ (1 - s') * (κ (s' - s) - 1) := by
      rw [branchChar_apply, branchChar_apply, ← hω, ← hκ, hadd]; ring
    rw [hdiff]
    -- norms: `‖ω^i‖ ≤ 1`, `‖κ(1−s')‖ ≤ 1`, `‖κ(s'−s) − 1‖ ≤ ‖s'−s‖ = ‖s − s'‖`
    have hω1 : ‖ω ^ i‖ ≤ 1 := PadicInt.norm_le_one _
    have hκ1 : ‖κ (1 - s')‖ ≤ 1 := PadicInt.norm_le_one _
    have hκd : ‖κ (s' - s) - 1‖ ≤ ‖s' - s‖ :=
      norm_onePAdicPow_sub_one_le p (PadicInt.angleUnit_sub_one_mem p x) (s' - s)
    calc ‖ω ^ i * κ (1 - s') * (κ (s' - s) - 1)‖
        = ‖ω ^ i‖ * ‖κ (1 - s')‖ * ‖κ (s' - s) - 1‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * ‖s' - s‖ := by gcongr
      _ = ‖s - s'‖ := by rw [one_mul, one_mul, norm_sub_rev]
  -- the `ℤ_[p]`-valued pairing is `1`-Lipschitz, hence continuous
  have hLip : LipschitzWith 1 (fun s : ℤ_[p] =>
      (PadicMeasure.zetaNum p m (branchChar p i (1 - s)) : ℤ_[p])) := by
    refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    refine le_trans (PadicMeasure.norm_apply_le p _ _) ?_
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    rw [ContinuousMap.coe_sub, Pi.sub_apply]
    exact hptbound s s' x
  exact continuous_subtype_val.comp hLip.continuous

/-- **RJW Theorem 7.1(i)** (TeX 2189–2190): for `0 < i < p−1` the branch
`ζ_{p,i}` is continuous ("analytic") at `s = 1` — indeed everywhere, but
we state the source's claim. -/
theorem continuousAt_zetaPBranch (hp2 : p ≠ 2) {i : ℕ} (hi0 : 0 < i)
    (hi : i < p - 1) : ContinuousAt (zetaPBranch p hp2 i) 1 := by
  classical
  obtain ⟨-, -, hgen⟩ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec
  set m := (PadicMeasure.exists_nat_topological_generator p hp2).choose
  set u := (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose
  -- the denominator `s ↦ ⟨u⟩^{1−s}·ω^i − 1` is continuous (`onePAdicPow` in the exponent)
  have hden_cont : Continuous (fun s : ℤ_[p] =>
      (((branchChar p i (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1) := by
    refine (continuous_subtype_val.comp ?_).sub continuous_const
    have hfun : (fun s : ℤ_[p] => (branchChar p i (1 - s) u : ℤ_[p]))
        = fun s : ℤ_[p] => (PadicInt.teichmuller p u : ℤ_[p]) ^ i
          * PadicInt.onePAdicPow p (PadicInt.angleUnit p u : ℤ_[p])
              (PadicInt.angleUnit_sub_one_mem p u) (1 - s) := by
      funext s; rw [branchChar_apply]
    rw [hfun]
    exact continuous_const.mul ((PadicInt.continuous_onePAdicPow p _ _).comp
      (continuous_const.sub continuous_id))
  -- the denominator is nonzero at `s = 1`
  have hden_ne : (((branchChar p i (1 - 1) u : ℤ_[p])) : ℚ_[p]) - 1 ≠ 0 :=
    branch_denom_ne_zero p hgen hi0 hi (1 - 1)
  -- assemble: `(denom)⁻¹ · numerator`
  unfold zetaPBranch
  exact (hden_cont.continuousAt.inv₀ hden_ne).mul
    (continuous_zetaNum_branch_pairing p m i).continuousAt

end character

section mass

variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- R7.4a: the unit factor `u_a` of `(1+T)^a − 1 = a·T·u_a`
(`u_a = Σ_n a⁻¹·C(a, n+1)·Tⁿ`, constant term `1`; TeX 2296–2300). -/
noncomputable def uA (a : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => ((a : K))⁻¹ * (a.choose (n + 1))

/-- The `n`-th coefficient of `(1+X)^a` over any commutative ring is `C(a, n)`
(the formal binomial theorem, transported from the polynomial statement). -/
private lemma coeff_one_add_X_pow {R : Type*} [CommRing R] (a n : ℕ) :
    PowerSeries.coeff n ((1 + PowerSeries.X) ^ a : PowerSeries R) = (a.choose n : R) := by
  rw [show (1 + PowerSeries.X : PowerSeries R) ^ a
        = (((1 + Polynomial.X : Polynomial R) ^ a : Polynomial R) : PowerSeries R) by
      push_cast [Polynomial.coe_pow]; rfl,
    Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The constant coefficient of `u_a` is `1` (`C(a,1)·a⁻¹ = 1` for `a ≠ 0`). -/
private lemma constantCoeff_uA {a : ℕ} (ha0 : a ≠ 0) :
    PowerSeries.constantCoeff (uA K a) = 1 := by
  have ha : (a : K) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, uA, PowerSeries.coeff_mk,
    Nat.choose_one_right, inv_mul_cancel₀ ha]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `u_a − 1` has zero constant term, hence is a legal substitution argument. -/
private lemma hasSubst_uA_sub_one {a : ℕ} (ha0 : a ≠ 0) :
    PowerSeries.HasSubst (uA K a - 1 : PowerSeries K) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    rw [map_sub, constantCoeff_uA K ha0, map_one, sub_self])

/-- R7.4b: RJW's antiderivative `F̃_a = log(T/(1+T) · (1+T)^a/((1+T)^a−1))`
(TeX 2268), realised through the factorisation
`F̃_a = −log_p(a) − log(u_a) + (a−1)·log(1+T)` (TeX eq:tilde F_a 2 +
eq:F_a tilde): the formal compositions are legal (`u_a − 1` has constant
term `0`). -/
noncomputable def FtildeA (a : ℕ) : PowerSeries K :=
  PowerSeries.C (-(extLog p ((a : K))))
    - (formalLog (K := K)).subst (uA K a - 1)
    + ((a - 1 : ℕ)) • formalLog (K := K)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- R7.4c: the constant coefficient is `−log_p(a)` (TeX eq:F_a(0)).

Statement note (T704): `a ≠ 0` added — `uA 0 = 0` makes the formal composition
junk (`HasSubst` fails at constant coefficient `−1`). -/
theorem constantCoeff_FtildeA {a : ℕ} (ha0 : a ≠ 0) :
    PowerSeries.constantCoeff (FtildeA p K a)
      = -(extLog p ((a : K))) := by
  -- the substitution term has zero constant coefficient
  have hc : PowerSeries.constantCoeff (uA K a - 1 : PowerSeries K) = 0 := by
    rw [map_sub, constantCoeff_uA K ha0, map_one, sub_self]
  have hsubst : PowerSeries.constantCoeff ((formalLog (K := K)).subst (uA K a - 1)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hc _ (constantCoeff_formalLog (K := K))
  rw [FtildeA, map_add, map_sub, PowerSeries.constantCoeff_C, hsubst, sub_zero,
    map_nsmul, constantCoeff_formalLog (K := K), smul_zero, add_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The `n`-th coefficient of `geomSum a` is `C(a, n+1)` (from
`geomSum·X = (1+X)^a − 1` and the binomial coefficient at index `n+1`). -/
private lemma coeff_geomSum (a n : ℕ) :
    PowerSeries.coeff n (PadicMeasure.geomSum p a) = (a.choose (n + 1) : ℤ_[p]) := by
  rw [← PowerSeries.coeff_succ_mul_X n (PadicMeasure.geomSum p a),
    PadicMeasure.geomSum_mul_X, map_sub, coeff_one_add_X_pow, PowerSeries.coeff_one,
    if_neg (Nat.succ_ne_zero n), sub_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Step A (RJW TeX 2296–2300): `a·u_a` is the base-changed geometric sum. -/
private lemma natCast_smul_uA_eq_map_geomSum {a : ℕ} (ha0 : a ≠ 0) :
    (a : K) • uA K a
      = PowerSeries.map ((algebraMap ℚ_[p] K).comp (PadicInt.Coe.ringHom))
          (PadicMeasure.geomSum p a) := by
  have ha : (a : K) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  ext n
  rw [PowerSeries.coeff_map, coeff_geomSum, map_natCast, map_smul, uA, PowerSeries.coeff_mk,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
include hp in
/-- Step B (RJW TeX 2271–2279): substituting `u_a − 1` into `(1+X)·∂(log) = 1`
gives `u_a·(∂log)(u_a − 1) = 1` (the formal `1/(1+(u_a−1)) = 1/u_a`). -/
private lemma uA_mul_subst_derivative_formalLog {a : ℕ} (ha0 : a ≠ 0) :
    uA K a * (PowerSeries.derivativeFun (formalLog (K := K))).subst (uA K a - 1) = 1 := by
  have hg := hasSubst_uA_sub_one K ha0
  have h := congrArg (fun f => f.subst (uA K a - 1))
    (one_add_mul_derivative_formalLog (p := p) (K := K))
  rw [← PowerSeries.coe_substAlgHom hg, map_mul, map_add, map_one, PowerSeries.substAlgHom_X hg,
    show (1 : PowerSeries K) + (uA K a - 1) = uA K a by ring] at h
  rwa [← PowerSeries.coe_substAlgHom hg]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- R7.4d (RJW Lemma 7.3, TeX 2271–2279): `∂F̃_a = F_a` formally.

Statement note (T704): hypothesis `¬p∣a` added — `Fa p a` is the junk value `0`
when `p ∣ a` (`Ring.inverse` of a non-unit) while `∂F̃_a ≠ 0`; RJW carries
`p ∤ a` from §4.1 throughout. -/
theorem one_add_mul_derivative_FtildeA {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (FtildeA p K a)
      = PowerSeries.map ((algebraMap ℚ_[p] K).comp (PadicInt.Coe.ringHom))
          (PadicMeasure.Fa p a) := by
  classical
  set M := PowerSeries.map ((algebraMap ℚ_[p] K).comp (PadicInt.Coe.ringHom)) with hM
  -- shorthands
  set S : PowerSeries K := M (PadicMeasure.geomSum p a) with hS
  set DuA : PowerSeries K := PowerSeries.derivativeFun (uA K a) with hDuA
  set P : PowerSeries K := (PowerSeries.derivativeFun (formalLog (K := K))).subst (uA K a - 1)
    with hP
  have hα : ((a : ℕ) : PowerSeries K) = PowerSeries.C ((a : ℕ) : K) := (map_natCast _ _).symm
  -- Step A and consequences
  have hAsmul := natCast_smul_uA_eq_map_geomSum (p := p) K ha0
  have hA : ((a : ℕ) : PowerSeries K) * uA K a = S := by
    rw [hS, ← hAsmul, PowerSeries.smul_eq_C_mul, hα]
  -- `S·X = (1+X)^a − 1` (base-changed `geomSum_mul_X`)
  have hSX : S * PowerSeries.X = (1 + PowerSeries.X) ^ a - 1 := by
    have : S * PowerSeries.X = M (PadicMeasure.geomSum p a * PowerSeries.X) := by
      rw [hS, map_mul, PowerSeries.map_X]
    rw [this, PadicMeasure.geomSum_mul_X, map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
  -- Step B
  have hB : uA K a * P = 1 := uA_mul_subst_derivative_formalLog (p := p) K ha0
  -- bridges between `derivativeFun` and the `d⁄dX` derivation
  have hDX : PowerSeries.derivativeFun (PowerSeries.X : PowerSeries K) = 1 :=
    PowerSeries.derivative_X
  have hDpow : PowerSeries.derivativeFun ((1 + PowerSeries.X) ^ a : PowerSeries K)
      = (a : PowerSeries K) * (1 + PowerSeries.X) ^ (a - 1)
        * PowerSeries.derivativeFun (1 + PowerSeries.X) := PowerSeries.derivative_pow K _ a
  -- `α·(u_a·X) = (1+X)^a − 1`
  have hαuAX : ((a : ℕ) : PowerSeries K) * (uA K a * PowerSeries.X)
      = (1 + PowerSeries.X) ^ a - 1 := by
    rw [← mul_assoc, hA, hSX]
  -- differentiate it: `α·(u_a + X·∂u_a) = ∂((1+X)^a)`
  have hDuAX : ((a : ℕ) : PowerSeries K) * (uA K a + PowerSeries.X * DuA)
      = PowerSeries.derivativeFun ((1 + PowerSeries.X) ^ a : PowerSeries K) := by
    have hlhs : PowerSeries.derivativeFun
        (((a : ℕ) : PowerSeries K) * (uA K a * PowerSeries.X))
          = ((a : ℕ) : PowerSeries K) * (uA K a + PowerSeries.X * DuA) := by
      rw [hα, ← PowerSeries.smul_eq_C_mul, PowerSeries.derivativeFun_smul,
        PowerSeries.derivativeFun_mul, hDX, hDuA]
      rw [PowerSeries.smul_eq_C_mul, ← hα, smul_eq_mul, smul_eq_mul]
      ring
    have hrhs : PowerSeries.derivativeFun ((1 + PowerSeries.X) ^ a - 1 : PowerSeries K)
        = PowerSeries.derivativeFun ((1 + PowerSeries.X) ^ a : PowerSeries K) := by
      rw [show ((1 + PowerSeries.X) ^ a - 1 : PowerSeries K)
            = (1 + PowerSeries.X) ^ a + (-1 : PowerSeries K) by ring,
        PowerSeries.derivativeFun_add]
      rw [show (-1 : PowerSeries K) = PowerSeries.C (-1 : K) by simp,
        PowerSeries.derivativeFun_C, add_zero]
    rw [← hlhs, hαuAX, hrhs]
  -- `(1+X)·∂((1+X)^a) = α·(1+X)^a`
  have hQ : (1 + PowerSeries.X)
        * PowerSeries.derivativeFun ((1 + PowerSeries.X) ^ a : PowerSeries K)
      = ((a : ℕ) : PowerSeries K) * (1 + PowerSeries.X) ^ a := by
    rw [hDpow, PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_one, hDX, zero_add, mul_one]
    rcases Nat.exists_eq_succ_of_ne_zero ha0 with ⟨b, rfl⟩
    rw [Nat.succ_sub_one, pow_succ]
    push_cast
    ring
  -- the multiplied-out differentiated Step A
  have rDA : ((a : ℕ) : PowerSeries K) * (1 + PowerSeries.X) * (uA K a + PowerSeries.X * DuA)
      = ((a : ℕ) : PowerSeries K) * (((a : ℕ) : PowerSeries K) * uA K a * PowerSeries.X + 1) := by
    have h1 : (1 + PowerSeries.X) * (((a : ℕ) : PowerSeries K) * (uA K a + PowerSeries.X * DuA))
        = ((a : ℕ) : PowerSeries K) * (1 + PowerSeries.X) ^ a := by rw [hDuAX, hQ]
    have h2 : (1 + PowerSeries.X) ^ a = ((a : ℕ) : PowerSeries K) * uA K a * PowerSeries.X + 1 := by
      rw [hA, hSX]; ring
    rw [h2] at h1; linear_combination h1
  -- LHS expansion: `(1+X)·∂F̃_a = −(1+X)·P·∂u_a + (α − 1)`
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
  have hLHSexp : (1 + PowerSeries.X) * PowerSeries.derivativeFun (FtildeA p K a)
      = -((1 + PowerSeries.X) * P * DuA) + (((a : ℕ) : PowerSeries K) - 1) := by
    have hsubF : ∀ x y : PowerSeries K,
        PowerSeries.derivativeFun (x - y)
          = PowerSeries.derivativeFun x - PowerSeries.derivativeFun y :=
      fun x y => map_sub (PowerSeries.derivative K) x y
    have hnsmul : ∀ (n : ℕ) (f : PowerSeries K),
        PowerSeries.derivativeFun (n • f) = n • PowerSeries.derivativeFun f :=
      fun n f => map_nsmul (PowerSeries.derivative K) n f
    have hDF : PowerSeries.derivativeFun (FtildeA p K a)
        = -(P * DuA) + (a - 1 : ℕ) • PowerSeries.derivativeFun (formalLog (K := K)) := by
      have dsubst : PowerSeries.derivativeFun ((formalLog (K := K)).subst (uA K a - 1))
          = (PowerSeries.derivativeFun (formalLog (K := K))).subst (uA K a - 1)
            * PowerSeries.derivativeFun (uA K a - 1) :=
        PowerSeries.derivative_subst (A := K) (hasSubst_uA_sub_one K ha0)
      have hsub : PowerSeries.derivativeFun ((formalLog (K := K)).subst (uA K a - 1))
          = P * DuA := by
        rw [dsubst, hP, hDuA, hsubF, PowerSeries.derivativeFun_one, sub_zero]
      rw [FtildeA, PowerSeries.derivativeFun_add, hsubF, PowerSeries.derivativeFun_C, hsub,
        hnsmul, zero_sub]
    rw [hDF, mul_add, mul_neg, ← mul_assoc, mul_smul_comm,
      one_add_mul_derivative_formalLog (p := p) (K := K), nsmul_eq_mul, mul_one,
      Nat.cast_sub ha1, Nat.cast_one]
  -- RHS·G computation
  have hRHSG : M (PadicMeasure.Fa p a) * ((1 + PowerSeries.X) ^ a - 1)
      = S - ((a : ℕ) : PowerSeries K) := by
    have hMG : M ((1 + PowerSeries.X) ^ a - 1 : PowerSeries ℤ_[p])
        = (1 + PowerSeries.X) ^ a - 1 := by
      rw [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
    calc M (PadicMeasure.Fa p a) * ((1 + PowerSeries.X) ^ a - 1)
        = M (PadicMeasure.Fa p a) * M ((1 + PowerSeries.X) ^ a - 1 : PowerSeries ℤ_[p]) := by
          rw [hMG]
      _ = M (((1 + PowerSeries.X) ^ a - 1) * PadicMeasure.Fa p a) := by rw [← map_mul, mul_comm]
      _ = M (PadicMeasure.geomSum p a - ((a : ℕ) : PowerSeries ℤ_[p])) := by
          rw [PadicMeasure.one_add_X_pow_sub_one_mul_Fa p ha]
      _ = S - ((a : ℕ) : PowerSeries K) := by rw [map_sub, hS, map_natCast]
  -- `G ≠ 0`
  have hG_ne : ((1 + PowerSeries.X) ^ a - 1 : PowerSeries K) ≠ 0 := by
    intro h
    have : PowerSeries.coeff 1 ((1 + PowerSeries.X) ^ a - 1 : PowerSeries K) = 0 := by rw [h]; simp
    rw [map_sub, coeff_one_add_X_pow, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero,
      Nat.choose_one_right] at this
    exact (Nat.cast_ne_zero.mpr ha0) this
  -- cancel `G` and assemble
  refine mul_right_cancel₀ hG_ne ?_
  rw [hRHSG, hLHSexp, ← hSX, ← hA]
  -- now a polynomial identity in `uA, DuA, P, X, α`; `hB : uA·P = 1`, `rDA` the chain
  linear_combination
    (-(((a : ℕ) : PowerSeries K)) * PowerSeries.X * (1 + PowerSeries.X) * DuA) * hB - rDA

/-- R7.5a: the §4 numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_a)` (=
`PadicMeasure.zetaNum`), pushed to `ℤ_p` and base-changed to `K`. -/
noncomputable def rhoA (a : ℕ) : MeasureR K ℤ_[p] :=
  MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))

/-- `PowerSeries.map` commutes with `derivativeFun` (re-proved locally; the
ValuesAtOne version is private). -/
private theorem map_derivativeFun' {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f (PowerSeries.derivativeFun F)
      = PowerSeries.derivativeFun (PowerSeries.map f F) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivativeFun,
    PowerSeries.coeff_derivativeFun, PowerSeries.coeff_map, map_mul, map_add,
    map_natCast, map_one]

/-- `PowerSeries.map` commutes with `∂ = (1+T)d/dT` (re-proved locally). -/
private theorem map_one_add_mul_derivativeFun' {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f ((1 + PowerSeries.X) * PowerSeries.derivativeFun F)
      = (1 + PowerSeries.X) * PowerSeries.derivativeFun (PowerSeries.map f F) := by
  rw [map_mul, map_add, map_one, PowerSeries.map_X, map_derivativeFun']

/-- The `ℤ_p`-level multiplication-by-`x` identity: the `x⁻¹` in `zetaNum`
cancels against the `x`-monomial on the units, so
`x·ι(zetaNum a) = Res_{ℤ_p^×}(μ_a)`. The analogue of the template's `hmeas`
(T614), here at the `ℤ_p`-iota level (later base-changed). -/
private lemma cmul_mahler_one_iota_zetaNum (a : ℕ) :
    PadicMeasure.cmul p (mahler 1) (PadicMeasure.iota p (PadicMeasure.zetaNum p a))
      = PadicMeasure.res p (PadicMeasure.isClopen_units p) (PadicMeasure.muA p a) := by
  refine LinearMap.ext fun f => ?_
  rw [PadicMeasure.cmul_apply, PadicMeasure.iota, PadicMeasure.pushforward_apply,
    PadicMeasure.zetaNum, PadicMeasure.unitsCmul_apply]
  have hfun : PadicMeasure.invCM p * ((mahler 1 * f).comp (PadicMeasure.unitsValCM p))
      = f.comp (PadicMeasure.unitsValCM p) := by
    refine ContinuousMap.ext fun u => ?_
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply,
      PadicMeasure.unitsValCM, ContinuousMap.coe_mk]
    rw [mahler_apply, Ring.choose_one_right, ← mul_assoc]
    rw [show PadicMeasure.invCM p u * (u : ℤ_[p]) = 1 from ?_, one_mul]
    change ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hfun, ← PadicMeasure.pushforward_apply, ← PadicMeasure.iota,
    PadicMeasure.iota_muAUnits]

omit [CharZero K] in
/-- R7.5b: `ρ_a` is supported on the units. -/
theorem psi_rhoA (a : ℕ) : MeasureR.psi p K (rhoA p K a) = 0 := by
  rw [← MeasureR.isSupportedOn_units_iff_psi_eq_zero, MeasureR.IsSupportedOn, rhoA,
    ← MeasureR.baseChange_res, PadicMeasure.res_iota]

omit [CharZero K] in
/-- R7.5c: multiplication by `x` recovers `Res_{ℤ_p^×}(μ_a)` —
`∂𝓐(ρ_a) = 𝓐(Res_{units}(μ_a))` over `K` (Lemma 6.3's pattern, T614). -/
theorem one_add_mul_derivative_mahlerK_rhoA (a : ℕ) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoA p K a))
      = mahlerK p K (MeasureR.res p K
          (PadicMeasure.isClopen_units p)
          (MeasureR.baseChange p K (PadicMeasure.muA p a))) := by
  -- base-change the `ℤ_p`-level multiplication-by-`x` identity to `K`
  have hbase : MeasureR.cmul p K (MeasureR.mahlerCM p K 1) (rhoA p K a)
      = MeasureR.res p K (PadicMeasure.isClopen_units p)
          (MeasureR.baseChange p K (PadicMeasure.muA p a)) := by
    have h := congrArg (MeasureR.baseChange p K) (cmul_mahler_one_iota_zetaNum p a)
    rwa [MeasureR.baseChange_cmul, MeasureR.algCM_mahler, MeasureR.baseChange_res] at h
  -- transport through `mahlerK` via `𝓐_{xμ} = ∂𝓐_μ` and `map`-commutation with `∂`
  rw [← hbase]
  simp only [mahlerK]
  rw [MeasureR.mahlerTransform_cmul_X,
    show MeasureR.del K (MeasureR.mahlerTransform p K (rhoA p K a))
      = (1 + PowerSeries.X)
        * PowerSeries.derivativeFun (MeasureR.mahlerTransform p K (rhoA p K a)) from rfl,
    map_one_add_mul_derivativeFun']

omit [CharZero K] in
/-- The `M`-bridge (Step 1 of the c₀-pin): `mahlerK` of the base-changed `μ_a` is
the `M`-image of `F_a`, where `M = (algebraMap ℚ_[p] K) ∘ ℤ_[p]↪ℚ_[p]`. The
`subtype ∘ (algebraMap ℤ_[p] (integerRing K))` composite is `M` definitionally
(the `Algebra ℤ_[p] (integerRing K)` instance is the codRestriction of `M`). -/
private lemma mahlerK_baseChange_muA (a : ℕ) :
    mahlerK p K (MeasureR.baseChange p K (PadicMeasure.muA p a))
      = PowerSeries.map ((algebraMap ℚ_[p] K).comp (PadicInt.Coe.ringHom))
          (PadicMeasure.Fa p a) := by
  rw [mahlerK, MeasureR.mahlerTransform_baseChange, PadicMeasure.mahlerTransform_muA]
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖(a : K)‖ = 1` when `p ∤ a` (the cast factors through `algebraMap ℚ_[p] K`,
which is norm-preserving; `‖(a : ℚ_[p])‖ = 1` since `p ∤ a`). -/
private lemma norm_natCast_eq_one_of_not_dvd {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) :
    ‖((a : ℕ) : K)‖ = 1 := by
  rw [show ((a : ℕ) : K) = algebraMap ℚ_[p] K ((a : ℕ) : ℚ_[p]) from (map_natCast _ _).symm,
    norm_algebraMap']
  refine le_antisymm (by simpa using Padic.norm_int_le_one (p := p) (a : ℤ)) ?_
  by_contra h
  rw [not_le] at h
  have he : ((a : ℤ) : ℚ_[p]) = ((a : ℕ) : ℚ_[p]) := by push_cast; ring
  rw [← he] at h
  exact ha (by exact_mod_cast (Padic.norm_intCast_lt_one_iff (p := p)).mp h)

omit [CompleteSpace K] [CharZero K] in
/-- The coefficients of `u_a` are integral (`= a⁻¹·C(a, n+1)`, `‖a⁻¹‖ = 1` for
`p ∤ a` and binomial coefficients are integral in the ultrametric field). -/
private lemma norm_coeff_uA_le_one {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (n : ℕ) :
    ‖PowerSeries.coeff n (uA K a)‖ ≤ 1 := by
  rw [uA, PowerSeries.coeff_mk, norm_mul, norm_inv,
    norm_natCast_eq_one_of_not_dvd (p := p) K ha, inv_one, one_mul]
  exact IsUltrametricDist.norm_natCast_le_one K _

omit [CompleteSpace K] in
/-- The coefficients of `u_a − 1` are integral (constant term `0`, the rest are
`u_a`-coefficients). -/
private lemma norm_coeff_uA_sub_one_le_one {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    (n : ℕ) : ‖PowerSeries.coeff n (uA K a - 1)‖ ≤ 1 := by
  rw [map_sub]
  cases n with
  | zero =>
    have hc : PowerSeries.constantCoeff (uA K a - 1 : PowerSeries K) = 0 := by
      rw [map_sub, constantCoeff_uA K ha0, map_one, sub_self]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub] at hc
    rw [hc, norm_zero]; exact zero_le_one
  | succ m =>
    rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), sub_zero]
    exact norm_coeff_uA_le_one (p := p) K ha (m + 1)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `(u_a − 1)^d` vanishes below degree `d` (constant coefficient `0`, so
`X^d ∣ (u_a − 1)^d`). -/
private lemma coeff_uA_sub_one_pow_eq_zero {a : ℕ} (ha0 : a ≠ 0) {k d : ℕ} (hkd : k < d) :
    PowerSeries.coeff k ((uA K a - 1) ^ d) = 0 :=
  PowerSeries.X_pow_dvd_iff.1
    (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by
      rw [map_sub, constantCoeff_uA K ha0, map_one, sub_self])) d) k hkd

omit [CompleteSpace K] in
/-- Powers of `u_a − 1` have integral coefficients (`‖coeff k ((u_a − 1)^d)‖ ≤ 1`,
by induction on `d` through the ultrametric bound on `coeff_mul`). -/
private lemma norm_coeff_uA_sub_one_pow_le_one {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    (d k : ℕ) : ‖PowerSeries.coeff k ((uA K a - 1) ^ d)‖ ≤ 1 := by
  induction d generalizing k with
  | zero => rw [pow_zero, PowerSeries.coeff_one]; split <;> simp [zero_le_one]
  | succ e ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rcases (Finset.antidiagonal k).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact zero_le_one
    obtain ⟨ab, -, hab⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun ab => PowerSeries.coeff ab.1 ((uA K a - 1) ^ e)
        * PowerSeries.coeff ab.2 (uA K a - 1))
    refine hab.trans ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _)
      (norm_coeff_uA_sub_one_le_one (p := p) K ha ha0 _)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- `‖(n : K)⁻¹‖ ≤ n` for `n ≥ 1` (re-proved locally; the ValuesAtOne version is
private). The norm of `(n : K)` is `p^{−v_p(n)}`, whose inverse is `ordProj[p] n ≤ n`. -/
private theorem norm_natCast_inv_le {n : ℕ} (hn : 1 ≤ n) :
    ‖((n : K))⁻¹‖ ≤ (n : ℝ) := by
  have hn0 : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnK : ((n : K)) = algebraMap ℚ_[p] K (n : ℚ_[p]) := (map_natCast _ n).symm
  have hnorm : ‖((n : K))⁻¹‖ = ((p ^ padicValNat p n : ℕ) : ℝ) := by
    rw [norm_inv, hnK, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation hn0,
      Padic.valuation_natCast, ← zpow_neg, neg_neg, zpow_natCast]
    push_cast; ring
  rw [hnorm, ← Nat.factorization_def n hp.out]
  exact_mod_cast Nat.ordProj_le p (by omega)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- The coefficients of `formalLog` are linearly bounded `‖coeff n‖ ≤ n + 1`
(re-proved locally; the `1/n`-factor has norm `≤ n`). -/
private theorem norm_coeff_formalLog_le (n : ℕ) :
    ‖PowerSeries.coeff n (formalLog K)‖ ≤ (n : ℝ) + 1 := by
  cases n with
  | zero => rw [coeff_zero_formalLog, norm_zero]; positivity
  | succ m =>
    rw [coeff_succ_formalLog, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖((m : K) + 1)⁻¹‖ = ‖(((m + 1 : ℕ) : K))⁻¹‖ := by rw [Nat.cast_succ]
      _ ≤ ((m + 1 : ℕ) : ℝ) := norm_natCast_inv_le (p := p) (K := K) (by omega)
      _ ≤ (↑(m + 1) : ℝ) + 1 := by push_cast; linarith

omit [CompleteSpace K] in
include hp in
/-- The substitution `(formalLog).subst (u_a − 1)` has linearly-bounded coefficients
`‖coeff n‖ ≤ n + 1`. Mirrors `norm_coeff_phiSeries_le_linear`: the `coeff_subst'`
finsum is supported on `d ≤ n` (since `(u_a − 1)^d` vanishes below `d`), each term
`‖coeff d formalLog‖·‖coeff n ((u_a − 1)^d)‖ ≤ (d+1)·1 ≤ n + 1`. -/
private theorem norm_coeff_subst_formalLog_le {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    (n : ℕ) :
    ‖PowerSeries.coeff n ((formalLog K).subst (uA K a - 1))‖ ≤ (n : ℝ) + 1 := by
  rw [PowerSeries.coeff_subst' (hasSubst_uA_sub_one K ha0),
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [coeff_uA_sub_one_pow_eq_zero K ha0 (by omega), smul_zero]))]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d hd => ?_
  rw [smul_eq_mul, norm_mul]
  rcases Nat.lt_or_ge n d with hnd | hdn
  · rw [coeff_uA_sub_one_pow_eq_zero K ha0 hnd, norm_zero, mul_zero]; positivity
  · calc ‖PowerSeries.coeff d (formalLog K)‖ * ‖PowerSeries.coeff n ((uA K a - 1) ^ d)‖
        ≤ ((d : ℝ) + 1) * 1 :=
          mul_le_mul (norm_coeff_formalLog_le (p := p) (K := K) d)
            (norm_coeff_uA_sub_one_pow_le_one (p := p) K ha ha0 d n) (norm_nonneg _)
            (by positivity)
      _ ≤ (n : ℝ) + 1 := by
          rw [mul_one]
          have hdn : (d : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
          linarith

omit [CompleteSpace K] in
include hp in
/-- The coefficients of `F̃_a` are linearly bounded `‖coeff n‖ ≤ C·(n+1)` with
`C = max 1 ‖log_p a‖`. Drives the summability of `seriesEval (F̃_a)` at `‖z‖ < 1`. -/
private theorem norm_coeff_FtildeA_le {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    (n : ℕ) :
    ‖PowerSeries.coeff n (FtildeA p K a)‖
      ≤ max 1 ‖extLog p ((a : K))‖ * ((n : ℝ) + 1) := by
  set C' := max 1 ‖extLog p ((a : K))‖ with hC'
  have hC1 : (1 : ℝ) ≤ C' := le_max_left _ _
  have hCnn : 0 ≤ C' := le_trans zero_le_one hC1
  rw [FtildeA, map_add, map_sub]
  have hb1 : ‖PowerSeries.coeff n (PowerSeries.C (-(extLog p ((a : K)))))‖
      ≤ C' * ((n : ℝ) + 1) := by
    rw [PowerSeries.coeff_C]
    split_ifs with h
    · rw [norm_neg]
      calc ‖extLog p ((a : K))‖ ≤ C' := le_max_right _ _
        _ ≤ C' * ((n : ℝ) + 1) := by nlinarith [hCnn]
    · rw [norm_zero]; positivity
  have hb2 : ‖PowerSeries.coeff n ((formalLog K).subst (uA K a - 1))‖
      ≤ C' * ((n : ℝ) + 1) := by
    calc ‖PowerSeries.coeff n ((formalLog K).subst (uA K a - 1))‖ ≤ (n : ℝ) + 1 :=
          norm_coeff_subst_formalLog_le (p := p) K ha ha0 n
      _ ≤ C' * ((n : ℝ) + 1) := by nlinarith [hC1]
  have hb3 : ‖PowerSeries.coeff n ((a - 1 : ℕ) • formalLog (K := K))‖
      ≤ C' * ((n : ℝ) + 1) := by
    rw [map_nsmul, nsmul_eq_mul, norm_mul]
    calc ‖((a - 1 : ℕ) : K)‖ * ‖PowerSeries.coeff n (formalLog K)‖
        ≤ 1 * ((n : ℝ) + 1) :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one K _)
            (norm_coeff_formalLog_le (p := p) (K := K) n) (norm_nonneg _) zero_le_one
      _ ≤ C' * ((n : ℝ) + 1) := by nlinarith [hC1]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ hb3)
  rw [sub_eq_add_neg]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hb1 ?_)
  rw [norm_neg]; exact hb2

include hp in
/-- `seriesEval (F̃_a) z` converges for `‖z‖ < 1` (linear-growth coefficients). -/
private theorem summable_seriesEval_FtildeA {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    {z : K} (hz : ‖z‖ < 1) :
    Summable fun m : ℕ => PowerSeries.coeff m (FtildeA p K a) * z ^ m :=
  summable_seriesEval_of_norm_coeff_le_linear (C := max 1 ‖extLog p ((a : K))‖)
    (norm_coeff_FtildeA_le (p := p) K ha ha0) hz

/-- R7.6a (the c₀-pin, T615-pattern — no Gauss clearing this time):
`p·𝓐(ρ_a)(0) = p·F̃_a(0) − Σ_{i<p} F̃_a(ξ^i − 1)`. -/
theorem p_mul_constantCoeff_mahlerK_rhoA {a : ℕ} (ha : ¬ (p : ℕ) ∣ a)
    (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) :
    (p : K) * PowerSeries.constantCoeff
        (mahlerK p K (rhoA p K a))
      = (p : K) * PowerSeries.constantCoeff (FtildeA p K a)
        - ∑ i : Fin p, seriesEval (FtildeA p K a)
            (ξ ^ (i : ℕ) - 1) := by
  -- the `ψ`-part `K`-series `B` (integral coefficients) and the antiderivative `C₁`
  obtain ⟨C₁, hC₁0, hC₁, hC₁bd⟩ := MeasureR.exists_antideriv_bounded (p := p)
    (mahlerK p K (MeasureR.psi p K (MeasureR.baseChange p K (PadicMeasure.muA p a))))
    (norm_coeff_mahlerK_le_one _ _)
  -- `(1+X)·∂F̃_a = M(F_a) = mahlerK(baseChange μ_a)`  (T704 + the `M`-bridge)
  have hFder : (1 + PowerSeries.X) * PowerSeries.derivativeFun (FtildeA p K a)
      = mahlerK p K (MeasureR.baseChange p K (PadicMeasure.muA p a)) := by
    rw [one_add_mul_derivative_FtildeA p K ha ha0, mahlerK_baseChange_muA]
  -- `(1+X)·∂(𝓐_ρ) = mahlerK(baseChange μ_a) − φ B`  (Res = 1 − φψ, T705)
  have hAder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoA p K a))
      = mahlerK p K (MeasureR.baseChange p K (PadicMeasure.muA p a))
        - phiSeries p (mahlerK p K
          (MeasureR.psi p K (MeasureR.baseChange p K (PadicMeasure.muA p a)))) := by
    rw [one_add_mul_derivative_mahlerK_rhoA, MeasureR.res_units_eq, mahlerK_sub, mahlerK_phi]
  -- the W-equation: `(1+X)·∂W = φ B` where `W := F̃_a − 𝓐_ρ`
  have hWder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (FtildeA p K a - mahlerK p K (rhoA p K a))
      = phiSeries p (mahlerK p K
          (MeasureR.psi p K (MeasureR.baseChange p K (PadicMeasure.muA p a)))) := by
    rw [show PowerSeries.derivativeFun (FtildeA p K a - mahlerK p K (rhoA p K a))
        = PowerSeries.derivativeFun (FtildeA p K a)
          - PowerSeries.derivativeFun (mahlerK p K (rhoA p K a)) from
        map_sub (PowerSeries.derivative K) _ _,
      mul_sub, hFder, hAder]
    ring
  -- `(1+X)·∂(φ C₁) = φ B`  (∂φ = p·φ∂ + scalar pull-through)
  have hphiC₁der : (1 + PowerSeries.X) * PowerSeries.derivativeFun (phiSeries p C₁)
      = phiSeries p (mahlerK p K
          (MeasureR.psi p K (MeasureR.baseChange p K (PadicMeasure.muA p a)))) := by
    rw [one_add_mul_derivative_phiSeries,
      show (p : K) • phiSeries p ((1 + PowerSeries.X) * PowerSeries.derivativeFun C₁)
        = phiSeries p ((p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C₁)) from by
        rw [PowerSeries.smul_eq_C_mul, ← phiSeries_C_mul, ← PowerSeries.smul_eq_C_mul], hC₁]
  -- `W − φ C₁` is `∂`-killed, hence the constant `C c₀ = constantCoeff(W − φC₁)`
  have hker : (1 + PowerSeries.X) * PowerSeries.derivativeFun
      ((FtildeA p K a - mahlerK p K (rhoA p K a)) - phiSeries p C₁) = 0 := by
    rw [show PowerSeries.derivativeFun
          ((FtildeA p K a - mahlerK p K (rhoA p K a)) - phiSeries p C₁)
        = PowerSeries.derivativeFun (FtildeA p K a - mahlerK p K (rhoA p K a))
          - PowerSeries.derivativeFun (phiSeries p C₁) from
        map_sub (PowerSeries.derivative K) _ _,
      mul_sub, hWder, hphiC₁der, sub_self]
  have hWeq := eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero (p := p) hker
  set c₀ := PowerSeries.constantCoeff
    ((FtildeA p K a - mahlerK p K (rhoA p K a)) - phiSeries p C₁) with hc₀def
  -- so `W = φ C₁ + C c₀`
  have hWval : FtildeA p K a - mahlerK p K (rhoA p K a)
      = phiSeries p C₁ + PowerSeries.C c₀ := by
    rw [← hWeq]; ring
  -- `‖z_j‖ < 1` and `(1 + z_j)^p = 1` for `z_j = ξ^j − 1`
  have hzlt : ∀ j : Fin p, ‖ξ ^ (j : ℕ) - 1‖ < 1 := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
    · rw [hj0, pow_zero, sub_self, norm_zero]; exact one_pos
    · have hcop : (j : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hjpos hdvd) (by omega : ¬ p ≤ (j : ℕ)))
      exact (by rw [pow_one] at *; exact hξ.pow_of_coprime (j : ℕ) hcop :
        IsPrimitiveRoot (ξ ^ (j : ℕ)) (p ^ 1)).norm_sub_one_lt (p := p) le_rfl
  have hzp : ∀ j : Fin p, (1 + (ξ ^ (j : ℕ) - 1)) ^ p = 1 := fun j => by
    rw [show (1 : K) + (ξ ^ (j : ℕ) - 1) = ξ ^ (j : ℕ) by ring, ← pow_mul, mul_comm,
      pow_mul, hξ.pow_eq_one, one_pow]
  -- summability facts at `z_j = ξ^j − 1`
  have hsumF : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (FtildeA p K a) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_seriesEval_FtildeA (p := p) K ha ha0 (hzlt j)
  have hsumA : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (mahlerK p K (rhoA p K a)) * (ξ ^ (j : ℕ) - 1) ^ m :=
    fun j => summable_seriesEval_of_norm_coeff_le_one (norm_coeff_mahlerK_le_one _ _) (hzlt j)
  -- the constant series `C c₀` evaluates summably (finite support)
  have hsumCc₀ : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.C c₀) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_of_ne_finset_zero (s := {0}) fun m hm => by
      rw [PowerSeries.coeff_C, if_neg (by simpa using hm), zero_mul]
  have hsumphiC₁ : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (phiSeries p C₁) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_seriesEval_of_norm_coeff_le_linear (C := (p : ℝ))
      (norm_coeff_phiSeries_le_linear p (C := (p : ℝ)) (by positivity) hC₁bd) (hzlt j)
  -- evaluating `W = φ C₁ + C c₀` at each `z_j` gives `c₀`; on the other side
  -- `seriesEval W z_j = F̃_a(z_j) − 𝓐_ρ(z_j)`. Sum over `j`.
  have hsumW : ∑ j : Fin p, (seriesEval (FtildeA p K a) (ξ ^ (j : ℕ) - 1)
        - seriesEval (mahlerK p K (rhoA p K a)) (ξ ^ (j : ℕ) - 1))
      = (p : K) * c₀ := by
    rw [show (∑ j : Fin p, (seriesEval (FtildeA p K a) (ξ ^ (j : ℕ) - 1)
          - seriesEval (mahlerK p K (rhoA p K a)) (ξ ^ (j : ℕ) - 1)))
        = ∑ j : Fin p, seriesEval
            (FtildeA p K a - mahlerK p K (rhoA p K a)) (ξ ^ (j : ℕ) - 1) from
      Finset.sum_congr rfl fun j _ => by rw [seriesEval_sub (hsumF j) (hsumA j)]]
    rw [show (∑ j : Fin p, seriesEval
            (FtildeA p K a - mahlerK p K (rhoA p K a)) (ξ ^ (j : ℕ) - 1))
        = ∑ _j : Fin p, c₀ from Finset.sum_congr rfl fun j _ => by
      rw [hWval, seriesEval_add (hsumphiC₁ j) (hsumCc₀ j),
        seriesEval_phi_at_root_of_summable p
          (summable_prod_of_norm_coeff_le_linear p (C := (p : ℝ)) hC₁bd (hzlt j)) (hzp j),
        hC₁0, seriesEval_C, zero_add]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the `𝓐_ρ`-sum vanishes: `Σ_j 𝓐_ρ(z_j) = p·constantCoeff (mahlerK (ψρ)) = 0`
  have hAsum : ∑ j : Fin p, seriesEval (mahlerK p K (rhoA p K a)) (ξ ^ (j : ℕ) - 1)
      = 0 := by
    rw [sum_seriesEval_mahlerK (p := p) hξ (rhoA p K a), psi_rhoA]
    simp [mahlerK]
  -- `p·c₀ = Σ_j F̃_a(z_j)`
  have hexpand : (p : K) * c₀
      = ∑ j : Fin p, seriesEval (FtildeA p K a) (ξ ^ (j : ℕ) - 1) := by
    rw [← hsumW, Finset.sum_sub_distrib, hAsum, sub_zero]
  -- `c₀ = constantCoeff F̃_a − constantCoeff 𝓐_ρ` (evaluate `W = φC₁ + C c₀` at `0`)
  have hcWexp : c₀ = PowerSeries.constantCoeff (FtildeA p K a)
      - PowerSeries.constantCoeff (mahlerK p K (rhoA p K a)) := by
    have : c₀ = PowerSeries.constantCoeff (FtildeA p K a - mahlerK p K (rhoA p K a)) := by
      rw [hWval, map_add, constantCoeff_phiSeries, hC₁0, zero_add, PowerSeries.constantCoeff_C]
    rw [this, map_sub]
  -- assemble the displayed identity
  have h1 : (p : K) * c₀ = (p : K) * PowerSeries.constantCoeff (FtildeA p K a)
      - (p : K) * PowerSeries.constantCoeff (mahlerK p K (rhoA p K a)) := by
    rw [hcWexp]; ring
  rw [hexpand] at h1
  linear_combination h1

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A power `G^d` of a series with zero constant coefficient vanishes below degree `d`
(`constantCoeff G = 0 ⟹ X ∣ G ⟹ X^d ∣ G^d`). Generic version of
`coeff_uA_sub_one_pow_eq_zero`. -/
private lemma coeff_pow_eq_zero_of_constantCoeff_zero {G : PowerSeries K}
    (hG0 : PowerSeries.constantCoeff G = 0) {k d : ℕ} (hkd : k < d) :
    PowerSeries.coeff k (G ^ d) = 0 :=
  PowerSeries.X_pow_dvd_iff.1
    (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hG0) d) k hkd

omit [CompleteSpace K] [CharZero K] in
/-- Powers of a series with `‖coeff · G‖ ≤ 1` have integral coefficients
(`‖coeff k (G^d)‖ ≤ 1`, by induction on `d` through the ultrametric `coeff_mul` bound).
Generic version of `norm_coeff_uA_sub_one_pow_le_one`. -/
private lemma norm_coeff_pow_le_one {G : PowerSeries K}
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ 1) (d k : ℕ) :
    ‖PowerSeries.coeff k (G ^ d)‖ ≤ 1 := by
  induction d generalizing k with
  | zero => rw [pow_zero, PowerSeries.coeff_one]; split <;> simp [zero_le_one]
  | succ e ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rcases (Finset.antidiagonal k).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact zero_le_one
    obtain ⟨ab, -, hab⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun ab => PowerSeries.coeff ab.1 (G ^ e) * PowerSeries.coeff ab.2 G)
    refine hab.trans ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hG _)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `seriesEval 1 z = 1` (the unit series is `C 1`). -/
private lemma seriesEval_one (z : K) : seriesEval (1 : PowerSeries K) z = 1 := by
  rw [show (1 : PowerSeries K) = PowerSeries.C (1 : K) from (map_one _).symm, seriesEval_C]

omit [CharZero K] in
/-- `seriesEval (G^d) z = (seriesEval G z)^d` for an `‖·‖ ≤ 1`-coefficient series `G`
at `‖z‖ < 1` (induction via `seriesEval_mul`, each power having integral coefficients). -/
private lemma seriesEval_pow {G : PowerSeries K} (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ 1)
    {z : K} (hz : ‖z‖ < 1) (d : ℕ) :
    seriesEval (G ^ d) z = (seriesEval G z) ^ d := by
  induction d with
  | zero => rw [pow_zero, pow_zero, seriesEval_one]
  | succ e ih =>
    rw [pow_succ, pow_succ,
      seriesEval_mul (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_pow_le_one K hG e) hz)
        (summable_seriesEval_of_norm_coeff_le_one hG hz), ih]

omit [CompleteSpace K] [CharZero K] in
/-- `‖seriesEval G z‖ ≤ ‖z‖` when `constantCoeff G = 0` and `‖coeff · G‖ ≤ 1` (each
term `‖coeff_n G · z^n‖ ≤ ‖z‖^n ≤ ‖z‖` for `n ≥ 1`, the `n = 0` term vanishes). -/
private lemma norm_seriesEval_le {G : PowerSeries K} (hG0 : PowerSeries.constantCoeff G = 0)
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ 1) {z : K} (hz : ‖z‖ ≤ 1) :
    ‖seriesEval G z‖ ≤ ‖z‖ := by
  rw [seriesEval]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
  cases n with
  | zero =>
    rw [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0, norm_zero]
    exact norm_nonneg _
  | succ m =>
    rw [norm_mul, norm_pow, pow_succ]
    calc ‖PowerSeries.coeff (m + 1) G‖ * (‖z‖ ^ m * ‖z‖)
        ≤ 1 * (1 * ‖z‖) :=
          mul_le_mul (hG _) (mul_le_mul (pow_le_one₀ (norm_nonneg _) hz) le_rfl
            (norm_nonneg _) zero_le_one) (by positivity) zero_le_one
      _ = ‖z‖ := by ring

omit [CharZero K] in
/-- **Step 1 bridge** (the main new infrastructure): substituting a series `G` with
`constantCoeff G = 0`, `‖coeff · G‖ ≤ 1` into `formalLog` and evaluating at `‖z‖ < 1`
gives `padicLog p (1 + seriesEval G z)`. Coefficientwise decomposition of `formalLog.subst G`
+ double-sum swap (mirrors `seriesEval_phi_of_summable_prod`) + `seriesEval_pow` reduce it to
`seriesEval (formalLog) (seriesEval G z) = padicLog p (1 + seriesEval G z)`. -/
private theorem seriesEval_subst_formalLog {G : PowerSeries K}
    (hG0 : PowerSeries.constantCoeff G = 0) (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ 1)
    {z : K} (hz : ‖z‖ < 1) :
    seriesEval ((formalLog (K := K)).subst G) z = padicLog p (1 + seriesEval G z) := by
  have hS : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero' hG0
  -- `‖seriesEval G z‖ < 1`
  have hW : ‖seriesEval G z‖ < 1 := lt_of_le_of_lt (norm_seriesEval_le K hG0 hG hz.le) hz
  -- the total family `T d n = coeff d (formalLog) · coeff n (G^d) · z^n`
  let T : ℕ → ℕ → K := fun d n =>
    PowerSeries.coeff d (formalLog K) * PowerSeries.coeff n (G ^ d) * z ^ n
  have hTval : ∀ d n, T d n
      = PowerSeries.coeff d (formalLog K) * PowerSeries.coeff n (G ^ d) * z ^ n := fun _ _ => rfl
  -- a uniform per-term bound: `‖T d n‖ ≤ (n+1)·‖z‖^n` on `d ≤ n`, `= 0` off it
  have hTbd : ∀ d n, d ≤ n → ‖T d n‖ ≤ ((n : ℝ) + 1) * ‖z‖ ^ n := by
    intro d n hdn
    rw [hTval, norm_mul, norm_mul, norm_pow]
    calc ‖PowerSeries.coeff d (formalLog K)‖ * ‖PowerSeries.coeff n (G ^ d)‖ * ‖z‖ ^ n
        ≤ ((d : ℝ) + 1) * 1 * ‖z‖ ^ n :=
          mul_le_mul (mul_le_mul (norm_coeff_formalLog_le (p := p) (K := K) d)
            (norm_coeff_pow_le_one K hG d n) (norm_nonneg _) (by positivity)) le_rfl
            (by positivity) (by positivity)
      _ ≤ ((n : ℝ) + 1) * ‖z‖ ^ n := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hdn 1)
            (by positivity)
  -- joint summability over `ℕ × ℕ`
  have hprod : Summable (Function.uncurry T) := by
    rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
      NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    rw [Filter.eventually_cofinite]
    have htend : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ‖z‖ ^ n) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * ‖z‖ ^ n) Filter.atTop (nhds 0) :=
        tendsto_self_mul_const_pow_of_lt_one (norm_nonneg z) hz
      have h2 : Filter.Tendsto (fun n : ℕ => ‖z‖ ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz
      simpa only [add_mul, one_mul, add_zero] using h1.add h2
    obtain ⟨N, hN⟩ := (htend.eventually_lt_const hε).exists_forall_of_atTop
    refine Set.Finite.subset (Set.Finite.prod (Set.finite_Iio (N + 1)) (Set.finite_Iio (N + 1)))
      fun dn hdn => ?_
    simp only [Set.mem_setOf_eq, not_lt, Function.uncurry] at hdn
    by_cases hdn1 : dn.2 < dn.1
    · exfalso
      rw [hTval, coeff_pow_eq_zero_of_constantCoeff_zero K hG0 hdn1, mul_zero, zero_mul,
        norm_zero] at hdn
      exact absurd (lt_of_lt_of_le hε hdn) (lt_irrefl _)
    rw [not_lt] at hdn1
    have hn : dn.2 < N + 1 := by
      by_contra hge
      rw [not_lt] at hge
      exact absurd (lt_of_le_of_lt (le_trans hdn (hTbd dn.1 dn.2 hdn1)) (hN dn.2 (by omega)))
        (lt_irrefl ε)
    exact Set.mem_prod.2 ⟨lt_of_le_of_lt hdn1 hn, hn⟩
  -- the LHS coefficientwise: `coeff n (formalLog.subst G) · z^n = ∑' d, T d n`
  have hLHScoeff : ∀ n : ℕ,
      PowerSeries.coeff n ((formalLog K).subst G) * z ^ n = ∑' d : ℕ, T d n := by
    intro n
    rw [PowerSeries.coeff_subst' hS,
      finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
        intro d hd
        simp only [Function.mem_support] at hd
        by_contra hmem
        simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
        exact hd (by rw [coeff_pow_eq_zero_of_constantCoeff_zero K hG0 (by omega), smul_zero]))]
    rw [Finset.sum_mul, tsum_eq_sum (s := Finset.range (n + 1)) fun d hd => by
      rw [hTval, coeff_pow_eq_zero_of_constantCoeff_zero K hG0
        (show n < d by simp only [Finset.mem_range, not_lt] at hd; omega), mul_zero, zero_mul]]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hTval, smul_eq_mul]
  -- the inner sum `∑'_n T d n = coeff d (formalLog) · (seriesEval G z)^d`
  have hRHScoeff : ∀ d : ℕ,
      (∑' n : ℕ, T d n) = PowerSeries.coeff d (formalLog K) * (seriesEval G z) ^ d := by
    intro d
    rw [show (fun n : ℕ => T d n)
        = fun n : ℕ => PowerSeries.coeff d (formalLog K)
          * (PowerSeries.coeff n (G ^ d) * z ^ n) from by funext n; rw [hTval]; ring,
      (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_pow_le_one K hG d) hz).tsum_mul_left,
      ← seriesEval, seriesEval_pow K hG hz]
  -- assemble: `seriesEval (formalLog.subst G) z = ∑'_n ∑'_d T d n = ∑'_d ∑'_n T d n`
  -- `= seriesEval (formalLog) (seriesEval G z) = padicLog p (1 + seriesEval G z)`
  have hWsub : (1 + seriesEval G z) - 1 = seriesEval G z := by ring
  rw [seriesEval]
  simp_rw [hLHScoeff]
  rw [Summable.tsum_comm hprod]
  simp_rw [hRHScoeff]
  rw [← seriesEval,
    ← MeasureR.seriesEval_formalLog (p := p) (z := 1 + seriesEval G z) (by rw [hWsub]; exact hW),
    hWsub]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] in
/-- `seriesEval X z = z` (the monomial `X` peels to its single nonzero term). -/
private lemma seriesEval_X (z : K) : seriesEval (PowerSeries.X : PowerSeries K) z = z := by
  rw [seriesEval, tsum_eq_single 1 fun n hn => by
    rw [PowerSeries.coeff_X, if_neg hn, zero_mul],
    PowerSeries.coeff_one_X, one_mul, pow_one]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] in
/-- `seriesEval (c • F) z = c · seriesEval F z`. -/
private lemma seriesEval_smul (c : K) (F : PowerSeries K) (z : K) :
    seriesEval (c • F) z = c * seriesEval F z := by
  rw [PowerSeries.smul_eq_C_mul, seriesEval_C_mul]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] in
/-- `(n : ℕ) • F = C (n : K) * F` for a `K`-coefficient power series. -/
private lemma nsmul_eq_C_natCast_mul (n : ℕ) (F : PowerSeries K) :
    (n • F) = PowerSeries.C ((n : K)) * F := by
  rw [← PowerSeries.smul_eq_C_mul, Nat.cast_smul_eq_nsmul]

/-- **Step 2** (RJW TeX 2296–2300, evaluated): for `‖z‖ < 1`,
`(a:K) · z · seriesEval (uA K a) z = (1 + z)^a − 1`. Evaluate the formal identity
`(a:K) • uA · X = (1+X)^a − 1` at `z` (`seriesEval_mul` + `seriesEval_X` + `seriesEval`
of the polynomial `(1+X)^a − 1`). -/
private lemma natCast_mul_seriesEval_uA {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    {z : K} (hz : ‖z‖ < 1) :
    (a : K) * z * seriesEval (uA K a) z = (1 + z) ^ a - 1 := by
  -- the formal identity `(a:K) • uA · X = (1+X)^a − 1`
  set M := PowerSeries.map ((algebraMap ℚ_[p] K).comp (PadicInt.Coe.ringHom)) with hM
  have hform : (a : K) • uA K a * PowerSeries.X = (1 + PowerSeries.X) ^ a - 1 := by
    rw [natCast_smul_uA_eq_map_geomSum (p := p) K ha0, ← hM,
      show (PowerSeries.X : PowerSeries K) = M PowerSeries.X from (PowerSeries.map_X _).symm,
      ← map_mul, PadicMeasure.geomSum_mul_X]
    simp only [map_sub, map_pow, map_add, map_one]
  -- summabilities
  have hu : Summable fun n : ℕ => PowerSeries.coeff n (uA K a) * z ^ n :=
    summable_seriesEval_of_norm_coeff_le_one (norm_coeff_uA_le_one (p := p) K ha) hz
  have hsmul : Summable fun n : ℕ => PowerSeries.coeff n ((a : K) • uA K a) * z ^ n := by
    have hcongr : (fun n : ℕ => PowerSeries.coeff n ((a : K) • uA K a) * z ^ n)
        = fun n : ℕ => (a : K) * (PowerSeries.coeff n (uA K a) * z ^ n) := by
      funext n
      rw [PowerSeries.smul_eq_C_mul, PowerSeries.coeff_C_mul]; ring
    rw [hcongr]; exact hu.mul_left (a : K)
  have hX : Summable fun n : ℕ => PowerSeries.coeff n (PowerSeries.X : PowerSeries K) * z ^ n :=
    summable_seriesEval_of_norm_coeff_le_one (fun n => by
      rw [PowerSeries.coeff_X]; split <;> simp [zero_le_one]) hz
  -- evaluate both sides
  have hlhs : seriesEval ((a : K) • uA K a * PowerSeries.X) z = (a : K) * z * seriesEval (uA K a) z
      := by
    rw [seriesEval_mul hsmul hX, seriesEval_smul, seriesEval_X]; ring
  have hrhs : seriesEval ((1 + PowerSeries.X) ^ a - 1 : PowerSeries K) z = (1 + z) ^ a - 1 := by
    rw [seriesEval_sub (z := z) ?_ ?_, seriesEval_one_add_X_pow,
      show (1 : PowerSeries K) = PowerSeries.C (1 : K) from (map_one _).symm, seriesEval_C]
    · exact summable_seriesEval_of_norm_coeff_le_one (fun n => by
        rw [coeff_one_add_X_pow]; exact IsUltrametricDist.norm_natCast_le_one K _) hz
    · exact summable_seriesEval_of_norm_coeff_le_one (fun n => by
        rw [show (1 : PowerSeries K) = PowerSeries.C (1 : K) from (map_one _).symm,
          PowerSeries.coeff_C]; split <;> simp [zero_le_one]) hz
  rw [← hlhs, hform, hrhs]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [CharZero K] in
/-- The open unit ball `‖· − 1‖ < 1` is closed under finite products (ultrametric:
`‖xy − 1‖ ≤ max(‖x − 1‖·‖y‖, ‖y − 1‖) < 1`). -/
private lemma norm_prod_sub_one_lt_one {ι : Type*} (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, ‖f i - 1‖ < 1) :
    ‖(∏ i ∈ s, f i) - 1‖ < 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have hfa : ‖f a - 1‖ < 1 := hf a (Finset.mem_insert_self a t)
    have hrt : ‖(∏ i ∈ t, f i) - 1‖ < 1 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hfanorm : ‖f a‖ ≤ 1 := by
      calc ‖f a‖ = ‖(f a - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ max ‖f a - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := by rw [norm_one]; exact max_le hfa.le le_rfl
    rw [show f a * (∏ i ∈ t, f i) - 1 = f a * ((∏ i ∈ t, f i) - 1) + (f a - 1) from by ring]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt
      (by rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hfanorm) hrt)
        hfa)

omit [CharZero K] in
/-- **Step 6** (the `padicLog`-of-product helper): for a finite family with all
`‖f i − 1‖ < 1`, `padicLog p (∏_{i∈s} f i) = ∑_{i∈s} padicLog p (f i)`
(induction via `padicLog_mul_of_norm_lt_one`; the unit ball is closed under products). -/
private lemma padicLog_prod_of_norm_lt_one {ι : Type*} (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, ‖f i - 1‖ < 1) :
    padicLog p (∏ i ∈ s, f i) = ∑ i ∈ s, padicLog p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.sum_insert hat,
      MeasureR.padicLog_mul_of_norm_lt_one (p := p) (hf a (Finset.mem_insert_self a t))
        (norm_prod_sub_one_lt_one K t f (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

omit [CharZero K] in
/-- `seriesEval (uA K a − 1) z = seriesEval (uA K a) z − 1` for `‖z‖ < 1` (the `−1` is the
constant series `C 1`, evaluating to `1`). -/
private lemma seriesEval_uA_sub_one {a : ℕ} (ha : ¬ (p : ℕ) ∣ a)
    {z : K} (hz : ‖z‖ < 1) :
    seriesEval (uA K a - 1) z = seriesEval (uA K a) z - 1 := by
  have h1 : Summable fun n : ℕ => PowerSeries.coeff n (1 : PowerSeries K) * z ^ n :=
    summable_seriesEval_of_norm_coeff_le_one (fun n => by
      rw [PowerSeries.coeff_one]; split <;> simp [zero_le_one]) hz
  rw [seriesEval_sub (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_uA_le_one (p := p) K ha)
    hz) h1, seriesEval_one]

/-- `seriesEval (uA K a) z` for `‖z‖ < 1` lands in the open unit ball: its distance to `1`
is `‖seriesEval (uA K a − 1) z‖ ≤ ‖z‖ < 1`. -/
private lemma norm_seriesEval_uA_sub_one_lt {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    {z : K} (hz : ‖z‖ < 1) : ‖seriesEval (uA K a) z - 1‖ < 1 := by
  rw [← seriesEval_uA_sub_one (p := p) K ha hz]
  exact lt_of_le_of_lt (norm_seriesEval_le K (by
    rw [map_sub, constantCoeff_uA K ha0, map_one, sub_self])
    (norm_coeff_uA_sub_one_le_one (p := p) K ha ha0) hz.le) hz

/-- **Step 3** (per-point evaluation): for `i : Fin p`, writing `z_i = ξ^i − 1`,
`seriesEval (F̃_a) z_i = −extLog(a) − padicLog p (seriesEval (uA K a) z_i)`
(the `(a−1)·log(1+T)` term evaluates to `(a−1)·padicLog(ξ^i) = 0` since `(ξ^i)^p = 1`). -/
private lemma seriesEval_FtildeA_at_root {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0)
    {ξ : K} (hξ : IsPrimitiveRoot ξ p) (i : Fin p) :
    seriesEval (FtildeA p K a) (ξ ^ (i : ℕ) - 1)
      = -(extLog p ((a : K))) - padicLog p (seriesEval (uA K a) (ξ ^ (i : ℕ) - 1)) := by
  set z := ξ ^ (i : ℕ) - 1 with hzdef
  -- `‖z‖ < 1` and `1 + z = ξ^i`
  have hzlt : ‖z‖ < 1 := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · rw [hzdef, hi0, pow_zero, sub_self, norm_zero]; exact one_pos
    · have hcop : (i : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hipos hdvd) (by omega : ¬ p ≤ (i : ℕ)))
      exact (by rw [pow_one] at *; exact hξ.pow_of_coprime (i : ℕ) hcop :
        IsPrimitiveRoot (ξ ^ (i : ℕ)) (p ^ 1)).norm_sub_one_lt (p := p) le_rfl
  have h1z : (1 : K) + z = ξ ^ (i : ℕ) := by rw [hzdef]; ring
  -- the three summability facts at `z`
  have hsC : Summable fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.C (-(extLog p ((a : K))))) * z ^ n :=
    summable_of_ne_finset_zero (s := {0}) fun m hm => by
      rw [PowerSeries.coeff_C, if_neg (by simpa using hm), zero_mul]
  have hsubst : Summable fun n : ℕ =>
      PowerSeries.coeff n ((formalLog K).subst (uA K a - 1)) * z ^ n :=
    summable_seriesEval_of_norm_coeff_le_linear (C := 1) (fun n => by
      rw [one_mul]; exact norm_coeff_subst_formalLog_le (p := p) K ha ha0 n) hzlt
  have hsLog : Summable fun n : ℕ =>
      PowerSeries.coeff n ((a - 1 : ℕ) • formalLog (K := K)) * z ^ n := by
    have hcongr : (fun n : ℕ => PowerSeries.coeff n ((a - 1 : ℕ) • formalLog (K := K)) * z ^ n)
        = fun n : ℕ => ((a - 1 : ℕ) : K) * (PowerSeries.coeff n (formalLog K) * z ^ n) := by
      funext n
      rw [nsmul_eq_C_natCast_mul, PowerSeries.coeff_C_mul]; ring
    rw [hcongr]
    exact (summable_seriesEval_of_norm_coeff_le_linear (C := 1) (fun n => by
      rw [one_mul]; exact norm_coeff_formalLog_le (p := p) (K := K) n) hzlt).mul_left _
  have hsCsub : Summable fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.C (-(extLog p ((a : K)))) - (formalLog K).subst (uA K a - 1))
        * z ^ n :=
    (hsC.sub hsubst).congr fun n => by rw [map_sub, sub_mul]
  -- evaluate `F̃_a = C(−extLog a) − (formalLog).subst(uA−1) + (a−1)•formalLog`
  rw [FtildeA, seriesEval_add hsCsub hsLog, seriesEval_sub hsC hsubst, seriesEval_C]
  -- the subst term: bridge value `= padicLog (1 + seriesEval (uA−1) z) = padicLog (uA z)`
  have hbridge : seriesEval ((formalLog K).subst (uA K a - 1)) z
      = padicLog p (seriesEval (uA K a) z) := by
    rw [seriesEval_subst_formalLog (p := p) K (by
        rw [map_sub, constantCoeff_uA K ha0, map_one, sub_self])
      (norm_coeff_uA_sub_one_le_one (p := p) K ha ha0) hzlt,
      seriesEval_uA_sub_one (p := p) K ha hzlt, add_sub_cancel]
  -- the `(a−1)•formalLog` term: `((a−1):K)·padicLog(ξ^i) = 0`
  have hformalLog : seriesEval (formalLog K) z = padicLog p (ξ ^ (i : ℕ)) := by
    have hznorm : ‖ξ ^ (i : ℕ) - 1‖ < 1 := by rw [← hzdef]; exact hzlt
    rw [show z = ξ ^ (i : ℕ) - 1 from hzdef,
      MeasureR.seriesEval_formalLog (p := p) hznorm]
  have hLogzero : padicLog p (ξ ^ (i : ℕ)) = 0 := by
    rw [← MeasureR.extLog_eq_padicLog_of_norm_lt_one (p := p) (by rw [← hzdef]; exact hzlt),
      extLog_eq_zero_of_pow_eq_one p hp.out.pos (by rw [← pow_mul, mul_comm, pow_mul,
        hξ.pow_eq_one, one_pow])]
  have hLogterm : seriesEval ((a - 1 : ℕ) • formalLog (K := K)) z = 0 := by
    rw [nsmul_eq_C_natCast_mul, seriesEval_C_mul, hformalLog, hLogzero, mul_zero]
  rw [hbridge, hLogterm, add_zero]

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **Step 5 reindex** (`{ξ^{a·i}} = μ_p \ {1}`): for `p ∤ a` the multiplier `i ↦ a·i mod p`
permutes `univ.erase 0`, so `Π_{i≠0}(ξ^{a·i} − 1) = Π_{i≠0}(ξ^i − 1)`
(`Finset.prod_nbij'` through `ZMod p`; `a⁻¹ mod p` is the inverse). -/
private lemma prod_erase_pow_twist {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p) :
    ∏ i ∈ Finset.univ.erase (0 : Fin p), (ξ ^ (a * (i : ℕ)) - 1)
      = ∏ i ∈ Finset.univ.erase (0 : Fin p), (ξ ^ (i : ℕ) - 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have haz : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  -- the order of `ξ` is `p`
  have hord : orderOf ξ = p := hξ.eq_orderOf ▸ rfl
  -- `(i : Fin p) = 0 ↔ (i : ZMod p) = 0` (both encode `i % p = 0` for `i < p`)
  have hcastFin : ∀ i : Fin p, ((i : ℕ) : ZMod p) = 0 ↔ i = 0 := fun i => by
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt i.2,
      ← Fin.val_eq_zero_iff]
  have hval0 : ∀ x : ZMod p, (⟨x.val, ZMod.val_lt x⟩ : Fin p) = 0 ↔ x = 0 := fun x => by
    rw [Fin.ext_iff, Fin.val_zero, ZMod.val_eq_zero]
  refine Finset.prod_nbij' (fun i => ⟨((a : ZMod p) * ((i : ℕ) : ZMod p)).val, ZMod.val_lt _⟩)
    (fun j => ⟨((a : ZMod p)⁻¹ * ((j : ℕ) : ZMod p)).val, ZMod.val_lt _⟩) ?_ ?_ ?_ ?_ ?_
  · -- forward maps `erase 0 → erase 0`
    intro i hi
    rw [Finset.mem_erase] at hi ⊢
    refine ⟨fun h => hi.1 ((hcastFin i).mp ?_), Finset.mem_univ _⟩
    rcases mul_eq_zero.mp ((hval0 _).mp h) with h0 | h0
    · exact absurd h0 haz
    · exact h0
  · -- inverse maps `erase 0 → erase 0`
    intro j hj
    rw [Finset.mem_erase] at hj ⊢
    refine ⟨fun h => hj.1 ((hcastFin j).mp ?_), Finset.mem_univ _⟩
    rcases mul_eq_zero.mp ((hval0 _).mp h) with h0 | h0
    · exact absurd (inv_eq_zero.mp h0) haz
    · exact h0
  · -- left inverse
    intro i _
    apply Fin.ext
    simp only [ZMod.natCast_val, ZMod.cast_id]
    rw [← mul_assoc, inv_mul_cancel₀ haz, one_mul, ZMod.val_cast_of_lt i.2]
  · -- right inverse
    intro j _
    apply Fin.ext
    simp only [ZMod.natCast_val, ZMod.cast_id]
    rw [← mul_assoc, mul_inv_cancel₀ haz, one_mul, ZMod.val_cast_of_lt j.2]
  · -- the summand matches: `ξ^{a·i} = ξ^{(a·i mod p)}`
    intro i _
    have hexp : ((a : ZMod p) * ((i : ℕ) : ZMod p)).val = (a * (i : ℕ)) % p := by
      rw [← Nat.cast_mul, ZMod.val_natCast]
    have hfo : IsOfFinOrder ξ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.out.pos, hξ.pow_eq_one⟩
    have hmod : a * (i : ℕ) ≡ ((a : ZMod p) * ((i : ℕ) : ZMod p)).val [MOD orderOf ξ] := by
      rw [hord, hexp]; exact (Nat.mod_modEq _ _).symm
    exact congrArg (· - 1) (hfo.pow_eq_pow_iff_modEq.mpr hmod)

omit [CompleteSpace K] [CharZero K] in
/-- **Step 7 (Fermat bound)**: for `p ∤ a`, `‖(a:K)^{p−1} − 1‖ ≤ p⁻¹`
(`a^{p−1} ≡ 1 mod p` over `ℤ`, so `a^{p−1} − 1 = p·m` in `K` with `‖m‖ ≤ 1`). -/
private lemma norm_natCast_pow_sub_one_le {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) :
    ‖((a : K)) ^ (p - 1) - 1‖ ≤ (p : ℝ)⁻¹ := by
  have haz : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  -- Fermat over `ℤ`: `p ∣ a^{p−1} − 1`
  have hdvd : (p : ℤ) ∣ (a : ℤ) ^ (p - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one haz, sub_self]
  obtain ⟨m, hm⟩ := hdvd
  -- transport to `K`: `a^{p−1} − 1 = p·m`
  have hK : ((a : K)) ^ (p - 1) - 1 = (p : K) * ((m : ℤ) : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hm
    push_cast at this
    linear_combination this
  rw [hK, norm_mul, norm_natCast_p p]
  calc (p : ℝ)⁻¹ * ‖((m : ℤ) : K)‖ ≤ (p : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K m) (by positivity)
    _ = (p : ℝ)⁻¹ := mul_one _

omit [CompleteSpace K] [CharZero K] in
/-- **Step 7 (membership)**: for `p` odd and `p ∤ a`, `(a:K)^{p−1}` lies in the exponential
ball (`‖·‖^{p−1} ≤ (p⁻¹)^{p−1} ≤ (p⁻¹)^2 < p⁻¹` using `p − 1 ≥ 2`). -/
private lemma inExpBall_natCast_pow_sub_one (hp2 : p ≠ 2) {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) :
    InExpBall p (((a : K)) ^ (p - 1) - 1) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnb := norm_natCast_pow_sub_one_le (p := p) K ha
  have hnn : (0 : ℝ) ≤ ‖((a : K)) ^ (p - 1) - 1‖ := norm_nonneg _
  rw [InExpBall]
  calc ‖((a : K)) ^ (p - 1) - 1‖ ^ (p - 1)
      ≤ ((p : ℝ)⁻¹) ^ (p - 1) := pow_le_pow_left₀ hnn hnb _
    _ ≤ ((p : ℝ)⁻¹) ^ 2 := pow_le_pow_of_le_one (by positivity)
        (by rw [inv_le_one_iff₀]; right; exact_mod_cast hp.out.one_le) (by omega)
    _ < (p : ℝ)⁻¹ := by
        rw [pow_two]
        refine (mul_lt_iff_lt_one_left (by positivity)).mpr ?_
        rw [inv_lt_one_iff₀]; right; exact_mod_cast by omega

/-- R7.6b (RJW Lemma 7.5's trace, TeX 2330–2349): the evaluated `μ_p`-sum
collapses — `Σ_{i<p} F̃_a(ξ^i − 1) = −log_p(a)` (the `{ξ^a} = μ_p`
reindex for `p ∤ a` and `Π_ξ(Xξ−1) = X^p−1`). -/
theorem sum_seriesEval_FtildeA (hp2 : p ≠ 2) {a : ℕ} (ha : ¬ (p : ℕ) ∣ a)
    (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) :
    ∑ i : Fin p, seriesEval (FtildeA p K a) (ξ ^ (i : ℕ) - 1)
      = -(extLog p ((a : K))) := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set u : Fin p → K := fun i => seriesEval (uA K a) (ξ ^ (i : ℕ) - 1) with hudef
  have haK : (a : K) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  -- `‖ξ^i − 1‖ < 1` for all `i`
  have hzlt : ∀ i : Fin p, ‖ξ ^ (i : ℕ) - 1‖ < 1 := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · rw [hi0, pow_zero, sub_self, norm_zero]; exact one_pos
    · have hcop : (i : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hipos hdvd) (by omega : ¬ p ≤ (i : ℕ)))
      exact (by rw [pow_one] at *; exact hξ.pow_of_coprime (i : ℕ) hcop :
        IsPrimitiveRoot (ξ ^ (i : ℕ)) (p ^ 1)).norm_sub_one_lt (p := p) le_rfl
  -- Step 3 per-point, summed
  rw [show (∑ i : Fin p, seriesEval (FtildeA p K a) (ξ ^ (i : ℕ) - 1))
      = ∑ i : Fin p, (-(extLog p ((a : K))) - padicLog p (u i)) from
    Finset.sum_congr rfl fun i _ => seriesEval_FtildeA_at_root (p := p) K ha ha0 hξ i,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- the `i = 0` log term vanishes (`u 0 = 1`)
  have hu0 : u (0 : Fin p) = 1 := by
    simp only [hudef]
    rw [Fin.val_zero, pow_zero, sub_self, seriesEval_zero_arg, constantCoeff_uA K ha0]
  have hsumlog : (∑ i : Fin p, padicLog p (u i))
      = ∑ i ∈ Finset.univ.erase (0 : Fin p), padicLog p (u i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin p)), hu0, padicLog_one, add_zero]
  -- `‖u i − 1‖ < 1` on the erase
  have hunorm : ∀ i ∈ Finset.univ.erase (0 : Fin p), ‖u i - 1‖ < 1 := fun i _ =>
    norm_seriesEval_uA_sub_one_lt (p := p) K ha ha0 (hzlt i)
  -- Step 5 product collapse: `Π_{i≠0} u i = ((a:K)^{p−1})⁻¹`
  have hzne : ∀ i ∈ Finset.univ.erase (0 : Fin p), ξ ^ (i : ℕ) - 1 ≠ 0 := by
    intro i hi
    rw [Finset.mem_erase] at hi
    have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero (fun h => hi.1 (Fin.ext (by simpa using h)))
    exact sub_ne_zero.mpr (hξ.pow_ne_one_of_pos_of_lt hipos.ne' i.2)
  have hProdZne : (∏ i ∈ Finset.univ.erase (0 : Fin p), (ξ ^ (i : ℕ) - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hzne
  -- card of the erase is `p − 1`
  have hcard : (Finset.univ.erase (0 : Fin p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hProdU : (∏ i ∈ Finset.univ.erase (0 : Fin p), u i) = ((a : K) ^ (p - 1))⁻¹ := by
    -- `Π_{i≠0} ((a:K)·z_i·u_i) = Π_{i≠0}(ξ^{a·i}−1) = Π_{i≠0}(ξ^i−1) = Π_{i≠0} z_i`
    have hStep2 : ∀ i ∈ Finset.univ.erase (0 : Fin p),
        (a : K) * (ξ ^ (i : ℕ) - 1) * u i = ξ ^ (a * (i : ℕ)) - 1 := by
      intro i _
      simp only [hudef]
      rw [natCast_mul_seriesEval_uA (p := p) K ha ha0 (hzlt i),
        show (1 : K) + (ξ ^ (i : ℕ) - 1) = ξ ^ (i : ℕ) from by ring, ← pow_mul, Nat.mul_comm]
    have hLHS : (∏ i ∈ Finset.univ.erase (0 : Fin p),
          ((a : K) * (ξ ^ (i : ℕ) - 1) * u i))
        = (a : K) ^ (p - 1) * (∏ i ∈ Finset.univ.erase (0 : Fin p), (ξ ^ (i : ℕ) - 1))
          * (∏ i ∈ Finset.univ.erase (0 : Fin p), u i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hcard]
    have hRHS : (∏ i ∈ Finset.univ.erase (0 : Fin p), ((a : K) * (ξ ^ (i : ℕ) - 1) * u i))
        = ∏ i ∈ Finset.univ.erase (0 : Fin p), (ξ ^ (i : ℕ) - 1) := by
      rw [Finset.prod_congr rfl hStep2, prod_erase_pow_twist (p := p) K ha hξ]
    rw [hLHS] at hRHS
    -- cancel `Π z_i` and solve for `Π u_i`
    have hkey : (a : K) ^ (p - 1) * (∏ i ∈ Finset.univ.erase (0 : Fin p), u i) = 1 := by
      refine mul_right_cancel₀ hProdZne ?_
      rw [one_mul]
      linear_combination hRHS
    have hpowne : ((a : K)) ^ (p - 1) ≠ 0 := pow_ne_zero _ haK
    field_simp
    linear_combination hkey
  -- Step 6 + 7: `Σ_{i≠0} padicLog(u i) = padicLog(Π u_i) = −padicLog((a:K)^{p−1})`
  rw [hsumlog, ← padicLog_prod_of_norm_lt_one (p := p) K _ u hunorm, hProdU]
  -- `padicLog((a:K)^{p−1}) = ((p−1:ℕ):K)·extLog(a)` (witness)
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hWitness : extLog p ((a : K))
      = ((p - 1 : ℕ) : ℚ_[p])⁻¹ • padicLog p (((a : K)) ^ (p - 1)) :=
    extLog_eq_of_witness p (by omega) (by rw [zpow_zero, one_mul])
      (inExpBall_natCast_pow_sub_one (p := p) K hp2 ha)
  have hpm1K : ((p - 1 : ℕ) : K) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  have hLogPow : padicLog p (((a : K)) ^ (p - 1)) = ((p - 1 : ℕ) : K) * extLog p ((a : K)) := by
    conv_rhs => rw [hWitness, Algebra.smul_def, map_inv₀, map_natCast, ← mul_assoc,
      mul_inv_cancel₀ hpm1K, one_mul]
  -- log of the inverse: `padicLog((a^{p−1})⁻¹) = −padicLog(a^{p−1})`
  have hInvLog : padicLog p (((a : K) ^ (p - 1))⁻¹) = -padicLog p (((a : K)) ^ (p - 1)) := by
    have hpowne : ((a : K)) ^ (p - 1) ≠ 0 := pow_ne_zero _ haK
    have hballnorm : ‖((a : K)) ^ (p - 1) - 1‖ < 1 :=
      lt_of_le_of_lt (norm_natCast_pow_sub_one_le (p := p) K ha)
        (by rw [inv_lt_one_iff₀]; right; exact_mod_cast hp.out.one_lt)
    have hinvnorm : ‖(((a : K)) ^ (p - 1))⁻¹ - 1‖ < 1 := by
      have hnorm1 : ‖((a : K)) ^ (p - 1)‖ = 1 := by
        rw [norm_pow, norm_natCast_eq_one_of_not_dvd (p := p) K ha, one_pow]
      rw [show (((a : K)) ^ (p - 1))⁻¹ - 1 = (((a : K)) ^ (p - 1))⁻¹ * (1 - ((a : K)) ^ (p - 1))
          from by field_simp, norm_mul, norm_inv, hnorm1, inv_one, one_mul,
        show (1 : K) - ((a : K)) ^ (p - 1) = -(((a : K)) ^ (p - 1) - 1) from by ring, norm_neg]
      exact hballnorm
    have hmul := MeasureR.padicLog_mul_of_norm_lt_one (p := p) hballnorm hinvnorm
    rw [mul_inv_cancel₀ hpowne, padicLog_one] at hmul
    linear_combination -hmul
  rw [hInvLog, hLogPow]
  -- final bookkeeping: `p•(−extLog a) − (−((p−1:ℕ):K)·extLog a) = −extLog a`
  have hpcast : ((p - 1 : ℕ) : K) = (p : K) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hpcast, nsmul_eq_mul]
  ring

/-- R7.6c (RJW Lemma 7.5, TeX 2320): the mass of `x⁻¹·Res(μ_a)` —
`((1−φψ)F̃_a)(0) = −(1−p⁻¹)·log_p(a)`, in the c₀-design form. -/
theorem constantCoeff_mahlerK_rhoA (hp2 : p ≠ 2) {a : ℕ}
    (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p) :
    PowerSeries.constantCoeff (mahlerK p K (rhoA p K a))
      = -(1 - (p : K)⁻¹) * extLog p ((a : K)) := by
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  -- `p·cc(𝓐ρ) = p·cc(F̃_a) − Σ_i F̃_a(z_i) = p·(−extLog a) − (−extLog a)`
  have hp_mul := p_mul_constantCoeff_mahlerK_rhoA (p := p) K ha ha0 hξ
  rw [constantCoeff_FtildeA p K ha0, sum_seriesEval_FtildeA (p := p) K hp2 ha ha0 hξ] at hp_mul
  -- divide by `p` (nonzero)
  field_simp
  linear_combination hp_mul

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- R7.7a (descent infrastructure): `padicLog` commutes with the structure map
`algebraMap ℚ_[p] K`. The map is an isometry (hence a closed embedding, `ℚ_[p]`
complete), so it pushes through the defining `tsum`; the `ℚ_[p]`-scalar `(n+1)⁻¹`
and the ring operations transport termwise. -/
private theorem map_padicLog (y : ℚ_[p]) :
    algebraMap ℚ_[p] K (padicLog p y) = padicLog p (algebraMap ℚ_[p] K y) := by
  rw [padicLog, padicLog,
    Topology.IsClosedEmbedding.map_tsum _ (algebraMap_isometry ℚ_[p] K).isClosedEmbedding]
  refine tsum_congr fun n => ?_
  rw [map_mul, map_pow, map_neg, map_one, Algebra.smul_def, Algebra.smul_def, map_mul, map_pow,
    map_sub, map_one, map_inv₀, map_add, map_natCast, map_one]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The structure map `algebraMap ℚ_[p] K` is `ℚ_[p]`-linear: it pulls a `ℚ_[p]`-scalar
through the `•`-action (`c • x = algebraMap c · x` on both sides). -/
private lemma map_smul_padic (c x : ℚ_[p]) :
    algebraMap ℚ_[p] K (c • x) = c • (algebraMap ℚ_[p] K x) := by
  simp [Algebra.smul_def]

/-- R7.7b (descent infrastructure): for `p ∤ a` the extended logarithm of `(a : K)`
is the structure-map image of `extLog p (a : ℚ_[p])`. Both sides use the same Fermat
witness `(a)^{p−1} = p^0·(a)^{p−1}` (`inExpBall_natCast_pow_sub_one`), so the identity
reduces to `map_padicLog` on `(a)^{p−1}` and the `ℚ_[p]`-scalar pull-through. -/
private theorem map_extLog_natCast (hp2 : p ≠ 2) {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) :
    extLog p ((a : K)) = algebraMap ℚ_[p] K (extLog p ((a : ℚ_[p]))) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  rw [extLog_eq_of_witness p (m := p - 1) (k := 0) (by omega) (by rw [zpow_zero, one_mul])
      (inExpBall_natCast_pow_sub_one (p := p) K hp2 ha),
    extLog_eq_of_witness p (m := p - 1) (k := 0) (by omega) (by rw [zpow_zero, one_mul])
      (inExpBall_natCast_pow_sub_one (p := p) ℚ_[p] hp2 ha),
    map_smul_padic (p := p) K, map_padicLog (p := p) K, map_pow, map_natCast]

omit [CharZero K] in
/-- R7.7c (descent infrastructure, the mass identification): the `K`-mass
`𝓐(ρ_a)(0)` is the structure-map image of the `ℚ_[p]`-coercion of the `ℤ_p`-mass
`zetaNum p a 1`. Unfolds `mahlerK = map subtype ∘ 𝓐`, peels the constant
coefficient to `ρ_a(mahlerCM 0)`, and identifies through `baseChange_algCM`
(`mahler 0 = 1`) and `iota = pushforward unitsValCM` (`1 ∘ unitsValCM = 1`); the
`subtype ∘ algebraMap ℤ_[p]` composite is `algebraMap ℚ_[p] K ∘ (↑·)` definitionally. -/
private theorem constantCoeff_mahlerK_rhoA_eq_algebraMap (a : ℕ) :
    PowerSeries.constantCoeff (mahlerK p K (rhoA p K a))
      = algebraMap ℚ_[p] K
          (((PadicMeasure.zetaNum p a (1 : C(ℤ_[p]ˣ, ℤ_[p]))) : ℤ_[p]) : ℚ_[p]) := by
  rw [mahlerK, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    MeasureR.coeff_mahlerTransform, rhoA,
    show MeasureR.mahlerCM p K 0 = MeasureR.algCM K (mahler 0) from
      (MeasureR.algCM_mahler _ _).symm,
    MeasureR.baseChange_algCM]
  change algebraMap ℚ_[p] K
      ((PadicMeasure.iota p (PadicMeasure.zetaNum p a) (mahler 0) : ℤ_[p]) : ℚ_[p]) = _
  congr 2
  rw [PadicMeasure.iota, PadicMeasure.pushforward_apply]
  congr 1
  ext u
  rw [ContinuousMap.comp_apply, mahler_apply, Ring.choose_zero_right]
  rfl

end mass

section descent

/-- R7.7 (eq:zeta p residue 2 + Lemma 7.5, descended to `ℚ_p`): the total
mass of the §4 numerator measure —
`∫_{ℤ_p^×} x⁻¹·μ_a = −(1−p⁻¹)·log_p(a)` (computed in `ℂ_p` and pulled
back along the injective structure map). -/
theorem zetaNum_one (hp2 : p ≠ 2) {a : ℕ} (ha : ¬ (p : ℕ) ∣ a)
    (ha0 : a ≠ 0) :
    (((PadicMeasure.zetaNum p a (1 : C(ℤ_[p]ˣ, ℤ_[p]))) : ℤ_[p]) : ℚ_[p])
      = -(1 - (p : ℚ_[p])⁻¹) * extLog p (((a : ℕ) : ℚ_[p])) := by
  -- `ℂ_[p]` contains a primitive `p`-th root of unity (alg. closed + char `0`)
  haveI : NeZero (p : ℂ_[p]) :=
    ⟨(Nat.cast_ne_zero (R := ℂ_[p])).mpr hp.out.ne_zero⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p
  -- descend by injectivity of the structure map `ℚ_p ↪ ℂ_p`
  refine (algebraMap ℚ_[p] ℂ_[p]).injective ?_
  -- the `ℂ_p`-mass identifies with the image of the `ℤ_p`-mass; compute it in `ℂ_p`
  rw [← constantCoeff_mahlerK_rhoA_eq_algebraMap (p := p) ℂ_[p] a,
    constantCoeff_mahlerK_rhoA (p := p) ℂ_[p] hp2 ha ha0 hξ,
    map_mul, map_neg, map_sub, map_one, map_inv₀, map_natCast,
    map_extLog_natCast (p := p) ℂ_[p] hp2 ha]

/-- The angle bracket `⟨u⟩` of a topological generator is nontrivial:
`(angleUnit p u : ℤ_[p]) ≠ 1`. If it were `1` then `u = ω(u)·⟨u⟩ = ω(u)`, so
`u^{p−1} = 1`, forcing `orderOf (unitsToZModPow p 2 u) ∣ p−1`; but `hgen 2`
makes that order `φ(p²) = p(p−1)`, and `p(p−1) ∣ p−1` is impossible. -/
private lemma angleUnit_coe_ne_one {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u) = ⊤) :
    (PadicInt.angleUnit p u : ℤ_[p]) ≠ 1 := by
  intro h
  -- `⟨u⟩ = 1` at the units level (coe-injective)
  have hau1 : PadicInt.angleUnit p u = 1 := Units.ext (by rw [h, Units.val_one])
  -- so `u = ω(u)` and `u^{p−1} = ω(u)^{p−1} = 1`
  have hueq : u = PadicInt.teichmuller p u := by
    conv_lhs => rw [← PadicInt.teichmuller_mul_angleUnit p u, hau1, mul_one]
  have hpow1 : u ^ (p - 1) = 1 := by
    rw [hueq]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
      PadicInt.teichmullerFun_pow_card_sub_one, Units.val_one])
  -- the level-2 reduction then has order dividing `p−1`
  have himg : (PadicMeasure.unitsToZModPow p 2 u) ^ (p - 1) = 1 := by
    rw [← map_pow, hpow1, map_one]
  have hdvd : orderOf (PadicMeasure.unitsToZModPow p 2 u) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one himg
  -- but `hgen 2` forces that order to be `φ(p²) = p(p−1)`
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have ho2 : orderOf (PadicMeasure.unitsToZModPow p 2 u) = p ^ (2 - 1) * (p - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers fun x => hgen 2 ▸ Subgroup.mem_top x,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp.out two_pos]
  rw [ho2, pow_one] at hdvd
  -- `p(p−1) ∣ p−1` is impossible (`p ≥ 2`, `p − 1 > 0`)
  have hp1 : 0 < p - 1 := by have := hp.out.one_lt; omega
  have hle := Nat.le_of_dvd hp1 hdvd
  have hp2le : 2 ≤ p := hp.out.two_le
  nlinarith [hp1, hp2le]

/-- `log_p⟨u⟩ ≠ 0` for a topological generator `u`: via the T523 bridge
`exp(1·log⟨u⟩) = ⟨u⟩`, so `log⟨u⟩ = 0` would give `⟨u⟩ = exp 0 = 1`,
contradicting `angleUnit_coe_ne_one`. -/
private lemma pZpLog_angleUnit_ne_zero (hp2 : p ≠ 2) {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u) = ⊤) :
    pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) ≠ 0 := by
  intro hL
  -- `⟨u⟩ = exp(1·log⟨u⟩) = exp 0 = 1`
  have hbridge := padicExp_smul_padicLog_eq_onePAdicPow p hp2
    (PadicInt.angleUnit_sub_one_mem p u) 1
  rw [PadicInt.onePAdicPow_apply_one, hL, mul_zero] at hbridge
  have hexp0 : pZpExp p (0 : ℤ_[p]) = 1 := by
    refine PadicInt.ext ?_
    rw [pZpExp_coe p hp2 (Ideal.zero_mem _), PadicInt.coe_zero, padicExp_zero, PadicInt.coe_one]
  rw [hexp0] at hbridge
  exact angleUnit_coe_ne_one p hgen (by rw [← hbridge])

/-- The extended logarithm of `(m : ℚ_[p])` equals the `ℚ_[p]`-coercion of
`log_p⟨u⟩`, where `m` and `u` are the topological-generator data with
`(u : ℤ_[p]) = (m : ℤ_[p])`. Via `u = ω(u)·⟨u⟩`, `extLog_mul`, and
`extLog ω = 0` (it is a `(p−1)`-th root of unity). -/
private lemma extLog_natCast_eq_pZpLog_angle (hp2 : p ≠ 2) {m : ℕ} {u : ℤ_[p]ˣ}
    (huv : (u : ℤ_[p]) = (m : ℤ_[p])) :
    extLog p ((m : ℚ_[p]))
      = ((pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) := by
  have hp1 : 0 < p - 1 := by have := hp.out.one_lt; omega
  -- `(m : ℚ_[p]) = (u : ℚ_[p]) = ω·⟨u⟩` (coerced)
  have hmq : ((m : ℕ) : ℚ_[p]) = (((u : ℤ_[p])) : ℚ_[p]) := by
    rw [huv, PadicInt.coe_natCast]
  have hsplit : (((u : ℤ_[p])) : ℚ_[p])
      = (((PadicInt.teichmuller p u : ℤ_[p])) : ℚ_[p])
        * (((PadicInt.angleUnit p u : ℤ_[p])) : ℚ_[p]) := by
    rw [← PadicInt.coe_mul, ← Units.val_mul, PadicInt.teichmuller_mul_angleUnit]
  -- `ω`-coe lies in the domain (it is a `(p−1)`-th root of unity)
  have hωpow : (((PadicInt.teichmuller p u : ℤ_[p])) : ℚ_[p]) ^ (p - 1) = 1 := by
    rw [← PadicInt.coe_pow, ← Units.val_pow_eq_pow_val,
      show (PadicInt.teichmuller p u) ^ (p - 1) = 1 from Units.ext (by
        rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
          PadicInt.teichmullerFun_pow_card_sub_one, Units.val_one]),
      Units.val_one, PadicInt.coe_one]
  have hωdom : ExtLogDomain p (((PadicInt.teichmuller p u : ℤ_[p])) : ℚ_[p]) :=
    ⟨p - 1, 0, 1, hp1, by rw [hωpow, zpow_zero, one_mul], inExpBall_one_sub_one p⟩
  -- `⟨u⟩`-coe lies in the domain (it is in `1 + pℤ_p`, the exp ball)
  have hanball : InExpBall p ((((PadicInt.angleUnit p u : ℤ_[p])) : ℚ_[p]) - 1) := by
    rw [show ((((PadicInt.angleUnit p u : ℤ_[p])) : ℚ_[p]) - 1)
        = (((PadicInt.angleUnit p u : ℤ_[p]) - 1 : ℤ_[p]) : ℚ_[p]) by
      rw [PadicInt.coe_sub, PadicInt.coe_one]]
    exact inExpBall_of_mem_span p hp2 (PadicInt.angleUnit_sub_one_mem p u)
  have handom : ExtLogDomain p (((PadicInt.angleUnit p u : ℤ_[p])) : ℚ_[p]) :=
    ⟨1, 0, _, one_pos, by rw [pow_one, zpow_zero, one_mul], hanball⟩
  rw [hmq, hsplit, extLog_mul p hωdom handom,
    extLog_eq_zero_of_pow_eq_one p hp1 hωpow, zero_add,
    extLog_eq_padicLog p hanball, ← pZpLog_coe p hp2 (PadicInt.angleUnit_sub_one_mem p u)]

/-- **RJW Theorem 7.1(ii)** (`thm:residue`, TeX 2191–2192): "The function
`ζ_{p,p−1}` has a simple pole at `s = 1` with residue `1 − p⁻¹`" — as the
topological limit `lim_{s→1, s≠1} (s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹`. -/
theorem tendsto_sub_one_mul_zetaPBranch (hp2 : p ≠ 2) :
    Filter.Tendsto
      (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1) * zetaPBranch p hp2 (p - 1) s)
      (nhdsWithin 1 {s | s ≠ 1})
      (nhds (1 - (p : ℚ_[p])⁻¹)) := by
  classical
  obtain ⟨hpm, huv, hgen⟩ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec
  set m := (PadicMeasure.exists_nat_topological_generator p hp2).choose with hm_def
  set u := (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose with hu_def
  set Lq : ℚ_[p] := ((pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) with hLq
  -- shorthands for the denominator and numerator
  set denom : ℤ_[p] → ℚ_[p] :=
    fun s => (((branchChar p (p - 1) (1 - s) u : ℤ_[p]) : ℚ_[p]) - 1) with hdenom
  set num : ℤ_[p] → ℚ_[p] :=
    fun s => ((PadicMeasure.zetaNum p m (branchChar p (p - 1) (1 - s)) : ℤ_[p]) : ℚ_[p])
    with hnum
  -- Step 1: `Lq ≠ 0`
  have hL0 : pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) ≠ 0 :=
    pZpLog_angleUnit_ne_zero p hp2 hgen
  have hLq0 : Lq ≠ 0 := by rw [hLq, Ne, PadicInt.coe_eq_zero]; exact hL0
  -- Step 2: denominator limit and its inverse
  have hden : Filter.Tendsto (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1)⁻¹ * denom s)
      (nhdsWithin 1 {s | s ≠ 1}) (nhds (-Lq)) := by
    rw [hLq]; exact tendsto_branch_denom_div p hp2 (u := u)
  have hinv : Filter.Tendsto (fun s : ℤ_[p] => (((s : ℚ_[p]) - 1)⁻¹ * denom s)⁻¹)
      (nhdsWithin 1 {s | s ≠ 1}) (nhds (-Lq)⁻¹) :=
    hden.inv₀ (neg_ne_zero.mpr hLq0)
  -- Step 3: numerator limit
  have hnumlim : Filter.Tendsto num (nhdsWithin 1 {s | s ≠ 1}) (nhds (num 1)) :=
    ((continuous_zetaNum_branch_pairing p m (p - 1)).continuousAt
      (x := 1)).mono_left nhdsWithin_le_nhds
  -- Step 4: the value `num 1`
  have hbr1 : branchChar p (p - 1) (1 - 1) = (1 : C(ℤ_[p]ˣ, ℤ_[p])) := by
    refine ContinuousMap.ext fun x => ?_
    rw [sub_self, branchChar_apply]
    have hωpow : (PadicInt.teichmuller p x : ℤ_[p]) ^ (p - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val,
        show (PadicInt.teichmuller p x) ^ (p - 1) = 1 from Units.ext (by
          rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
            PadicInt.teichmullerFun_pow_card_sub_one, Units.val_one]),
        Units.val_one]
    rw [hωpow, one_mul, AddChar.map_zero_eq_one, ContinuousMap.one_apply]
  have hnum1 : num 1 = -(1 - (p : ℚ_[p])⁻¹) * extLog p ((m : ℚ_[p])) := by
    have hm0 : m ≠ 0 := fun h => hpm (by rw [h]; exact dvd_zero p)
    simp only [hnum]
    rw [hbr1, zetaNum_one p hp2 hpm hm0]
  -- Step 5: `extLog p (m:ℚ_[p]) = Lq`
  have hextlog : extLog p ((m : ℚ_[p])) = Lq := by
    rw [hLq]; exact extLog_natCast_eq_pZpLog_angle p hp2 huv
  -- Step 6: assemble the limit value
  have hval : (-Lq)⁻¹ * num 1 = 1 - (p : ℚ_[p])⁻¹ := by
    rw [hnum1, hextlog, show (-Lq)⁻¹ = -(Lq⁻¹) from (neg_inv ..).symm]
    field_simp
  -- the product limit, congruent to the target function
  have htend : Filter.Tendsto
      (fun s : ℤ_[p] => (((s : ℚ_[p]) - 1)⁻¹ * denom s)⁻¹ * num s)
      (nhdsWithin 1 {s | s ≠ 1}) (nhds ((-Lq)⁻¹ * num 1)) := hinv.mul hnumlim
  rw [hval] at htend
  refine htend.congr fun s => ?_
  -- pointwise: `((s−1)⁻¹·denom)⁻¹·num = (s−1)·ζ_{p,p−1}(s)`
  simp only [hdenom, hnum, zetaPBranch]
  rw [mul_inv_rev, inv_inv]
  ring

end descent

end PadicLFunctions
