import BernoulliRegular.IrregularPrimes.VonStaudtConsequences
import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonLemma96Proof

/-!
# T-KELLNER-POWERSUM: `NoSecondOrderIrregularPair 37 32`, proven, and unconditional FLT37

This file **proves** the carried Kellner boundary `NoSecondOrderIrregularPair 37 32`
(`¬ 37³ ∣ B₁₁₈₄.num`) by the **Faulhaber power-sum method**, and concludes the
unconditional `FermatLastTheoremFor 37`.

## The method

The kernel computes `S := ∑_{a < 37²} a^1184` modulo `37⁵` by `decide`
(GMP-backed `Nat` arithmetic): `S ≡ 2·37⁴ (mod 37⁵)`.

Faulhaber's formula (mathlib `sum_range_pow`) at `n = 37²`, `p = 1184` gives
`S = ∑_{i ≤ 1184} B_i · C(1185, i) · (37²)^{1185-i} / 1185`. The `i = 1184` term is
`37² · B₁₁₈₄` (using `C(1185, 1184) = 1185`), the `i = 1183` term vanishes
(`B₁₁₈₃ = 0`, odd index), and every term with `i ≤ 1182` carries
`(37²)^{1185-i} = 37^{2(1185-i)}` with `2(1185 - i) ≥ 6`, so the tail is
`37⁵ · R` where `R` is **37-integral** (`¬ 37 ∣ R.den`) — the von Staudt–Clausen
bound `v₃₇(B_i) ≥ -1` (i.e. `37 · B_i` is 37-integral) absorbs the worst
denominator, and `37 ∤ 1185`.

Hence `37² · B₁₁₈₄ = S - 37⁵ · R ≡ 2·37⁴ (mod 37⁵ · ℤ₍₃₇₎)`, i.e.
`B₁₁₈₄ = 2·37² + 37³ · W` with `W` 37-integral. Since `37 ∤ B₁₁₈₄.den`
(von Staudt–Clausen: `36 ∤ 1184`), `37³ ∣ B₁₁₈₄.num` would make
`2/37 = B₁₁₈₄/37³ - W` 37-integral — contradiction.

This replaces the parametric `KellnerProp27_thirtyseven_thirtytwo` route of
`BernoulliFast/KellnerSecondOrder.lean` with a proof, so the FLT37 endpoint
`fermatLastTheoremFor_thirtyseven_of_kellner` now closes unconditionally.
-/

@[expose] public section

namespace BernoulliRegular

/-! ## The kernel power-sum computation

`∑_{a < 1369} a^1184 ≡ 3748322 (mod 37⁵)`, with `1369 = 37²` and `3748322 = 2·37⁴`.
Plain `decide`: the kernel evaluates the 1369-term sum with GMP `Nat` arithmetic. -/

set_option exponentiation.threshold 2000 in
set_option maxRecDepth 4000000 in
theorem kellnerPowerSum_mod_pow_five :
    ((Finset.range 1369).sum (fun a => a ^ (1184 : ℕ))) % (37 ^ 5) = 3748322 := by
  decide

/-! ## 37-integrality mini-API

A rational `x` is *37-integral* iff `¬ 37 ∣ x.den`. We record closure under
addition, subtraction, multiplication, finite sums, and division by naturals
prime to `37`. -/

theorem thirtyseven_nat_prime : Nat.Prime 37 := by norm_num

theorem den_add_not_dvd_thirtyseven {x y : ℚ} (hx : ¬ 37 ∣ x.den) (hy : ¬ 37 ∣ y.den) :
    ¬ 37 ∣ (x + y).den := by
  intro h
  rcases (Nat.Prime.dvd_mul thirtyseven_nat_prime).mp (h.trans (Rat.add_den_dvd x y)) with h' | h'
  exacts [hx h', hy h']

theorem den_sub_not_dvd_thirtyseven {x y : ℚ} (hx : ¬ 37 ∣ x.den) (hy : ¬ 37 ∣ y.den) :
    ¬ 37 ∣ (x - y).den := by
  intro h
  rcases (Nat.Prime.dvd_mul thirtyseven_nat_prime).mp (h.trans (Rat.sub_den_dvd x y)) with h' | h'
  exacts [hx h', hy h']

theorem den_mul_not_dvd_thirtyseven {x y : ℚ} (hx : ¬ 37 ∣ x.den) (hy : ¬ 37 ∣ y.den) :
    ¬ 37 ∣ (x * y).den := by
  intro h
  rcases (Nat.Prime.dvd_mul thirtyseven_nat_prime).mp (h.trans (Rat.mul_den_dvd x y)) with h' | h'
  exacts [hx h', hy h']

theorem den_sum_not_dvd_thirtyseven {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, ¬ 37 ∣ (f i).den) : ¬ 37 ∣ (∑ i ∈ s, f i).den := by
  intro hdvd
  obtain ⟨i, hi, hd⟩ := (thirtyseven_nat_prime.prime.dvd_finsetProd_iff
    (fun i => (f i).den)).mp (hdvd.trans (Finset.Rat.den_sum_dvd_prod_den s f))
  exact h i hi hd

theorem den_one_div_natCast_dvd (n : ℕ) : ((1 : ℚ) / (n : ℚ)).den ∣ n := by
  have h : (1 : ℚ) / (n : ℚ) = Rat.divInt 1 (n : ℤ) := by
    rw [Rat.divInt_eq_div]
    norm_num
  rw [h]
  exact_mod_cast Rat.den_dvd 1 (n : ℤ)

theorem den_thirtyseven_eq_one : (37 : ℚ).den = 1 := by
  rw [show (37 : ℚ) = ((37 : ℕ) : ℚ) by norm_num, Rat.den_natCast]

theorem den_div_natCast_not_dvd_thirtyseven {x : ℚ} (hx : ¬ 37 ∣ x.den) {n : ℕ}
    (hn : ¬ 37 ∣ n) : ¬ 37 ∣ (x / (n : ℚ)).den := by
  rw [div_eq_mul_inv, ← one_div]
  exact den_mul_not_dvd_thirtyseven hx fun h => hn (h.trans (den_one_div_natCast_dvd n))

theorem den_pow_thirtyseven_not_dvd (e : ℕ) : ¬ 37 ∣ ((37 : ℚ) ^ e).den := by
  have h : (37 : ℚ) ^ e = ((37 ^ e : ℕ) : ℚ) := by norm_cast
  rw [h, Rat.den_natCast]
  norm_num

/-! ## The von Staudt–Clausen ingredients

`37 · B_i` is 37-integral for every `i` (the correction sum contributes at worst
one factor `37` in the denominator), and `B₁₁₈₄` itself is 37-integral
(`36 = 37 - 1` does not divide `1184`). -/

theorem den_thirtyseven_mul_bernoulli_not_dvd (i : ℕ) :
    ¬ 37 ∣ ((37 : ℚ) * bernoulli i).den := by
  rcases Nat.even_or_odd i with he | ho
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [bernoulli_zero, mul_one]
      norm_num
    · obtain ⟨T, hT⟩ := bernoulli_add_vonStaudtCorrection_mem_int he
      have hsum : (37 : ℚ) * bernoulli i =
          ((37 * T : ℤ) : ℚ) - ∑ q ∈ vonStaudtPrimesFor i, (37 : ℚ) * ((1 : ℚ) / q) := by
        rw [← Finset.mul_sum]
        push_cast
        linarith [hT]
      rw [hsum]
      refine den_sub_not_dvd_thirtyseven ?_ ?_
      · rw [Rat.den_intCast]
        norm_num
      · refine den_sum_not_dvd_thirtyseven fun q hq => ?_
        have hq' : q.Prime := by
          rw [vonStaudtPrimesFor, Finset.mem_filter] at hq
          exact hq.2.1
        rcases eq_or_ne q 37 with rfl | hne
        · rw [show (37 : ℚ) * ((1 : ℚ) / ((37 : ℕ) : ℚ)) = 1 by norm_num]
          norm_num
        · intro hd
          have h2 := Rat.mul_den_dvd (37 : ℚ) ((1 : ℚ) / (q : ℚ))
          rw [den_thirtyseven_eq_one, one_mul] at h2
          have h3 : 37 ∣ q := hd.trans (h2.trans (den_one_div_natCast_dvd q))
          exact hne (((Nat.prime_dvd_prime_iff_eq thirtyseven_nat_prime hq').mp h3).symm)
  · rcases eq_or_ne i 1 with rfl | hne
    · rw [bernoulli_one]
      intro hd
      have h2 := Rat.mul_den_dvd (37 : ℚ) (-1 / 2 : ℚ)
      rw [den_thirtyseven_eq_one, one_mul] at h2
      have hhalf : ((-1 / 2 : ℚ)).den ∣ 2 := by
        have h : (-1 / 2 : ℚ) = ((-1 : ℤ) : ℚ) / (((2 : ℕ) : ℤ) : ℚ) := by push_cast; ring
        rw [h, Rat.intCast_div_eq_divInt]
        exact_mod_cast Rat.den_dvd (-1) ((2 : ℕ) : ℤ)
      have h3 : (37 : ℕ) ∣ 2 := hd.trans (h2.trans hhalf)
      omega
    · have h1 : 1 < i := by
        rcases ho with ⟨k, hk⟩
        omega
      rw [bernoulli_eq_zero_of_odd ho h1, mul_zero]
      decide

theorem den_bernoulli_1184_not_dvd : ¬ 37 ∣ (bernoulli 1184).den := by
  obtain ⟨T, hT⟩ := bernoulli_add_vonStaudtCorrection_mem_int (n := 1184) (by norm_num)
  have hC : ¬ 37 ∣ (∑ q ∈ vonStaudtPrimesFor 1184, (1 : ℚ) / q).den :=
    vonStaudtCorrection_den_not_dvd_of_not_sub_one_dvd thirtyseven_nat_prime (by norm_num)
  have hB : bernoulli 1184 = (T : ℚ) - ∑ q ∈ vonStaudtPrimesFor 1184, (1 : ℚ) / q := by
    linarith [hT]
  rw [hB]
  refine den_sub_not_dvd_thirtyseven ?_ hC
  rw [Rat.den_intCast]
  norm_num

/-! ## The Faulhaber bridge

`∑_{k < 1369} k^1184 = 37² · B₁₁₈₄ + 37⁵ · R` in `ℚ`, with `R` 37-integral. -/

theorem exists_faulhaber_decomposition_1184 :
    ∃ R : ℚ, ¬ 37 ∣ R.den ∧
      (∑ k ∈ Finset.range 1369, (k : ℚ) ^ 1184)
        = 37 ^ 2 * bernoulli 1184 + 37 ^ 5 * R := by
  refine ⟨∑ i ∈ Finset.range 1183,
      37 * bernoulli i * ((Nat.choose 1185 i : ℕ) : ℚ) * (37 : ℚ) ^ (2 * (1185 - i) - 6)
        / ((1185 : ℕ) : ℚ), ?_, ?_⟩
  · refine den_sum_not_dvd_thirtyseven fun i _ => ?_
    refine den_div_natCast_not_dvd_thirtyseven ?_ (by norm_num)
    refine den_mul_not_dvd_thirtyseven
      (den_mul_not_dvd_thirtyseven (den_thirtyseven_mul_bernoulli_not_dvd i) ?_)
      (den_pow_thirtyseven_not_dvd _)
    rw [Rat.den_natCast]
    norm_num
  · have hterm : ∀ i ∈ Finset.range 1183,
        bernoulli i * ((1184 + 1).choose i : ℚ) * ((1369 : ℕ) : ℚ) ^ (1184 + 1 - i)
            / (((1184 : ℕ) : ℚ) + 1)
          = 37 ^ 5 * (37 * bernoulli i * ((Nat.choose 1185 i : ℕ) : ℚ)
              * (37 : ℚ) ^ (2 * (1185 - i) - 6) / ((1185 : ℕ) : ℚ)) := by
      intro i hi
      have hi' : i < 1183 := Finset.mem_range.mp hi
      rw [show ((1184 : ℕ) + 1) = 1185 from rfl,
        show ((1369 : ℕ) : ℚ) = (37 : ℚ) ^ 2 by norm_num,
        show (((1184 : ℕ) : ℚ) + 1) = ((1185 : ℕ) : ℚ) by norm_num, ← pow_mul]
      have hexp : (37 : ℚ) ^ (2 * (1185 - i)) = 37 ^ 5 * 37 ^ (2 * (1185 - i) - 6) * 37 := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      rw [hexp]
      ring
    rw [sum_range_pow]
    rw [Finset.sum_range_succ]
    rw [show Finset.range 1184 = Finset.range (1183 + 1) from rfl, Finset.sum_range_succ]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    rw [show bernoulli 1183 = 0 from bernoulli_eq_zero_of_odd (by norm_num) (by norm_num)]
    rw [show ((1184 : ℕ) + 1 - 1183) = 2 from rfl, show ((1184 : ℕ) + 1 - 1184) = 1 from rfl]
    rw [Nat.choose_succ_self_right]
    rw [show ((1184 : ℕ) + 1) = 1185 from rfl]
    rw [show ((1369 : ℕ) : ℚ) = (37 : ℚ) ^ 2 by norm_num,
      show (((1184 : ℕ) : ℚ) + 1) = (1185 : ℚ) by norm_num,
      show ((1185 : ℕ) : ℚ) = (1185 : ℚ) by norm_num]
    ring

/-! ## Extracting `B₁₁₈₄ = 2·37² + 37³·W` with `W` 37-integral -/

theorem exists_bernoulli_1184_decomposition :
    ∃ W : ℚ, ¬ 37 ∣ W.den ∧ bernoulli 1184 = 37 ^ 3 * W + 2 * 37 ^ 2 := by
  obtain ⟨R, hRden, hF⟩ := exists_faulhaber_decomposition_1184
  set S : ℕ := (Finset.range 1369).sum (fun a => a ^ (1184 : ℕ)) with hSdef
  have hmod : S % 37 ^ 5 = 3748322 := kellnerPowerSum_mod_pow_five
  have hdm : (S : ℚ) = 37 ^ 5 * ((S / 37 ^ 5 : ℕ) : ℚ) + 3748322 := by
    have h0 : 37 ^ 5 * (S / 37 ^ 5) + 3748322 = S := by
      conv_rhs => rw [← Nat.div_add_mod S (37 ^ 5)]
      rw [hmod]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) h0.symm
  have hSQ : (S : ℚ) = ∑ k ∈ Finset.range 1369, (k : ℚ) ^ 1184 := by
    rw [hSdef]
    push_cast
    rfl
  refine ⟨((S / 37 ^ 5 : ℕ) : ℚ) - R,
    den_sub_not_dvd_thirtyseven (by rw [Rat.den_natCast]; norm_num) hRden, ?_⟩
  linear_combination (hdm - hSQ - hF) / 1369

/-! ## The 37-adic contradiction and the Kellner target -/

theorem thirtyseven_dvd_den_two_div_thirtyseven : 37 ∣ ((2 : ℚ) / 37).den := by
  have hdvd : ((2 : ℚ) / 37).den ∣ 37 := by
    have h : (2 : ℚ) / 37 = ((2 : ℤ) : ℚ) / (((37 : ℕ) : ℤ) : ℚ) := by push_cast; ring
    rw [h, Rat.intCast_div_eq_divInt]
    exact_mod_cast Rat.den_dvd 2 ((37 : ℕ) : ℤ)
  rcases (Nat.dvd_prime thirtyseven_nat_prime).mp hdvd with h1 | h37
  · exfalso
    have hint : ((((2 : ℚ) / 37).num : ℤ) : ℚ) = (2 : ℚ) / 37 :=
      Rat.coe_int_num_of_den_eq_one h1
    have h2 : (37 : ℚ) * ((((2 : ℚ) / 37).num : ℤ) : ℚ) = 2 := by
      rw [hint]
      norm_num
    have h3 : (37 : ℤ) * ((2 : ℚ) / 37).num = 2 := by exact_mod_cast h2
    omega
  · rw [h37]

theorem den_div_thirtyseven_pow_three_dvd {x : ℚ} (h : (37 : ℤ) ^ 3 ∣ x.num) :
    (x / (37 : ℚ) ^ 3).den ∣ x.den := by
  obtain ⟨c, hc⟩ := h
  have h0 : x = (37 : ℚ) ^ 3 * ((c : ℚ) / (x.den : ℚ)) := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [hc]
    push_cast
    ring
  have hxc : x / (37 : ℚ) ^ 3 = (c : ℚ) / (x.den : ℚ) := by
    conv_lhs => rw [h0]
    exact mul_div_cancel_left₀ _ (by norm_num)
  rw [hxc]
  have h1 : (c : ℚ) / (x.den : ℚ) = (c : ℚ) / (((x.den : ℕ) : ℤ) : ℚ) := by
    norm_cast
  rw [h1, Rat.intCast_div_eq_divInt]
  exact_mod_cast Rat.den_dvd c ((x.den : ℕ) : ℤ)

/-- **The Kellner second-order target, proven**: `37³ ∤ B₁₁₈₄.num`
(`1184 = 32 · 37`), by the Faulhaber power-sum method. -/
theorem noSecondOrderIrregularPair_thirtyseven_thirtytwo :
    NoSecondOrderIrregularPair 37 32 := by
  unfold NoSecondOrderIrregularPair
  rw [show (32 * 37 : ℕ) = 1184 by norm_num]
  intro hdvd
  obtain ⟨W, hW, hB⟩ := exists_bernoulli_1184_decomposition
  have hkey : (2 : ℚ) / 37 = bernoulli 1184 / (37 : ℚ) ^ 3 - W := by
    rw [hB]
    field_simp
    ring
  have hsubden := Rat.sub_den_dvd (bernoulli 1184 / (37 : ℚ) ^ 3) W
  rw [← hkey] at hsubden
  rcases (Nat.Prime.dvd_mul thirtyseven_nat_prime).mp
    (thirtyseven_dvd_den_two_div_thirtyseven.trans hsubden) with h | h
  · exact den_bernoulli_1184_not_dvd (h.trans (den_div_thirtyseven_pow_three_dvd hdvd))
  · exact hW h

/-- **Fermat's Last Theorem for `p = 37`, unconditional**: the carried Kellner
input of `fermatLastTheoremFor_thirtyseven_of_kellner` is now the proven
`noSecondOrderIrregularPair_thirtyseven_thirtytwo`. -/
theorem fermatLastTheoremFor_thirtyseven : FermatLastTheoremFor 37 :=
  FLT37.Eichler.fermatLastTheoremFor_thirtyseven_of_kellner
    noSecondOrderIrregularPair_thirtyseven_thirtytwo

end BernoulliRegular

end
