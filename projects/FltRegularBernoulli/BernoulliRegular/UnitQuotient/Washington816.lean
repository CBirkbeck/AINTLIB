import BernoulliRegular.UnitQuotient.Washington814ForwardD
import BernoulliRegular.CyclotomicUnits.KummerLogDeterminant
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.RealPthRootDescent

/-!
# Washington Theorem 8.16 (class form): `[pollaczekUnit i]_{mod 37} = 0 ⟹ 37 ∣ B_i`

This is the remaining §8.3 analytic boundary after the forward step `Washington814Forward37`
was discharged by the eigenspace/index bridge of `Washington814ForwardD.lean`.

The strategy (reviewer Target 2, finite-sum form, avoiding the full Kubota–Leopoldt
`L_p`): write `pollaczekUnitPlusKplus i` as a `CPlusExponentProduct` whose exponent vector
is the Pollaczek/Vandermonde column `e_a = (a+2)^{p-1-i}`.  If `[pollaczekUnit i] = 0` then
this product is a 37-th power (modulo torsion, which the completed logarithm kills), so the
completed-log relation gives `concreteKummerLogMatrix.mulVec (e mod 37) = 0`.  Because
`concreteKummerLogMatrix = diag(rowFactor) · Vandermonde` and the `rowFactor`s are the
Bernoulli factors (`kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero`), the `i`-th
component forces `rowFactor_i = 0`, i.e. `bernoulliFactor 37 i = 0`, i.e. `37 ∣ B_i`
(`bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num`).

This file is under construction: the entry identity (Pollaczek unit as exponent product)
is established first.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.3 Thm 8.16, Cor 5.13.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

open CyclotomicUnits

namespace FLT37

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [hp37 : Fact (Nat.Prime 37)] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The `K⁺`-side symmetrised Pollaczek unit is the sign-free `CPlusExponentProduct` whose
exponent vector is the Pollaczek/Vandermonde column `e_a = (a+2)^{p-1-i}`. -/
theorem pollaczekUnitPlusKplus_eq_CPlusExponentProduct (i : ℕ) :
    Sinnott.pollaczekUnitPlusKplus 37 K i (by norm_num) (by norm_num) =
      CPlusExponentProduct (p := 37) (K := K) (by norm_num) 0
        (fun a : Fin ((37 - 3) / 2) => ((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) := by
  have h_rank_eq :
      NumberField.Units.rank (NumberField.maximalRealSubfield K) = (37 - 3) / 2 :=
    (NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
      (BernoulliRegular.units_rank_eq_prime_sub_three_div_two (p := 37) (K := K))
  rw [CPlusExponentProduct, zpow_zero, one_mul, Sinnott.pollaczekUnitPlusKplus]
  refine Fintype.prod_equiv (finCongr h_rank_eq)
      (fun j => Sinnott.cyclotomicUnitFamilyKplusFinRank 37 K (by norm_num) (by norm_num) j ^
        (((j : ℕ) + 2) ^ (37 - 1 - i)))
      (fun a : Fin ((37 - 3) / 2) =>
        CPlusGenerator (p := 37) (K := K) (by norm_num) a ^
          ((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) ?_
  intro j
  rw [zpow_natCast, finCongr_apply, Fin.val_cast]
  congr 1

/-- The Kummer log matrix acts on a vector componentwise as `rowFactor_j` times the
Vandermonde action, from `concreteKummerLogMatrix = diag(rowFactor) · Vandermonde`. -/
theorem concreteKummerLogMatrix_mulVec_apply
    (v : Fin (kummerLogRank 37) → ZMod 37) (j : Fin (kummerLogRank 37)) :
    (concreteKummerLogMatrix (p := 37) (K := K) (by norm_num) (by norm_num)).mulVec v j =
      kummerLogDetRowFactor (p := 37) j *
        (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec v j := by
  rw [concreteKummerLogMatrix_eq_diagonal_mul_vandermonde (p := 37) (K := K)
      (by norm_num) (by norm_num), ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

/-- **WF-816 (A): a vanishing bare class makes the K⁺ Pollaczek unit a 37-th power.**
By WF-814c (`pollaczekUnitPlus_isPthPower_of_pollaczekUnit_class_eq_zero`, whose realness
argument cancels the cyclotomic torsion) `pollaczekUnitPlus i = α^37` in `(𝓞 K)ˣ`; this `α`
is a `K`-level 37-th root of `algebraMap (pollaczekUnitPlusKplus i)`, so the real-`p`-th-root
descent `exists_real_unit_pow_eq_of_K_root` makes `pollaczekUnitPlusKplus i` a 37-th power in
`(𝓞 K⁺)ˣ`, i.e. a member of `pPowerSubgroup (EPlus) 37`. -/
theorem pollaczekUnitPlusKplus_mem_pPowerSubgroup_of_class_eq_zero (i : ℕ)
    (h : cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) = 0) :
    Sinnott.pollaczekUnitPlusKplus 37 K i (by norm_num) (by norm_num) ∈
      pPowerSubgroup (EPlus (K := K)) 37 := by
  obtain ⟨α, hα⟩ := pollaczekUnitPlus_isPthPower_of_pollaczekUnit_class_eq_zero i h
  obtain ⟨w, hw⟩ := LehmerVandiver.CaseI.exists_real_unit_pow_eq_of_K_root
    (p' := 37) (K' := K) (by norm_num)
    (Sinnott.pollaczekUnitPlusKplus 37 K i (by norm_num) (by norm_num)) ((α : 𝓞 K) : K)
    (by
      have hcompat :
          algebraMap (NumberField.maximalRealSubfield K) K
              ((Sinnott.pollaczekUnitPlusKplus 37 K i (by norm_num) (by norm_num) :
                𝓞 (NumberField.maximalRealSubfield K)) :
                NumberField.maximalRealSubfield K) =
            ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
              (Sinnott.pollaczekUnitPlusKplus 37 K i (by norm_num) (by norm_num) :
                𝓞 (NumberField.maximalRealSubfield K)) : 𝓞 K) : K) := rfl
      rw [hcompat,
        Sinnott.algebraMapPollaczekUnitPlusKplus_eq 37 K i (by norm_num) (by norm_num), hα]
      push_cast
      ring)
  exact ⟨w, Subgroup.mem_top w, hw.symm⟩

/-- **WF-816 (B+C): a vanishing bare class kills the Kummer-log matrix action** on the
Pollaczek exponent vector. From `pollaczekUnitPlusKplus i ∈ pPowerSubgroup` the completed-log
relation gives a `37`-divisible Kummer-log combination, whose mod-`37` matrix reduction is `0`. -/
theorem concreteKummerLogMatrix_mulVec_pollaczek_eq_zero (i : ℕ)
    (h : cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) = 0) :
    (concreteKummerLogMatrix (p := 37) (K := K) (by norm_num) (by norm_num)).mulVec
        (fun a : Fin (kummerLogRank 37) =>
          ((((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) : ZMod 37)) = 0 := by
  have hmem := pollaczekUnitPlusKplus_mem_pPowerSubgroup_of_class_eq_zero (K := K) i h
  rw [pollaczekUnitPlusKplus_eq_CPlusExponentProduct] at hmem
  refine concreteKummerLogMatrix_mulVec_exponents_eq_zero (p := 37) (K := K) (by norm_num)
    (by norm_num) (fun a => ((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) ?_
  simpa [concreteKummerLogVector] using
    completedLog_relation_of_CPlus_product_mem_powers (p := 37) (K := K) (by norm_num)
      (by norm_num) 0 (fun a => ((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) hmem

omit [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- Sum over all of `ZMod 37` rewritten as a sum over the residue range `0,…,36`. -/
theorem sum_zmod37_eq_sum_range (f : ZMod 37 → ZMod 37) :
    ∑ x : ZMod 37, f x = ∑ b ∈ Finset.range 37, f (b : ZMod 37) := by
  refine Finset.sum_nbij' (fun x => ZMod.val x) (fun b => (b : ZMod 37)) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro b _; exact Finset.mem_univ _
  · intro x _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro b hb
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
  · intro x _; rw [ZMod.natCast_val, ZMod.cast_id]

omit [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **The Pollaczek-range power sum `∑_a (a+2)^k ≡ -1 (mod 37)`** (even `0 < k < 36`).

Write `S = ∑_{b=2}^{18} b^k` (`= ∑_{a:Fin 17} (a+2)^k`, the Pollaczek range). The full sum
over `ZMod 37` vanishes; splitting `{0,…,36}` as `{0,1} ∪ {2,…,18} ∪ {19,…,35} ∪ {36}` and
reflecting `{19,…,35}` onto `{2,…,18}` via `b ↦ 37 - b` (negation, `k` even) gives
`1 + S + S + 1 = 0`, i.e. `2(S + 1) = 0`, so `S = -1`.

Everything is combined **inside this single lemma**: combining two ZMod-37 sum equalities
across lemma boundaries makes the `Fact (Nat.Prime 37) → Field` instance whnf-loop on the
shared `∑ … (↑b)^k` term. Here `S` appears twice from same-elaboration pieces, so it combines
via `← two_mul` exactly as the matched copies do. -/
theorem sum_fin_add_two_pow_eq_neg_one {k : ℕ} (hk_even : Even k) (hk_pos : 0 < k)
    (hk : k < 36) :
    ∑ a : Fin ((37 - 3) / 2), (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ k = -1 := by
  have hfull : ∑ b ∈ Finset.range 37, ((b : ZMod 37)) ^ k = 0 := by
    rw [← sum_zmod37_eq_sum_range (fun x => x ^ k)]
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod 37) k (by simpa using hk)
  have hrefl : ∑ b ∈ Finset.Ico (19 : ℕ) 36, ((b : ZMod 37)) ^ k =
      ∑ c ∈ Finset.Ico (2 : ℕ) 19, ((c : ZMod 37)) ^ k := by
    refine Finset.sum_nbij' (fun b => 37 - b) (fun c => 37 - c) ?_ ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.mem_Ico] at hb ⊢; omega
    · intro c hc; simp only [Finset.mem_Ico] at hc ⊢; omega
    · intro b hb; simp only [Finset.mem_Ico] at hb ⊢; omega
    · intro c hc; simp only [Finset.mem_Ico] at hc ⊢; omega
    · intro b hb
      simp only [Finset.mem_Ico] at hb
      rw [show ((37 - b : ℕ) : ZMod 37) = -(b : ZMod 37) from by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]]
      rw [hk_even.neg_pow]
  have hIco02 : ∑ b ∈ Finset.Ico (0 : ℕ) 2, ((b : ZMod 37)) ^ k = 1 := by
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ, Finset.sum_range_one,
      Nat.cast_zero, zero_pow hk_pos.ne', Nat.cast_one, one_pow, zero_add]
  have hIco3637 : ∑ b ∈ Finset.Ico (36 : ℕ) 37, ((b : ZMod 37)) ^ k = 1 := by
    rw [Finset.sum_Ico_eq_sum_range, show (37 : ℕ) - 36 = 1 from rfl, Finset.sum_range_one]
    have h36 : ((36 + 0 : ℕ) : ZMod 37) = -1 := by
      rw [show (36 + 0 : ℕ) = 37 - 1 from rfl, Nat.cast_sub (by omega), ZMod.natCast_self,
        Nat.cast_one, zero_sub]
    rw [h36, hk_even.neg_one_pow]
  have hsplit : ∑ b ∈ Finset.range 37, ((b : ZMod 37)) ^ k =
      (∑ b ∈ Finset.Ico (0 : ℕ) 2, ((b : ZMod 37)) ^ k) +
        ((∑ b ∈ Finset.Ico (2 : ℕ) 19, ((b : ZMod 37)) ^ k) +
          ((∑ b ∈ Finset.Ico (19 : ℕ) 36, ((b : ZMod 37)) ^ k) +
            ∑ b ∈ Finset.Ico (36 : ℕ) 37, ((b : ZMod 37)) ^ k)) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun b => ((b : ZMod 37)) ^ k)
        (by omega : (0 : ℕ) ≤ 2) (by omega : (2 : ℕ) ≤ 37),
      ← Finset.sum_Ico_consecutive (fun b => ((b : ZMod 37)) ^ k)
        (by omega : (2 : ℕ) ≤ 19) (by omega : (19 : ℕ) ≤ 37),
      ← Finset.sum_Ico_consecutive (fun b => ((b : ZMod 37)) ^ k)
        (by omega : (19 : ℕ) ≤ 36) (by omega : (36 : ℕ) ≤ 37)]
  rw [hsplit, hrefl, hIco02, hIco3637] at hfull
  have hreindex : ∑ a : Fin ((37 - 3) / 2), (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ k =
      ∑ b ∈ Finset.Ico (2 : ℕ) 19, ((b : ZMod 37)) ^ k := by
    rw [Fin.sum_univ_eq_sum_range (fun m => (((m + 2 : ℕ)) : ZMod 37) ^ k) ((37 - 3) / 2),
      Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr (by norm_num) (fun i _ => by rw [Nat.add_comm 2 i])
  rw [hreindex]
  -- hfull : 1 + (S + (S + 1)) = 0  ⟹  2 * (S + 1) = 0
  have h2 : (2 : ZMod 37) ≠ 0 := by
    rw [show (2 : ZMod 37) = ((2 : ℕ) : ZMod 37) from by push_cast; ring,
      show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
      ZMod.natCast_eq_natCast_iff]
    decide
  have hSform : 2 * ((∑ b ∈ Finset.Ico (2 : ℕ) 19, ((b : ZMod 37)) ^ k) + 1) = 0 := by
    rw [mul_add]; linear_combination hfull
  rcases mul_eq_zero.mp hSform with h | h
  · exact absurd h h2
  · linear_combination h

omit [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- Fermat: every `(a+2)` (`2 ≤ a+2 ≤ 18 < 37`) satisfies `(a+2)^36 = 1` in `ZMod 37`, so the
sum over the `17`-element Pollaczek range is `17`. -/
theorem sum_fin_pow_36 :
    ∑ a : Fin ((37 - 3) / 2), (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 36 = 17 := by
  have h1 : ∀ a : Fin ((37 - 3) / 2), (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 36 = 1 := by
    intro a
    have hlt : (a : ℕ) < (37 - 3) / 2 := a.isLt
    have hne : (((a : ℕ) + 2 : ℕ) : ZMod 37) ≠ 0 :=
      zmod_natCast_ne_zero_of_pos_lt (by omega) (by omega)
    exact ZMod.pow_card_sub_one_eq_one hne
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  simp

omit [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- The difference of Pollaczek power sums driving the `(V·e)_{j₀}` value: `17 - (-1) = 18`. -/
theorem pollaczek_pow_diff (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34) :
    (∑ a : Fin ((37 - 3) / 2), (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 36) -
      ∑ a : Fin ((37 - 3) / 2), (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (36 - i) = 18 := by
  rw [sum_fin_pow_36, sum_fin_add_two_pow_eq_neg_one
    ((Nat.even_sub (by omega : i ≤ 36)).mpr (iff_of_true (by norm_num) hi_even))
    (by omega) (by omega)]
  norm_num

omit [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **The `j₀`-component of the Vandermonde action on the Pollaczek exponent vector is `18 ≠ 0`**
(where `2(j₀+1) = i`). Per term `((a+2)^i - 1)·(a+2)^{36-i} = (a+2)^36 - (a+2)^{36-i}`, and the
summed difference is `17 - (-1) = 18` by `pollaczek_pow_diff`. -/
theorem vandermonde_mulVec_pollaczek_eq_18 (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (j₀ : Fin (kummerLogRank 37)) (hj0 : 2 * ((j₀ : ℕ) + 1) = i) :
    (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
        (fun a : Fin (kummerLogRank 37) =>
          ((((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) : ZMod 37)) j₀ = 18 := by
  have hterm : ∀ a : Fin (kummerLogRank 37),
      vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num) j₀ a *
          ((((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ)) : ZMod 37) =
        (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 36 - (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (36 - i) := by
    intro a
    simp only [vandermondeTeichmullerEvenSubOneMatrix, teichmullerEvenNode, kummerLogColumnIndex,
      CPlusGeneratorIndex]
    push_cast
    rw [← pow_mul, hj0, sub_mul, one_mul, ← pow_add,
      show i + (37 - 1 - i) = 36 from by omega, show (37 - 1 - i) = 36 - i from by omega]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib]
  exact pollaczek_pow_diff i hi_even hi2 hi34

/-- **The `j₀`-row factor vanishes** (where `2(j₀+1)=i`), from `[pollaczekUnit i]=0`.
The Kummer-log matrix kills the Pollaczek exponent vector; its `j₀`-component is
`rowFactor_{j₀} · 18`, and `18 ≠ 0`, so `rowFactor_{j₀} = 0`. -/
theorem kummerLogDetRowFactor_eq_zero_of_pollaczek (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i)
    (hi34 : i ≤ 34) (j₀ : Fin (kummerLogRank 37)) (hj0 : 2 * ((j₀ : ℕ) + 1) = i)
    (h : cyclotomicUnitToFreePartModPAdd (p := 37) K (Additive.ofMul (pollaczekUnit 37 K i)) = 0) :
    kummerLogDetRowFactor (p := 37) j₀ = 0 := by
  have heval := congrFun (concreteKummerLogMatrix_mulVec_pollaczek_eq_zero (K := K) i h) j₀
  rw [Pi.zero_apply, concreteKummerLogMatrix_mulVec_apply,
    vandermonde_mulVec_pollaczek_eq_18 i hi_even hi2 hi34 j₀ hj0] at heval
  have h18 : (18 : ZMod 37) ≠ 0 := by
    rw [show (18 : ZMod 37) = ((18 : ℕ) : ZMod 37) from by push_cast; ring,
      show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
      ZMod.natCast_eq_natCast_iff]
    decide
  exact (mul_eq_zero.mp heval).resolve_right h18

/-- **WF-816, class form: `[pollaczekUnit i]_{mod 37} = 0 ⟹ 37 ∣ B_i`** (even `2 ≤ i ≤ 34`).
Choosing the row `j₀ = i/2 - 1` (so `2(j₀+1) = i`), the vanishing class makes the `j₀`-row
factor `0`, hence the Bernoulli factor at `kummerLogRowIndex j₀ = i/2` is `0`, i.e. `37 ∣ B_i`. -/
theorem flt37_dvd_bernoulli_of_pollaczek_class_eq_zero (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i)
    (hi34 : i ≤ 34)
    (h : cyclotomicUnitToFreePartModPAdd (p := 37) K (Additive.ofMul (pollaczekUnit 37 K i)) = 0) :
    (37 : ℤ) ∣ (bernoulli i).num := by
  have hi2dvd : (2 : ℕ) ∣ i := hi_even.two_dvd
  obtain ⟨j, hj⟩ : ∃ j : ℕ, i = 2 * (j + 1) := ⟨i / 2 - 1, by omega⟩
  have hj_lt : j < kummerLogRank 37 := by simp only [kummerLogRank]; omega
  have hval : ((⟨j, hj_lt⟩ : Fin (kummerLogRank 37)) : ℕ) = j := rfl
  have hj0 : 2 * (((⟨j, hj_lt⟩ : Fin (kummerLogRank 37)) : ℕ) + 1) = i := by rw [hval]; omega
  have hrow : kummerLogDetRowFactor (p := 37) ⟨j, hj_lt⟩ = 0 :=
    kummerLogDetRowFactor_eq_zero_of_pollaczek i hi_even hi2 hi34 ⟨j, hj_lt⟩ hj0 h
  have hbf : bernoulliFactor 37 (kummerLogRowIndex (p := 37) ⟨j, hj_lt⟩) = 0 := by
    by_contra hne
    exact ((kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero (p := 37) (by norm_num)
      ⟨j, hj_lt⟩).mpr hne) hrow
  rw [show kummerLogRowIndex (p := 37) (⟨j, hj_lt⟩ : Fin (kummerLogRank 37)) = j + 1 from rfl]
    at hbf
  rw [hj]
  by_contra hdvd
  exact (bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num (p := 37) (j := j + 1)
    (by omega) (by omega)).mpr hdvd hbf

end FLT37

end BernoulliRegular

end
