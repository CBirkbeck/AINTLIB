import BernoulliRegular.HMinus.HMinusCriterion
import BernoulliRegular.HMinus.LValueReduction.Teichmuller
import BernoulliRegular.BernoulliFast.KellnerSecondOrder
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.Washington83
import BernoulliRegular.UnitQuotient.Washington83UnitForward
import Mathlib.GroupTheory.PGroup

/-!
# The Case-I Herbrand bound, analytic route (Eichler pigeonhole input)

This file closes the **Case-I Herbrand bound** `p-rank C⁻ ≤ 1` for `p = 37`
purely via the *analytic* class-number side, bypassing Stickelberger and
Gross–Koblitz.  Concretely, for `K = CyclotomicField 37 ℚ` we prove:

* `flt37_not_dvd_sq_hMinus : ¬ (37 : ℕ)^2 ∣ hMinus K`
  — the sharp `v₃₇(h⁻) = 1` statement (reduced to the single sharp `p`-adic
  fact below);
* `flt37_not_dvd_sq_h : ¬ (37 : ℕ)^2 ∣ h K`
  — from `h = h⁺ · h⁻`, `37 ∤ h⁺` (Sinnott / Washington §8.3) and the previous;
* `card_le_prime_of_ptorsion_subgroup_of_not_dvd_sq` — the abstract pigeonhole:
  a `p`-torsion subgroup of a finite abelian group with `p² ∤ card` has order `≤ p`;
* `caseI_pRank_minus_bound : Nat.card C⁻ ≤ 37` for any `37`-torsion subgroup
  `C⁻ ⊆ ClassGroup (𝓞 K)`.

The last statement is exactly the pigeonhole input that Eichler's argument
(DM-A3) needs: any subgroup of the cyclotomic class group killed by `37` has
order at most `37`.

## The valuation reduction

The relative class number satisfies (Diekmann Thm 42 / 43, in the `ℚ_[p]` form
`hMinus_formula_teichmuller`)

  `(h⁻ : ℚ_p) = (2p) · ∏_{1 ≤ j ≤ p-2, j odd} (-½ · B_{1,ω^j})`.

The boundary factor `j = p-2` combines with the `(2p)` prefactor into the
`p`-unit `1 + p·z₀` (`boundary_teichmuller_factor_eq_one_add_p_mul`), and each
*regular* factor `-½ · B_{1,ω^j}` is a `p`-adic **unit** (its mod-`p`
approximant `-½ · B_{j+1}/(j+1)` is a unit because `37 ∤ B_{j+1}.num`,
`flt37_bernoulli_table`).  Hence `‖h⁻‖ = ‖-½ · B_{1,ω^{31}}‖ = 37^{-v}` where
`v = v₃₇(B_{1,ω^{31}})`, and `37² ∣ h⁻ ↔ v ≥ 2`.

The single sharp `p`-adic input is `v₃₇(B_{1,ω^{31}}) ≤ 1`, i.e. the irregular
generalized Bernoulli factor is not divisible by `37²`.  Mathematically this is
the mod-`37²` Kummer congruence `B_{1,ω^{31}} ≡ B_{32}/32 (mod 37²)` combined
with `kellner_at_zero_not_dvd` (`37² ∤ B_{32}.num`).

## References
* Diekmann, *FLT for regular primes*, §4, Thm 42–43.
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §4.3, §6.2, §8.3.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

namespace FLT37

namespace Eichler

/-! ## Step 1, part A: the per-character `p`-adic factor norms

For a *regular* odd index `j` (one with `37 ∤ B_{j+1}.num`), the generalized
Bernoulli factor `-½ · B_{1,ω^j}` is a `p`-adic unit; for the *irregular*
index its norm is `37^{-v}` with `v = v₃₇(B_{1,ω^j})`. -/

section Factors

variable {p : ℕ} [hp : Fact p.Prime]

/-- A regular odd Bernoulli factor `-½ · B_{1,ω^j}` (with `37 ∤ B_{j+1}.num`,
`j` odd, `0 < j`, `j + 1 < p - 1`) has `p`-adic norm `1`.

The mod-`p` Kummer bridge `B_{1,ω^j} ≡ B_{j+1}/(j+1) (mod p)`
(`bernoulliGen_teichmuller_pow_sModEq_div`) writes the factor as `a + p·z` with
`a` the `p`-adic-integer realization of `-½ · B_{j+1}/(j+1)`
(`exists_padicInt_bernoulli_factor`); `a` is a **unit** since
`p ∤ B_{j+1}.num`, so `‖factor - a‖ ≤ ‖p‖ < 1 = ‖a‖`, whence `‖factor‖ = 1`. -/
theorem norm_oddBernoulliFactor_eq_one_of_not_dvd_num (hp_odd : p ≠ 2)
    {j : ℕ} (hj_odd : Odd j) (hj_pos : 0 < j) (hj_small : j + 1 < p - 1)
    (hnum : ¬ (p : ℤ) ∣ (bernoulli (j + 1)).num) :
    ‖(-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1‖ = 1 := by
  classical
  have hp_gt : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd)
  -- denominator of `B_{j+1}` is prime to `p` (since `j + 1 < p - 1`).
  have hden : ¬ p ∣ (bernoulli (j + 1)).den :=
    BernoulliRegular.prime_not_dvd_bernoulli_den_of_lt_sub_one (p := p) (n := j + 1)
      hp_odd (by omega)
  -- the `p`-adic-integer realization `a` of `-½ · B_{j+1}/(j+1)`, a unit.
  obtain ⟨a, ha, haU⟩ := exists_padicInt_bernoulli_factor (p := p) (hp := hp) (n := j + 1)
    hp_odd (by omega) (by omega) hden
  have ha_unit : IsUnit a := haU.mpr hnum
  -- `‖a‖ = 1`.
  have ha_norm : ‖((a : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    have : ‖a‖ = 1 := (PadicInt.isUnit_iff (z := a)).mp ha_unit
    simpa [PadicInt.padic_norm_e_of_padicInt] using this
  -- `-½ · B_{1,ω^j} = a + p·z` (mod-`p` Kummer bridge).
  obtain ⟨c, hc⟩ := neg_one_half_mem_padicInt (p := p) hp_odd
  have hj_not_dvd : ¬ (p - 1) ∣ (j + 1) :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hj_p_plus : ¬ (p : ℕ) ∣ (j + 1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hj_p_plus_two : ¬ (p : ℕ) ∣ (j + 2) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  obtain ⟨z, hz⟩ := bernoulliGen_teichmuller_pow_sModEq_div
    (p := p) hp_odd hj_odd hj_pos hj_not_dvd hj_p_plus hj_p_plus_two (by omega)
  have hz' : BernoulliGen ((teichmullerCharQp p) ^ j) 1 =
      ((((bernoulli (j + 1) : ℚ) / ((j : ℕ) + 1 : ℚ)) : ℚ) : ℚ_[p]) +
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
    rw [sub_eq_iff_eq_add] at hz
    simpa [add_comm] using hz
  -- `(a : ℚ_p) = -½ · B_{j+1}/(j+1)` (matching `ha`), so the factor is `a + p·(c·z)`.
  have hbridge : (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1 =
      ((a : ℤ_[p]) : ℚ_[p]) + (p : ℚ_[p]) * ((c : ℚ_[p]) * (z : ℚ_[p])) := by
    have ha' : ((a : ℤ_[p]) : ℚ_[p]) =
        (c : ℚ_[p]) * ((((bernoulli (j + 1) : ℚ) / ((j : ℕ) + 1 : ℚ)) : ℚ) : ℚ_[p]) := by
      rw [ha, ← hc]; push_cast; ring_nf
    have hcz : (-(1 / 2 : ℚ_[p])) = (c : ℚ_[p]) := hc.symm
    rw [hcz, hz', ha']; ring
  -- the error `p·(c·z)` has norm `< 1`.
  have hcz_int : ‖((c * z : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := by
    simpa [PadicInt.padic_norm_e_of_padicInt] using (c * z).2
  have herr : ‖(p : ℚ_[p]) * ((c : ℚ_[p]) * (z : ℚ_[p]))‖ < 1 := by
    have hp_lt : ‖(p : ℚ_[p])‖ < 1 :=
      (Padic.norm_natCast_lt_one_iff (p := p) (n := p)).2 dvd_rfl
    have hczeq : (c : ℚ_[p]) * (z : ℚ_[p]) = ((c * z : ℤ_[p]) : ℚ_[p]) := by
      rw [PadicInt.coe_mul]
    rw [hczeq]
    calc
      ‖(p : ℚ_[p]) * ((c * z : ℤ_[p]) : ℚ_[p])‖
          = ‖(p : ℚ_[p])‖ * ‖((c * z : ℤ_[p]) : ℚ_[p])‖ := norm_mul _ _
      _ ≤ ‖(p : ℚ_[p])‖ * 1 := mul_le_mul_of_nonneg_left hcz_int (norm_nonneg _)
      _ = ‖(p : ℚ_[p])‖ := mul_one _
      _ < 1 := hp_lt
  -- conclude `‖factor‖ = ‖a‖ = 1`.
  have hne : ‖((a : ℤ_[p]) : ℚ_[p])‖ ≠ ‖(p : ℚ_[p]) * ((c : ℚ_[p]) * (z : ℚ_[p]))‖ := by
    rw [ha_norm]; exact (ne_of_lt herr).symm
  rw [hbridge, Padic.add_eq_max_of_ne hne, ha_norm]
  exact max_eq_left (le_of_lt herr)

/-- The boundary factor `(2p)·(-½ B_{1,ω^{p-2}})` has `p`-adic norm `1`: it
equals `1 + p·z₀` (`boundary_teichmuller_factor_eq_one_add_p_mul`), and
`‖1 + p·z₀‖ = 1` since `‖p·z₀‖ < 1`. -/
theorem norm_boundary_factor_eq_one (hp_odd : p ≠ 2) :
    ‖(2 * p : ℚ_[p]) * ((-(1 / 2 : ℚ_[p])) *
        BernoulliGen ((teichmullerCharQp p) ^ (p - 2)) 1)‖ = 1 := by
  obtain ⟨z₀, hz₀⟩ := boundary_teichmuller_factor_eq_one_add_p_mul (p := p) hp_odd
  have herr : ‖(p : ℚ_[p]) * (z₀ : ℚ_[p])‖ < 1 := by
    have hp_lt : ‖(p : ℚ_[p])‖ < 1 :=
      (Padic.norm_natCast_lt_one_iff (p := p) (n := p)).2 dvd_rfl
    calc
      ‖(p : ℚ_[p]) * (z₀ : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ * ‖(z₀ : ℚ_[p])‖ := norm_mul _ _
      _ ≤ ‖(p : ℚ_[p])‖ * 1 := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            simpa [PadicInt.padic_norm_e_of_padicInt] using z₀.2
      _ = ‖(p : ℚ_[p])‖ := mul_one _
      _ < 1 := hp_lt
  have hmul_assoc : (2 * p : ℚ_[p]) * ((-(1 / 2 : ℚ_[p])) *
      BernoulliGen ((teichmullerCharQp p) ^ (p - 2)) 1) =
      (2 * p : ℚ_[p]) * (-(1 / 2 : ℚ_[p])) *
        BernoulliGen ((teichmullerCharQp p) ^ (p - 2)) 1 := by ring
  have hne : ‖(1 : ℚ_[p])‖ ≠ ‖(p : ℚ_[p]) * (z₀ : ℚ_[p])‖ := by
    rw [norm_one]; exact (ne_of_lt herr).symm
  rw [hmul_assoc, hz₀, Padic.add_eq_max_of_ne hne, norm_one, max_eq_left (le_of_lt herr)]

end Factors

/-! ## Step 1, part B: `‖(h⁻ : ℚ₃₇)‖ = ‖-½ · B_{1,ω^{31}}‖`

The relative class number's `p`-adic norm is exactly the norm of the single
irregular generalized-Bernoulli factor: all other factors (and the boundary
factor times the `2p` prefactor) are `p`-adic units. -/

section HMinusNorm

variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K] [IsCMField K]

private def oddSet (n : ℕ) : Finset ℕ := (Finset.range n).filter fun j => Odd j

/-- `‖(h⁻ : ℚ₃₇)‖ = ‖-½ · B_{1,ω^{31}}‖`.

`(h⁻ : ℚ₃₇) = (2·37) · ∏_{j ∈ oddSet 36} (-½ B_{1,ω^j})`
(`hMinus_formula_teichmuller`).  Splitting off the boundary index `35` and the
irregular index `31`, the remaining product times `2·37` is a unit (boundary
factor `× 2·37` is `1 + 37z₀`, each regular factor is a unit), so
`(h⁻ : ℚ₃₇) = (-½ B_{1,ω^{31}}) · (unit)`. -/
theorem norm_hMinus_eq_norm_irregularFactor :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    ‖((hMinus K : ℕ) : ℚ_[37])‖ =
      ‖(-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  classical
  set f : ℕ → ℚ_[37] := fun j => (-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ j) 1
    with hf
  -- The class-number formula.
  have hformula : ((hMinus K : ℕ) : ℚ_[37]) = (2 * 37 : ℚ_[37]) * ∏ j ∈ oddSet 36, f j := by
    have := hMinus_formula_teichmuller (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
    simpa [oddSet, hf, show (37 : ℕ) - 1 = 36 from by decide] using this
  -- `oddSet 36 = insert 35 (oddSet 34)`.
  have hset36 : oddSet 36 = insert 35 (oddSet 34) := by decide
  have h35_notin : (35 : ℕ) ∉ oddSet 34 := by decide
  -- `oddSet 34 = insert 31 ((oddSet 34).erase 31)`, with `31 ∈ oddSet 34`.
  have h31_mem : (31 : ℕ) ∈ oddSet 34 := by decide
  -- Compute the product.
  rw [hformula, hset36, Finset.prod_insert h35_notin,
    ← Finset.prod_erase_mul (oddSet 34) f h31_mem]
  -- now: ‖(2·37) · (f 35 · ((∏_{erase 31} f) · f 31))‖
  -- rearrange to f 31 · W with W a unit.
  set R : ℚ_[37] := ∏ j ∈ (oddSet 34).erase 31, f j with hR
  have hrearrange : (2 * 37 : ℚ_[37]) * (f 35 * (R * f 31)) =
      f 31 * ((2 * 37 : ℚ_[37]) * f 35 * R) := by ring
  rw [hrearrange, norm_mul]
  -- W = (2·37)·f 35 · R has norm 1.
  have hWnorm : ‖(2 * 37 : ℚ_[37]) * f 35 * R‖ = 1 := by
    have hbd : ‖(2 * 37 : ℚ_[37]) * f 35‖ = 1 := by
      have := norm_boundary_factor_eq_one (p := 37) (by decide : (37 : ℕ) ≠ 2)
      simpa [hf, show (37 : ℕ) - 2 = 35 from by decide] using this
    have hRnorm : ‖R‖ = 1 := by
      rw [hR, norm_prod]
      apply Finset.prod_eq_one
      intro j hj
      have hj_mem : j ∈ oddSet 34 := Finset.mem_of_mem_erase hj
      have hj_ne : j ≠ 31 := Finset.ne_of_mem_erase hj
      have hj_odd : Odd j := (Finset.mem_filter.mp hj_mem).2
      have hj_lt : j < 34 := Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1
      have hj_pos : 0 < j := by rcases hj_odd with ⟨k, hk⟩; omega
      -- regular factor: `37 ∤ B_{j+1}.num`.
      have hnum : ¬ (37 : ℤ) ∣ (bernoulli (j + 1)).num := by
        have hj1_even : Even (j + 1) := hj_odd.add_one
        have hj1_two : 2 ≤ j + 1 := by omega
        have hj1_34 : j + 1 ≤ 34 := by omega
        have hj1_ne32 : j + 1 ≠ 32 := by omega
        exact Sinnott.flt37_bernoulli_table (j + 1) hj1_even hj1_two hj1_34 hj1_ne32
      exact norm_oddBernoulliFactor_eq_one_of_not_dvd_num (p := 37)
        (by decide : (37 : ℕ) ≠ 2) hj_odd hj_pos (by omega) hnum
    rw [norm_mul, hbd, hRnorm, mul_one]
  rw [hWnorm, mul_one]

end HMinusNorm

/-! ## Steps 2–5: from `37² ∤ h⁻` to the Herbrand pigeonhole bound

Throughout, `K = CyclotomicField 37 ℚ`. We assume the standard cyclotomic
instances (`Fact (Nat.Prime 37)`, `IsCMField`) as for the rest of the FLT37
development. -/

section ChainSteps

variable [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **Step 3: `37² ∤ h`.** Given `37² ∤ h⁻` (step 1) and `37 ∤ h⁺` (Sinnott,
`Sinnott.flt37_not_dvd_hPlus`), the factorisation `h = h⁺ · h⁻` forces
`37² ∤ h`: if `37² ∣ h⁺ · h⁻` while `37 ∤ h⁺`, then `37²` is coprime to `h⁺`,
hence `37² ∣ h⁻`, contradiction. -/
theorem flt37_not_dvd_sq_h_of_not_dvd_sq_hMinus
    (hMinus_sharp : ¬ (37 : ℕ) ^ 2 ∣ hMinus (CyclotomicField 37 ℚ)) :
    ¬ (37 : ℕ) ^ 2 ∣ h (CyclotomicField 37 ℚ) := by
  have hp_odd : (37 : ℕ) ≠ 2 := by decide
  have hplus : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    Sinnott.flt37_not_dvd_hPlus
  intro hsq
  -- `h = h⁺ · h⁻`.
  rw [h_eq_hPlus_mul_hMinus (p := 37) (hp_odd := hp_odd) (K := CyclotomicField 37 ℚ)] at hsq
  -- `37` is coprime to `h⁺` (since `37` is prime and `37 ∤ h⁺`).
  have hcop : Nat.Coprime (37 ^ 2) (hPlus (CyclotomicField 37 ℚ)) := by
    have h37cop : Nat.Coprime 37 (hPlus (CyclotomicField 37 ℚ)) :=
      (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hplus
    exact Nat.Coprime.pow_left 2 h37cop
  -- `37² ∣ h⁺ · h⁻` and `gcd(37², h⁺) = 1` give `37² ∣ h⁻`.
  exact hMinus_sharp (hcop.dvd_of_dvd_mul_left hsq)

/-- **`37² ∣ h⁻ ↔ ‖factor‖ ≤ 37⁻²`.** Via `norm_hMinus_eq_norm_irregularFactor`
and `Padic.norm_int_le_pow_iff_dvd` (`‖(k:ℚ₃₇)‖ ≤ 37^{-n} ↔ 37^n ∣ k`). -/
theorem dvd_sq_hMinus_iff_norm_irregularFactor_le :
    (37 : ℕ) ^ 2 ∣ hMinus (CyclotomicField 37 ℚ) ↔
      ‖(-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ ≤
        (37 : ℝ) ^ (-2 : ℤ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `‖h⁻‖ = ‖factor‖`.
  have hnorm := norm_hMinus_eq_norm_irregularFactor (CyclotomicField 37 ℚ)
  rw [← hnorm]
  -- `‖(h⁻ : ℚ₃₇)‖ ≤ 37^{-2} ↔ (37² : ℤ) ∣ (h⁻ : ℤ) ↔ 37² ∣ h⁻`.
  have key := Padic.norm_int_le_pow_iff_dvd (p := 37)
    (k := (hMinus (CyclotomicField 37 ℚ) : ℤ)) 2
  -- normalise casts in `key`.
  have hcast_norm : ‖((hMinus (CyclotomicField 37 ℚ) : ℤ) : ℚ_[37])‖ =
      ‖((hMinus (CyclotomicField 37 ℚ) : ℕ) : ℚ_[37])‖ := by norm_cast
  rw [hcast_norm] at key
  -- match the exponent and the divisibility cast.
  have hpow : ((37 : ℕ) : ℝ) ^ (-(2 : ℕ) : ℤ) = (37 : ℝ) ^ (-2 : ℤ) := by norm_num
  have hdvd : ((37 : ℕ) ^ 2 : ℤ) ∣ (hMinus (CyclotomicField 37 ℚ) : ℤ) ↔
      (37 : ℕ) ^ 2 ∣ hMinus (CyclotomicField 37 ℚ) := by exact_mod_cast Iff.rfl
  rw [hpow, hdvd] at key
  exact key.symm

/-! ## The sharp valuation, via a direct Teichmüller modular computation

We prove `v₃₇(B_{1,ω^{31}}) = 1` **unconditionally** by computing the conductor-
cleared sum `37·B_{1,ω^{31}} = ∑_{a} ω³¹(a)·a` modulo `37³` and observing it is
`37²·23` with `37 ∤ 23`.

The bridge is the higher Teichmüller congruence: for an odd prime `p`,
`ω(a) ≡ (a.val)^{p²} (mod p³)` (a two-step Frobenius lift of `ω(a) ≡ a (mod p)`),
hence `ω³¹(a)·a ≡ (a.val)^{31·p²+1} (mod p³)`.  For `p = 37` this exponent is
`31·37²+1 = 42440`, and `∑_{a=1}^{36} a^{42440} ≡ 31487 = 37²·23 (mod 37³)`. -/

section TeichmullerComputation

variable {p : ℕ} [hp : Fact p.Prime]

open BernoulliRegular (teichmuller teichmullerChar teichmullerChar_apply toZMod_teichmuller
  teichmuller_pow_card)

omit [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **Higher Teichmüller congruence (mod `p³`).** `ω(a) ≡ (a.val : ℤ_[p])^{p²}
(mod p³)`, i.e. modulo `(maximalIdeal ℤ_[p])^3`.

This is the two-step Frobenius lift of `ω(a) ≡ a (mod p)`: starting from
`ω(a) ≡ (a.val : ℤ_[p]) (mod maximalIdeal)` and applying `SModEq.pow_pow_add_one`
with `m = 2` gives `ω(a)^{p²} ≡ (a.val)^{p²} (mod maximalIdeal³)`; but
`ω(a)^{p²} = ω(a)` by the Frobenius fixed-point property
(`teichmuller_pow_card` twice). -/
theorem teichmuller_sModEq_pow_val_pow_two (a : ZMod p) :
    teichmuller p a ≡ (a.val : ℤ_[p]) ^ (p ^ 2)
      [SMOD (IsLocalRing.maximalIdeal ℤ_[p]) ^ 3] := by
  -- Step A: `ω(a) ≡ (a.val : ℤ_[p]) (mod maximalIdeal)`.
  have h_base : teichmuller p a ≡ (a.val : ℤ_[p]) [SMOD IsLocalRing.maximalIdeal ℤ_[p]] := by
    rw [SModEq.sub_mem, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, toZMod_teichmuller,
      map_natCast, ZMod.natCast_val, ZMod.cast_id, sub_self]
  -- Step B: raise to the `p²`-th power, gaining two factors of the maximal ideal.
  have hp_mem : ((p : ℕ) : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  have h_pow := h_base.pow_pow_add_one hp_mem 2
  -- Step C: `(teichmuller p a)^{p²} = teichmuller p a`.
  rw [show (2 : ℕ) + 1 = 3 from rfl] at h_pow
  have hfix : teichmuller p a ^ (p ^ 2) = teichmuller p a := by
    rw [pow_succ, pow_one, pow_mul, teichmuller_pow_card, teichmuller_pow_card]
  rwa [hfix] at h_pow

/-- **Term-level congruence (mod `p³`).** For `p ≠ 2` and any `a : ZMod p`, the
summand `ωⁱ(a)·a.val` of the conductor-cleared `B_{1,ωⁱ}` is congruent modulo
`p³` to `(a.val : ℤ_[p])^{i·p²+1}`.

Both sides vanish for `a = 0`; for `a ≠ 0` use `MulChar.pow_apply'` to rewrite
`ωⁱ(a) = ω(a)^i`, then the higher congruence raised to the `i`-th power and
multiplied by `a.val`. -/
theorem teichmullerChar_pow_mul_val_sModEq (i : ℕ) (a : ZMod p) :
    ((teichmullerChar p) ^ i) a * (a.val : ℤ_[p]) ≡
      (a.val : ℤ_[p]) ^ (i * p ^ 2 + 1) [SMOD (IsLocalRing.maximalIdeal ℤ_[p]) ^ 3] := by
  rcases eq_or_ne a 0 with rfl | ha
  · -- `a = 0`: `(0).val = 0`, both sides are `0`.
    simp [ZMod.val_zero]
  · -- `a ≠ 0`: `ωⁱ(a) = ω(a)^i`.
    rcases Nat.eq_zero_or_pos i with rfl | hi_pos
    · -- `i = 0`: LHS `= 1·a.val = a.val`, RHS `= (a.val)^{0+1} = a.val`.
      have ha_unit : IsUnit a := by
        rw [isUnit_iff_ne_zero]; exact ha
      simp [MulChar.one_apply ha_unit]
    have hi_ne : i ≠ 0 := hi_pos.ne'
    rw [MulChar.pow_apply' _ hi_ne, teichmullerChar_apply]
    -- `ω(a)^i ≡ ((a.val)^{p²})^i (mod p³)`.
    have hcong : teichmuller p a ^ i ≡ ((a.val : ℤ_[p]) ^ (p ^ 2)) ^ i
        [SMOD (IsLocalRing.maximalIdeal ℤ_[p]) ^ 3] :=
      SModEq.pow i (teichmuller_sModEq_pow_val_pow_two a)
    -- multiply by `a.val` and tidy the exponent.
    have hmul := hcong.mul (SModEq.refl ((a.val : ℤ_[p])))
    have hexp : ((a.val : ℤ_[p]) ^ (p ^ 2)) ^ i * (a.val : ℤ_[p]) =
        (a.val : ℤ_[p]) ^ (i * p ^ 2 + 1) := by
      rw [← pow_mul, ← pow_succ]
      congr 1
      ring
    rwa [hexp] at hmul

end TeichmullerComputation

/-! ### The mod-`37³` power-sum identity -/

section PowerSum

-- The core finite computation: `∑_{a=0}^{36} a^{42440} ≡ 31487 (mod 37³)`, at the
-- `Nat` level.  Proved by kernel evaluation (`decide`): the kernel computes the 36
-- `Nat` powers `a^{42440}` (via GMP) and reduces their sum modulo `37³ = 50653`.
-- The `exponentiation.threshold` option lets the kernel evaluate the large powers
-- and `maxRecDepth` accommodates the `Finset.range 37` fold; both are scoped here.
omit [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
set_option exponentiation.threshold 100000 in
set_option maxRecDepth 100000 in
/-- The core finite computation `∑_{a=0}^{36} a^{42440} ≡ 31487 (mod 37³)`
(`Nat`-level, kernel-decidable). -/
theorem sum_range_pow_mod_eq :
    ((Finset.range 37).sum (fun a => a ^ (42440 : ℕ))) % (37 ^ 3) = 31487 := by
  decide

set_option linter.unusedSectionVars false in
/-- The explicit mod-`37³` value of the irregular power sum: in `ℤ_[37]`,
`∑_{a : ZMod 37} (a.val)^{42440} ≡ 31487 (mod 37³)`, where `42440 = 31·37²+1` is
the exponent produced by the Teichmüller bridge for the index `i = 31`.

We prove this by transporting the corresponding identity in `ZMod (37^3)` (a
finite, decidable computation: `36` modular `42440`-th powers) through the ring
hom `ℤ_[37] → ZMod (37^3)` (`PadicInt.toZModPow 3`), whose kernel is exactly
`(maximalIdeal ℤ_[37])^3`. -/
theorem sum_val_pow_sModEq_const :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    (∑ a : ZMod 37, (a.val : ℤ_[37]) ^ (42440 : ℕ)) ≡ (31487 : ℤ_[37])
      [SMOD (IsLocalRing.maximalIdeal ℤ_[37]) ^ 3] := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Work modulo `37³` via `PadicInt.toZModPow 3 : ℤ_[37] →+* ZMod (37^3)`,
  -- whose kernel is exactly `(maximalIdeal ℤ_[37])^3`.
  have hideal : (IsLocalRing.maximalIdeal ℤ_[37]) ^ 3
      = RingHom.ker (PadicInt.toZModPow 3 : ℤ_[37] →+* ZMod (37 ^ 3)) := by
    rw [PadicInt.ker_toZModPow, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  rw [SModEq.sub_mem, hideal, RingHom.mem_ker, map_sub, map_sum, sub_eq_zero]
  -- Each `toZModPow 3 (a.val : ℤ_[37]) = (a.val : ZMod (37^3))` (cast); the
  -- constant `31487` maps to itself.
  have hterm : ∀ a : ZMod 37,
      (PadicInt.toZModPow 3 ((a.val : ℤ_[37]) ^ (42440 : ℕ))) =
        ((a.val : ZMod (37 ^ 3)) ^ (42440 : ℕ)) := by
    intro a
    rw [map_pow, map_natCast]
  simp_rw [hterm]
  rw [show (PadicInt.toZModPow 3 (31487 : ℤ_[37]) : ZMod (37 ^ 3)) = (31487 : ZMod (37 ^ 3)) by
    rw [show (31487 : ℤ_[37]) = ((31487 : ℕ) : ℤ_[37]) by norm_cast, map_natCast]; norm_cast]
  -- Goal: `∑_{a : ZMod 37} (a.val : ZMod (37^3))^42440 = 31487` in `ZMod (37^3)`.
  -- Reindex `ZMod 37 ↔ range 37` via `val` to land on a `Nat`-cast identity.
  have hbij : (∑ a : ZMod 37, (a.val : ZMod (37 ^ 3)) ^ (42440 : ℕ))
      = ((∑ n ∈ Finset.range 37, n ^ (42440 : ℕ) : ℕ) : ZMod (37 ^ 3)) := by
    rw [Nat.cast_sum]
    refine Finset.sum_bij' (fun (a : ZMod 37) _ => a.val) (fun (n : ℕ) _ => (n : ZMod 37))
      (fun a _ => Finset.mem_range.mpr (ZMod.val_lt a)) (fun n _ => Finset.mem_univ _)
      ?_ ?_ ?_
    · intro a _; rw [ZMod.natCast_val, ZMod.cast_id]
    · intro n hn; rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]
    · intro a _; rw [Nat.cast_pow, ZMod.natCast_val]
  rw [hbij]
  -- The `Nat`-level power sum, reduced modulo `37³`, is `31487` (a finite,
  -- kernel-decidable computation: `36` modular `42440`-th powers).
  have hnat : ((Finset.range 37).sum (fun a => a ^ (42440 : ℕ))) % (37 ^ 3) = 31487 :=
    sum_range_pow_mod_eq
  -- Cast `hnat` to `ZMod (37^3)`: `((∑) : ZMod) = ((∑ % 37^3) : ZMod) = 31487`.
  rw [← ZMod.natCast_mod ((Finset.range 37).sum (fun a => a ^ (42440 : ℕ))) (37 ^ 3), hnat]
  norm_cast

end PowerSum

section SharpInput

variable [Fact (Nat.Prime 37)]

/-- **The sharp `p`-adic input for Case-I (`v₃₇(h⁻) = 1`).**

`(37 : ℝ)^{-2} < ‖-½ · B_{1,ω^{31}}‖`, i.e. the irregular generalized-Bernoulli
factor has `37`-adic valuation at most `1`.  This is now **proved**
unconditionally by `flt37SharpHMinusValuation_proved` (a direct Teichmüller
modular computation: `37·B_{1,ω^{31}} ≡ 31487 = 37²·23 (mod 37³)`); it is kept as
a `Prop` so that the downstream chain (`flt37_not_dvd_sq_hMinus`,
`caseI_pRank_minus_bound`) can be stated either parametrically or
unconditionally. -/
def Flt37SharpHMinusValuation : Prop :=
    (37 : ℝ) ^ (-2 : ℤ) <
      ‖(-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖

/-! ### Assembling the sharp valuation from the modular computation -/

set_option linter.unusedSectionVars false in
/-- The conductor-cleared irregular Bernoulli number realised in `ℤ_[37]`:
`37 · B_{1,ω^{31}} = (S : ℚ_[37])` where `S = ∑_{a} ω³¹(a)·a.val ∈ ℤ_[37]`.

This is `natCast_mul_BernoulliGen_one_of_ne_one` for the non-trivial character
`ω³¹ = (teichmullerCharQp 37)^31`, with the `ℚ_[37]`-sum recognised as the
coercion of the `ℤ_[37]`-sum (each `ω³¹(a)` is the coercion of the `ℤ_[37]`-valued
`(teichmullerChar 37)^31 a`). -/
theorem thirtyseven_mul_bernoulliGen_eq_intSum :
    (37 : ℚ_[37]) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1 =
      ((∑ a : ZMod 37, ((teichmullerChar 37) ^ 31) a * (a.val : ℤ_[37]) : ℤ_[37]) : ℚ_[37]) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set ωZ : DirichletCharacter ℤ_[37] 37 := (teichmullerChar 37) ^ 31 with hωZ
  set ωQ : DirichletCharacter ℚ_[37] 37 := (teichmullerCharQp 37) ^ 31 with hωQ
  have hωQ_def : ωQ = ωZ.ringHomComp PadicInt.Coe.ringHom :=
    teichmullerCharQp_pow_eq_ringHomComp (p := 37) (n := 31)
  -- `ω³¹ ≠ 1` since `36 ∤ 31`.
  have hne : ¬ (37 - 1) ∣ 31 := by decide
  have hωQ_ne_one : ωQ ≠ 1 :=
    teichmullerCharQp_pow_ne_one_of_not_dvd (p := 37) hne
  -- the cleared first-value formula.
  have hB := natCast_mul_BernoulliGen_one_of_ne_one (R := ℚ_[37]) (N := 37) (χ := ωQ) hωQ_ne_one
  -- the `ℚ`-sum is the coercion of the `ℤ_[37]`-sum.
  have hS_coe : ((∑ a : ZMod 37, ωZ a * (a.val : ℤ_[37]) : ℤ_[37]) : ℚ_[37]) =
      ∑ a : ZMod 37, ωQ a * (a.val : ℚ_[37]) := by
    rw [PadicInt.coe_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hωQ_def, PadicInt.coe_mul, PadicInt.coe_natCast]
    rfl
  have h37 : (37 : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) := by norm_cast
  rw [h37, hB, ← hS_coe]

set_option linter.unusedSectionVars false in
set_option maxRecDepth 8000 in
/-- The integral sum `S = ∑_{a} ω³¹(a)·a.val` is congruent to `31487` modulo
`37³` in `ℤ_[37]`.

Each summand `ω³¹(a)·a.val ≡ (a.val)^{31·37²+1} = (a.val)^{42440} (mod 37³)`
(`teichmullerChar_pow_mul_val_sModEq` at `i = 31`); summing
(`SModEq.sum`) and applying `sum_val_pow_sModEq_const` gives `S ≡ 31487`. -/
theorem intSum_sModEq_const :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    (∑ a : ZMod 37, ((teichmullerChar 37) ^ 31) a * (a.val : ℤ_[37])) ≡ (31487 : ℤ_[37])
      [SMOD (IsLocalRing.maximalIdeal ℤ_[37]) ^ 3] := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hexp : 31 * 37 ^ 2 + 1 = 42440 := by norm_num
  refine SModEq.trans (SModEq.sum (s := Finset.univ) (fun a _ => ?_)) sum_val_pow_sModEq_const
  -- `ω³¹(a)·a.val ≡ (a.val)^{31·37²+1}`, and `31·37²+1 = 42440`.
  have h := teichmullerChar_pow_mul_val_sModEq (p := 37) 31 a
  rwa [hexp] at h

set_option linter.unusedSectionVars false in
set_option maxRecDepth 8000 in
/-- **Norm bridge.** From the `mod 37³` congruence `37·B_{1,ω^{31}} ≡ 31487`
in `ℤ_[37]`, the difference in `ℚ_[37]` has norm `≤ 37⁻³`:
`‖37·B_{1,ω^{31}} - 31487‖ ≤ 37⁻³`. -/
theorem norm_thirtyseven_mul_bernoulliGen_sub_const_le :
    ‖(37 : ℚ_[37]) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1 - (31487 : ℚ_[37])‖ ≤
      (37 : ℝ) ^ (-3 : ℤ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set S : ℤ_[37] := ∑ a : ZMod 37, ((teichmullerChar 37) ^ 31) a * (a.val : ℤ_[37]) with hS
  -- `S - 31487 ∈ (maximalIdeal)^3`, hence `‖S - 31487‖ ≤ 37⁻³` in `ℤ_[37]`.
  have hnorm_int : ‖S - (31487 : ℤ_[37])‖ ≤ (37 : ℝ) ^ (-3 : ℤ) := by
    have hmem : S - (31487 : ℤ_[37]) ∈ (IsLocalRing.maximalIdeal ℤ_[37]) ^ 3 :=
      SModEq.sub_mem.mp intSum_sModEq_const
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] at hmem
    have hpow : ((37 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) = (37 : ℝ) ^ (-3 : ℤ) := by norm_num
    rw [← hpow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (S - (31487 : ℤ_[37])) 3).2 hmem
  -- transport to `ℚ_[37]` via the isometric coercion.
  have hcoe_eq : (37 : ℚ_[37]) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1 - (31487 : ℚ_[37])
      = (((S - (31487 : ℤ_[37])) : ℤ_[37]) : ℚ_[37]) := by
    rw [thirtyseven_mul_bernoulliGen_eq_intSum, ← hS, PadicInt.coe_sub]
    norm_cast
  rw [hcoe_eq, PadicInt.padic_norm_e_of_padicInt]
  exact hnorm_int

set_option linter.unusedSectionVars false in
/-- The constant `31487 = 37²·23` has `37`-adic norm exactly `37⁻²` (since
`37 ∤ 23`). -/
theorem norm_const_eq :
    ‖(31487 : ℚ_[37])‖ = (37 : ℝ) ^ (-2 : ℤ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `31487 = 37² · 23` as naturals, with `37 ∤ 23`.
  have hfac : (31487 : ℚ_[37]) = ((37 ^ 2 : ℕ) : ℚ_[37]) * ((23 : ℕ) : ℚ_[37]) := by
    norm_num
  rw [hfac, norm_mul]
  -- `‖(37² : ℚ₃₇)‖ = 37⁻²`.
  have h1 : ‖((37 ^ 2 : ℕ) : ℚ_[37])‖ = (37 : ℝ) ^ (-2 : ℤ) := by
    rw [show ((37 ^ 2 : ℕ) : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) ^ 2 by push_cast; ring, norm_pow,
      Padic.norm_p]
    rw [show (-2 : ℤ) = -(2 : ℕ) by norm_num, zpow_neg, zpow_natCast]; norm_num
  -- `‖(23 : ℚ₃₇)‖ = 1` since `37 ∤ 23`.
  have h2 : ‖((23 : ℕ) : ℚ_[37])‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 37) (n := 23)).2 (by decide)
  rw [h1, h2, mul_one]

set_option linter.unusedSectionVars false in
/-- **The sharp valuation, proved.** `(37 : ℝ)^{-2} < ‖-½·B_{1,ω^{31}}‖`, i.e.
`v₃₇(B_{1,ω^{31}}) ≤ 1`, established unconditionally by the Teichmüller modular
computation `37·B_{1,ω^{31}} ≡ 31487 = 37²·23 (mod 37³)`.

`‖37·B - 31487‖ ≤ 37⁻³ < 37⁻² = ‖31487‖`, so by ultrametricity `‖37·B‖ = 37⁻²`;
dividing by the `37`-unit `37·(-½)⁻¹` gives `‖-½·B‖ = ‖37·B‖/37⁻¹·… = 37⁻¹ > 37⁻²`. -/
theorem flt37SharpHMinusValuation_proved : Flt37SharpHMinusValuation := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  unfold Flt37SharpHMinusValuation
  -- `‖37·B‖ = ‖31487‖ = 37⁻²` by ultrametricity.
  have hlt : ‖(37 : ℚ_[37]) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1 - (31487 : ℚ_[37])‖ <
      ‖(31487 : ℚ_[37])‖ := by
    rw [norm_const_eq]
    refine lt_of_le_of_lt norm_thirtyseven_mul_bernoulliGen_sub_const_le ?_
    apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 37)
    norm_num
  have hnorm_37B : ‖(37 : ℚ_[37]) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ =
      (37 : ℝ) ^ (-2 : ℤ) := by
    rw [Padic.norm_eq_of_norm_sub_lt_right hlt, norm_const_eq]
  -- `‖37·B‖ = ‖37‖·‖B‖ = 37⁻¹·‖B‖`, so `‖B‖ = 37⁻¹`.
  have h37norm : ‖(37 : ℚ_[37])‖ = (37 : ℝ) ^ (-1 : ℤ) := by
    rw [show (37 : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) by norm_cast, Padic.norm_p]; simp
  have hnormB : ‖BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ = (37 : ℝ) ^ (-1 : ℤ) := by
    have hmul : (37 : ℝ) ^ (-1 : ℤ) * ‖BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ =
        (37 : ℝ) ^ (-2 : ℤ) := by rw [← h37norm, ← norm_mul]; exact hnorm_37B
    have h37ne : (37 : ℝ) ^ (-1 : ℤ) ≠ 0 := by positivity
    -- `37⁻¹ · ‖B‖ = 37⁻²` and `37⁻² = 37⁻¹ · 37⁻¹` ⟹ `‖B‖ = 37⁻¹`.
    have hsplit : (37 : ℝ) ^ (-2 : ℤ) = (37 : ℝ) ^ (-1 : ℤ) * (37 : ℝ) ^ (-1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (37 : ℝ) ≠ 0)]; norm_num
    rw [hsplit] at hmul
    exact mul_left_cancel₀ h37ne hmul
  -- `‖-½·B‖ = ‖B‖ = 37⁻¹ > 37⁻²`.
  have hhalf : ‖(-(1 / 2 : ℚ_[37]))‖ = 1 := by
    rw [norm_neg]
    have : ‖(2 : ℚ_[37])‖ = 1 := by
      have : ‖((2 : ℕ) : ℚ_[37])‖ = 1 :=
        (Padic.norm_natCast_eq_one_iff (p := 37) (n := 2)).2 (by decide)
      simpa using this
    rw [show (1 / 2 : ℚ_[37]) = (2 : ℚ_[37])⁻¹ by norm_num, norm_inv, this, inv_one]
  rw [norm_mul, hhalf, one_mul, hnormB]
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 37)
  norm_num

set_option linter.unusedSectionVars false in
/-- The classical irregular Bernoulli ratio `B₃₂/32`, as a `37`-adic number,
has norm `> 37⁻²` — equivalently `v₃₇(B₃₂/32) ≤ 1`.  This is **proved** from the
banked `kellner_at_zero_not_dvd` (`37² ∤ B₃₂.num`): if `‖(B₃₂/32 : ℚ₃₇)‖ ≤ 37⁻²`
then, multiplying by the `37`-unit `B₃₂.den · 32`, `‖(B₃₂.num : ℚ₃₇)‖ ≤ 37⁻²`,
i.e. `37² ∣ B₃₂.num`, contradiction. -/
theorem norm_bernoulli_thirtytwo_ratio_gt :
    (37 : ℝ) ^ (-2 : ℤ) <
      ‖(((bernoulli 32 : ℚ) / 32 : ℚ) : ℚ_[37])‖ := by
  -- `37 ∤ B₃₂.den` (= 510) and `37 ∤ 32`, so `D := B₃₂.den · 32` is a `37`-unit.
  have hden : (bernoulli 32).den = 510 := bernoulli_thirtytwo_den_eq
  by_contra hle
  push Not at hle
  -- `(B₃₂/32 : ℚ₃₇) · (B₃₂.den · 32) = (B₃₂.num : ℚ₃₇)`.
  have hnum_eq : (((bernoulli 32 : ℚ) / 32 : ℚ) : ℚ_[37]) *
      (((bernoulli 32).den : ℚ_[37]) * (32 : ℚ_[37])) = ((bernoulli 32).num : ℚ_[37]) := by
    have hQ : ((bernoulli 32 : ℚ) / 32) * (((bernoulli 32).den : ℚ) * 32) =
        ((bernoulli 32).num : ℚ) := by
      have h32 : (32 : ℚ) ≠ 0 := by norm_num
      have hden0 : ((bernoulli 32).den : ℚ) ≠ 0 := by
        exact_mod_cast Rat.den_ne_zero (bernoulli 32)
      have hbase : (bernoulli 32 : ℚ) * ((bernoulli 32).den : ℚ) = ((bernoulli 32).num : ℚ) := by
        have hnd := Rat.num_div_den (bernoulli 32)
        field_simp at hnd
        linarith [hnd]
      calc ((bernoulli 32 : ℚ) / 32) * (((bernoulli 32).den : ℚ) * 32)
          = (bernoulli 32 : ℚ) * ((bernoulli 32).den : ℚ) * (32 / 32) := by ring
        _ = (bernoulli 32 : ℚ) * ((bernoulli 32).den : ℚ) := by rw [div_self h32, mul_one]
        _ = ((bernoulli 32).num : ℚ) := hbase
    calc (((bernoulli 32 : ℚ) / 32 : ℚ) : ℚ_[37]) *
            (((bernoulli 32).den : ℚ_[37]) * (32 : ℚ_[37]))
          = ((((bernoulli 32 : ℚ) / 32) * (((bernoulli 32).den : ℚ) * 32) : ℚ) : ℚ_[37]) := by
            push_cast; ring
      _ = ((bernoulli 32).num : ℚ_[37]) := by rw [hQ]; push_cast; ring
  -- the unit factor has norm `1`.
  have hD_norm : ‖((bernoulli 32).den : ℚ_[37]) * (32 : ℚ_[37])‖ = 1 := by
    rw [norm_mul]
    have h1 : ‖((bernoulli 32).den : ℚ_[37])‖ = 1 := by
      rw [hden]
      exact (Padic.norm_natCast_eq_one_iff (p := 37) (n := 510)).2 (by decide)
    have h2 : ‖(32 : ℚ_[37])‖ = 1 := by
      have : ‖((32 : ℕ) : ℚ_[37])‖ = 1 :=
        (Padic.norm_natCast_eq_one_iff (p := 37) (n := 32)).2 (by decide)
      simpa using this
    rw [h1, h2, mul_one]
  -- conclude `‖(B₃₂.num : ℚ₃₇)‖ ≤ 37⁻²`, i.e. `37² ∣ B₃₂.num`, contradiction.
  have hnum_le : ‖((bernoulli 32).num : ℚ_[37])‖ ≤ (37 : ℝ) ^ (-2 : ℤ) := by
    rw [← hnum_eq, norm_mul, hD_norm, mul_one]
    exact hle
  have hdvd : ((37 : ℕ) ^ 2 : ℤ) ∣ (bernoulli 32).num := by
    have := (Padic.norm_int_le_pow_iff_dvd (p := 37) (k := (bernoulli 32).num) 2).1
    apply this
    have hpow : ((37 : ℕ) : ℝ) ^ (-(2 : ℕ) : ℤ) = (37 : ℝ) ^ (-2 : ℤ) := by norm_num
    rw [hpow]; exact hnum_le
  exact kellner_at_zero_not_dvd (by exact_mod_cast hdvd)

/-- **The remaining analytic boundary: the mod-`37²` Kummer congruence.**

`B_{1,ω^{31}} ≡ B₃₂/32 (mod 37²)` in `ℚ₃₇`, i.e. the two `37`-adic numbers
differ by something of norm `≤ 37⁻²`.  This is the sharp (mod-`p²`) form of the
Kummer congruence `bernoulliGen_teichmuller_pow_sModEq_div` (which only gives the
mod-`p` form) specialised to the irregular index `(p, k) = (37, 32)`. -/
def Flt37KummerCongruenceModSq : Prop :=
    ‖BernoulliGen ((teichmullerCharQp 37) ^ 31) 1 -
        (((bernoulli 32 : ℚ) / 32 : ℚ) : ℚ_[37])‖ ≤ (37 : ℝ) ^ (-2 : ℤ)

set_option linter.unusedSectionVars false in
/-- **The sharp valuation from the mod-`37²` Kummer congruence.**  Given the
congruence `B_{1,ω^{31}} ≡ B₃₂/32 (mod 37²)`, ultrametricity with
`norm_bernoulli_thirtytwo_ratio_gt` (`‖B₃₂/32‖ > 37⁻²`) yields
`‖B_{1,ω^{31}}‖ = ‖B₃₂/32‖ > 37⁻²`, hence `Flt37SharpHMinusValuation`. -/
theorem flt37SharpHMinusValuation_of_kummerCongruenceModSq
    (h : Flt37KummerCongruenceModSq) : Flt37SharpHMinusValuation := by
  unfold Flt37KummerCongruenceModSq at h
  unfold Flt37SharpHMinusValuation
  -- `‖-½ · B_{1,ω^{31}}‖ = ‖B_{1,ω^{31}}‖`.
  have hhalf : ‖(-(1 / 2 : ℚ_[37]))‖ = 1 := by
    rw [norm_neg]
    have : ‖(2 : ℚ_[37])‖ = 1 := by
      have : ‖((2 : ℕ) : ℚ_[37])‖ = 1 :=
        (Padic.norm_natCast_eq_one_iff (p := 37) (n := 2)).2 (by decide)
      simpa using this
    rw [show (1 / 2 : ℚ_[37]) = (2 : ℚ_[37])⁻¹ by norm_num, norm_inv, this, inv_one]
  have hfactor : ‖(-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ =
      ‖BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ := by
    rw [norm_mul, hhalf, one_mul]
  rw [hfactor]
  -- `‖B_{1,ω^{31}}‖ = ‖B₃₂/32‖` via the strict ultrametric estimate.
  have hgt := norm_bernoulli_thirtytwo_ratio_gt
  have hlt : ‖BernoulliGen ((teichmullerCharQp 37) ^ 31) 1 -
      (((bernoulli 32 : ℚ) / 32 : ℚ) : ℚ_[37])‖ <
      ‖(((bernoulli 32 : ℚ) / 32 : ℚ) : ℚ_[37])‖ := lt_of_le_of_lt h hgt
  rw [Padic.norm_eq_of_norm_sub_lt_right hlt]
  exact hgt

end SharpInput

section ChainStep1

variable [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)]

set_option linter.unusedSectionVars false in
/-- **Step 1: `37² ∤ h⁻`** from the sharp valuation input.

By `dvd_sq_hMinus_iff_norm_irregularFactor_le`, `37² ∣ h⁻` is equivalent to
`‖factor‖ ≤ 37⁻²`; `Flt37SharpHMinusValuation` is exactly its negation. -/
theorem flt37_not_dvd_sq_hMinus (h_sharp : Flt37SharpHMinusValuation) :
    ¬ (37 : ℕ) ^ 2 ∣ hMinus (CyclotomicField 37 ℚ) := by
  rw [dvd_sq_hMinus_iff_norm_irregularFactor_le]
  exact not_le.mpr h_sharp

set_option linter.unusedSectionVars false in
/-- **Step 1 ⇒ Step 3 packaged: `37² ∤ h` from the sharp valuation input.** -/
theorem flt37_not_dvd_sq_h (h_sharp : Flt37SharpHMinusValuation) :
    ¬ (37 : ℕ) ^ 2 ∣ h (CyclotomicField 37 ℚ) :=
  flt37_not_dvd_sq_h_of_not_dvd_sq_hMinus (flt37_not_dvd_sq_hMinus h_sharp)

set_option linter.unusedSectionVars false in
/-- **`37² ∤ h⁻`, unconditional.** The sharp `37`-adic valuation
`v₃₇(h⁻) = v₃₇(B_{1,ω^{31}}) = 1` is supplied by the Teichmüller modular
computation (`flt37SharpHMinusValuation_proved`), so no hypothesis remains. -/
theorem flt37_not_dvd_sq_hMinus_uncond :
    ¬ (37 : ℕ) ^ 2 ∣ hMinus (CyclotomicField 37 ℚ) :=
  flt37_not_dvd_sq_hMinus flt37SharpHMinusValuation_proved

set_option linter.unusedSectionVars false in
/-- **`37² ∤ h`, unconditional.** Combines the unconditional `37² ∤ h⁻`
(`flt37_not_dvd_sq_hMinus_uncond`), `37 ∤ h⁺` (Sinnott), and `h = h⁺·h⁻`. -/
theorem flt37_not_dvd_sq_h_uncond :
    ¬ (37 : ℕ) ^ 2 ∣ h (CyclotomicField 37 ℚ) :=
  flt37_not_dvd_sq_h flt37SharpHMinusValuation_proved

end ChainStep1

end ChainSteps

/-! ### Group-theoretic pigeonhole: a `p`-torsion subgroup of a group with
`p² ∤ card` has order `≤ p` -/

/-- **Steps 4–5 (abstract form).** If `G` is a finite commutative group with
`p² ∤ Nat.card G`, then any subgroup `C` all of whose elements are killed by `p`
(`∀ x : C, x ^ p = 1`) has `Nat.card C ≤ p`.

Proof: `C` is a `p`-group (every element has order dividing the prime `p`, so a
power of `p`), hence `Nat.card C = p ^ n` for some `n`.  Lagrange gives
`Nat.card C ∣ Nat.card G`, so `n ≤ 1` (else `p² ∣ p^n ∣ Nat.card G`).  Thus
`Nat.card C ≤ p`. -/
theorem card_le_prime_of_ptorsion_subgroup_of_not_dvd_sq
    {G : Type*} [CommGroup G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ p ^ 2 ∣ Nat.card G)
    (C : Subgroup G) (hC : ∀ x : C, x ^ p = 1) :
    Nat.card C ≤ p := by
  have hp : p.Prime := Fact.out
  -- `C` is a `p`-group.
  have hpgroup : IsPGroup p C := by
    intro x
    exact ⟨1, by simpa [pow_one] using hC x⟩
  -- Hence `Nat.card C = p ^ n`.
  obtain ⟨n, hn⟩ := hpgroup.exists_card_eq
  -- Lagrange: `Nat.card C ∣ Nat.card G`.
  have hdvd : Nat.card C ∣ Nat.card G := Subgroup.card_subgroup_dvd_card C
  -- `n ≤ 1`.
  have hn_le : n ≤ 1 := by
    by_contra hlt
    push Not at hlt
    -- `2 ≤ n`, so `p² ∣ p^n = Nat.card C ∣ Nat.card G`.
    have hp2_dvd : p ^ 2 ∣ p ^ n := pow_dvd_pow p hlt
    exact hG (dvd_trans hp2_dvd (hn ▸ hdvd))
  -- `Nat.card C = p ^ n ≤ p ^ 1 = p`.
  calc Nat.card C = p ^ n := hn
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hn_le
    _ = p := pow_one p

/-! ## The Case-I Herbrand bound (Eichler pigeonhole input) -/

section HerbrandBound

variable [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)]

set_option linter.unusedSectionVars false in
/-- **The Case-I Herbrand bound, `37² ∤ h` form.** For any `37`-torsion subgroup
`C⁻ ⊆ ClassGroup (𝓞 (CyclotomicField 37 ℚ))` (i.e. `x ^ 37 = 1` for all
`x ∈ C⁻`), `Nat.card C⁻ ≤ 37`.

This is Eichler's pigeonhole input (DM-A3): the `37`-Sylow of the cyclotomic
class group is cyclic (`37² ∤ h`), so every `37`-torsion subgroup has order at
most `37`, equivalently `p`-rank `C⁻ ≤ 1`. -/
theorem caseI_pRank_minus_bound_of_not_dvd_sq_h
    (hh : ¬ (37 : ℕ) ^ 2 ∣ h (CyclotomicField 37 ℚ))
    (C : Subgroup (ClassGroup (𝓞 (CyclotomicField 37 ℚ))))
    (hC : ∀ x : C, x ^ 37 = 1) :
    Nat.card C ≤ 37 := by
  -- `Nat.card (ClassGroup (𝓞 K)) = h K`, so `37² ∤ Nat.card (ClassGroup …)`.
  have hcard : ¬ (37 : ℕ) ^ 2 ∣ Nat.card (ClassGroup (𝓞 (CyclotomicField 37 ℚ))) := by
    rwa [Nat.card_eq_fintype_card, ← BernoulliRegular.h]
  exact card_le_prime_of_ptorsion_subgroup_of_not_dvd_sq (p := 37) hcard C hC

/-- **The Case-I Herbrand bound from the sharp valuation input.** Combines the
analytic `37² ∤ h⁻` (`flt37_not_dvd_sq_hMinus`), `37 ∤ h⁺` (Sinnott), and the
cyclic-Sylow pigeonhole.  Closed modulo the single sharp `37`-adic fact
`Flt37SharpHMinusValuation` (`v₃₇(B_{1,ω^{31}}) ≤ 1`). -/
theorem caseI_pRank_minus_bound (h_sharp : Flt37SharpHMinusValuation)
    (C : Subgroup (ClassGroup (𝓞 (CyclotomicField 37 ℚ))))
    (hC : ∀ x : C, x ^ 37 = 1) :
    Nat.card C ≤ 37 :=
  caseI_pRank_minus_bound_of_not_dvd_sq_h (flt37_not_dvd_sq_h h_sharp) C hC

set_option linter.unusedSectionVars false in
/-- **The Case-I Herbrand bound, unconditional.** For any `37`-torsion subgroup
`C⁻ ⊆ ClassGroup (𝓞 (CyclotomicField 37 ℚ))`, `Nat.card C⁻ ≤ 37`.

The sharp valuation `v₃₇(B_{1,ω^{31}}) ≤ 1` is now **proved** by the Teichmüller
modular computation (`flt37SharpHMinusValuation_proved`:
`37·B_{1,ω^{31}} ≡ 37²·23 (mod 37³)`), so the Eichler pigeonhole input is
unconditional: the `37`-Sylow of the cyclotomic class group is cyclic. -/
theorem caseI_pRank_minus_bound_uncond
    (C : Subgroup (ClassGroup (𝓞 (CyclotomicField 37 ℚ))))
    (hC : ∀ x : C, x ^ 37 = 1) :
    Nat.card C ≤ 37 :=
  caseI_pRank_minus_bound flt37SharpHMinusValuation_proved C hC

end HerbrandBound

end Eichler

end FLT37

end BernoulliRegular

end
