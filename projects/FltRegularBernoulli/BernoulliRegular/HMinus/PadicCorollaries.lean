module

public import Mathlib.NumberTheory.Bernoulli
public import BernoulliRegular.KummerCongruence
public import BernoulliRegular.HMinus.LValueReduction

/-!
# `h⁻` mod `p` corollaries (Diekmann page 51)

The two displayed congruences on page 51 of Diekmann 2023, used directly in
the proof of Theorem 42:

* `hMinus_formula_teichmuller_mod_p` — separating the boundary factor `j = p - 2`
  gives `h⁻ ≡ ∏_{1 ≤ j ≤ p-4, odd j} (-1/2) · B_{1,ω^j}  (mod p)`.
* `hMinus_formula_bernoulli_mod_p` — substituting Corollary 34 gives
  `h⁻ ≡ ∏_{1 ≤ j ≤ p-4, odd j} (-1/2) · B_{j+1} / (j+1)  (mod p)`.

Both are proved on top of `hMinus_formula_teichmuller`
(`BernoulliRegular.HMinus.LValueReduction`), now fully proved in the
completed T023 chain. These corollaries are therefore established on a
sorry-free base.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

section PadicCorollaries

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

lemma neg_one_half_mem_padicInt (hp_odd' : p ≠ 2) :
    ∃ c : ℤ_[p], (c : ℚ_[p]) = -(1 / 2 : ℚ_[p]) := by
  have hp' : Nat.Prime p := hp.out
  have h2_not_dvd : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by positivity) h
    exact hp_odd' (le_antisymm hle hp'.two_le)
  have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simpa [Nat.coprime_comm] using hp'.coprime_iff_not_dvd.mpr h2_not_dvd
  let c : ℤ_[p] := -((h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val)
  have hunit_mul : ((((h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) : ℚ_[p])) * (2 : ℚ_[p]) = 1 := by
    have h2_spec : ((h2_unit.unit : (ℤ_[p])ˣ) : ℤ_[p]) = 2 := h2_unit.unit_spec
    have h2_specQ : ((((h2_unit.unit : (ℤ_[p])ˣ).val : ℤ_[p]) : ℚ_[p])) = (2 : ℚ_[p]) :=
      congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) h2_spec
    rw [← h2_specQ]
    change (((((h2_unit.unit⁻¹ : (ℤ_[p])ˣ) * h2_unit.unit).val : ℤ_[p]) : ℚ_[p])) = 1
    simp
  have hhalf : ((((h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) : ℚ_[p])) = (1 / 2 : ℚ_[p]) :=
    eq_one_div_of_mul_eq_one_left hunit_mul
  refine ⟨c, ?_⟩
  simp [c, hhalf]

lemma prod_eq_prod_add_p_mul
    {α : Type*} (s : Finset α) (f : α → ℚ_[p]) (g : α → ℤ_[p])
    (hfg : ∀ a ∈ s, ∃ z : ℤ_[p],
      f a = (g a : ℚ_[p]) + (p : ℚ_[p]) * (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      (∏ a ∈ s, f a) = ((∏ a ∈ s, g a : ℤ_[p]) : ℚ_[p]) + (p : ℚ_[p]) * (z : ℚ_[p]) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨za, hza⟩ := hfg a (by simp)
      have hs : ∀ b ∈ s, ∃ z : ℤ_[p],
          f b = (g b : ℚ_[p]) + (p : ℚ_[p]) * (z : ℚ_[p]) :=
        fun b hb ↦ hfg b (by simp [hb])
      obtain ⟨zs, hzs⟩ := ih hs
      let w : ℤ_[p] := g a * zs + za * (∏ b ∈ s, g b) + (p : ℤ_[p]) * za * zs
      refine ⟨w, ?_⟩
      calc
        (∏ b ∈ insert a s, f b) = f a * ∏ b ∈ s, f b := by simp [ha]
        _ = (((g a : ℤ_[p]) : ℚ_[p]) + (p : ℚ_[p]) * (za : ℚ_[p])) *
              ((((∏ b ∈ s, g b : ℤ_[p]) : ℚ_[p])) + (p : ℚ_[p]) * (zs : ℚ_[p])) := by
                rw [hza, hzs]
        _ = (((g a * ∏ b ∈ s, g b : ℤ_[p]) : ℚ_[p])) +
              (p : ℚ_[p]) * (w : ℚ_[p]) := by
                simp [w]
                ring
        _ = (((∏ b ∈ insert a s, g b : ℤ_[p]) : ℚ_[p])) +
              (p : ℚ_[p]) * (w : ℚ_[p]) := by
                simp [ha]

/-- Diekmann page 51, first displayed congruence after equation (32): after
separating off the boundary factor `j = p - 2`, the relative class number is
congruent modulo `p` to the product over the remaining odd Teichmüller
characters.

Equivalently, there is some `z ∈ ℤ_p` such that

`h⁻ = ∏_{1 ≤ j ≤ p-4, odd j} (-1/2) · B_{1,ω^j} + pz`.

This is the form obtained by combining `hMinus_formula_teichmuller` with the
boundary-factor congruence from Diekmann's page 51. -/
theorem hMinus_formula_teichmuller_mod_p (hp_odd' : p ≠ 2) :
    ∃ z : ℤ_[p],
      ((hMinus K : ℕ) : ℚ_[p]) =
        Finset.prod ((Finset.range (p - 2)).filter fun j ↦ Odd j) (fun j ↦
          (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1) +
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp_gt : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')
  obtain ⟨c, hc⟩ := neg_one_half_mem_padicInt (p := p) hp_odd'
  let S := (Finset.range (p - 2)).filter fun j ↦ Odd j
  have hfactor :
      ∀ j ∈ S,
        ∃ a : ℤ_[p],
          (a : ℚ_[p]) = (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1 := by
    intro j hj
    have hj_lt : j < p - 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_odd : Odd j := (Finset.mem_filter.mp hj).2
    have hj_pos : 0 < j := by
      obtain ⟨k, hk⟩ := hj_odd
      omega
    have hj_not_dvd : ¬ (p - 1) ∣ (j + 1) := by
      refine Nat.not_dvd_of_pos_of_lt (by omega) ?_
      omega
    have hj_p_plus : ¬ (p : ℕ) ∣ (j + 1) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hj_p_plus_two : ¬ (p : ℕ) ∣ (j + 2) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨a₀, ha₀, _⟩ := exists_padicInt_bernoulli_factor
      (p := p) (hp := hp) (n := j + 1) hp_odd' (by omega) (by omega)
      (BernoulliRegular.prime_not_dvd_bernoulli_den_of_lt_sub_one
        (p := p) (n := j + 1) (hp := hp) hp_odd' (by omega))
    obtain ⟨z, hz⟩ := bernoulliGen_teichmuller_pow_sModEq_div
      (p := p) hp_odd' hj_odd hj_pos hj_not_dvd hj_p_plus hj_p_plus_two
      (by omega : j + 1 < p - 1)
    have hz' : BernoulliGen ((teichmullerCharQp p) ^ j) 1 =
        ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p])) +
          (p : ℚ_[p]) * (z : ℚ_[p]) := by
      rw [sub_eq_iff_eq_add] at hz
      simpa [add_comm] using hz
    refine ⟨a₀ + (p : ℤ_[p]) * (c * z), ?_⟩
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_mul, ha₀, hc, hz']
    simp [mul_add, mul_comm, mul_left_comm, mul_assoc, add_comm]
  classical
  let a : ℕ → ℤ_[p] := fun j ↦ if hj : j ∈ S then Classical.choose (hfactor j hj) else 1
  let A : ℤ_[p] := ∏ j ∈ S, a j
  have hA_cast :
      (A : ℚ_[p]) =
        Finset.prod S (fun j ↦
          (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1) := by
    calc
      (A : ℚ_[p]) = ∏ j ∈ S, ((a j : ℤ_[p]) : ℚ_[p]) := by
        dsimp [A]
        change (algebraMap ℤ_[p] ℚ_[p]) (∏ j ∈ S, a j) = ∏ j ∈ S, (algebraMap ℤ_[p] ℚ_[p]) (a j)
        rw [map_prod]
      _ = Finset.prod S (fun j ↦
            (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1) := by
          refine Finset.prod_congr rfl fun j hj ↦ ?_
          simpa [a, hj] using (Classical.choose_spec (hfactor j hj))
  have hp_sub_two_odd : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp_odd'
    refine ⟨k - 1, ?_⟩
    rw [hk]
    omega
  have hsplit : ((Finset.range (p - 1)).filter fun j ↦ Odd j) = insert (p - 2) S := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      show j ∈ S ↔ j < p - 2 ∧ Odd j by
        dsimp [S]
        rw [Finset.mem_filter, Finset.mem_range]]
    constructor
    · intro h
      by_cases hj : j = p - 2
      · exact Or.inl hj
      · exact Or.inr ⟨by omega, h.2⟩
    · intro h
      rcases h with rfl | h
      · exact ⟨by omega, hp_sub_two_odd⟩
      · exact ⟨by omega, h.2⟩
  obtain ⟨z₀, hz₀⟩ := boundary_teichmuller_factor_eq_one_add_p_mul (p := p) hp_odd'
  refine ⟨A * z₀, ?_⟩
  calc
    ((hMinus K : ℕ) : ℚ_[p])
        = (2 * p : ℚ_[p]) *
            Finset.prod ((Finset.range (p - 1)).filter fun j ↦ Odd j)
              (fun j ↦ (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1) :=
          hMinus_formula_teichmuller (p := p) (K := K) hp_odd'
    _ = (Finset.prod S (fun j ↦
            (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1)) *
          ((2 * p : ℚ_[p]) * (-(1 / 2 : ℚ_[p])) *
            BernoulliGen ((teichmullerCharQp p) ^ (p - 2)) 1) := by
          rw [hsplit, Finset.prod_insert]
          · ring
          · simp [S]
    _ = (A : ℚ_[p]) * (1 + (p : ℚ_[p]) * (z₀ : ℚ_[p])) := by rw [hA_cast, hz₀]
    _ = (A : ℚ_[p]) + (p : ℚ_[p]) * ((A * z₀ : ℤ_[p]) : ℚ_[p]) := by
          push_cast
          ring
    _ = Finset.prod S (fun j ↦
          (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1) +
          (p : ℚ_[p]) * ((A * z₀ : ℤ_[p]) : ℚ_[p]) := by rw [hA_cast]

/-- Diekmann page 51, second displayed congruence: substituting Corollary 34
into the preceding formula gives a product indexed by the classical Bernoulli
numbers.

Equivalently, there is some `z ∈ ℤ_p` such that

`h⁻ = ∏_{1 ≤ j ≤ p-4, odd j} (-1/2) · B_{j+1}/(j+1) + pz`.

This is the product form used to read off the divisibility criterion in
Theorem 42. -/
theorem hMinus_formula_bernoulli_mod_p (hp_odd' : p ≠ 2) :
    ∃ z : ℤ_[p],
      ((hMinus K : ℕ) : ℚ_[p]) =
        Finset.prod ((Finset.range (p - 2)).filter fun j ↦ Odd j) (fun j ↦
          (-(1 / 2 : ℚ_[p])) *
            ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p]))) +
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  obtain ⟨z₀, hz₀⟩ := hMinus_formula_teichmuller_mod_p (p := p) (K := K) hp_odd'
  obtain ⟨c, hc⟩ := neg_one_half_mem_padicInt (p := p) hp_odd'
  let S := (Finset.range (p - 2)).filter fun j ↦ Odd j
  have hfactor :
      ∀ j ∈ S,
        ∃ a : ℤ_[p],
          (a : ℚ_[p]) =
            (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p])) := by
    intro j hj
    have hj_lt : j < p - 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    obtain ⟨a, ha, _⟩ := exists_padicInt_bernoulli_factor
      (p := p) (hp := hp) (n := j + 1) hp_odd' (by omega) (by omega)
      (BernoulliRegular.prime_not_dvd_bernoulli_den_of_lt_sub_one
        (p := p) (n := j + 1) (hp := hp) hp_odd' (by omega))
    exact ⟨a, by simpa [Nat.cast_add, Nat.cast_one] using ha⟩
  classical
  let a : ℕ → ℤ_[p] := fun j ↦
    if hj : j ∈ S then Classical.choose (hfactor j hj) else 1
  have ha_cast :
      ∀ j ∈ S,
        ((a j : ℤ_[p]) : ℚ_[p]) =
          (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p])) := by
    intro j hj
    simpa [a, hj] using (Classical.choose_spec (hfactor j hj))
  have hbridge :
      ∀ j ∈ S,
        ∃ z : ℤ_[p],
          (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1 =
            (a j : ℚ_[p]) + (p : ℚ_[p]) * (z : ℚ_[p]) := by
    intro j hj
    have hp_gt : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')
    have hj_lt : j < p - 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_odd : Odd j := (Finset.mem_filter.mp hj).2
    have hj_pos : 0 < j := by
      obtain ⟨k, hk⟩ := hj_odd
      omega
    have hj_not_dvd : ¬ (p - 1) ∣ (j + 1) := by
      refine Nat.not_dvd_of_pos_of_lt (by omega) ?_
      omega
    have hj_p_plus : ¬ (p : ℕ) ∣ (j + 1) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hj_p_plus_two : ¬ (p : ℕ) ∣ (j + 2) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨z, hz⟩ := bernoulliGen_teichmuller_pow_sModEq_div
      (p := p) hp_odd' hj_odd hj_pos hj_not_dvd hj_p_plus hj_p_plus_two
      (by omega : j + 1 < p - 1)
    have hz' : BernoulliGen ((teichmullerCharQp p) ^ j) 1 =
        ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p])) +
          (p : ℚ_[p]) * (z : ℚ_[p]) := by
      rw [sub_eq_iff_eq_add] at hz
      simpa [add_comm] using hz
    refine ⟨c * z, ?_⟩
    calc
      (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1
          = (c : ℚ_[p]) *
              (((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p])) +
                (p : ℚ_[p]) * (z : ℚ_[p])) := by
                  rw [← hc, hz']
      _ = (a j : ℚ_[p]) + (p : ℚ_[p]) * ((c * z : ℤ_[p]) : ℚ_[p]) := by
            rw [ha_cast j hj, PadicInt.coe_mul, hc]
            ring
  obtain ⟨z₁, hz₁⟩ := prod_eq_prod_add_p_mul (p := p) S
    (fun j ↦ (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1) a hbridge
  have hA_cast :
      (((∏ j ∈ S, a j : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) =
        Finset.prod S (fun j ↦
          (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p]))) := by
    change (algebraMap ℤ_[p] ℚ_[p]) (∏ j ∈ S, a j) = _
    rw [map_prod]
    exact Finset.prod_congr rfl ha_cast
  refine ⟨z₁ + z₀, ?_⟩
  calc
    ((hMinus K : ℕ) : ℚ_[p]) =
        Finset.prod S (fun j ↦ (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1) +
          (p : ℚ_[p]) * (z₀ : ℚ_[p]) := hz₀
    _ = (((∏ j ∈ S, a j : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) +
          (p : ℚ_[p]) * (z₁ : ℚ_[p]) + (p : ℚ_[p]) * (z₀ : ℚ_[p]) := by
            rw [hz₁]
    _ = Finset.prod S (fun j ↦
          (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p]))) +
          (p : ℚ_[p]) * ((z₁ + z₀ : ℤ_[p]) : ℚ_[p]) := by
            rw [hA_cast]
            push_cast
            ring

end PadicCorollaries

end BernoulliRegular
