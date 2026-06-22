import BernoulliRegular.KummerCongruence.Bridge
import BernoulliRegular.IrregularPrimes.VonStaudtConsequences
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Kummer congruence interface for the Carlitz route

The final infinitude proof needs the unrestricted Kummer congruence:

```lean
m > 0, n > 0, Even m, Even n,
m ≡ n [MOD p - 1], ¬ (p - 1) ∣ n
  ⟹ B_m / m ≡ B_n / n mod p.
```

This file proves the congruence by the elementary Voronoi route: von
Staudt-Clausen integrality controls Bernoulli denominators, the strong
Faulhaber power-sum congruence feeds a strong Voronoi congruence, and the
primitive-root comparison removes the auxiliary side conditions.
-/

noncomputable section

namespace BernoulliRegular

/-! ### Basic congruence and p-unit bookkeeping -/

/-- Reflexivity for the local witness shape `x ≡ y (mod p)`. -/
theorem qpadic_mod_p_refl {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} :
    ∃ z : ℤ_[p], x - x = (p : ℚ_[p]) * (z : ℚ_[p]) :=
  ⟨0, by simp⟩

/-- Symmetry for the local witness shape `x ≡ y (mod p)`. -/
theorem qpadic_mod_p_symm {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]}
    (hxy : ∃ w : ℤ_[p], x - y = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p], y - x = (p : ℚ_[p]) * (w : ℚ_[p]) := by
  obtain ⟨w, hw⟩ := hxy
  refine ⟨-w, ?_⟩
  calc
    y - x = -(x - y) := by ring
    _ = (p : ℚ_[p]) * ((-w : ℤ_[p]) : ℚ_[p]) := by
      rw [hw]
      push_cast
      ring

/-- Transitivity for the local witness shape `x ≡ y (mod p)`. -/
theorem qpadic_mod_p_trans {p : ℕ} [Fact p.Prime] {x y z : ℚ_[p]}
    (hxy : ∃ w : ℤ_[p], x - y = (p : ℚ_[p]) * (w : ℚ_[p]))
    (hyz : ∃ w : ℤ_[p], y - z = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p], x - z = (p : ℚ_[p]) * (w : ℚ_[p]) := by
  obtain ⟨wxy, hwxy⟩ := hxy
  obtain ⟨wyz, hwyz⟩ := hyz
  refine ⟨wxy + wyz, ?_⟩
  calc
    x - z = (x - y) + (y - z) := by ring
    _ = (p : ℚ_[p]) * (((wxy + wyz : ℤ_[p]) : ℚ_[p])) := by
      rw [hwxy, hwyz]
      push_cast
      ring

/-- Add two congruence witnesses modulo `p`. -/
theorem qpadic_mod_p_add {p : ℕ} [Fact p.Prime] {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : ∃ w : ℤ_[p], x₁ - y₁ = (p : ℚ_[p]) * (w : ℚ_[p]))
    (h₂ : ∃ w : ℤ_[p], x₂ - y₂ = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p],
      (x₁ + x₂) - (y₁ + y₂) = (p : ℚ_[p]) * (w : ℚ_[p]) := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  refine ⟨w₁ + w₂, ?_⟩
  rw [show (x₁ + x₂) - (y₁ + y₂) = (x₁ - y₁) + (x₂ - y₂) by ring]
  rw [hw₁, hw₂]
  push_cast
  ring

/-- Subtract two congruence witnesses modulo `p`. -/
theorem qpadic_mod_p_sub {p : ℕ} [Fact p.Prime] {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : ∃ w : ℤ_[p], x₁ - y₁ = (p : ℚ_[p]) * (w : ℚ_[p]))
    (h₂ : ∃ w : ℤ_[p], x₂ - y₂ = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p],
      (x₁ - x₂) - (y₁ - y₂) = (p : ℚ_[p]) * (w : ℚ_[p]) := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  refine ⟨w₁ - w₂, ?_⟩
  rw [show (x₁ - x₂) - (y₁ - y₂) = (x₁ - y₁) - (x₂ - y₂) by ring]
  rw [hw₁, hw₂]
  push_cast
  ring

/-- Left multiplication by a p-adic integer preserves congruence modulo `p`. -/
theorem qpadic_mod_p_mul_padicInt {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) {x y : ℚ_[p]}
    (hxy : ∃ w : ℤ_[p], x - y = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p],
      (a : ℚ_[p]) * x - (a : ℚ_[p]) * y =
        (p : ℚ_[p]) * (w : ℚ_[p]) := by
  obtain ⟨w, hw⟩ := hxy
  refine ⟨a * w, ?_⟩
  rw [← mul_sub, hw]
  push_cast
  ring

/-- Right multiplication by a p-adic integer preserves congruence modulo `p`. -/
theorem qpadic_mod_p_padicInt_mul {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]} (a : ℤ_[p])
    (hxy : ∃ w : ℤ_[p], x - y = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p],
      x * (a : ℚ_[p]) - y * (a : ℚ_[p]) =
        (p : ℚ_[p]) * (w : ℚ_[p]) := by
  obtain ⟨w, hw⟩ := hxy
  refine ⟨w * a, ?_⟩
  rw [← sub_mul, hw]
  push_cast
  ring

/-- A natural number not divisible by `p` is a unit in `ℤ_[p]`. -/
theorem padicInt_natCast_isUnit_of_not_dvd
    {p n : ℕ} [Fact p.Prime] (h : ¬ p ∣ n) :
    IsUnit ((n : ℕ) : ℤ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact hp.coprime_iff_not_dvd.mpr h

/-- Split a positive natural number into its exact `p`-power and p-prime part. -/
theorem nat_eq_primePow_factorization_mul_unitPart
    {p n : ℕ} (_hn : n ≠ 0) :
    n = p ^ n.factorization p * (n / p ^ n.factorization p) :=
  (Nat.ordProj_mul_ordCompl_eq_self n p).symm

/-- The p-prime part of a nonzero natural number is not divisible by `p`. -/
theorem prime_not_dvd_factorization_unitPart
    {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ∣ n / p ^ n.factorization p :=
  hp.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hp hn)

/-- The p-prime part of a positive natural number is a p-adic unit. -/
theorem padicInt_factorization_unitPart_isUnit
    {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    IsUnit (((n / p ^ n.factorization p : ℕ) : ℤ_[p])) :=
  padicInt_natCast_isUnit_of_not_dvd
    (prime_not_dvd_factorization_unitPart (p := p) (n := n) Fact.out hn)

/-- Cast the exact `p`-power decomposition of a natural number to `ℚ_[p]`. -/
theorem qpadic_natCast_eq_primePow_mul_unitPart
    {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    ((n : ℕ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ n.factorization p *
        ((n / p ^ n.factorization p : ℕ) : ℚ_[p]) := by
  conv_lhs =>
    rw [nat_eq_primePow_factorization_mul_unitPart (p := p) (n := n) hn]
  push_cast
  ring

/-- Divide a natural numerator by a natural denominator after the numerator has
enough exact `p`-power to cover the denominator's `p`-part and an additional
`p^r`.  The remaining denominator is a p-adic unit. -/
theorem qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd
    {p A q r : ℕ} [Fact p.Prime] (hq_pos : 0 < q)
    (hdiv : p ^ (q.factorization p + r) ∣ A) :
    ∃ z : ℤ_[p],
      ((A : ℕ) : ℚ_[p]) / ((q : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ r * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set s : ℕ := q.factorization p with hs_def
  set u : ℕ := q / p ^ s with hu_def
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hs_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := q) hp hq_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have huInv_mul : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have huInv_mul_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) huInv_mul
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨(c : ℤ_[p]) * uInv, ?_⟩
  have hq_cast :
      ((q : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ s * ((u : ℕ) : ℚ_[p]) := by
    rw [hs_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := q) hq_ne
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_pow_ne : (p : ℚ_[p]) ^ s ≠ 0 := pow_ne_zero _ hpQ_ne
  rw [hc]
  push_cast
  rw [pow_add, hq_cast]
  calc
    ((p : ℚ_[p]) ^ s * (p : ℚ_[p]) ^ r * (c : ℚ_[p])) /
        ((p : ℚ_[p]) ^ s * (u : ℚ_[p]))
        = (p : ℚ_[p]) ^ r * ((c : ℚ_[p]) / (u : ℚ_[p])) := by
          field_simp [hp_pow_ne]
    _ = (p : ℚ_[p]) ^ r * ((c : ℚ_[p]) * (uInv : ℚ_[p])) := by
      rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right huInv_mul_Qp]
    _ = (p : ℚ_[p]) ^ r * (((c : ℤ_[p]) * uInv : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

/-! ### Basic arithmetic for the unrestricted Voronoi route -/

/-- Under the non-boundary even-index hypotheses of Kummer, an odd prime is
automatically at least `5`: the only excluded odd prime case is `p = 3`, where
`p - 1 = 2` divides every even index. -/
theorem five_le_of_odd_prime_and_even_nonboundary
    {p n : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hn_even : Even n) (hnot : ¬ (p - 1) ∣ n) :
    5 ≤ p := by
  have hp : Nat.Prime p := Fact.out
  by_contra hlt
  have hp_lt_five : p < 5 := Nat.lt_of_not_ge hlt
  have hp_ge_two : 2 ≤ p := hp.two_le
  interval_cases p <;> try contradiction
  · have htwo_dvd : 2 ∣ n := even_iff_two_dvd.mp hn_even
    exact hnot (by simpa using htwo_dvd)

/-- Remove the zero term from a positive power sum over `range p`.  This fixes
the indexing convention for the Voronoi proof while letting later lemmas keep
using `Finset.range p`, which matches the existing project infrastructure. -/
theorem range_pow_sum_eq_Icc_one_sub_one
    {p h : ℕ} [Fact p.Prime] (hh_pos : 0 < h) :
    (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h) =
      ∑ x ∈ Finset.Icc 1 (p - 1), (x : ℚ_[p]) ^ h := by
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hset : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0), by omega⟩
    · intro hx
      rcases hx with rfl | hx
      · exact hp_pos
      · omega
  rw [hset, Finset.sum_insert]
  · simp [hh_pos.ne']
  · simp

/-- Numerical valuation estimate from the elementary Voronoi proof.  For
`p ≥ 5`, the combined `p`-adic contributions of consecutive denominators
`s` and `s + 1` leave at least two powers beyond the `p`-adic contribution
already present in the index `h`. -/
theorem factorization_add_succ_factorization_add_two_le
    {p s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hs : 2 ≤ s) :
    s.factorization p + (s + 1).factorization p + 2 ≤ s := by
  have hp : Nat.Prime p := Fact.out
  have hp_pred_ge_four : 4 ≤ p - 1 := by omega
  have hs_ne : s ≠ 0 := by omega
  have hs_succ_ne : s + 1 ≠ 0 := by omega
  have hfac_s :=
    Nat.factorization_mul_pred_le_pred (ell := p) (n := s) hp hs_ne
  have hfac_succ :=
    Nat.factorization_mul_pred_le_pred (ell := p) (n := s + 1) hp hs_succ_ne
  have hfac_s_four : 4 * s.factorization p ≤ s - 1 := by
    calc
      4 * s.factorization p ≤ (p - 1) * s.factorization p :=
        Nat.mul_le_mul_right _ hp_pred_ge_four
      _ = s.factorization p * (p - 1) := by rw [Nat.mul_comm]
      _ ≤ s - 1 := hfac_s
  have hfac_succ_four : 4 * (s + 1).factorization p ≤ s := by
    calc
      4 * (s + 1).factorization p ≤
          (p - 1) * (s + 1).factorization p :=
        Nat.mul_le_mul_right _ hp_pred_ge_four
      _ = (s + 1).factorization p * (p - 1) := by rw [Nat.mul_comm]
      _ ≤ (s + 1) - 1 := hfac_succ
      _ = s := by omega
  omega

/-- Divisibility form of `factorization_add_succ_factorization_add_two_le`:
the `p^s` factor in the TeX Faulhaber term has enough room for the two
denominator valuations and the required extra `p^2`. -/
theorem primePow_factorization_add_succ_add_two_dvd_primePow
    {p s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hs : 2 ≤ s) :
    p ^ (s.factorization p + (s + 1).factorization p + 2) ∣ p ^ s :=
  pow_dvd_pow p (factorization_add_succ_factorization_add_two_le hp_ge_five hs)

/-- Binomial-strength divisibility for the higher Faulhaber terms.  The
factor `Nat.choose h s` supplies the difference between `v_p(s)` and
`v_p(h)`, while `p^(s+1)` has enough remaining p-power to absorb the
denominator `s + 1` and leave three extra powers relative to `h`. -/
theorem primePow_succFactorization_add_indexFactorization_add_three_dvd_choose_mul_primePow
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hs_two : 2 ≤ s) (hs_le : s ≤ h) :
    p ^ ((s + 1).factorization p + (h.factorization p + 3)) ∣
      Nat.choose h s * p ^ (s + 1) := by
  have hp : Nat.Prime p := Fact.out
  have hchoose_pos : 0 < Nat.choose h s := Nat.choose_pos hs_le
  have hchoose_ne : Nat.choose h s ≠ 0 := hchoose_pos.ne'
  have hpow_ne : p ^ (s + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hprod_ne : Nat.choose h s * p ^ (s + 1) ≠ 0 :=
    Nat.mul_ne_zero hchoose_ne hpow_ne
  have hchoose_lower :
      h.factorization p ≤ (Nat.choose h s).factorization p + s.factorization p :=
    Nat.factorization_le_factorization_choose_add (p := p) hs_le (by omega)
  have hden :=
    factorization_add_succ_factorization_add_two_le (p := p) hp_ge_five hs_two
  have htarget_le :
      (s + 1).factorization p + (h.factorization p + 3) ≤
        (Nat.choose h s).factorization p + (s + 1) := by
    omega
  refine (hp.pow_dvd_iff_le_factorization hprod_ne).mpr ?_
  calc
    (s + 1).factorization p + (h.factorization p + 3)
        ≤ (Nat.choose h s).factorization p + (s + 1) := htarget_le
    _ = (Nat.choose h s * p ^ (s + 1)).factorization p := by
      rw [Nat.factorization_mul hchoose_ne hpow_ne]
      simp [Nat.Prime.factorization_self hp]

/-- Convert an extra `p^(v_p(h)+3)` factor into the strong modulus
`h*p^2`, keeping one extra factor of `p` in the p-adic-integer witness. -/
theorem primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeSq
    {p h : ℕ} [Fact p.Prime] (hh_pos : 0 < h) (z : ℤ_[p]) :
    ∃ w : ℤ_[p],
      (p : ℚ_[p]) ^ (h.factorization p + 3) * (z : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set v : ℕ := h.factorization p with hv_def
  set u : ℕ := h / p ^ v with hu_def
  have hh_ne : h ≠ 0 := hh_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hv_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := h) hp hh_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hu_mul_inv : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hu_mul_inv_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul_inv
  refine ⟨(p : ℕ) * z * uInv, ?_⟩
  have hh_cast :
      ((h : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ v * ((u : ℕ) : ℚ_[p]) := by
    rw [hv_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := h) hh_ne
  rw [hh_cast]
  push_cast
  rw [pow_add]
  calc
    (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) =
        (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 2 * ((p : ℚ_[p]) * (z : ℚ_[p])) := by
      ring
    _ = (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((p : ℚ_[p]) * (z : ℚ_[p]) * (uInv : ℚ_[p])) := by
      rw [show (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((p : ℚ_[p]) * (z : ℚ_[p]) * (uInv : ℚ_[p])) =
          (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 2 *
            ((p : ℚ_[p]) * (z : ℚ_[p])) *
              ((u : ℚ_[p]) * (uInv : ℚ_[p])) by ring]
      rw [hu_mul_inv_Qp]
      ring

/-- The higher binomial terms in the strong power-sum proof are multiples of
`h*p^2` after dividing by their Faulhaber denominator. -/
theorem binomial_divisor_term_mem_h_p_sq
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hs_two : 2 ≤ s) (hs_le : s ≤ h) :
    ∃ z : ℤ_[p],
      (((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hdiv :
      p ^ ((s + 1).factorization p + (h.factorization p + 3)) ∣
        Nat.choose h s * p ^ (s + 1) :=
    primePow_succFactorization_add_indexFactorization_add_three_dvd_choose_mul_primePow
      (p := p) hp_ge_five hs_two hs_le
  obtain ⟨z, hz⟩ :=
    qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd
      (p := p) (A := Nat.choose h s * p ^ (s + 1)) (q := s + 1)
      (r := h.factorization p + 3) (by omega) hdiv
  obtain ⟨w, hw⟩ :=
    primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeSq
      (p := p) (h := h) hh_pos z
  refine ⟨w, ?_⟩
  calc
    (((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) =
        (p : ℚ_[p]) ^ (h.factorization p + 3) * (z : ℚ_[p]) := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hz
    _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := hw

/-- Stronger form of
`primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeSq`:
the same factor is an `h*p^3` multiple.  This is the form used before
multiplying by a Bernoulli number, whose denominator may contain one `p`. -/
theorem primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeCubed
    {p h : ℕ} [Fact p.Prime] (hh_pos : 0 < h) (z : ℤ_[p]) :
    ∃ w : ℤ_[p],
      (p : ℚ_[p]) ^ (h.factorization p + 3) * (z : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * (w : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set v : ℕ := h.factorization p with hv_def
  set u : ℕ := h / p ^ v with hu_def
  have hh_ne : h ≠ 0 := hh_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hv_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := h) hp hh_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hu_mul_inv : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hu_mul_inv_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul_inv
  refine ⟨z * uInv, ?_⟩
  have hh_cast :
      ((h : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ v * ((u : ℕ) : ℚ_[p]) := by
    rw [hv_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := h) hh_ne
  rw [hh_cast]
  push_cast
  rw [pow_add]
  calc
    (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) =
        (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 3 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) := by
      rw [show (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 3 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) =
          (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) *
            ((u : ℚ_[p]) * (uInv : ℚ_[p])) by ring]
      rw [hu_mul_inv_Qp]
      ring

/-- Cubic-strength version of `binomial_divisor_term_mem_h_p_sq`, used before
the possible single `p` in a Bernoulli denominator is absorbed. -/
theorem binomial_divisor_term_mem_h_p_cubed
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hs_two : 2 ≤ s) (hs_le : s ≤ h) :
    ∃ z : ℤ_[p],
      (((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) := by
  have hdiv :
      p ^ ((s + 1).factorization p + (h.factorization p + 3)) ∣
        Nat.choose h s * p ^ (s + 1) :=
    primePow_succFactorization_add_indexFactorization_add_three_dvd_choose_mul_primePow
      (p := p) hp_ge_five hs_two hs_le
  obtain ⟨z, hz⟩ :=
    qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd
      (p := p) (A := Nat.choose h s * p ^ (s + 1)) (q := s + 1)
      (r := h.factorization p + 3) (by omega) hdiv
  obtain ⟨w, hw⟩ :=
    primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeCubed
      (p := p) (h := h) hh_pos z
  refine ⟨w, ?_⟩
  calc
    (((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) =
        (p : ℚ_[p]) ^ (h.factorization p + 3) * (z : ℚ_[p]) := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hz
    _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * (w : ℚ_[p]) := hw

/-- Von Staudt denominator control in the only form needed by the strong
Faulhaber proof: `p*B_n` is always p-adically integral. -/
theorem p_mul_bernoulli_mem_padicInt
    {p n : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) :
    ∃ z : ℤ_[p],
      (p : ℚ_[p]) * ((bernoulli n : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · exact p_mul_bernoulli_mem_padicInt_vonStaudt (p := p) (n := n) hn_even
  · rcases eq_or_ne n 1 with rfl | hn_ne_one
    · have hp : Nat.Prime p := Fact.out
      have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) :=
        padicInt_natCast_isUnit_of_not_dvd (p := p) (n := 2) (by
          intro h
          have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by omega) h
          exact hp_odd (le_antisymm hp_le_two hp.two_le))
      set twoInv : ℤ_[p] := (h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val
      have htwo_mul_inv : ((2 : ℕ) : ℤ_[p]) * twoInv = 1 := by
        change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
        simp
      have htwo_mul_inv_Qp : (2 : ℚ_[p]) * ((twoInv : ℤ_[p]) : ℚ_[p]) = 1 := by
        exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) htwo_mul_inv
      refine ⟨-((p : ℕ) : ℤ_[p]) * twoInv, ?_⟩
      rw [bernoulli_one]
      have h2Q_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
      have h_half : ((-1 / 2 : ℚ) : ℚ_[p]) = -((twoInv : ℤ_[p]) : ℚ_[p]) :=
        mul_left_cancel₀ h2Q_ne (by push_cast; linear_combination htwo_mul_inv_Qp)
      rw [h_half]
      push_cast
      ring
    · refine ⟨0, ?_⟩
      have hn_gt : 1 < n := by
        rcases hn_odd with ⟨k, hk⟩
        omega
      rw [bernoulli_eq_zero_of_odd hn_odd hn_gt]
      simp

/-- Shifted higher Faulhaber terms with `s ≥ 2`: after multiplying by the
Bernoulli factor, the cubic coefficient bound loses at most one `p` and still
lands in `h*p^2`. -/
theorem shifted_faulhaber_term_mem_h_p_sq_of_two_le
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hs_two : 2 ≤ s) (hs_le : s ≤ h) :
    ∃ z : ℤ_[p],
      ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          ((((Nat.choose h s : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p]))) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hp_odd : p ≠ 2 := by omega
  obtain ⟨c, hc⟩ :=
    binomial_divisor_term_mem_h_p_cubed (p := p) hp_ge_five hh_pos hs_two hs_le
  obtain ⟨b, hb⟩ := p_mul_bernoulli_mem_padicInt (p := p) (n := h - s) hp_odd
  refine ⟨b * c, ?_⟩
  rw [hc]
  push_cast
  linear_combination ((h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (c : ℚ_[p])) * hb

/-- The exceptional shifted term `s = 1` in the strong Faulhaber proof.  For
`h > 2` it vanishes by odd Bernoulli zeroes; for `h = 2`, the denominator `4`
is a p-adic unit because `p ≥ 5`. -/
theorem shifted_faulhaber_one_term_mem_h_p_sq
    {p h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h) :
    ∃ z : ℤ_[p],
      ((bernoulli (h - 1) : ℚ) : ℚ_[p]) *
          ((((Nat.choose h 1 : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ 2) / ((2 : ℕ) : ℚ_[p]))) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  rcases eq_or_ne h 2 with rfl | hh_ne_two
  · have h4_unit : IsUnit ((4 : ℕ) : ℤ_[p]) :=
      padicInt_natCast_isUnit_of_not_dvd (p := p) (n := 4) (by
        intro hdiv
        have hp_le_four : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
        omega)
    set fourInv : ℤ_[p] := (h4_unit.unit⁻¹ : (ℤ_[p])ˣ).val
    have hfour_mul_inv : ((4 : ℕ) : ℤ_[p]) * fourInv = 1 := by
      change ((h4_unit.unit * h4_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
      simp
    have hfour_mul_inv_Qp : (4 : ℚ_[p]) * ((fourInv : ℤ_[p]) : ℚ_[p]) = 1 := by
      exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hfour_mul_inv
    refine ⟨-fourInv, ?_⟩
    rw [bernoulli_one, Nat.choose_one_right]
    push_cast
    have h : ((fourInv : ℤ_[p]) : ℚ_[p]) = (4 : ℚ_[p])⁻¹ :=
      (inv_eq_of_mul_eq_one_right hfour_mul_inv_Qp).symm
    rw [h]
    field_simp
    ring
  · refine ⟨0, ?_⟩
    rcases hh_even with ⟨m, hm⟩
    have hm_ge_two : 2 ≤ m := by
      by_contra hlt
      have hm_lt_two : m < 2 := Nat.lt_of_not_ge hlt
      interval_cases m <;> omega
    have h_odd : Odd (h - 1) := by
      refine ⟨m - 1, ?_⟩
      omega
    have h_gt : 1 < h - 1 := by omega
    rw [bernoulli_eq_zero_of_odd h_odd h_gt]
    push_cast
    ring

/-- Algebraic binomial reindexing used to pass from mathlib's Faulhaber
summand indexed by `i` to the TeX summand indexed by `s = h - i`. -/
theorem choose_succ_div_eq_choose_div
    {p h s : ℕ} [Fact p.Prime] (hs : s ≤ h) :
    ((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) / ((h + 1 : ℕ) : ℚ_[p]) =
      ((Nat.choose h s : ℕ) : ℚ_[p]) / ((s + 1 : ℕ) : ℚ_[p]) := by
  have hsym : Nat.choose (h + 1) (h - s) = Nat.choose (h + 1) (s + 1) := by
    have hs1 : s + 1 ≤ h + 1 := by omega
    have := Nat.choose_symm (n := h + 1) (k := s + 1) hs1
    simpa [Nat.add_sub_cancel_right, Nat.add_sub_assoc hs] using this
  have hmul_nat :
      (h + 1) * Nat.choose h s = Nat.choose (h + 1) (s + 1) * (s + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.add_one_mul_choose_eq h s
  have hmul :
      ((h + 1 : ℕ) : ℚ_[p]) * ((Nat.choose h s : ℕ) : ℚ_[p]) =
        ((Nat.choose (h + 1) (s + 1) : ℕ) : ℚ_[p]) *
          ((s + 1 : ℕ) : ℚ_[p]) := by
    exact_mod_cast hmul_nat
  have hh_ne : ((h + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs_ne : ((s + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hsym]
  field_simp [hh_ne, hs_ne]
  rw [hmul]

/-- Each non-leading Faulhaber summand is an `h*p^2` multiple, after
reindexing `i < h` as `s = h - i`. -/
theorem faulhaber_remainder_term_mem_h_p_sq
    {p h i : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h) (hi : i < h) :
    ∃ z : ℤ_[p],
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  set s : ℕ := h - i with hs_def
  have hs_pos : 0 < s := by omega
  have hs_le : s ≤ h := by omega
  have hi_eq : i = h - s := by omega
  have hexp_hs : h + 1 - (h - s) = s + 1 := by omega
  have hcoef :
      ((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p]) =
        ((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p]) := by
    have hchoose := choose_succ_div_eq_choose_div (p := p) (h := h) (s := s) hs_le
    calc
      ((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p]) =
          (((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) /
              ((h + 1 : ℕ) : ℚ_[p])) * ((p : ℚ_[p]) ^ (s + 1)) := by ring
      _ = (((Nat.choose h s : ℕ) : ℚ_[p]) / ((s + 1 : ℕ) : ℚ_[p])) *
            ((p : ℚ_[p]) ^ (s + 1)) := by rw [hchoose]
      _ = ((Nat.choose h s : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p]) := by ring
  by_cases hs_one : s = 1
  · obtain ⟨z, hz⟩ := shifted_faulhaber_one_term_mem_h_p_sq
      (p := p) (h := h) hp_ge_five hh_pos hh_even
    refine ⟨z, ?_⟩
    calc
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) =
        ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p])) := by
          rw [hi_eq, hexp_hs]
          ring
      _ = ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose h s : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) := by
          rw [hcoef]
      _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
          rw [hs_one]
          simpa using hz
  · have hs_two : 2 ≤ s := by omega
    obtain ⟨z, hz⟩ := shifted_faulhaber_term_mem_h_p_sq_of_two_le
      (p := p) (h := h) (s := s) hp_ge_five hh_pos hs_two hs_le
    refine ⟨z, ?_⟩
    calc
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) =
        ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose (h + 1) (h - s) : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((h + 1 : ℕ) : ℚ_[p])) := by
          rw [hi_eq, hexp_hs]
          ring
      _ = ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          (((Nat.choose h s : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p])) := by
          rw [hcoef]
      _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := hz

/-- Sum of all non-leading Faulhaber summands. -/
theorem faulhaber_remainder_sum_mem_h_p_sq
    {p h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h) :
    ∃ W : ℤ_[p],
      (∑ i ∈ Finset.range h,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p])) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]) := by
  choose w hw using (fun (i : ℕ) (hi : i < h) =>
    faulhaber_remainder_term_mem_h_p_sq (p := p) (h := h) (i := i)
      hp_ge_five hh_pos hh_even hi)
  set W : ℤ_[p] := ∑ i ∈ Finset.attach (Finset.range h),
    w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W, ?_⟩
  rw [← Finset.sum_attach]
  rw [show ((h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p])) =
      ∑ i ∈ Finset.attach (Finset.range h),
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[p]) : ℚ_[p]) from ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact hw i.1 (Finset.mem_range.mp i.2)
  · rw [hW_def]
    simp [PadicInt.coe_sum, Finset.mul_sum]

/-- Strong Faulhaber power-sum congruence from the TeX proof: the usual
`S_h(p) - p*B_h` difference carries the stronger modulus `h*p^2`. -/
theorem sum_range_pow_sub_p_mul_bernoulli_strong
    {p h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h)
    (_hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ h)) -
          (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  obtain ⟨W, hW⟩ := faulhaber_remainder_sum_mem_h_p_sq
    (p := p) (h := h) hp_ge_five hh_pos hh_even
  refine ⟨W, ?_⟩
  have h_faulhaber_Q : (∑ k ∈ Finset.range p, (k : ℚ) ^ h) =
      ∑ i ∈ Finset.range (h + 1),
        bernoulli i * ((Nat.choose (h + 1) i : ℕ) : ℚ) *
          (p : ℚ) ^ (h + 1 - i) / (h + 1 : ℚ) := by
    rw [sum_range_pow p h]
  have h_faulhaber_Qp : (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ h) =
      ∑ i ∈ Finset.range (h + 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) := by
    have := congrArg (fun q : ℚ => (q : ℚ_[p])) h_faulhaber_Q
    push_cast at this
    push_cast
    exact this
  have hterm_h :
      ((bernoulli h : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) h : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (h + 1 - h)) / ((h + 1 : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) := by
    have hhp1_ne : ((h + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.choose_succ_self_right h, show h + 1 - h = 1 by omega]
    push_cast
    field_simp [hhp1_ne]
  have h_split :
      (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ h) -
          (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) =
        ∑ i ∈ Finset.range h,
          ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (h + 1) i : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (h + 1 - i)) / ((h + 1 : ℕ) : ℚ_[p]) := by
    rw [h_faulhaber_Qp, Finset.sum_range_succ, hterm_h]
    ring
  rw [h_split]
  exact hW

/-! ### Strong Voronoi binomial expansion bookkeeping -/

/-- For `p ≥ 5`, every `ν ≥ 2` carries enough p-power to leave two powers
after removing the exact p-part of `ν`. -/
theorem factorization_add_two_le_self
    {p nu : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hnu_two : 2 ≤ nu) :
    nu.factorization p + 2 ≤ nu := by
  have hp : Nat.Prime p := Fact.out
  have hp_pred_ge_four : 4 ≤ p - 1 := by omega
  have hnu_ne : nu ≠ 0 := by omega
  have hfac := Nat.factorization_mul_pred_le_pred (ell := p) (n := nu) hp hnu_ne
  have hfac_four : 4 * nu.factorization p ≤ nu - 1 := by
    calc
      4 * nu.factorization p ≤ (p - 1) * nu.factorization p :=
        Nat.mul_le_mul_right _ hp_pred_ge_four
      _ = nu.factorization p * (p - 1) := by rw [Nat.mul_comm]
      _ ≤ nu - 1 := hfac
  omega

/-- The high-order Voronoi binomial coefficient `choose h ν * p^ν`, with
`ν ≥ 2`, is divisible by the p-part of `h` and two more powers of `p`. -/
theorem primePow_indexFactorization_add_two_dvd_choose_mul_primePow
    {p h nu : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hnu_two : 2 ≤ nu) (hnu_le : nu ≤ h) :
    p ^ (h.factorization p + 2) ∣ Nat.choose h nu * p ^ nu := by
  have hp : Nat.Prime p := Fact.out
  have hchoose_pos : 0 < Nat.choose h nu := Nat.choose_pos hnu_le
  have hchoose_ne : Nat.choose h nu ≠ 0 := hchoose_pos.ne'
  have hpow_ne : p ^ nu ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hprod_ne : Nat.choose h nu * p ^ nu ≠ 0 :=
    Nat.mul_ne_zero hchoose_ne hpow_ne
  have hchoose_lower :
      h.factorization p ≤ (Nat.choose h nu).factorization p + nu.factorization p :=
    Nat.factorization_le_factorization_choose_add (p := p) hnu_le (by omega)
  have hnu_fac : nu.factorization p + 2 ≤ nu :=
    factorization_add_two_le_self (p := p) hp_ge_five hnu_two
  have htarget_le : h.factorization p + 2 ≤ (Nat.choose h nu).factorization p + nu := by
    omega
  refine (hp.pow_dvd_iff_le_factorization hprod_ne).mpr ?_
  calc
    h.factorization p + 2 ≤ (Nat.choose h nu).factorization p + nu := htarget_le
    _ = (Nat.choose h nu * p ^ nu).factorization p := by
      rw [Nat.factorization_mul hchoose_ne hpow_ne]
      simp [Nat.Prime.factorization_self hp]

/-- Convert a `p^(v_p(h)+2)` multiple into the strong Voronoi modulus
`h*p^2`. -/
theorem primePow_indexFactorization_add_two_mul_padicInt_eq_natCast_mul_primeSq
    {p h : ℕ} [Fact p.Prime] (hh_pos : 0 < h) (z : ℤ_[p]) :
    ∃ w : ℤ_[p],
      (p : ℚ_[p]) ^ (h.factorization p + 2) * (z : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set v : ℕ := h.factorization p with hv_def
  set u : ℕ := h / p ^ v with hu_def
  have hh_ne : h ≠ 0 := hh_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hv_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := h) hp hh_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hu_mul_inv : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hu_mul_inv_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul_inv
  refine ⟨z * uInv, ?_⟩
  have hh_cast :
      ((h : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ v * ((u : ℕ) : ℚ_[p]) := by
    rw [hv_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := h) hh_ne
  rw [hh_cast]
  push_cast
  rw [pow_add]
  calc
    (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) =
        (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) := by
      rw [show (p : ℚ_[p]) ^ v * (u : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
          ((z : ℚ_[p]) * (uInv : ℚ_[p])) =
          (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) *
            ((u : ℚ_[p]) * (uInv : ℚ_[p])) by ring]
      rw [hu_mul_inv_Qp]
      ring

/-- P-adic form of
`primePow_indexFactorization_add_two_dvd_choose_mul_primePow`. -/
theorem choose_mul_primePow_mem_h_p_sq
    {p h nu : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hnu_two : 2 ≤ nu) (hnu_le : nu ≤ h) :
    ∃ z : ℤ_[p],
      ((Nat.choose h nu : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ nu =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hdiv : p ^ (h.factorization p + 2) ∣ Nat.choose h nu * p ^ nu :=
    primePow_indexFactorization_add_two_dvd_choose_mul_primePow
      (p := p) hp_ge_five hnu_two hnu_le
  obtain ⟨z, hz⟩ :=
    qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd
      (p := p) (A := Nat.choose h nu * p ^ nu) (q := 1)
      (r := h.factorization p + 2) (by omega) (by simpa using hdiv)
  obtain ⟨w, hw⟩ :=
    primePow_indexFactorization_add_two_mul_padicInt_eq_natCast_mul_primeSq
      (p := p) (h := h) hh_pos z
  refine ⟨w, ?_⟩
  calc
    ((Nat.choose h nu : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ nu =
        (p : ℚ_[p]) ^ (h.factorization p + 2) * (z : ℚ_[p]) := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hz
    _ = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := hw

/-- A high-order binomial term in `(X - p*Y)^h`, with order `ν ≥ 2`, is a
multiple of `h*p^2`. -/
theorem binomial_high_term_mem_h_p_sq
    {p h nu X Y : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hnu_two : 2 ≤ nu) (hnu_le : nu ≤ h) :
    ∃ z : ℤ_[p],
      ((X : ℚ_[p]) ^ (h - nu)) * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ nu *
          ((Nat.choose h (h - nu) : ℕ) : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  obtain ⟨c, hc⟩ := choose_mul_primePow_mem_h_p_sq
    (p := p) (h := h) (nu := nu) hp_ge_five hh_pos hnu_two hnu_le
  refine ⟨((X : ℕ) : ℤ_[p]) ^ (h - nu) * ((-1 : ℤ_[p]) ^ nu) *
    ((Y : ℕ) : ℤ_[p]) ^ nu * c, ?_⟩
  have hchoose : Nat.choose h (h - nu) = Nat.choose h nu :=
    Nat.choose_symm hnu_le
  rw [hchoose]
  push_cast
  linear_combination
    ((X : ℚ_[p]) ^ (h - nu) * (-1 : ℚ_[p]) ^ nu * (Y : ℚ_[p]) ^ nu) * hc

/-- Pointwise strong Voronoi binomial approximation for one residue. -/
theorem voronoi_term_mod_h_p_sq
    {p a h j : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hh_pos : 0 < h) :
    ∃ z : ℤ_[p],
      ((((j * a) % p : ℕ) : ℚ_[p]) ^ h) =
        ((j * a : ℕ) : ℚ_[p]) ^ h -
          (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
            (((j * a / p : ℕ)) : ℚ_[p]) +
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  set X : ℕ := j * a with hX_def
  set Y : ℕ := j * a / p with hY_def
  have h_div_mod :
      ((X : ℕ) : ℚ_[p]) =
        (Y : ℚ_[p]) * (p : ℚ_[p]) + (((j * a) % p : ℕ) : ℚ_[p]) := by
    rw [hX_def, hY_def]
    rw [show ((j * a : ℕ) : ℚ_[p]) =
        (((j * a / p) * p + (j * a) % p : ℕ) : ℚ_[p]) from by
      rw [← (Nat.div_add_mod' _ _).symm]]
    push_cast
    ring
  have h_r :
      (((j * a) % p : ℕ) : ℚ_[p]) =
        (X : ℚ_[p]) - (p : ℚ_[p]) * (Y : ℚ_[p]) := by
    linear_combination -h_div_mod
  rcases eq_or_ne h 1 with rfl | hh_ne_one
  · refine ⟨0, ?_⟩
    rw [h_r]
    push_cast
    ring
  · have hh_two : 2 ≤ h := by omega
    choose w hw using (fun (m : ℕ) (hm : m < h - 1) =>
      binomial_high_term_mem_h_p_sq (p := p) (h := h) (nu := h - m)
        (X := X) (Y := Y) hp_ge_five hh_pos (by omega) (by omega))
    set W : ℤ_[p] := ∑ m ∈ Finset.attach (Finset.range (h - 1)),
      w m.1 (Finset.mem_range.mp m.2) with hW_def
    refine ⟨W, ?_⟩
    have h_tail :
        (∑ m ∈ Finset.range (h - 1),
          (X : ℚ_[p]) ^ m * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - m) *
            ((Nat.choose h m : ℕ) : ℚ_[p])) =
          (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]) := by
      rw [← Finset.sum_attach]
      rw [show ((h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p])) =
          ∑ m ∈ Finset.attach (Finset.range (h - 1)),
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 *
              ((w m.1 (Finset.mem_range.mp m.2) : ℤ_[p]) : ℚ_[p]) from ?_]
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hm_lt : m.1 < h - 1 := Finset.mem_range.mp m.2
        have hm_le : m.1 ≤ h := by omega
        have hhm : h - (h - m.1) = m.1 := Nat.sub_sub_self hm_le
        have hwm := hw m.1 hm_lt
        simpa [hhm] using hwm
      · rw [hW_def]
        simp [PadicInt.coe_sum, Finset.mul_sum]
    let term : ℕ → ℚ_[p] := fun m =>
      (X : ℚ_[p]) ^ m * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - m) *
        ((Nat.choose h m : ℕ) : ℚ_[p])
    have hsplit_range : (∑ m ∈ Finset.range h, term m) =
        (∑ m ∈ Finset.range (h - 1), term m) + term (h - 1) := by
      simpa [term, show h - 1 + 1 = h by omega] using Finset.sum_range_succ term (h - 1)
    rw [h_r]
    rw [show (X : ℚ_[p]) - (p : ℚ_[p]) * (Y : ℚ_[p]) =
        (X : ℚ_[p]) + (-(p : ℚ_[p]) * (Y : ℚ_[p])) by ring]
    rw [add_pow]
    change (∑ m ∈ Finset.range (h + 1), term m) =
      ((X : ℚ_[p]) ^ h -
          (h : ℚ_[p]) * (X : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) * (Y : ℚ_[p]) +
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]))
    rw [Finset.sum_range_succ, hsplit_range]
    change (∑ m ∈ Finset.range (h - 1),
          (X : ℚ_[p]) ^ m * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - m) *
            ((Nat.choose h m : ℕ) : ℚ_[p])) +
        ((X : ℚ_[p]) ^ (h - 1) * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - (h - 1)) *
            ((Nat.choose h (h - 1) : ℕ) : ℚ_[p])) +
        ((X : ℚ_[p]) ^ h * (-(p : ℚ_[p]) * (Y : ℚ_[p])) ^ (h - h) *
            ((Nat.choose h h : ℕ) : ℚ_[p])) = _
    rw [h_tail]
    rw [show h - (h - 1) = 1 by omega, show h - h = 0 by omega]
    rw [show Nat.choose h (h - 1) = h by
      rw [show h = (h - 1) + 1 by omega]
      exact Nat.choose_succ_self_right (h - 1)]
    rw [Nat.choose_self]
    push_cast
    ring

/-- Strong Voronoi binomial/permutation identity with modulus `h*p^2`.  This
is the side-condition-free replacement for the old `p^2` identity in the
Voronoi route. -/
theorem voronoi_sum_mod_h_p_sq
    {p a h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (ha_coprime : ¬ p ∣ a) (hh_pos : 0 < h) :
    ∃ W : ℤ_[p],
      ((a : ℚ_[p]) ^ h - 1) * (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h) -
        (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) *
          (∑ x ∈ Finset.range p,
            (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p])) =
      (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p]) := by
  choose w hw using (fun (j : ℕ) (_hj : j ∈ Finset.range p) =>
    voronoi_term_mod_h_p_sq (p := p) (a := a) (h := h) (j := j) hp_ge_five hh_pos)
  set wt : ℕ → ℤ_[p] := fun j => if hj : j ∈ Finset.range p then w j hj else 0
    with hwt_def
  have hwt_eq : ∀ (j : ℕ) (hj : j ∈ Finset.range p), wt j = w j hj := by
    intro j hj
    rw [hwt_def]
    simp [hj]
  set W_sum : ℤ_[p] := ∑ j ∈ Finset.range p, wt j with hW_sum_def
  refine ⟨-W_sum, ?_⟩
  set S1 : ℚ_[p] := ∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h with hS1_def
  set S2 : ℚ_[p] := ∑ x ∈ Finset.range p,
    (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p]) with hS2_def
  have h_perm :
      (∑ j ∈ Finset.range p, (((j * a) % p : ℕ) : ℚ_[p]) ^ h) = S1 := by
    rw [hS1_def]
    exact voronoi_permutation ha_coprime (fun n : ℕ => (n : ℚ_[p]) ^ h)
  have h_sum_binom :
      (∑ j ∈ Finset.range p, (((j * a) % p : ℕ) : ℚ_[p]) ^ h) =
        ∑ j ∈ Finset.range p,
          (((j * a : ℕ) : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
              (((j * a / p : ℕ)) : ℚ_[p]) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hwt_eq j hj]
    exact hw j hj
  have h_sum : S1 =
        ∑ j ∈ Finset.range p,
          (((j * a : ℕ) : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
              (((j * a / p : ℕ)) : ℚ_[p]) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) := by
    rw [← h_perm, h_sum_binom]
  have h_ja_pow : ∀ j : ℕ, ((j * a : ℕ) : ℚ_[p]) ^ h =
      (a : ℚ_[p]) ^ h * (j : ℚ_[p]) ^ h := by
    intro j
    push_cast
    ring
  have h_ja_pow_sub1 : ∀ j : ℕ, ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) =
      (a : ℚ_[p]) ^ (h - 1) * (j : ℚ_[p]) ^ (h - 1) := by
    intro j
    push_cast
    ring
  have h_sum_rewrite :
        ∑ j ∈ Finset.range p,
          (((j * a : ℕ) : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * ((j * a : ℕ) : ℚ_[p]) ^ (h - 1) * (p : ℚ_[p]) *
              (((j * a / p : ℕ)) : ℚ_[p]) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) =
        ∑ j ∈ Finset.range p,
          ((a : ℚ_[p]) ^ h * (j : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) *
              ((j : ℚ_[p]) ^ (h - 1) * (((j * a / p : ℕ)) : ℚ_[p])) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h_ja_pow j, h_ja_pow_sub1 j]
    ring
  rw [h_sum_rewrite] at h_sum
  have h_three :
        ∑ j ∈ Finset.range p,
          ((a : ℚ_[p]) ^ h * (j : ℚ_[p]) ^ h -
            (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) *
              ((j : ℚ_[p]) ^ (h - 1) * (((j * a / p : ℕ)) : ℚ_[p])) +
            (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (wt j : ℚ_[p])) =
        (a : ℚ_[p]) ^ h * S1 -
          (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * S2 +
          (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W_sum : ℚ_[p]) := by
    simp [hS1_def, hS2_def, hW_sum_def, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum, PadicInt.coe_sum]
  rw [h_three] at h_sum
  rw [hS1_def, hS2_def]
  push_cast
  linear_combination -h_sum

/-- Side-condition-free Voronoi congruence modulo `p`, obtained by
substituting the strong Faulhaber congruence into `voronoi_sum_mod_h_p_sq`
and cancelling the nonzero rational factor `h*p` in `ℚ_[p]`. -/
theorem voronoi_congruence_mod_p_strong
    {p a h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (ha_coprime : ¬ p ∣ a)
    (hh_pos : 0 < h) (hh_even : Even h)
    (hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ h - 1) *
          (((bernoulli h : ℚ) / (h : ℕ) : ℚ) : ℚ_[p]) -
        (a : ℚ_[p]) ^ (h - 1) *
          (∑ x ∈ Finset.range p,
            (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p])) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  obtain ⟨Wv, hWv⟩ := voronoi_sum_mod_h_p_sq (p := p) (a := a) (h := h)
    hp_ge_five ha_coprime hh_pos
  obtain ⟨Wf, hWf⟩ := sum_range_pow_sub_p_mul_bernoulli_strong
    (p := p) (h := h) hp_ge_five hh_pos hh_even hnot
  set S : ℚ_[p] := ∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h with hS_def
  set Q : ℚ_[p] := ∑ x ∈ Finset.range p,
    (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p]) with hQ_def
  set B : ℚ_[p] := ((bernoulli h : ℚ) : ℚ_[p]) with hB_def
  have hWv' : ((a : ℚ_[p]) ^ h - 1) * S -
        (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * Q =
      (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (Wv : ℚ_[p]) := by
    simpa [hS_def, hQ_def] using hWv
  have hWf' : S - (p : ℚ_[p]) * B =
      (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (Wf : ℚ_[p]) := by
    simpa [hS_def, hB_def] using hWf
  have hp_ne : (p : ℚ_[p]) ≠ 0 := by
    have hp : Nat.Prime p := Fact.out
    exact_mod_cast hp.ne_zero
  have hh_ne : (h : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hh_pos.ne'
  refine ⟨Wv - ((a : ℤ_[p]) ^ h - 1) * Wf, ?_⟩
  have hp_mul_hmain : (p : ℚ_[p]) *
      (((a : ℚ_[p]) ^ h - 1) * B -
        (h : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * Q) =
      (p : ℚ_[p]) * ((h : ℚ_[p]) * (p : ℚ_[p]) *
        (((Wv : ℤ_[p]) : ℚ_[p]) - (((a : ℚ_[p]) ^ h - 1) * (Wf : ℚ_[p])))) := by
    linear_combination hWv' - ((a : ℚ_[p]) ^ h - 1) * hWf'
  have hmain : ((a : ℚ_[p]) ^ h - 1) * B -
      (h : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) * Q =
      (h : ℚ_[p]) * (p : ℚ_[p]) *
        (((Wv : ℤ_[p]) : ℚ_[p]) - (((a : ℚ_[p]) ^ h - 1) * (Wf : ℚ_[p]))) :=
    mul_left_cancel₀ hp_ne hp_mul_hmain
  have hdivB : (((bernoulli h : ℚ) / (h : ℕ) : ℚ) : ℚ_[p]) =
      B / (h : ℚ_[p]) := by
    rw [hB_def]
    push_cast
    rfl
  have htarget_mul : (h : ℚ_[p]) *
      (((a : ℚ_[p]) ^ h - 1) * (B / (h : ℚ_[p])) -
        (a : ℚ_[p]) ^ (h - 1) * Q) =
      (h : ℚ_[p]) * ((p : ℚ_[p]) *
        (((Wv : ℤ_[p]) : ℚ_[p]) - (((a : ℚ_[p]) ^ h - 1) * (Wf : ℚ_[p])))) := by
    field_simp [hh_ne]
    linear_combination hmain
  have htarget := mul_left_cancel₀ hh_ne htarget_mul
  rw [hQ_def, hdivB]
  push_cast
  exact htarget

/-- Voronoi congruence gives the `p`-integrality of divided Bernoulli numbers
away from the boundary `(p - 1) ∣ h`, for primes `p ≥ 5`.

This is the classical primitive-root extraction: choose `a` whose residue class
generates `(ZMod p)ˣ`; then `a ^ h - 1` is a `p`-adic unit because
`(p - 1) ∤ h`, so the Voronoi congruence can be divided by that unit. -/
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_voronoi
    {p h : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h)
    (hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      (((bernoulli h : ℚ) / (h : ℕ) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set a : ℕ := (g : ZMod p).val with ha_def
  have ha_coprimeZ : Nat.Coprime a p := ZMod.val_coe_unit_coprime g
  have ha_coprime : ¬ p ∣ a := by
    rw [Nat.coprime_comm] at ha_coprimeZ
    exact hp.coprime_iff_not_dvd.mp ha_coprimeZ
  have ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [ha_def]
    exact ZMod.natCast_zmod_val _
  have hg_order : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen, Nat.card_eq_fintype_card,
      ZMod.card_units]
  have hA_unit : IsUnit ((a : ℤ_[p]) ^ h - 1) := by
    rw [PadicInt.isUnit_iff]
    by_contra h_norm
    have h_mem : ((a : ℤ_[p]) ^ h - 1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      PadicInt.mem_nonunits.mpr (lt_of_le_of_ne (PadicInt.norm_le_one _) h_norm)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at h_mem
    rw [map_sub, map_one, map_pow, map_natCast, ha_cast, sub_eq_zero] at h_mem
    have h_gk : g ^ h = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h_mem)
    exact hnot (hg_order ▸ orderOf_dvd_of_pow_eq_one h_gk)
  obtain ⟨zv, hzv⟩ := voronoi_congruence_mod_p_strong
    (p := p) (a := a) (h := h) hp_ge_five ha_coprime hh_pos hh_even hnot
  set Bdiv : ℚ_[p] := (((bernoulli h : ℚ) / (h : ℕ) : ℚ) : ℚ_[p]) with hBdiv_def
  set Qint : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (h - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hQint_def
  have hQint_cast :
      (∑ x ∈ Finset.range p,
            (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : ℕ) : ℚ_[p])) =
        (Qint : ℚ_[p]) := by
    rw [hQint_def]
    simp [PadicInt.coe_sum]
  set AInv : ℤ_[p] := (hA_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hAInv_def
  have hA_mul_inv : (((a : ℤ_[p]) ^ h - 1) : ℤ_[p]) * AInv = 1 := by
    change ((hA_unit.unit * hA_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hA_mul_inv_Qp :
      (((a : ℤ_[p]) ^ h - 1 : ℤ_[p]) : ℚ_[p]) * (AInv : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hA_mul_inv
  push_cast at hA_mul_inv_Qp
  refine ⟨AInv * (((a : ℤ_[p]) ^ (h - 1)) * Qint + (p : ℤ_[p]) * zv), ?_⟩
  have hA_B : (((a : ℚ_[p]) ^ h - 1) * Bdiv) =
      ((((a : ℤ_[p]) ^ (h - 1)) * Qint + (p : ℤ_[p]) * zv : ℤ_[p]) : ℚ_[p]) := by
    rw [hQint_cast] at hzv
    push_cast
    linear_combination hzv
  calc
    (((bernoulli h : ℚ) / (h : ℕ) : ℚ) : ℚ_[p]) = Bdiv := by
      rw [hBdiv_def]
    _ = (AInv : ℚ_[p]) * (((a : ℚ_[p]) ^ h - 1) * Bdiv) := by
      calc
        Bdiv = 1 * Bdiv := by ring
        _ = (((a : ℚ_[p]) ^ h - 1) * (AInv : ℚ_[p])) * Bdiv := by
          rw [hA_mul_inv_Qp]
        _ = (AInv : ℚ_[p]) * (((a : ℚ_[p]) ^ h - 1) * Bdiv) := by ring
    _ = (AInv : ℚ_[p]) *
        (((((a : ℤ_[p]) ^ (h - 1)) * Qint + (p : ℤ_[p]) * zv : ℤ_[p]) : ℚ_[p])) := by
      rw [hA_B]
    _ = ((AInv * (((a : ℤ_[p]) ^ (h - 1)) * Qint + (p : ℤ_[p]) * zv) : ℤ_[p]) :
        ℚ_[p]) := by
      push_cast
      ring

/-- Powers of a chosen unit generator only depend on the exponent modulo
`p - 1`, once the generator order has been identified with `p - 1`. -/
theorem primitiveRoot_unit_pow_eq_of_modEq
    {p m n : ℕ} [Fact p.Prime] {g : (ZMod p)ˣ}
    (hg_order : orderOf g = p - 1)
    (hmn : m ≡ n [MOD p - 1]) :
    g ^ m = g ^ n := by
  rw [pow_eq_pow_iff_modEq, hg_order]
  exact hmn

/-- If two predecessor exponents are congruent modulo `p - 1`, the Voronoi
floor sums differ by a multiple of `p` in `ℚ_[p]`. -/
theorem voronoi_floor_sum_sModEq_of_pred_modEq
    {p a m n : ℕ} [Fact p.Prime]
    (_hm_pos : 0 < m) (_hn_pos : 0 < n)
    (hmn : (m - 1) ≡ (n - 1) [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (m - 1) * ((x * a / p : ℕ) : ℚ_[p])) -
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (n - 1) * ((x * a / p : ℕ) : ℚ_[p])) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set SmZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (m - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSmZ_def
  set SnZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (n - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSnZ_def
  have h_pow_pred_ZMod : ∀ j : ℕ, j < p → j ≠ 0 →
      ((j : ℕ) : ZMod p) ^ (m - 1) = ((j : ℕ) : ZMod p) ^ (n - 1) := by
    intro j hjp hj_ne
    have hj_coprime : Nat.Coprime j p :=
      (hp.coprime_iff_not_dvd.mpr
        (fun hdvd => hj_ne (Nat.eq_zero_of_dvd_of_lt hdvd hjp))).symm
    lift (((j : ℕ) : ZMod p)) to (ZMod p)ˣ using
      (ZMod.isUnit_iff_coprime j p).mpr hj_coprime
      with u hu
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    congr 1
    rw [pow_eq_pow_iff_modEq]
    have h_ord_dvd : orderOf u ∣ (p - 1) := by
      rw [← ZMod.card_units, ← Nat.card_eq_fintype_card]
      exact orderOf_dvd_natCard u
    exact hmn.of_dvd h_ord_dvd
  have h_sum_toZMod : PadicInt.toZMod SmZ = PadicInt.toZMod SnZ := by
    rw [hSmZ_def, hSnZ_def]
    simp only [map_sum, map_mul, map_pow, map_natCast]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hj_ne : j = 0
    · subst j
      simp
    · congr 1
      exact h_pow_pred_ZMod j hj hj_ne
  have h_sub_mem : SmZ - SnZ ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
    have h_sub : PadicInt.toZMod (SmZ - SnZ) = 0 := by
      rw [map_sub, h_sum_toZMod, sub_self]
    have h_ker : SmZ - SnZ ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod]
      exact h_sub
    rwa [PadicInt.maximalIdeal_eq_span_p] at h_ker
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp h_sub_mem
  refine ⟨z, ?_⟩
  have hSm_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (m - 1) * ((x * a / p : ℕ) : ℚ_[p])) = (SmZ : ℚ_[p]) := by
    rw [hSmZ_def]
    simp [PadicInt.coe_sum]
  have hSn_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (n - 1) * ((x * a / p : ℕ) : ℚ_[p])) = (SnZ : ℚ_[p]) := by
    rw [hSnZ_def]
    simp [PadicInt.coe_sum]
  rw [hSm_cast, hSn_cast]
  have hzQ := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hz
  push_cast at hzQ
  linear_combination hzQ

/-- If `n` is not a multiple of `p - 1` and `m ≡ n [MOD p - 1]`, then `m` is
not a multiple of `p - 1` either. -/
private theorem not_sub_one_dvd_of_modEq {p m n : ℕ}
    (hnot : ¬ (p - 1) ∣ n) (hmn : m ≡ n [MOD p - 1]) : ¬ (p - 1) ∣ m := by
  intro hdvd
  have h_n_mod : n ≡ 0 [MOD p - 1] :=
    hmn.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)
  exact hnot (Nat.modEq_zero_iff_dvd.mp h_n_mod)

/-- A congruence of positive exponents modulo `p - 1` descends to their
predecessors. -/
private theorem modEq_pred_of_modEq {p m n : ℕ} (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hmn : m ≡ n [MOD p - 1]) : (m - 1) ≡ (n - 1) [MOD p - 1] := by
  have h1 : (m - 1) + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
  have h2 : (n - 1) + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
  have h_mod_add1 : (m - 1) + 1 ≡ (n - 1) + 1 [MOD p - 1] := by
    rw [h1, h2]
    exact hmn
  exact Nat.ModEq.add_right_cancel' 1 h_mod_add1

/-- For a chosen unit generator `g` of `(ZMod p)ˣ` whose value is the residue of
`a`, the element `a ^ k - 1` is a unit in `ℤ_[p]` whenever `k` is not a multiple
of `p - 1`. -/
private theorem padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd {p k : ℕ}
    [Fact p.Prime] {a : ℕ} {g : (ZMod p)ˣ} (hg_order : orderOf g = p - 1)
    (ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p)) (hk : ¬ (p - 1) ∣ k) :
    IsUnit ((a : ℤ_[p]) ^ k - 1) := by
  rw [PadicInt.isUnit_iff]
  by_contra h_norm
  have h_mem : ((a : ℤ_[p]) ^ k - 1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    PadicInt.mem_nonunits.mpr (lt_of_le_of_ne (PadicInt.norm_le_one _) h_norm)
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at h_mem
  rw [map_sub, map_one, map_pow, map_natCast, ha_cast, sub_eq_zero] at h_mem
  have h_gk : g ^ k = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h_mem)
  exact hk (hg_order ▸ orderOf_dvd_of_pow_eq_one h_gk)

/-- Powers of the residue `a` in `ZMod p` only depend on the exponent modulo
`p - 1`, via the chosen unit generator. -/
private theorem natCast_pow_eq_of_modEq {p k l : ℕ} [Fact p.Prime] {a : ℕ}
    {g : (ZMod p)ˣ} (hg_order : orderOf g = p - 1)
    (ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p)) (hkl : k ≡ l [MOD p - 1]) :
    ((a : ℕ) : ZMod p) ^ k = ((a : ℕ) : ZMod p) ^ l := by
  rw [ha_cast]
  simpa [Units.val_pow_eq_pow_val] using
    congrArg (fun u : (ZMod p)ˣ => (u : ZMod p))
      (primitiveRoot_unit_pow_eq_of_modEq (p := p) (g := g) hg_order hkl)

/-- Two `p`-adic integers with the same image in `ZMod p` differ by a multiple
of `p`. -/
private theorem padicInt_sub_mem_span_p_of_toZMod_eq {p : ℕ} [Fact p.Prime]
    {x y : ℤ_[p]} (h : PadicInt.toZMod x = PadicInt.toZMod y) :
    x - y ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
  have h_sub : PadicInt.toZMod (x - y) = 0 := by rw [map_sub, h, sub_self]
  have h_ker : x - y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]
    exact h_sub
  rwa [PadicInt.maximalIdeal_eq_span_p] at h_ker

/-- A unit times the value of its inverse unit is `1`. -/
private theorem padicInt_isUnit_mul_unitInv {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (hx : IsUnit x) : x * (hx.unit⁻¹ : (ℤ_[p])ˣ).val = 1 := by
  change ((hx.unit * hx.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
  simp

/-- If two `p`-adic integers differ by `p * d`, their images in `ℚ_[p]` satisfy
`(y : ℚ_[p]) = (x : ℚ_[p]) - p * d`. -/
private theorem qp_eq_sub_p_mul_of_padicInt_eq {p : ℕ} [Fact p.Prime]
    {x y d : ℤ_[p]} (hd : x - y = (p : ℤ_[p]) * d) :
    (y : ℚ_[p]) = (x : ℚ_[p]) - (p : ℚ_[p]) * (d : ℚ_[p]) := by
  have hdQ := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hd
  push_cast at hdQ ⊢
  linear_combination -hdQ

/-- The `ℚ_[p]`-valued Voronoi floor sum is the image of its `ℤ_[p]`-valued
counterpart. -/
private theorem voronoi_floorSum_qp_eq_padicInt_coe {p : ℕ} [Fact p.Prime]
    (e a : ℕ) :
    (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ e * ((x * a / p : ℕ) : ℚ_[p])) =
      ((∑ x ∈ Finset.range p,
        ((x : ℕ) : ℤ_[p]) ^ e * (((x * a / p : ℕ) : ℤ_[p])) : ℤ_[p]) : ℚ_[p]) := by
  simp [PadicInt.coe_sum]

/-- An inverse identity in `ℤ_[p]` transports to `ℚ_[p]`. -/
private theorem qp_mul_eq_one_of_padicInt_mul_eq_one {p : ℕ} [Fact p.Prime]
    {w v : ℤ_[p]} (h : w * v = 1) : (w : ℚ_[p]) * (v : ℚ_[p]) = 1 := by
  simpa using congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) h

/-- Final algebraic cancellation of the Kummer congruence over `ℚ_[p]`.

Given the two single-exponent Voronoi expansions `(A - 1) * B = A₁ * S + p * z`,
the combined floor-sum identity packaged in `E`, and the two unit inverses of
`Aₘ - 1` and `Aₙ - 1`, the divided-Bernoulli difference is `p` times the
explicit witness. -/
private theorem bernoulli_div_sub_eq_p_mul_of_expansions {p : ℕ} [Fact p.Prime]
    {Am Bm Am1 Sm zm AmInv An Bn An1 Sn zn AnInv E : ℚ_[p]}
    (hBm : (Am - 1) * Bm = Am1 * Sm + (p : ℚ_[p]) * zm)
    (hBn : (An - 1) * Bn = An1 * Sn + (p : ℚ_[p]) * zn)
    (hE : (An - 1) * Am1 * Sm - (Am - 1) * An1 * Sn = (p : ℚ_[p]) * E)
    (hAmInv : (Am - 1) * AmInv = 1) (hAnInv : (An - 1) * AnInv = 1) :
    Bm - Bn = (p : ℚ_[p]) * (AmInv * AnInv * E + AmInv * zm - AnInv * zn) := by
  have h_Am_ne : Am - 1 ≠ 0 := fun h0 => one_ne_zero <| by
    rw [← hAmInv, h0, zero_mul]
  have h_An_ne : An - 1 ≠ 0 := fun h0 => one_ne_zero <| by
    rw [← hAnInv, h0, zero_mul]
  have h_key :
      (Am - 1) * (An - 1) * (Bm - Bn) =
        (Am - 1) * (An - 1) * ((p : ℚ_[p]) *
          (AmInv * AnInv * E + AmInv * zm - AnInv * zn)) := by
    have h_lhs :
        (Am - 1) * (An - 1) * (Bm - Bn) =
          (An - 1) * ((Am - 1) * Bm) - (Am - 1) * ((An - 1) * Bn) := by ring
    rw [h_lhs, hBm, hBn]
    rw [show (An - 1) * (Am1 * Sm + (p : ℚ_[p]) * zm) -
          (Am - 1) * (An1 * Sn + (p : ℚ_[p]) * zn) =
        ((An - 1) * Am1 * Sm - (Am - 1) * An1 * Sn) +
          (p : ℚ_[p]) * ((An - 1) * zm - (Am - 1) * zn) from by ring, hE]
    rw [show (Am - 1) * (An - 1) * ((p : ℚ_[p]) *
          (AmInv * AnInv * E + AmInv * zm - AnInv * zn)) =
        (p : ℚ_[p]) * (((Am - 1) * AmInv) * ((An - 1) * AnInv) * E) +
          (p : ℚ_[p]) * (((Am - 1) * AmInv) * (An - 1) * zm) -
          (p : ℚ_[p]) * (((An - 1) * AnInv) * (Am - 1) * zn) from by ring,
      hAmInv, hAnInv]
    ring
  exact mul_left_cancel₀ (mul_ne_zero h_Am_ne h_An_ne) h_key

/-- Full divided-Bernoulli Kummer congruence for primes `p ≥ 5`, proved from
the side-condition-free Voronoi congruence. -/
theorem bernoulli_div_sModEq_of_modEq_full_geFive
    {p m n : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hnot_m : ¬ (p - 1) ∣ m := not_sub_one_dvd_of_modEq hnot hmn
  have hmn_pred : (m - 1) ≡ (n - 1) [MOD p - 1] :=
    modEq_pred_of_modEq hm_pos hn_pos hmn
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set a : ℕ := (g : ZMod p).val with ha_def
  have ha_coprimeZ : Nat.Coprime a p := ZMod.val_coe_unit_coprime g
  have ha_coprime : ¬ p ∣ a := by
    rw [Nat.coprime_comm] at ha_coprimeZ
    exact hp.coprime_iff_not_dvd.mp ha_coprimeZ
  have ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [ha_def]
    exact ZMod.natCast_zmod_val _
  have hg_order : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen, Nat.card_eq_fintype_card,
      ZMod.card_units]
  have h_mn_ZMod : ((a : ℕ) : ZMod p) ^ m = ((a : ℕ) : ZMod p) ^ n :=
    natCast_pow_eq_of_modEq hg_order ha_cast hmn
  have h_mn1_ZMod : ((a : ℕ) : ZMod p) ^ (m - 1) =
      ((a : ℕ) : ZMod p) ^ (n - 1) :=
    natCast_pow_eq_of_modEq hg_order ha_cast hmn_pred
  obtain ⟨z_m, hz_m⟩ := voronoi_congruence_mod_p_strong
    (p := p) (a := a) (h := m) hp_ge_five ha_coprime hm_pos hm_even hnot_m
  obtain ⟨z_n, hz_n⟩ := voronoi_congruence_mod_p_strong
    (p := p) (a := a) (h := n) hp_ge_five ha_coprime hn_pos hn_even hnot
  set Am : ℤ_[p] := (a : ℤ_[p]) ^ m with hAm_def
  set An : ℤ_[p] := (a : ℤ_[p]) ^ n with hAn_def
  set Am1 : ℤ_[p] := (a : ℤ_[p]) ^ (m - 1) with hAm1_def
  set An1 : ℤ_[p] := (a : ℤ_[p]) ^ (n - 1) with hAn1_def
  set SmZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (m - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSmZ_def
  set SnZ : ℤ_[p] := ∑ x ∈ Finset.range p,
    ((x : ℕ) : ℤ_[p]) ^ (n - 1) * (((x * a / p : ℕ) : ℤ_[p])) with hSnZ_def
  have h_toZMod_a : PadicInt.toZMod (a : ℤ_[p]) = ((a : ℕ) : ZMod p) := by
    rw [map_natCast]
  have h_Am_An_toZMod : PadicInt.toZMod Am = PadicInt.toZMod An := by
    rw [hAm_def, hAn_def, map_pow, map_pow, h_toZMod_a]
    exact h_mn_ZMod
  obtain ⟨d_A, hd_A⟩ :=
    Ideal.mem_span_singleton.mp (padicInt_sub_mem_span_p_of_toZMod_eq h_Am_An_toZMod)
  have h_Am1_An1_toZMod : PadicInt.toZMod Am1 = PadicInt.toZMod An1 := by
    rw [hAm1_def, hAn1_def, map_pow, map_pow, h_toZMod_a]
    exact h_mn1_ZMod
  obtain ⟨d_A1, hd_A1⟩ :=
    Ideal.mem_span_singleton.mp
      (padicInt_sub_mem_span_p_of_toZMod_eq h_Am1_An1_toZMod)
  obtain ⟨d_S, hd_S⟩ := voronoi_floor_sum_sModEq_of_pred_modEq
    (p := p) (a := a) (m := m) (n := n) hm_pos hn_pos hmn_pred
  have h_Am_sub_one_unit : IsUnit (Am - 1) := by
    rw [hAm_def]
    exact padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd hg_order ha_cast hnot_m
  have h_An_sub_one_unit : IsUnit (An - 1) := by
    rw [hAn_def]
    exact padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd hg_order ha_cast hnot
  set AmInv : ℤ_[p] := (h_Am_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hAmInv_def
  have hAmInv_mul : (Am - 1) * AmInv = 1 :=
    padicInt_isUnit_mul_unitInv h_Am_sub_one_unit
  set AnInv : ℤ_[p] := (h_An_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hAnInv_def
  have hAnInv_mul : (An - 1) * AnInv = 1 :=
    padicInt_isUnit_mul_unitInv h_An_sub_one_unit
  set E : ℤ_[p] := (Am - 1) * (d_A1 * SmZ + An1 * d_S) - d_A * Am1 * SmZ
    with hE_def
  refine ⟨AmInv * AnInv * E + AmInv * z_m - AnInv * z_n, ?_⟩
  set Am_Q : ℚ_[p] := (Am : ℚ_[p]) with hAm_Q_def
  set An_Q : ℚ_[p] := (An : ℚ_[p]) with hAn_Q_def
  set Am1_Q : ℚ_[p] := (Am1 : ℚ_[p]) with hAm1_Q_def
  set An1_Q : ℚ_[p] := (An1 : ℚ_[p]) with hAn1_Q_def
  set Sm_Q : ℚ_[p] := (SmZ : ℚ_[p]) with hSm_Q_def
  set Sn_Q : ℚ_[p] := (SnZ : ℚ_[p]) with hSn_Q_def
  set Bm_div : ℚ_[p] := (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p])
    with hBm_div_def
  set Bn_div : ℚ_[p] := (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p])
    with hBn_div_def
  have hSm_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (m - 1) * ((x * a / p : ℕ) : ℚ_[p])) = Sm_Q :=
    voronoi_floorSum_qp_eq_padicInt_coe (m - 1) a
  have hSn_cast :
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (n - 1) * ((x * a / p : ℕ) : ℚ_[p])) = Sn_Q :=
    voronoi_floorSum_qp_eq_padicInt_coe (n - 1) a
  have hz_m_Q :
      (Am_Q - 1) * Bm_div - Am1_Q * Sm_Q = (p : ℚ_[p]) * (z_m : ℚ_[p]) := by
    rw [hAm_Q_def, hAm1_Q_def, hAm_def, hAm1_def, hBm_div_def]
    rw [hSm_cast] at hz_m
    convert hz_m using 2 <;> push_cast [hBm_div_def] <;> ring
  have hz_n_Q :
      (An_Q - 1) * Bn_div - An1_Q * Sn_Q = (p : ℚ_[p]) * (z_n : ℚ_[p]) := by
    rw [hAn_Q_def, hAn1_Q_def, hAn_def, hAn1_def, hBn_div_def]
    rw [hSn_cast] at hz_n
    convert hz_n using 2 <;> push_cast [hBn_div_def] <;> ring
  have hS_Q : Sm_Q - Sn_Q = (p : ℚ_[p]) * (d_S : ℚ_[p]) := by
    rw [hSm_cast, hSn_cast] at hd_S
    exact hd_S
  have h_An_eq_Q : An_Q = Am_Q - (p : ℚ_[p]) * (d_A : ℚ_[p]) :=
    qp_eq_sub_p_mul_of_padicInt_eq hd_A
  have h_An1_eq_Q : An1_Q = Am1_Q - (p : ℚ_[p]) * (d_A1 : ℚ_[p]) :=
    qp_eq_sub_p_mul_of_padicInt_eq hd_A1
  have h_Sn_eq_Q : Sn_Q = Sm_Q - (p : ℚ_[p]) * (d_S : ℚ_[p]) := by
    linear_combination -hS_Q
  have hE_eq_Q :
      (An_Q - 1) * Am1_Q * Sm_Q - (Am_Q - 1) * An1_Q * Sn_Q =
        (p : ℚ_[p]) * ((E : ℤ_[p]) : ℚ_[p]) := by
    rw [hE_def]
    push_cast
    rw [← hAm_Q_def, ← hAm1_Q_def, ← hAn1_Q_def, ← hSm_Q_def]
    rw [h_An_eq_Q, h_An1_eq_Q, h_Sn_eq_Q]
    ring
  set AmInv_Q : ℚ_[p] := ((AmInv : ℤ_[p]) : ℚ_[p]) with hAmInv_Q_def
  set AnInv_Q : ℚ_[p] := ((AnInv : ℤ_[p]) : ℚ_[p]) with hAnInv_Q_def
  set z_m_Q : ℚ_[p] := ((z_m : ℤ_[p]) : ℚ_[p]) with hz_m_Q_def
  set z_n_Q : ℚ_[p] := ((z_n : ℤ_[p]) : ℚ_[p]) with hz_n_Q_def
  set E_Q : ℚ_[p] := ((E : ℤ_[p]) : ℚ_[p]) with hE_Q_def
  have h_Am_AmInv : (Am_Q - 1) * AmInv_Q = 1 := by
    have h := qp_mul_eq_one_of_padicInt_mul_eq_one hAmInv_mul
    rw [hAm_Q_def, hAmInv_Q_def]
    push_cast at h
    linear_combination h
  have h_An_AnInv : (An_Q - 1) * AnInv_Q = 1 := by
    have h := qp_mul_eq_one_of_padicInt_mul_eq_one hAnInv_mul
    rw [hAn_Q_def, hAnInv_Q_def]
    push_cast at h
    linear_combination h
  have h_witness_eq :
      (((AmInv * AnInv * E + AmInv * z_m - AnInv * z_n : ℤ_[p]) : ℚ_[p])) =
        AmInv_Q * AnInv_Q * E_Q + AmInv_Q * z_m_Q - AnInv_Q * z_n_Q := by
    rw [hAmInv_Q_def, hAnInv_Q_def, hz_m_Q_def, hz_n_Q_def, hE_Q_def]
    push_cast
    ring
  rw [h_witness_eq]
  have h_Bm_expand :
      (Am_Q - 1) * Bm_div = Am1_Q * Sm_Q + (p : ℚ_[p]) * z_m_Q := by
    rw [hz_m_Q_def]
    linear_combination hz_m_Q
  have h_Bn_expand :
      (An_Q - 1) * Bn_div = An1_Q * Sn_Q + (p : ℚ_[p]) * z_n_Q := by
    rw [hz_n_Q_def]
    linear_combination hz_n_Q
  exact bernoulli_div_sub_eq_p_mul_of_expansions h_Bm_expand h_Bn_expand hE_eq_Q
    h_Am_AmInv h_An_AnInv

/-- The p-unit case of divided Bernoulli integrality.  The remaining Adams
work is exactly the case where `p ∣ k`, so the denominator has a nontrivial
p-power that must be cancelled by the numerator. -/
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_of_not_dvd
    {p k : ℕ} [Fact p.Prime]
    (_hk_pos : 0 < k) (hk_even : Even k)
    (hnot : ¬ (p - 1) ∣ k) (hk_not_dvd : ¬ p ∣ k) :
    ∃ z : ℤ_[p],
      (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  obtain ⟨b, hb⟩ :=
    bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd
      (p := p) (n := k) hk_even hnot
  have hk_unit : IsUnit ((k : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := k) hk_not_dvd
  set kInv : ℤ_[p] := (hk_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hkInv_mul : ((k : ℕ) : ℤ_[p]) * kInv = 1 := by
    change ((hk_unit.unit * hk_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hkInv_mul_Qp : ((k : ℕ) : ℚ_[p]) * ((kInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hkInv_mul
  refine ⟨kInv * b, ?_⟩
  have h_div :
      (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) =
        ((bernoulli k : ℚ) : ℚ_[p]) / ((k : ℕ) : ℚ_[p]) := by
    push_cast
    rfl
  rw [h_div, hb, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hkInv_mul_Qp]
  push_cast
  ring

/-- Divided Bernoulli integrality after the exact Adams p-power cancellation
has been supplied.  This is the algebraic bridge from the future Adams theorem
to `B_k / k ∈ ℤ_[p]`: after removing `p ^ v_p(k)`, only a p-unit remains in
the denominator. -/
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_of_adams_exact
    {p k : ℕ} [Fact p.Prime] (hk_pos : 0 < k)
    (h_adams : ∃ b : ℤ_[p],
      ((bernoulli k : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ k.factorization p * (b : ℚ_[p])) :
    ∃ z : ℤ_[p],
      (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  set s : ℕ := k.factorization p with hs_def
  set u : ℕ := k / p ^ s with hu_def
  have hk_ne : k ≠ 0 := hk_pos.ne'
  have hu_not_dvd : ¬ p ∣ u := by
    rw [hu_def, hs_def]
    exact prime_not_dvd_factorization_unitPart (p := p) (n := k) hp hk_ne
  have hu_unit : IsUnit ((u : ℕ) : ℤ_[p]) :=
    padicInt_natCast_isUnit_of_not_dvd (p := p) (n := u) hu_not_dvd
  set uInv : ℤ_[p] := (hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have huInv_mul : ((u : ℕ) : ℤ_[p]) * uInv = 1 := by
    change ((hu_unit.unit * hu_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have huInv_mul_Qp : ((u : ℕ) : ℚ_[p]) * ((uInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) huInv_mul
  obtain ⟨b, hb⟩ := h_adams
  refine ⟨uInv * b, ?_⟩
  have hk_cast :
      ((k : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ s * ((u : ℕ) : ℚ_[p]) := by
    rw [hs_def, hu_def]
    exact qpadic_natCast_eq_primePow_mul_unitPart (p := p) (n := k) hk_ne
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_pow_ne : (p : ℚ_[p]) ^ s ≠ 0 := pow_ne_zero _ hpQ_ne
  have h_div :
      (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) =
        ((bernoulli k : ℚ) : ℚ_[p]) / ((k : ℕ) : ℚ_[p]) := by
    push_cast
    rfl
  rw [h_div, hb, hk_cast]
  calc
    (p : ℚ_[p]) ^ s * (b : ℚ_[p]) /
        ((p : ℚ_[p]) ^ s * (u : ℚ_[p]))
        = (b : ℚ_[p]) / (u : ℚ_[p]) := by
          field_simp [hp_pow_ne]
    _ = (b : ℚ_[p]) * (uInv : ℚ_[p]) := by
      rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right huInv_mul_Qp]
    _ = ((uInv * b : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

/-- Teichmuller powers only depend on the exponent modulo `p - 1`. -/
theorem teichmullerCharQp_pow_eq_of_modEq
    {p m n : ℕ} [Fact p.Prime] (hmn : m ≡ n [MOD p - 1]) :
    (teichmullerCharQp p) ^ m = (teichmullerCharQp p) ^ n := by
  rw [pow_eq_pow_iff_modEq, orderOf_teichmullerCharQp]
  exact hmn

/-- Predessor-exponent form of `teichmullerCharQp_pow_eq_of_modEq`. -/
theorem teichmullerCharQp_pow_pred_eq_of_modEq
    {p m n : ℕ} [Fact p.Prime] (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hmn : m ≡ n [MOD p - 1]) :
    (teichmullerCharQp p) ^ (m - 1) = (teichmullerCharQp p) ^ (n - 1) := by
  have hmn_pred : (m - 1) ≡ (n - 1) [MOD p - 1] := by
    have h1 : (m - 1) + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
    have h2 : (n - 1) + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
    have h_mod_add1 : (m - 1) + 1 ≡ (n - 1) + 1 [MOD p - 1] := by
      rw [h1, h2]
      exact hmn
    exact Nat.ModEq.add_right_cancel' 1 h_mod_add1
  exact teichmullerCharQp_pow_eq_of_modEq hmn_pred

/-- Non-boundary exponents give nontrivial Teichmuller powers. -/
theorem teichmullerCharQp_pow_ne_one_of_not_sub_one_dvd
    {p n : ℕ} [Fact p.Prime] (hnot : ¬ (p - 1) ∣ n) :
    (teichmullerCharQp p) ^ n ≠ 1 :=
  teichmullerCharQp_pow_ne_one_of_not_dvd (p := p) hnot

/-- **Standard Kummer congruence for divided Bernoulli numbers.**

This is the public full congruence used by the Carlitz route.  The odd-prime
case reduces to `p ≥ 5`: if `p = 3`, then `p - 1 = 2` divides every even
non-boundary exponent, contradicting the hypotheses. -/
theorem bernoulli_div_sModEq_of_modEq_full
    {p m n : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp_ge_five : 5 ≤ p :=
    five_le_of_odd_prime_and_even_nonboundary (p := p) hp_odd hn_even hnot
  exact bernoulli_div_sModEq_of_modEq_full_geFive hp_ge_five hm_pos hn_pos
    hm_even hn_even hnot hmn

/-- Kummer congruence implies the `p`-integrality of divided Bernoulli numbers
away from the boundary `(p - 1) ∣ k`. -/
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd
    {p k : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k)
    (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : Nat.Prime p := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp_odd
  have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hp_sub_even : Even (p - 1) := by
    rcases hpodd with ⟨a, ha⟩
    rw [ha]
    exact ⟨a, by omega⟩
  let k' : ℕ := k % (p - 1)
  have hk'_ne_zero : k' ≠ 0 := fun hzero =>
    hnot (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hk'_pos : 0 < k' := Nat.pos_of_ne_zero hk'_ne_zero
  have hk'_lt : k' < p - 1 := by
    dsimp [k']
    exact Nat.mod_lt _ hp_sub_pos
  have hk'_even : Even k' := by
    dsimp [k']
    exact Even.mod_even hk_even hp_sub_even
  have hmod : k ≡ k' [MOD p - 1] := by
    dsimp [k']
    exact (Nat.mod_modEq k (p - 1)).symm
  have hnot_k' : ¬ (p - 1) ∣ k' := fun hdvd =>
    not_lt_of_ge (Nat.le_of_dvd hk'_pos hdvd) hk'_lt
  obtain ⟨z, hz⟩ :=
    bernoulli_div_sModEq_of_modEq_full (p := p) hp_odd hk_pos hk'_pos
      hk_even hk'_even hnot_k' hmod
  obtain ⟨b, hb⟩ := bernoulli_div_mem_padicInt (p := p) hp_odd hk'_pos hk'_lt
  refine ⟨b + (p : ℤ_[p]) * z, ?_⟩
  calc
    (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p])
        =
        (((bernoulli k' : ℚ) / (k' : ℕ) : ℚ) : ℚ_[p]) +
          (p : ℚ_[p]) * (z : ℚ_[p]) := by
          linear_combination hz
    _ = ((b + (p : ℤ_[p]) * z : ℤ_[p]) : ℚ_[p]) := by
      rw [hb]
      push_cast
      ring

/-- **Adams divisibility.**  If an odd prime power `p^r` divides a positive
even non-boundary Bernoulli index `k`, then `B_k` contains the same `p^r`
factor p-adically. -/
theorem adams_bernoulli_dvd_of_prime_power_dvd_index
    {p k r : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k) (_hr_pos : 0 < r)
    (hpr : p ^ r ∣ k) (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      ((bernoulli k : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ r * (z : ℚ_[p]) := by
  obtain ⟨b, hb⟩ :=
    bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd (p := p)
      hp_odd hk_pos hk_even hnot
  obtain ⟨c, hc⟩ := hpr
  have hkQ_ne : ((k : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
  have hBk :
      ((bernoulli k : ℚ) : ℚ_[p]) =
        ((k : ℕ) : ℚ_[p]) *
          (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) := by
    push_cast
    field_simp [hkQ_ne]
  have hk_cast :
      ((k : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ r * (c : ℚ_[p]) := by
    rw [hc]
    push_cast
    ring
  refine ⟨(c : ℤ_[p]) * b, ?_⟩
  rw [hBk, hb, hk_cast]
  push_cast
  ring

/-- If the unrestricted Corollary 34 bridge is available for every positive
even non-boundary index, then the full Kummer congruence follows by identifying
the Teichmuller characters.  This isolates the remaining finite-character
source theorem needed for `IRR-06`. -/
theorem bernoulli_div_sModEq_of_modEq_of_teichmullerBridge
    {p m n : ℕ} [Fact p.Prime]
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1])
    (hbridge : ∀ {k : ℕ}, 0 < k → Even k → ¬ (p - 1) ∣ k →
      ∃ z : ℤ_[p],
        (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) -
          BernoulliGen ((teichmullerCharQp p) ^ (k - 1)) 1 =
        (p : ℚ_[p]) * (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hnot_m : ¬ (p - 1) ∣ m := by
    intro hdvd
    have h_n_mod : n ≡ 0 [MOD p - 1] :=
      hmn.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)
    exact hnot (Nat.modEq_zero_iff_dvd.mp h_n_mod)
  obtain ⟨zm, hzm⟩ := hbridge hm_pos hm_even hnot_m
  obtain ⟨zn, hzn⟩ := hbridge hn_pos hn_even hnot
  have hχ := teichmullerCharQp_pow_pred_eq_of_modEq (p := p) hm_pos hn_pos hmn
  rw [hχ] at hzm
  refine ⟨zm - zn, ?_⟩
  calc
    (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p])
        = ((((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
            BernoulliGen ((teichmullerCharQp p) ^ (n - 1)) 1) -
          ((((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) -
            BernoulliGen ((teichmullerCharQp p) ^ (n - 1)) 1) := by ring
    _ = (p : ℚ_[p]) * ((zm : ℚ_[p]) - (zn : ℚ_[p])) := by
      rw [hzm, hzn]
      ring
    _ = (p : ℚ_[p]) * ((zm - zn : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

/-- The Step 2 power-sum congruence with its former bounded-`p^3` dependency
replaced by the direct von Staudt-Clausen consequence
`p * B_j ∈ ℤ_[p]`.  This removes one Voronoi-chain artifact, but the full
Kummer congruence still needs the unrestricted finite-character bridge or the
p-adic `L` proof. -/
theorem sum_range_pow_sModEq_p_mul_bernoulli_vonStaudt
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_two : 2 ≤ t) (ht_even : Even t)
    (h_p_not_dvd_t_plus_one : ¬ (p : ℕ) ∣ (t + 1)) :
    ∃ z : ℤ_[p],
      ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t)) -
          (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p]) =
        ((p : ℚ_[p]) ^ 2) * (z : ℚ_[p]) := by
  refine sum_range_pow_sModEq_p_mul_bernoulli hp_odd ht_two ht_even
    h_p_not_dvd_t_plus_one ?_
  intro _j _hj _hj_two hj_even
  exact p_mul_bernoulli_mem_padicInt_vonStaudt (p := p) hj_even

/-- Unrestricted first half of the finite-character bridge:
`B_{1,ω^n}` is congruent modulo `p` to the lifted classical Bernoulli number
`B_{p*n+1}` for every positive odd `n`.  This removes the bounded Faulhaber
artifact from the bridge proof.  The remaining step for full Corollary 34 is a
side-condition-free comparison between `B_{p*n+1}` and `B_{n+1}/(n+1)`. -/
theorem bernoulliGen_teichmuller_pow_sModEq_bernoulli_lift
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {n : ℕ} (hn_odd : Odd n) (hn_pos : 0 < n) :
    ∃ z : ℤ_[p],
      BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          ((bernoulli (p * n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  set t : ℕ := p * n + 1 with ht_def
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  /- **Ingredient 1** (from Step 1 + T006). -/
  have h_ingr1 : ∃ z : ℤ_[p],
      (p : ℚ_[p]) * BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) =
        (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
    have hn_ne_zero : n ≠ 0 := hn_pos.ne'
    have hn_not_dvd : ¬ (p - 1) ∣ n := by
      intro hdvd
      have hp_minus_one_even : 2 ∣ (p - 1) := by
        obtain ⟨k, _⟩ := hp.odd_of_ne_two hp_odd
        exact ⟨k, by omega⟩
      have h2n : 2 ∣ n := dvd_trans hp_minus_one_even hdvd
      obtain ⟨k, hk⟩ := hn_odd
      rw [hk] at h2n
      omega
    have hωQ_ne_one : (teichmullerCharQp p) ^ n ≠ 1 :=
      teichmullerCharQp_pow_ne_one_of_not_dvd (p := p) hn_not_dvd
    have hT006 := natCast_mul_BernoulliGen_one_of_ne_one
      (R := ℚ_[p]) (N := p) (χ := (teichmullerCharQp p) ^ n) hωQ_ne_one
    have hterm_mem : ∀ a : ZMod p,
        (teichmuller p a) ^ n * (a.val : ℤ_[p]) - (a.val : ℤ_[p]) ^ t ∈
        (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2 := by
      intro a
      have h_mod : teichmuller p a ≡ (a.val : ℤ_[p]) ^ p
          [SMOD (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2] :=
        SModEq.sub_mem.mpr (teichmuller_sub_pow_val_mem_pow_two (p := p) a)
      have h_pow := h_mod.pow n
      have h_mul := h_pow.mul (SModEq.refl (a.val : ℤ_[p]))
      rw [SModEq.sub_mem] at h_mul
      have h_simp : ((a.val : ℤ_[p]) ^ p) ^ n * (a.val : ℤ_[p]) =
          (a.val : ℤ_[p]) ^ t := by
        rw [← pow_mul, ht_def, ← pow_succ]
      rw [h_simp] at h_mul
      exact h_mul
    let S : ℤ_[p] := ∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p])
    let T : ℤ_[p] := ∑ a : ZMod p, (a.val : ℤ_[p]) ^ t
    have hST_mem : S - T ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2 := by
      change (∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p])) -
          (∑ a : ZMod p, (a.val : ℤ_[p]) ^ t) ∈ _
      rw [← Finset.sum_sub_distrib]
      exact Ideal.sum_mem _ fun a _ => hterm_mem a
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hST_mem
    obtain ⟨w, hw⟩ := hST_mem
    refine ⟨w, ?_⟩
    have hS_coe : ((S : ℤ_[p]) : ℚ_[p]) =
        ∑ a : ZMod p, ((teichmullerCharQp p) ^ n) a * (a.val : ℚ_[p]) := by
      change ((∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p]) : ℤ_[p]) :
        ℚ_[p]) = _
      rw [PadicInt.coe_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
      congr 1
      rw [teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := n),
        MulChar.ringHomComp_apply, MulChar.pow_apply' _ hn_ne_zero,
        map_pow, teichmullerChar_apply]
      rfl
    have hT_coe : ((T : ℤ_[p]) : ℚ_[p]) =
        ∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t := by
      change ((∑ a : ZMod p, (a.val : ℤ_[p]) ^ t : ℤ_[p]) : ℚ_[p]) = _
      rw [PadicInt.coe_sum]
      simp_rw [show ∀ a : ZMod p,
          (((a.val : ℤ_[p]) ^ t : ℤ_[p]) : ℚ_[p]) = ((a.val : ℚ_[p]) ^ t) from
        fun a => by rw [PadicInt.coe_pow, PadicInt.coe_natCast]]
      refine Finset.sum_nbij (fun a => a.val) ?_ ?_ ?_ ?_
      · intro a _
        simp only [Finset.mem_range]
        exact ZMod.val_lt a
      · intros a _ b _ hab
        exact ZMod.val_injective _ hab
      · intros k hk
        simp only [Finset.coe_univ, Set.image_univ, Set.mem_range]
        simp only [Finset.mem_coe, Finset.mem_range] at hk
        exact ⟨(k : ZMod p), ZMod.val_natCast_of_lt hk⟩
      · intros a _
        rfl
    calc (p : ℚ_[p]) * BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t)
        = (((S : ℤ_[p]) : ℚ_[p])) - ((T : ℤ_[p]) : ℚ_[p]) := by
          rw [hS_coe, hT_coe, hT006]
      _ = (((S - T : ℤ_[p]) : ℚ_[p])) := by rw [PadicInt.coe_sub]
      _ = (((p : ℤ_[p]) ^ 2 * w : ℤ_[p]) : ℚ_[p]) := by rw [hw]
      _ = (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := by push_cast; ring
  obtain ⟨z₁, hz₁⟩ := h_ingr1
  /- **Ingredient 2** (Step 2), with direct von Staudt integrality. -/
  have h_ingr2 : ∃ z : ℤ_[p],
      (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
          (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
    refine sum_range_pow_sModEq_p_mul_bernoulli_vonStaudt hp_odd ?_ ?_ ?_
    · have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    · rw [ht_def]
      exact ((hp.odd_of_ne_two hp_odd).mul hn_odd).add_one
    · intro hdvd
      have h_pn : p ∣ p * n := ⟨n, rfl⟩
      have h_eq : t + 1 = p * n + 2 := by simp [ht_def]
      rw [h_eq] at hdvd
      have hp2 : p ∣ 2 := by simpa using Nat.dvd_sub hdvd h_pn
      exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
  obtain ⟨z₂, hz₂⟩ := h_ingr2
  refine ⟨z₁ + z₂, ?_⟩
  have h_bridge' : BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
      ((bernoulli t : ℚ) : ℚ_[p]) = (p : ℚ_[p]) * ((z₁ : ℚ_[p]) + (z₂ : ℚ_[p])) :=
    (mul_right_inj' hpQ_ne).mp <| by linear_combination hz₁ + hz₂
  have h_bridge : BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
      ((bernoulli t : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * ((z₁ + z₂ : ℤ_[p]) : ℚ_[p]) := by
    rw [h_bridge']
    push_cast
    ring
  simpa [ht_def] using h_bridge

/-- Reduction from the remaining lifted Bernoulli comparison to the
finite-character bridge.  This is deliberately only a reduction: the input
`hcmp` is the exact remaining source theorem needed to remove the Voronoi unit
side conditions. -/
theorem bernoulliGen_teichmuller_pow_sModEq_div_of_liftComparison
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {n : ℕ} (hn_odd : Odd n) (hn_pos : 0 < n)
    (hcmp : ∃ z : ℤ_[p],
      (((bernoulli (p * n + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  obtain ⟨z₁, hz₁⟩ :=
    bernoulliGen_teichmuller_pow_sModEq_bernoulli_lift hp_odd hn_odd hn_pos
  obtain ⟨z₂, hz₂⟩ := hcmp
  refine ⟨z₁ + z₂, ?_⟩
  calc
    BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
        (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p])
        =
        (BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (((bernoulli (p * n + 1) : ℚ) : ℚ_[p]))) +
        ((((bernoulli (p * n + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p])) := by
          ring
    _ = (p : ℚ_[p]) * ((z₁ : ℚ_[p]) + (z₂ : ℚ_[p])) := by
      rw [hz₁, hz₂]
      ring
    _ = (p : ℚ_[p]) * ((z₁ + z₂ : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

/-- Full Kummer congruence reduced to the single lifted comparison
`B_(p*r+1) ≡ B_(r+1)/(r+1) (mod p)`.  This keeps the proof-source boundary
visible: proving the comparison uniformly is exactly the remaining
side-condition-free Kummer theorem, not an already discharged package. -/
theorem bernoulli_div_sModEq_of_modEq_full_of_liftComparison
    {p m n : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1])
    (hcmp : ∀ {r : ℕ}, Odd r → 0 < r → ¬ (p - 1) ∣ r + 1 →
      ∃ z : ℤ_[p],
        (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
            (((bernoulli (r + 1) : ℚ) / (r + 1) : ℚ) : ℚ_[p]) =
          (p : ℚ_[p]) * (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  refine bernoulli_div_sModEq_of_modEq_of_teichmullerBridge
    hm_pos hn_pos hm_even hn_even hnot hmn ?_
  intro k hk_pos hk_even hnot_k
  have hk_pred_pos : 0 < k - 1 := by
    obtain ⟨r, hr⟩ := hk_even
    omega
  have hk_pred_odd : Odd (k - 1) := by
    obtain ⟨r, hr⟩ := hk_even
    rcases r with _ | r
    · omega
    · exact ⟨r, by omega⟩
  have hnot_pred : ¬ (p - 1) ∣ (k - 1) + 1 := by
    intro hdvd
    have hk_succ : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos
    exact hnot_k (by simpa [hk_succ] using hdvd)
  obtain ⟨z, hz⟩ :=
    bernoulliGen_teichmuller_pow_sModEq_div_of_liftComparison hp_odd
      hk_pred_odd hk_pred_pos (hcmp hk_pred_odd hk_pred_pos hnot_pred)
  have hz' :
      BernoulliGen ((teichmullerCharQp p) ^ (k - 1)) 1 -
          (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
    have hk_succ : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos
    have hden : (((k - 1 : ℕ) : ℚ) + 1) = (k : ℚ) := by
      exact_mod_cast hk_succ
    simpa [hk_succ, hden] using hz
  refine ⟨-z, ?_⟩
  calc
    (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) -
        BernoulliGen ((teichmullerCharQp p) ^ (k - 1)) 1
        = -(BernoulliGen ((teichmullerCharQp p) ^ (k - 1)) 1 -
            (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p])) := by
          ring
    _ = (p : ℚ_[p]) * ((-z : ℤ_[p]) : ℚ_[p]) := by
      rw [hz']
      push_cast
      ring

/-- The remaining lifted comparison follows from the standard unrestricted
Kummer congruence.  This formalizes the specialization `m = p*r + 1`,
`n = r + 1`: Kummer gives `B_m / m ≡ B_n / n`, and `m ≡ 1 (mod p)` plus
von Staudt integrality lets us replace `B_m / m` by `B_m`. -/
theorem bernoulli_pr_plus_one_sModEq_div_of_kummerCongruence
    {p r : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (hr_odd : Odd r) (hr_pos : 0 < r)
    (hnot : ¬ (p - 1) ∣ r + 1)
    (hkummer : ∀ {m n : ℕ}, 0 < m → 0 < n → Even m → Even n →
      ¬ (p - 1) ∣ n → m ≡ n [MOD p - 1] →
      ∃ z : ℤ_[p],
        (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
          (((bernoulli n : ℚ) / (n : ℕ) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (r + 1) : ℚ) / (r + 1 : ℕ) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp_prime : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp_prime.two_le (Ne.symm hp_odd)
  have hp_nat_odd : Odd p := hp_prime.odd_of_ne_two hp_odd
  have hm_pos : 0 < p * r + 1 := Nat.succ_pos _
  have hn_pos : 0 < r + 1 := lt_trans hr_pos (Nat.lt_succ_self r)
  have hm_even : Even (p * r + 1) := (hp_nat_odd.mul hr_odd).add_one
  have hn_even : Even (r + 1) := hr_odd.add_one
  have hmn : p * r + 1 ≡ r + 1 [MOD p - 1] := by
    have hr_le : r ≤ p * r := Nat.le_mul_of_pos_left r (by omega)
    have hpr : (p - 1) * r = p * r - r := by
      rw [Nat.sub_mul, Nat.one_mul]
    have h_eq : p * r + 1 = (r + 1) + (p - 1) * r := by omega
    unfold Nat.ModEq
    rw [h_eq, Nat.add_mul_mod_self_left]
  have hnot_m : ¬ (p - 1) ∣ p * r + 1 := by
    intro hdvd
    have hm_zero : p * r + 1 ≡ 0 [MOD p - 1] :=
      Nat.modEq_zero_iff_dvd.mpr hdvd
    have hn_zero : r + 1 ≡ 0 [MOD p - 1] := hmn.symm.trans hm_zero
    exact hnot (Nat.modEq_zero_iff_dvd.mp hn_zero)
  obtain ⟨zK, hzK⟩ :=
    hkummer hm_pos hn_pos hm_even hn_even hnot hmn
  obtain ⟨bm, hbm⟩ :=
    bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd hm_even hnot_m
  have hm_not_dvd_p : ¬ p ∣ p * r + 1 := by
    intro hdvd
    have hpr_dvd : p ∣ p * r := ⟨r, rfl⟩
    have hp_dvd_one : p ∣ 1 := (Nat.dvd_add_right hpr_dvd).mp hdvd
    exact absurd (Nat.le_of_dvd (by omega) hp_dvd_one) (by omega)
  have hm_unit : IsUnit (((p * r + 1 : ℕ) : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp_prime.coprime_iff_not_dvd.mpr hm_not_dvd_p
  set mInv : ℤ_[p] := (hm_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hmInv_def
  have hmInv_mul : ((p * r + 1 : ℕ) : ℤ_[p]) * mInv = 1 := by
    change ((hm_unit.unit * hm_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hmInv_mul_Qp :
      ((p * r + 1 : ℕ) : ℚ_[p]) * ((mInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hmInv_mul
  have hBm_div :
      (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) =
        (bm : ℚ_[p]) * (mInv : ℚ_[p]) := by
    have h_div :
        (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) =
          ((bernoulli (p * r + 1) : ℚ) : ℚ_[p]) /
            ((p * r + 1 : ℕ) : ℚ_[p]) := by
      push_cast
      rfl
    rw [h_div, hbm, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hmInv_mul_Qp]
  have hBm_sub_div :
      (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (((r : ℤ_[p]) * bm * mInv : ℤ_[p]) : ℚ_[p]) := by
    rw [hbm, hBm_div]
    calc
      (bm : ℚ_[p]) - (bm : ℚ_[p]) * (mInv : ℚ_[p])
          =
          (((p * r + 1 : ℕ) : ℚ_[p]) * (mInv : ℚ_[p]) -
              (mInv : ℚ_[p])) * (bm : ℚ_[p]) := by
            rw [hmInv_mul_Qp]
            ring
      _ = ((((p * r + 1 : ℕ) : ℚ_[p]) - 1) * (mInv : ℚ_[p])) *
            (bm : ℚ_[p]) := by ring
      _ = ((p : ℚ_[p]) * (r : ℚ_[p]) * (mInv : ℚ_[p])) * (bm : ℚ_[p]) := by
        have hm_sub : ((p * r + 1 : ℕ) : ℚ_[p]) - 1 =
            (p : ℚ_[p]) * (r : ℚ_[p]) := by
          push_cast
          ring
        rw [hm_sub]
      _ = (p : ℚ_[p]) * (((r : ℤ_[p]) * bm * mInv : ℤ_[p]) : ℚ_[p]) := by
        push_cast
        ring
  refine ⟨(r : ℤ_[p]) * bm * mInv + zK, ?_⟩
  calc
    (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
        (((bernoulli (r + 1) : ℚ) / (r + 1 : ℕ) : ℚ) : ℚ_[p])
        =
        ((((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p])) +
        ((((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) -
          (((bernoulli (r + 1) : ℚ) / (r + 1 : ℕ) : ℚ) : ℚ_[p])) := by
          ring
    _ = (p : ℚ_[p]) *
        ((((r : ℤ_[p]) * bm * mInv : ℤ_[p]) : ℚ_[p]) + (zK : ℚ_[p])) := by
      rw [hBm_sub_div, hzK]
      ring
    _ = (p : ℚ_[p]) * ((((r : ℤ_[p]) * bm * mInv + zK : ℤ_[p]) : ℚ_[p])) := by
      push_cast
      ring

/-- The lifted comparison `B_(p*r+1) ≡ B_(r+1)/(r+1) (mod p)`, now proved
directly from the clean public full-Kummer theorem. -/
theorem bernoulli_pr_plus_one_sModEq_div_clean
    {p r : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hr_odd : Odd r) (hr_pos : 0 < r)
    (hnot : ¬ (p - 1) ∣ r + 1) :
    ∃ z : ℤ_[p],
      (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (r + 1) : ℚ) / (r + 1 : ℕ) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp_prime.two_le (Ne.symm hp_odd)
  have hp_nat_odd : Odd p := hp_prime.odd_of_ne_two hp_odd
  have hm_pos : 0 < p * r + 1 := Nat.succ_pos _
  have hn_pos : 0 < r + 1 := lt_trans hr_pos (Nat.lt_succ_self r)
  have hm_even : Even (p * r + 1) := (hp_nat_odd.mul hr_odd).add_one
  have hn_even : Even (r + 1) := hr_odd.add_one
  have hmn : p * r + 1 ≡ r + 1 [MOD p - 1] := by
    have hr_le : r ≤ p * r := Nat.le_mul_of_pos_left r (by omega)
    have hpr : (p - 1) * r = p * r - r := by
      rw [Nat.sub_mul, Nat.one_mul]
    have h_eq : p * r + 1 = (r + 1) + (p - 1) * r := by omega
    unfold Nat.ModEq
    rw [h_eq, Nat.add_mul_mod_self_left]
  have hnot_m : ¬ (p - 1) ∣ p * r + 1 := by
    intro hdvd
    have hm_zero : p * r + 1 ≡ 0 [MOD p - 1] :=
      Nat.modEq_zero_iff_dvd.mpr hdvd
    have hn_zero : r + 1 ≡ 0 [MOD p - 1] := hmn.symm.trans hm_zero
    exact hnot (Nat.modEq_zero_iff_dvd.mp hn_zero)
  obtain ⟨zK, hzK⟩ :=
    bernoulli_div_sModEq_of_modEq_full (p := p) hp_odd hm_pos hn_pos
      hm_even hn_even hnot hmn
  obtain ⟨bm, hbm⟩ :=
    bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd hm_even hnot_m
  have hm_not_dvd_p : ¬ p ∣ p * r + 1 := by
    intro hdvd
    have hpr_dvd : p ∣ p * r := ⟨r, rfl⟩
    have hp_dvd_one : p ∣ 1 := (Nat.dvd_add_right hpr_dvd).mp hdvd
    exact absurd (Nat.le_of_dvd (by omega) hp_dvd_one) (by omega)
  have hm_unit : IsUnit (((p * r + 1 : ℕ) : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp_prime.coprime_iff_not_dvd.mpr hm_not_dvd_p
  set mInv : ℤ_[p] := (hm_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hmInv_def
  have hmInv_mul : ((p * r + 1 : ℕ) : ℤ_[p]) * mInv = 1 := by
    change ((hm_unit.unit * hm_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hmInv_mul_Qp :
      ((p * r + 1 : ℕ) : ℚ_[p]) * ((mInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hmInv_mul
  have hBm_div :
      (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) =
        (bm : ℚ_[p]) * (mInv : ℚ_[p]) := by
    have h_div :
        (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) =
          ((bernoulli (p * r + 1) : ℚ) : ℚ_[p]) /
            ((p * r + 1 : ℕ) : ℚ_[p]) := by
      push_cast
      rfl
    rw [h_div, hbm, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hmInv_mul_Qp]
  have hBm_sub_div :
      (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (((r : ℤ_[p]) * bm * mInv : ℤ_[p]) : ℚ_[p]) := by
    rw [hbm, hBm_div]
    calc
      (bm : ℚ_[p]) - (bm : ℚ_[p]) * (mInv : ℚ_[p])
          =
          (((p * r + 1 : ℕ) : ℚ_[p]) * (mInv : ℚ_[p]) -
              (mInv : ℚ_[p])) * (bm : ℚ_[p]) := by
            rw [hmInv_mul_Qp]
            ring
      _ = ((((p * r + 1 : ℕ) : ℚ_[p]) - 1) * (mInv : ℚ_[p])) *
            (bm : ℚ_[p]) := by ring
      _ = ((p : ℚ_[p]) * (r : ℚ_[p]) * (mInv : ℚ_[p])) * (bm : ℚ_[p]) := by
        have hm_sub : ((p * r + 1 : ℕ) : ℚ_[p]) - 1 =
            (p : ℚ_[p]) * (r : ℚ_[p]) := by
          push_cast
          ring
        rw [hm_sub]
      _ = (p : ℚ_[p]) * (((r : ℤ_[p]) * bm * mInv : ℤ_[p]) : ℚ_[p]) := by
        push_cast
        ring
  refine ⟨(r : ℤ_[p]) * bm * mInv + zK, ?_⟩
  calc
    (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
        (((bernoulli (r + 1) : ℚ) / (r + 1 : ℕ) : ℚ) : ℚ_[p])
        =
        ((((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p])) +
        ((((bernoulli (p * r + 1) : ℚ) / (p * r + 1 : ℕ) : ℚ) : ℚ_[p]) -
          (((bernoulli (r + 1) : ℚ) / (r + 1 : ℕ) : ℚ) : ℚ_[p])) := by
          ring
    _ = (p : ℚ_[p]) *
        ((((r : ℤ_[p]) * bm * mInv : ℤ_[p]) : ℚ_[p]) + (zK : ℚ_[p])) := by
      rw [hBm_sub_div, hzK]
      ring
    _ = (p : ℚ_[p]) * ((((r : ℤ_[p]) * bm * mInv + zK : ℤ_[p]) : ℚ_[p])) := by
      push_cast
      ring

/-- Voronoi's congruence with the old bounded-`p^3` dependency removed.
The remaining `p ∤ k + 1` assumption is the genuine unit needed by this
elementary Voronoi proof route. -/
theorem voronoi_congruence_mod_p_vonStaudt
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_two : 2 ≤ k) (hk_even : Even k) (_hk_coprime : ¬ (p - 1) ∣ k)
    (h_p_not_dvd_kPlus : ¬ (p : ℕ) ∣ (k + 1)) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) *
            ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hk_pos : 0 < k := by omega
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨W, hW⟩ := voronoi_sum_mod_p_sq ha_coprime hk_pos
  obtain ⟨W', hW'⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even
    (fun _j _hj _hj_two hj_even =>
      p_mul_bernoulli_mem_padicInt_vonStaudt (p := p) hj_even)
  have hkp1_unit : IsUnit ((k + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_kPlus
  set u : ℤ_[p] := (hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hu_def
  have hu_mul : ((k + 1 : ℕ) : ℤ_[p]) * u = 1 := by
    change ((hkp1_unit.unit * hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hu_mul_Qp : ((k + 1 : ℕ) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul
  refine ⟨W - ((a : ℤ_[p]) ^ k - 1) * u * W', ?_⟩
  set S1 : ℚ_[p] := ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ k with hS1_def
  set S2 : ℚ_[p] :=
    ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℚ_[p]) with hS2_def
  have hW_Q : ((a : ℚ_[p]) ^ k - 1) * S1 -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * (p : ℚ_[p]) * S2 =
      (p : ℚ_[p]) ^ 2 * ((W : ℤ_[p]) : ℚ_[p]) := by
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hW
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, PadicInt.coe_one] at this
    rw [hS1_def, hS2_def]
    push_cast at this
    exact this
  have hkp1Q_ne : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_S1_sub : S1 - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    have h_mul : ((k + 1 : ℕ) : ℚ_[p]) *
        (S1 - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
        ((k + 1 : ℕ) : ℚ_[p]) *
        (((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p])) := by
      rw [hS1_def, hW']
      linear_combination -((p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p])) * hu_mul_Qp
    exact mul_left_cancel₀ hkp1Q_ne h_mul
  have hS1_eq : S1 = (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) +
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    linear_combination h_S1_sub
  rw [hS1_eq] at hW_Q
  have hS2_cast : ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) =
      S2 := by
    rw [hS2_def]
    push_cast
    rfl
  have hX : ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * S2 =
      (p : ℚ_[p]) * (((W : ℤ_[p]) : ℚ_[p]) -
        ((a : ℚ_[p]) ^ k - 1) * ((u : ℤ_[p]) : ℚ_[p]) * ((W' : ℤ_[p]) : ℚ_[p])) :=
    mul_left_cancel₀ hpQ_ne (by linear_combination hW_Q)
  rw [hS2_cast]
  push_cast
  linear_combination hX

/-- For the natural-number Voronoi floor sums `∑ j, j ^ (k - 1) * (j * a / p)`,
congruent predecessor exponents give equal images in `ZMod p`. -/
private theorem natCast_floorSum_pred_eq_zmod {p a m n : ℕ} [Fact p.Prime]
    (hmn : (m - 1) ≡ (n - 1) [MOD p - 1]) :
    ((∑ j ∈ Finset.range p, j ^ (m - 1) * (j * a / p) : ℕ) : ZMod p) =
      ((∑ j ∈ Finset.range p, j ^ (n - 1) * (j * a / p) : ℕ) : ZMod p) := by
  have hp : Nat.Prime p := Fact.out
  have h_pow_pred_ZMod : ∀ j : ℕ, j < p → j ≠ 0 →
      ((j : ℕ) : ZMod p) ^ (m - 1) = ((j : ℕ) : ZMod p) ^ (n - 1) := by
    intro j hjp hj_ne
    have hj_coprime : Nat.Coprime j p :=
      (hp.coprime_iff_not_dvd.mpr
        (fun hdvd => hj_ne (Nat.eq_zero_of_dvd_of_lt hdvd hjp))).symm
    lift (((j : ℕ) : ZMod p)) to (ZMod p)ˣ using
      (ZMod.isUnit_iff_coprime j p).mpr hj_coprime
      with u hu
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    congr 1
    rw [pow_eq_pow_iff_modEq]
    have h_ord_dvd : orderOf u ∣ (p - 1) := by
      rw [← ZMod.card_units, ← Nat.card_eq_fintype_card]
      exact orderOf_dvd_natCard u
    exact hmn.of_dvd h_ord_dvd
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  by_cases hj_ne : j = 0
  · simp [hj_ne]
  · rw [h_pow_pred_ZMod j hj hj_ne]

/-- Final algebraic cancellation of the Kummer congruence over `ℚ_[p]` for the
von-Staudt Voronoi route. Compared with `bernoulli_div_sub_eq_p_mul_of_expansions`,
the single-exponent expansions carry an extra index factor `mQ`, `nQ`, and the
conclusion is about the divided Bernoulli numbers `Bmdiv = Bm / mQ`. -/
private theorem bernoulli_div_sub_eq_p_mul_of_vonStaudt_expansions {p : ℕ}
    [Fact p.Prime]
    {Am Bm Bmdiv mQ Am1 Sm zm AmInv mInv
      An Bn Bndiv nQ An1 Sn zn AnInv nInv E : ℚ_[p]}
    (hmBm : mQ * Bmdiv = Bm) (hnBn : nQ * Bndiv = Bn)
    (hBmexp : (Am - 1) * Bm = mQ * Am1 * Sm + (p : ℚ_[p]) * zm)
    (hBnexp : (An - 1) * Bn = nQ * An1 * Sn + (p : ℚ_[p]) * zn)
    (hE : (An - 1) * Am1 * Sm - (Am - 1) * An1 * Sn = (p : ℚ_[p]) * E)
    (hAmInv : (Am - 1) * AmInv = 1) (hAnInv : (An - 1) * AnInv = 1)
    (hmInv : mQ * mInv = 1) (hnInv : nQ * nInv = 1) :
    Bmdiv - Bndiv =
      (p : ℚ_[p]) * (AmInv * AnInv * E + AmInv * mInv * zm - AnInv * nInv * zn) := by
  have h_Am_ne : Am - 1 ≠ 0 := fun h0 => one_ne_zero <| by
    rw [← hAmInv, h0, zero_mul]
  have h_An_ne : An - 1 ≠ 0 := fun h0 => one_ne_zero <| by
    rw [← hAnInv, h0, zero_mul]
  have hmQ_ne : mQ ≠ 0 := fun h0 => one_ne_zero <| by rw [← hmInv, h0, zero_mul]
  have hnQ_ne : nQ ≠ 0 := fun h0 => one_ne_zero <| by rw [← hnInv, h0, zero_mul]
  have h_key :
      (Am - 1) * (An - 1) * mQ * nQ * (Bmdiv - Bndiv) =
        (Am - 1) * (An - 1) * mQ * nQ * ((p : ℚ_[p]) *
          (AmInv * AnInv * E + AmInv * mInv * zm - AnInv * nInv * zn)) := by
    have h_lhs :
        (Am - 1) * (An - 1) * mQ * nQ * (Bmdiv - Bndiv) =
        (An - 1) * nQ * ((Am - 1) * (mQ * Bmdiv)) -
          (Am - 1) * mQ * ((An - 1) * (nQ * Bndiv)) := by ring
    rw [h_lhs, hmBm, hnBn]
    rw [hBmexp, hBnexp]
    rw [show (An - 1) * nQ * (mQ * Am1 * Sm + (p : ℚ_[p]) * zm) -
        (Am - 1) * mQ * (nQ * An1 * Sn + (p : ℚ_[p]) * zn) =
        (mQ * nQ * ((An - 1) * Am1 * Sm - (Am - 1) * An1 * Sn)) +
        ((p : ℚ_[p]) * ((An - 1) * nQ * zm - (Am - 1) * mQ * zn)) from by ring, hE]
    rw [show (Am - 1) * (An - 1) * mQ * nQ * ((p : ℚ_[p]) *
          (AmInv * AnInv * E + AmInv * mInv * zm - AnInv * nInv * zn)) =
        (p : ℚ_[p]) *
            (((Am - 1) * AmInv) * ((An - 1) * AnInv) * mQ * nQ * E) +
        (p : ℚ_[p]) * ((An - 1) * ((Am - 1) * AmInv) *
          (mQ * mInv) * nQ * zm) -
        (p : ℚ_[p]) * ((Am - 1) * ((An - 1) * AnInv) *
          (nQ * nInv) * mQ * zn) from by ring,
      hAmInv, hAnInv, hmInv, hnInv]
    ring
  have h_cancel_ne : (Am - 1) * (An - 1) * mQ * nQ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h_Am_ne h_An_ne) hmQ_ne) hnQ_ne
  exact mul_left_cancel₀ h_cancel_ne h_key

/-- Kummer congruence from the Voronoi route with the old bounded-`p^3`
hypotheses removed.  This is still not Diekmann Corollary 33: the elementary
Voronoi proof here still needs the unit assumptions `p ∤ m`, `p ∤ n`,
`p ∤ m + 1`, and `p ∤ n + 1`. -/
theorem bernoulli_div_sModEq_of_modEq_voronoiNoBound
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {m n : ℕ} (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (h_pSubOne_not_dvd_n : ¬ (p - 1) ∣ n)
    (h_mn_modEq : m ≡ n [MOD (p - 1)])
    (hm_coprime_p : ¬ (p : ℕ) ∣ m) (hn_coprime_p : ¬ (p : ℕ) ∣ n)
    (hm_p_plus : ¬ (p : ℕ) ∣ (m + 1)) (hn_p_plus : ¬ (p : ℕ) ∣ (n + 1)) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / m : ℚ) : ℚ_[p]) -
          (((bernoulli n : ℚ) / n : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hm_two : 2 ≤ m := by obtain ⟨r, hr⟩ := hm_even; omega
  have hn_two : 2 ≤ n := by obtain ⟨r, hr⟩ := hn_even; omega
  have h_pSubOne_not_dvd_m : ¬ (p - 1) ∣ m :=
    not_sub_one_dvd_of_modEq h_pSubOne_not_dvd_n h_mn_modEq
  have hmn_pred : (m - 1) ≡ (n - 1) [MOD p - 1] :=
    modEq_pred_of_modEq hm_pos hn_pos h_mn_modEq
  -- Pick a generator of `(ZMod p)ˣ` and its residue representative `a`.
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set a : ℕ := (g : ZMod p).val with ha_def
  have ha_coprimeZ : Nat.Coprime a p := ZMod.val_coe_unit_coprime g
  have ha_coprime : ¬ (p : ℕ) ∣ a := by
    rw [Nat.coprime_comm] at ha_coprimeZ
    exact hp.coprime_iff_not_dvd.mp ha_coprimeZ
  have ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [ha_def]; exact ZMod.natCast_zmod_val _
  have hg_order : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen, Nat.card_eq_fintype_card,
      ZMod.card_units]
  -- Single-exponent von-Staudt Voronoi congruences at `m` and `n`.
  obtain ⟨z_m, hz_m⟩ :=
    voronoi_congruence_mod_p_vonStaudt hp_odd ha_coprime hm_two hm_even
      h_pSubOne_not_dvd_m hm_p_plus
  obtain ⟨z_n, hz_n⟩ :=
    voronoi_congruence_mod_p_vonStaudt hp_odd ha_coprime hn_two hn_even
      h_pSubOne_not_dvd_n hn_p_plus
  set Am : ℤ_[p] := (a : ℤ_[p]) ^ m with hAm_def
  set An : ℤ_[p] := (a : ℤ_[p]) ^ n with hAn_def
  set Am1 : ℤ_[p] := (a : ℤ_[p]) ^ (m - 1) with hAm1_def
  set An1 : ℤ_[p] := (a : ℤ_[p]) ^ (n - 1) with hAn1_def
  set Sm : ℕ := ∑ j ∈ Finset.range p, j ^ (m - 1) * (j * a / p) with hSm_def
  set Sn : ℕ := ∑ j ∈ Finset.range p, j ^ (n - 1) * (j * a / p) with hSn_def
  -- The exponent congruences force the `p`-adic data to agree mod `p`.
  have h_toZMod_a : PadicInt.toZMod (a : ℤ_[p]) = ((a : ℕ) : ZMod p) := by
    rw [map_natCast]
  have h_Am_An_toZMod : PadicInt.toZMod Am = PadicInt.toZMod An := by
    rw [hAm_def, hAn_def, map_pow, map_pow, h_toZMod_a]
    exact natCast_pow_eq_of_modEq hg_order ha_cast h_mn_modEq
  obtain ⟨d_A, hd_A⟩ := Ideal.mem_span_singleton.mp
    (padicInt_sub_mem_span_p_of_toZMod_eq h_Am_An_toZMod)
  have h_Am1_An1_toZMod : PadicInt.toZMod Am1 = PadicInt.toZMod An1 := by
    rw [hAm1_def, hAn1_def, map_pow, map_pow, h_toZMod_a]
    exact natCast_pow_eq_of_modEq hg_order ha_cast hmn_pred
  obtain ⟨d_A1, hd_A1⟩ := Ideal.mem_span_singleton.mp
    (padicInt_sub_mem_span_p_of_toZMod_eq h_Am1_An1_toZMod)
  have h_Sm_Sn_toZMod' :
      PadicInt.toZMod ((Sm : ℤ_[p])) = PadicInt.toZMod ((Sn : ℤ_[p])) := by
    rw [map_natCast, map_natCast, hSm_def, hSn_def]
    exact natCast_floorSum_pred_eq_zmod hmn_pred
  obtain ⟨d_S, hd_S⟩ := Ideal.mem_span_singleton.mp
    (padicInt_sub_mem_span_p_of_toZMod_eq h_Sm_Sn_toZMod')
  -- All four relevant elements are units in `ℤ_[p]`.
  have h_Am_sub_one_unit : IsUnit (Am - 1) := hAm_def ▸
    padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd hg_order ha_cast h_pSubOne_not_dvd_m
  have h_An_sub_one_unit : IsUnit (An - 1) := hAn_def ▸
    padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd hg_order ha_cast h_pSubOne_not_dvd_n
  have h_m_unit : IsUnit ((m : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hm_coprime_p
  have h_n_unit : IsUnit ((n : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hn_coprime_p
  set mInv : ℤ_[p] := (h_m_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hmInv_mul : ((m : ℕ) : ℤ_[p]) * mInv = 1 := padicInt_isUnit_mul_unitInv h_m_unit
  set nInv : ℤ_[p] := (h_n_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hnInv_mul : ((n : ℕ) : ℤ_[p]) * nInv = 1 := padicInt_isUnit_mul_unitInv h_n_unit
  set AmInv : ℤ_[p] := (h_Am_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hAmInv_mul : (Am - 1) * AmInv = 1 := padicInt_isUnit_mul_unitInv h_Am_sub_one_unit
  set AnInv : ℤ_[p] := (h_An_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hAnInv_mul : (An - 1) * AnInv = 1 := padicInt_isUnit_mul_unitInv h_An_sub_one_unit
  -- Package the combined floor-sum identity in `E` over `ℤ_[p]`.
  set SmZ : ℤ_[p] := ((Sm : ℕ) : ℤ_[p]) with hSmZ_def
  set SnZ : ℤ_[p] := ((Sn : ℕ) : ℤ_[p]) with hSnZ_def
  set E : ℤ_[p] := (Am - 1) * (d_A1 * SmZ + An1 * d_S) - d_A * Am1 * SmZ with hE_def
  have hE_eq :
      (An - 1) * Am1 * SmZ - (Am - 1) * An1 * SnZ = (p : ℤ_[p]) * E := by
    have h_An_eq : An = Am - (p : ℤ_[p]) * d_A := by linear_combination -hd_A
    have h_An1_eq : An1 = Am1 - (p : ℤ_[p]) * d_A1 := by linear_combination -hd_A1
    have h_SnZ_eq : SnZ = SmZ - (p : ℤ_[p]) * d_S := by linear_combination -hd_S
    rw [hE_def, h_An_eq, h_An1_eq, h_SnZ_eq]; ring
  refine ⟨AmInv * AnInv * E + AmInv * mInv * z_m - AnInv * nInv * z_n, ?_⟩
  -- Transport everything to `ℚ_[p]` and abbreviate.
  set Am_Q : ℚ_[p] := (Am : ℚ_[p]) with hAm_Q_def
  set An_Q : ℚ_[p] := (An : ℚ_[p]) with hAn_Q_def
  set Am1_Q : ℚ_[p] := (Am1 : ℚ_[p]) with hAm1_Q_def
  set An1_Q : ℚ_[p] := (An1 : ℚ_[p]) with hAn1_Q_def
  set Sm_Q : ℚ_[p] := (SmZ : ℚ_[p]) with hSm_Q_def
  set Sn_Q : ℚ_[p] := (SnZ : ℚ_[p]) with hSn_Q_def
  set mQ : ℚ_[p] := ((m : ℕ) : ℚ_[p]) with hmQ_def
  set nQ : ℚ_[p] := ((n : ℕ) : ℚ_[p]) with hnQ_def
  set Bm_Q : ℚ_[p] := ((bernoulli m : ℚ) : ℚ_[p]) with hBm_Q_def
  set Bn_Q : ℚ_[p] := ((bernoulli n : ℚ) : ℚ_[p]) with hBn_Q_def
  set Bm_div : ℚ_[p] := (((bernoulli m : ℚ) / m : ℚ) : ℚ_[p]) with hBm_div_def
  set Bn_div : ℚ_[p] := (((bernoulli n : ℚ) / n : ℚ) : ℚ_[p]) with hBn_div_def
  set z_m_Q : ℚ_[p] := ((z_m : ℤ_[p]) : ℚ_[p]) with hz_m_Q_def
  set z_n_Q : ℚ_[p] := ((z_n : ℤ_[p]) : ℚ_[p]) with hz_n_Q_def
  set E_Q : ℚ_[p] := ((E : ℤ_[p]) : ℚ_[p]) with hE_Q_def
  set AmInv_Q : ℚ_[p] := ((AmInv : ℤ_[p]) : ℚ_[p]) with hAmInv_Q_def
  set AnInv_Q : ℚ_[p] := ((AnInv : ℤ_[p]) : ℚ_[p]) with hAnInv_Q_def
  set mInv_Q : ℚ_[p] := ((mInv : ℤ_[p]) : ℚ_[p]) with hmInv_Q_def
  set nInv_Q : ℚ_[p] := ((nInv : ℤ_[p]) : ℚ_[p]) with hnInv_Q_def
  have h_mBm : mQ * Bm_div = Bm_Q := by
    rw [hBm_div_def, hmQ_def, hBm_Q_def]
    push_cast
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm_pos.ne' :
      ((m : ℕ) : ℚ_[p]) ≠ 0)]
  have h_nBn : nQ * Bn_div = Bn_Q := by
    rw [hBn_div_def, hnQ_def, hBn_Q_def]
    push_cast
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn_pos.ne' :
      ((n : ℕ) : ℚ_[p]) ≠ 0)]
  have h_Sm_cast :
      ((∑ j ∈ Finset.range p, j ^ (m - 1) * (j * a / p) : ℕ) : ℚ_[p]) = Sm_Q := by
    rw [hSm_Q_def, hSmZ_def, hSm_def, PadicInt.coe_natCast]
  have h_Sn_cast :
      ((∑ j ∈ Finset.range p, j ^ (n - 1) * (j * a / p) : ℕ) : ℚ_[p]) = Sn_Q := by
    rw [hSn_Q_def, hSnZ_def, hSn_def, PadicInt.coe_natCast]
  -- The two single-exponent expansions, in the abbreviated form expected by the
  -- final algebraic cancellation helper.
  have h_Bm_expand : (Am_Q - 1) * Bm_Q = mQ * Am1_Q * Sm_Q + (p : ℚ_[p]) * z_m_Q := by
    have := hz_m
    rw [h_Sm_cast] at this
    rw [hAm_Q_def, hAm1_Q_def, hAm_def, hAm1_def, hBm_Q_def, hmQ_def, hz_m_Q_def]
    push_cast
    linear_combination this
  have h_Bn_expand : (An_Q - 1) * Bn_Q = nQ * An1_Q * Sn_Q + (p : ℚ_[p]) * z_n_Q := by
    have := hz_n
    rw [h_Sn_cast] at this
    rw [hAn_Q_def, hAn1_Q_def, hAn_def, hAn1_def, hBn_Q_def, hnQ_def, hz_n_Q_def]
    push_cast
    linear_combination this
  have hE_eq_Q :
      (An_Q - 1) * Am1_Q * Sm_Q - (Am_Q - 1) * An1_Q * Sn_Q =
        (p : ℚ_[p]) * E_Q := by
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hE_eq
    rw [hAm_Q_def, hAn_Q_def, hAm1_Q_def, hAn1_Q_def, hSm_Q_def, hSn_Q_def, hE_Q_def]
    push_cast at this ⊢
    linear_combination this
  have h_mQ_mInv : mQ * mInv_Q = 1 := hmQ_def ▸ hmInv_Q_def ▸
    qp_mul_eq_one_of_padicInt_mul_eq_one hmInv_mul
  have h_nQ_nInv : nQ * nInv_Q = 1 := hnQ_def ▸ hnInv_Q_def ▸
    qp_mul_eq_one_of_padicInt_mul_eq_one hnInv_mul
  have h_Am_AmInv : (Am_Q - 1) * AmInv_Q = 1 := by
    have := qp_mul_eq_one_of_padicInt_mul_eq_one hAmInv_mul
    rw [hAm_Q_def, hAmInv_Q_def]; push_cast at this; linear_combination this
  have h_An_AnInv : (An_Q - 1) * AnInv_Q = 1 := by
    have := qp_mul_eq_one_of_padicInt_mul_eq_one hAnInv_mul
    rw [hAn_Q_def, hAnInv_Q_def]; push_cast at this; linear_combination this
  have h_witness_eq :
      ((((AmInv * AnInv * E + AmInv * mInv * z_m - AnInv * nInv * z_n :
        ℤ_[p]) : ℚ_[p]))) =
        AmInv_Q * AnInv_Q * E_Q + AmInv_Q * mInv_Q * z_m_Q -
          AnInv_Q * nInv_Q * z_n_Q := by
    rw [hAmInv_Q_def, hAnInv_Q_def, hmInv_Q_def, hnInv_Q_def, hz_m_Q_def,
      hz_n_Q_def, hE_Q_def]
    push_cast
    ring
  rw [h_witness_eq]
  exact bernoulli_div_sub_eq_p_mul_of_vonStaudt_expansions h_mBm h_nBn
    h_Bm_expand h_Bn_expand hE_eq_Q h_Am_AmInv h_An_AnInv h_mQ_mInv h_nQ_nInv

/-- Corollary 34 bridge with all bounded-Faulhaber restrictions removed, but
still under the genuine unit hypotheses used by the elementary Voronoi route.
The remaining fully unrestricted bridge needs the p-adic `L`/standard Kummer
source, or a proof that removes `p ∣ n + 1` and `p ∣ n + 2` cases. -/
theorem bernoulliGen_teichmuller_pow_sModEq_div_voronoiNoBound
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {n : ℕ} (hn_odd : Odd n) (hn_pos : 0 < n)
    (h_pSubOne_not_dvd_nPlus : ¬ (p - 1) ∣ (n + 1))
    (hn_p_plus : ¬ (p : ℕ) ∣ (n + 1))
    (hn_p_plus_two : ¬ (p : ℕ) ∣ (n + 2)) :
    ∃ z : ℤ_[p],
      BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  set t : ℕ := p * n + 1 with ht_def
  obtain ⟨z₁, hz₁⟩ :=
    bernoulliGen_teichmuller_pow_sModEq_bernoulli_lift hp_odd hn_odd hn_pos
  have h_ingr3 : ∃ z : ℤ_[p],
      (((bernoulli t : ℚ) : ℚ_[p])) -
          (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
    have ht_pos : 0 < t := by simp [ht_def]
    have hn1_pos : 0 < n + 1 := Nat.succ_pos n
    have hn1_even : Even (n + 1) := hn_odd.add_one
    have hp_odd_pred : Odd p := hp.odd_of_ne_two hp_odd
    have ht_even : Even t := (hp_odd_pred.mul hn_odd).add_one
    have h_mn_modEq : t ≡ (n + 1) [MOD (p - 1)] := by
      have h_eq : t = (n + 1) + (p - 1) * n := by
        simp only [ht_def]
        have hn_le : n ≤ p * n := Nat.le_mul_of_pos_left n (by omega)
        have hpn : (p - 1) * n = p * n - n := by rw [Nat.sub_mul, Nat.one_mul]
        omega
      unfold Nat.ModEq
      rw [h_eq, Nat.add_mul_mod_self_left]
    have ht_coprime : ¬ (p : ℕ) ∣ t := fun h => by
      have h_pn : p ∣ p * n := ⟨n, rfl⟩
      rw [(ht_def : t = p * n + 1)] at h
      exact absurd (Nat.le_of_dvd (by omega) ((Nat.dvd_add_right h_pn).mp h)) (by omega)
    have ht_p_plus : ¬ (p : ℕ) ∣ (t + 1) := fun h => by
      have h_pn : p ∣ p * n := ⟨n, rfl⟩
      have h_eq_t1 : t + 1 = p * n + 2 := by simp [ht_def]
      rw [h_eq_t1] at h
      have hp2 : p ∣ 2 := by simpa using Nat.dvd_sub h h_pn
      exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
    obtain ⟨z', hz'⟩ := bernoulli_div_sModEq_of_modEq_voronoiNoBound hp_odd
      ht_pos hn1_pos ht_even hn1_even h_pSubOne_not_dvd_nPlus h_mn_modEq
      ht_coprime hn_p_plus ht_p_plus hn_p_plus_two
    obtain ⟨bn1, hbn1⟩ :=
      bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd hn1_even h_pSubOne_not_dvd_nPlus
    have hn1_unit : IsUnit ((n + 1 : ℕ) : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr hn_p_plus
    set n1Inv : ℤ_[p] := (hn1_unit.unit⁻¹ : (ℤ_[p])ˣ).val
    have hn1Inv_mul : ((n + 1 : ℕ) : ℤ_[p]) * n1Inv = 1 := by
      change ((hn1_unit.unit * hn1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
      simp
    have hn1Inv_mul_Qp : ((n + 1 : ℕ) : ℚ_[p]) * ((n1Inv : ℤ_[p]) : ℚ_[p]) = 1 := by
      simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hn1Inv_mul
    set b : ℤ_[p] := bn1 * n1Inv with hb_def
    have hb : (((bernoulli (n + 1) : ℚ) / (n + 1 : ℕ) : ℚ) : ℚ_[p]) =
        ((b : ℤ_[p]) : ℚ_[p]) := by
      have h_div : (((bernoulli (n + 1) : ℚ) / (n + 1 : ℕ) : ℚ) : ℚ_[p]) =
          ((bernoulli (n + 1) : ℚ) : ℚ_[p]) / ((n + 1 : ℕ) : ℚ_[p]) := by
        push_cast
        rfl
      rw [h_div, hbn1, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hn1Inv_mul_Qp]
      simp only [hb_def, PadicInt.coe_mul]
    refine ⟨(n : ℤ_[p]) * b + (t : ℤ_[p]) * z', ?_⟩
    rw [hb] at hz'
    have h_BtOverT : (((bernoulli t : ℚ) / t : ℚ) : ℚ_[p]) =
        (b : ℚ_[p]) + (p : ℚ_[p]) * (z' : ℚ_[p]) := by
      linear_combination hz'
    have h_Bt : ((bernoulli t : ℚ) : ℚ_[p]) = (t : ℚ_[p]) *
        (((bernoulli t : ℚ) / t : ℚ) : ℚ_[p]) := by
      have htQ_ne : ((t : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr ht_pos.ne'
      push_cast
      field_simp [htQ_ne]
    rw [h_Bt, h_BtOverT]
    have hb' : (((bernoulli (n + 1) : ℚ) / (↑n + 1) : ℚ) : ℚ_[p]) =
        (b : ℚ_[p]) := by
      rw [show ((((bernoulli (n + 1) : ℚ) / (↑n + 1) : ℚ)) : ℚ_[p]) =
          (((bernoulli (n + 1) : ℚ) / ↑(n + 1) : ℚ) : ℚ_[p]) from by
            push_cast
            ring_nf, hb]
    rw [hb']
    have ht_sub : (t : ℚ_[p]) = (p : ℚ_[p]) * (n : ℚ_[p]) + 1 := by
      simp only [ht_def]
      push_cast
      ring
    push_cast
    rw [ht_sub]
    ring
  obtain ⟨z₂, hz₂⟩ := h_ingr3
  refine ⟨z₁ + z₂, ?_⟩
  calc
    BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
        (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p])
        = (BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
            ((bernoulli t : ℚ) : ℚ_[p])) +
          (((bernoulli t : ℚ) : ℚ_[p]) -
            (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p])) := by ring
    _ = (p : ℚ_[p]) * ((z₁ : ℚ_[p]) + (z₂ : ℚ_[p])) := by
      rw [show BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          ((bernoulli t : ℚ) : ℚ_[p]) =
          (p : ℚ_[p]) * (z₁ : ℚ_[p]) from by simpa [ht_def] using hz₁, hz₂]
      ring
    _ = (p : ℚ_[p]) * ((z₁ + z₂ : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

end BernoulliRegular
