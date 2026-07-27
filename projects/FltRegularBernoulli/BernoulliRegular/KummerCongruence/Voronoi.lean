module

public import BernoulliRegular.KummerCongruence.VonStaudtClausen

/-!
# Kummer congruences — Voronoi's congruence (Cohen Prop 9.5.20)

Voronoi's elementary congruence for generalized Bernoulli numbers:

  `(a^k − 1) · B_k ≡ k · a^{k−1} · ∑_{j=0}^{p−1} j^{k−1} · ⌊ja/p⌋ (mod p)`

for `a` coprime to `p`, `k ≥ 2` even with `(p−1) ∤ k` and `p ∤ (k+1)`.

This module proves `voronoi_congruence_mod_p` using a polynomial linear approximation,
permutation of residues, and a per-term binomial bound modulo `p²`. See the umbrella
`BernoulliRegular.KummerCongruence` for how it proves T011 (Kummer's congruence).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

/-- **Voronoi polynomial identity** (helper): in any commutative ring `R`,
for `k ≥ 1` and any `x y : R`,
  `(x - p·y)^k = x^k - k · x^{k-1} · p · y + p² · z`
for some explicit `z : R`. The `z` is the tail of the binomial expansion
(terms with `i ≥ 2`), each of which carries a factor of `p^i ≥ p²`. -/
lemma voronoi_sub_pow_linear_approx {R : Type*} [CommRing R]
    (p : R) {k : ℕ} (hk : 1 ≤ k) (x y : R) : ∃ z : R,
      (x - p * y) ^ k = x ^ k - (k : R) * x ^ (k - 1) * p * y + p ^ 2 * z := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      refine ⟨0, ?_⟩
      push_cast
      ring
    ·
      have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      obtain ⟨z, hz⟩ := ih hn_pos
      refine ⟨z * x + (n : R) * x ^ (n - 1) * y * y - p * y * z, ?_⟩
      have h_pow_shift : x ^ (n - 1) * x = x ^ n := by
        rw [← pow_succ]
        congr 1
        omega
      have h_lhs : (x - p * y) ^ (n + 1) =
          (x ^ n - (n : R) * x ^ (n - 1) * p * y + p ^ 2 * z) * (x - p * y) := by
        rw [pow_succ, hz]
      rw [h_lhs, show (n + 1 - 1 : ℕ) = n from by omega, pow_succ x n,
        show ((n + 1 : ℕ) : R) = (n : R) + 1 from by norm_cast]
      linear_combination -((n : R) * p * y) * h_pow_shift

/-- **Voronoi permutation** (helper): if `a` is coprime to `p` (odd prime),
then multiplication by `a` permutes residues mod `p`. Hence for any function
`f : ℕ → R` (where `R` is an additive commutative monoid),
  `∑_{j < p} f((j * a) % p) = ∑_{j < p} f(j)`.

Proof via `Finset.sum_nbij'` with bijection `j ↦ (j * a) % p` and inverse
`j ↦ (j * b) % p` where `b = (a : ZMod p)⁻¹.val` is the modular inverse. -/
lemma voronoi_permutation {p : ℕ} [hp : Fact p.Prime]
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ j ∈ Finset.range p, f ((j * a) % p) = ∑ j ∈ Finset.range p, f j := by
  have hp_prime : Nat.Prime p := hp.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  set b : ℕ := ((a : ZMod p)⁻¹).val with hb_def
  have ha_unit : IsUnit ((a : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.symm ((hp_prime.coprime_iff_not_dvd).mpr ha_coprime)
  have hab : ((a : ZMod p) * (a : ZMod p)⁻¹) = 1 :=
    ZMod.mul_inv_of_unit _ ha_unit
  have hb_zmod : ((b : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := by
    rw [hb_def, ZMod.natCast_val, ZMod.cast_id]
  refine Finset.sum_nbij' (fun i ↦ (i * a) % p) (fun j ↦ (j * b) % p) ?_ ?_ ?_ ?_ ?_
  · intros i _
    simp only [Finset.mem_range]
    exact Nat.mod_lt _ hp_prime.pos
  · intros j _
    simp only [Finset.mem_range]
    exact Nat.mod_lt _ hp_prime.pos
  · intros i hi
    simp only [Finset.mem_range] at hi
    rw [show ((i * a) % p * b) % p = (i * a * b) % p by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]]
    have h_zmod : ((i * a * b : ℕ) : ZMod p) = (i : ZMod p) := by
      push_cast
      rw [hb_zmod]
      rw [show ((i : ZMod p) * (a : ZMod p) * (a : ZMod p)⁻¹) =
        (i : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) from by ring, hab, mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod, Nat.mod_eq_of_lt hi]
  · intros j hj
    simp only [Finset.mem_range] at hj
    rw [show ((j * b) % p * a) % p = (j * b * a) % p by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]]
    have h_zmod : ((j * b * a : ℕ) : ZMod p) = (j : ZMod p) := by
      push_cast
      rw [hb_zmod]
      rw [show ((j : ZMod p) * (a : ZMod p)⁻¹ * (a : ZMod p)) =
        (j : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) from by ring, hab, mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod, Nat.mod_eq_of_lt hj]
  · intros
    rfl

/-- **Voronoi div/mod cast** (helper): in `ℤ_[p]`, every natural number `n`
splits along division by `p` as
  `(n : ℤ_[p]) = ⌊n/p⌋ · p + (n mod p)`.
This is the `ℤ_[p]` image of `Nat.div_add_mod`. -/
lemma voronoi_natCast_div_add_mod {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ((n : ℕ) : ℤ_[p]) =
      ((n / p : ℕ) : ℤ_[p]) * (p : ℤ_[p]) + ((n % p : ℕ) : ℤ_[p]) := by
  exact_mod_cast (Nat.div_add_mod' n p).symm

/-- **Voronoi per-term approximation** (helper): in `ℤ_[p]`, for `k ≥ 1` and any
`j : ℕ`, the `k`-th power of the residue `(j * a) mod p` agrees with `(j·a)^k`
up to a first-order `p`-correction and a `p²` remainder:
  `((j·a) mod p)^k = (j·a)^k - k·(j·a)^{k-1}·p·⌊ja/p⌋ + p²·w`
for some `w : ℤ_[p]`. Obtained from the binomial expansion
`voronoi_sub_pow_linear_approx` applied to `x = j·a`, `y = ⌊ja/p⌋`, after
rewriting `(j·a) mod p = j·a - p·⌊ja/p⌋` via `voronoi_natCast_div_add_mod`. -/
lemma voronoi_residue_pow_approx {p : ℕ} [Fact p.Prime] {a k : ℕ}
    (hk_pos : 0 < k) (j : ℕ) : ∃ w : ℤ_[p],
      (((j * a) % p : ℕ) : ℤ_[p]) ^ k =
        ((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            ((j * a / p : ℕ) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w := by
  obtain ⟨z, hz⟩ := voronoi_sub_pow_linear_approx (R := ℤ_[p])
    (p := (p : ℤ_[p])) (k := k) hk_pos ((j * a : ℕ) : ℤ_[p])
    ((j * a / p : ℕ) : ℤ_[p])
  refine ⟨z, ?_⟩
  have h_rj : (((j * a) % p : ℕ) : ℤ_[p]) =
      ((j * a : ℕ) : ℤ_[p]) - (p : ℤ_[p]) * ((j * a / p : ℕ) : ℤ_[p]) := by
    linear_combination -voronoi_natCast_div_add_mod (p := p) (j * a)
  exact h_rj ▸ hz

/-- **Voronoi sum identity mod p²** (helper): in `ℤ_[p]`, for `k ≥ 1`,
`a` coprime to `p`,
  `(a^k - 1) · ∑_{j<p} j^k - k · a^{k-1} · p · ∑_{j<p} j^{k-1} · ⌊ja/p⌋`
is in `p²·ℤ_p`.

This is obtained by summing the binomial identity
`((j·a) mod p)^k = (j·a - p·⌊ja/p⌋)^k ≡
  (j·a)^k - k·(j·a)^{k-1}·p·⌊ja/p⌋ (mod p²)`
and using that `j ↦ (j·a) mod p` is a permutation. -/
lemma voronoi_sum_mod_p_sq {p : ℕ} [hp : Fact p.Prime]
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_pos : 0 < k) :
    ∃ W : ℤ_[p],
      (((a : ℤ_[p]) ^ k - 1) * ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) -
          (k : ℤ_[p]) * ((a : ℤ_[p]) ^ (k - 1)) * (p : ℤ_[p]) *
            ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℤ_[p])) =
        (p : ℤ_[p]) ^ 2 * W := by
  choose w hw using fun j : ℕ ↦
    voronoi_residue_pow_approx (p := p) (a := a) (k := k) hk_pos j
  have h_perm : ((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ) : ℤ_[p]) =
      ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) := by
    congr 1
    exact voronoi_permutation ha_coprime (fun n : ℕ ↦ n ^ k)
  refine ⟨-(∑ j ∈ Finset.range p, w j), ?_⟩
  have h_sum_binom : (((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ)) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            ((j * a / p : ℕ) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Nat.cast_pow]
    exact hw j
  have h_sum_ℤp : ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            ((j * a / p : ℕ) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    rw [← h_perm, h_sum_binom]
  push_cast at h_sum_ℤp ⊢
  simp_rw [mul_pow] at h_sum_ℤp
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h_sum_ℤp
  have h_power_sum :
      (∑ j ∈ Finset.range p, (j : ℤ_[p]) ^ k * (a : ℤ_[p]) ^ k) =
        (a : ℤ_[p]) ^ k * ∑ j ∈ Finset.range p, (j : ℤ_[p]) ^ k := by
    rw [← Finset.sum_mul]
    ring
  have h_weighted_sum :
      (∑ j ∈ Finset.range p,
        (k : ℤ_[p]) * ((j : ℤ_[p]) ^ (k - 1) * (a : ℤ_[p]) ^ (k - 1)) *
          (p : ℤ_[p]) * (j * a / p : ℕ)) =
        (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
          ∑ j ∈ Finset.range p, (j : ℤ_[p]) ^ (k - 1) * (j * a / p : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h_remainder_sum :
      (∑ j ∈ Finset.range p, (p : ℤ_[p]) ^ 2 * w j) =
        (p : ℤ_[p]) ^ 2 * ∑ j ∈ Finset.range p, w j := by
    rw [Finset.mul_sum]
  rw [h_power_sum, h_weighted_sum, h_remainder_sum] at h_sum_ℤp
  linear_combination -h_sum_ℤp

/-- **Voronoi's congruence** (Cohen Prop 9.5.20, specialized to `n = p`).

For `a, p` coprime, `k ≥ 2` even with `(p-1) ∤ k` and `p ∤ (k+1)`:
  `(a^k - 1) · B_k ≡ k · a^{k-1} · ∑_{j=0}^{p-1} j^{k-1} · ⌊ja/p⌋ (mod p)`
in `ℤ_[p]`.

The sum uses `Finset.range p` (including `j = 0`, whose term is `0`
when `k ≥ 2`). Note `B_k ∈ ℤ_[p]` for `(p-1) ∤ k` (vSC generic), and
`a^k - 1`, `k`, `a^{k-1}` are all in `ℤ_[p]`.

**Proof outline:**

1. *Permutation lemma:* `j ↦ (j·a) mod p` is a bijection on `[0, p)`,
   hence `∑_{j<p} ((j·a) mod p)^k = ∑_{j<p} j^k`.

2. *Per-term binomial mod p²:* for each `j < p`, write
   `j·a = p·q + r` with `r = (j·a) mod p`, `q = (j·a) / p`. Then
   `r^k = (j·a - p·q)^k ≡ (j·a)^k - k · (j·a)^{k-1} · p · q (mod p²)`.

3. *Sum in ℤ (via ℤ_p):* Summing step 2 over `j < p` and using step 1
   for the LHS gives, in `ℤ_p`:
   `(a^k - 1) · ∑_j j^k - k · a^{k-1} · p · ∑_j j^{k-1} · ⌊ja/p⌋ ∈ p²·ℤ_p`.

4. *Faulhaber substitution:* multiplying by `(k+1)` and using
   `sum_range_pow_sub_p_mul_bernoulli_weighted`, substitute
   `(k+1) · ∑_j j^k = (k+1)·p·B_k + p²·W` to get
   `p · (k+1) · ((a^k-1)·B_k - k·a^{k-1}·∑_j j^{k-1}·⌊ja/p⌋) ∈ p²·ℤ_p`.
   Dividing by `p · (k+1)` (both `p`-units: `(k+1)` is by hypothesis,
   `p` we divide via mul_left_cancel₀) gives the claim.
-/
theorem voronoi_congruence_mod_p {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_two : 2 ≤ k) (hk_even : Even k) (_hk_coprime : ¬ (p - 1) ∣ k)
    (h_p_not_dvd_kPlus : ¬ (p : ℕ) ∣ (k + 1))
    (h_below_k : ∀ j, j ≤ k → ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) *
            ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp_prime : Nat.Prime p := hp.out
  have hk_pos : 0 < k := by omega
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
  obtain ⟨W, hW⟩ := voronoi_sum_mod_p_sq ha_coprime hk_pos
  obtain ⟨W', hW'⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even
    (fun j hj hj_two hj_even ↦
      p_mul_bernoulli_mem_padicInt_restricted hp_odd hj_two hj_even
        (fun j' hj' ↦ h_below_k j' (Nat.le_trans hj' hj.le)))
  have hkp1_unit : IsUnit ((k + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp_prime.coprime_iff_not_dvd.mpr h_p_not_dvd_kPlus
  set u : ℤ_[p] := (hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hu_mul : ((k + 1 : ℕ) : ℤ_[p]) * u = 1 := by
    change ((hkp1_unit.unit * hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    exact Units.mul_inv hkp1_unit.unit
  have hu_mul_Qp : ((k + 1 : ℕ) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hu_mul
  refine ⟨W - ((a : ℤ_[p]) ^ k - 1) * u * W', ?_⟩
  set powerSum : ℚ_[p] := ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ k with hpowerSum_def
  set weightedSum : ℚ_[p] :=
    ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℚ_[p])
      with hweightedSum_def
  have hWQ : ((a : ℚ_[p]) ^ k - 1) * powerSum -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * (p : ℚ_[p]) * weightedSum =
      (p : ℚ_[p]) ^ 2 * ((W : ℤ_[p]) : ℚ_[p]) := by
    have := congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hW
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, PadicInt.coe_one] at this
    rw [hpowerSum_def, hweightedSum_def]
    push_cast at this
    exact this
  have hk_add_one_ne : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpowerSum_sub : powerSum - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    have hcancel : ((k + 1 : ℕ) : ℚ_[p]) *
        (powerSum - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
        ((k + 1 : ℕ) : ℚ_[p]) *
        (((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p])) := by
      rw [hpowerSum_def, hW']
      linear_combination -((p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p])) * hu_mul_Qp
    exact mul_left_cancel₀ hk_add_one_ne hcancel
  have hpowerSum_eq : powerSum = (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) +
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    linear_combination hpowerSum_sub
  rw [hpowerSum_eq] at hWQ
  have hweightedSum_cast :
      ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) =
        weightedSum := by
    rw [hweightedSum_def]
    push_cast
    rfl
  have hresult : ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * weightedSum =
      (p : ℚ_[p]) * (((W : ℤ_[p]) : ℚ_[p]) -
        ((a : ℚ_[p]) ^ k - 1) * ((u : ℤ_[p]) : ℚ_[p]) * ((W' : ℤ_[p]) : ℚ_[p])) :=
    mul_left_cancel₀ hpQ_ne (by linear_combination hWQ)
  rw [hweightedSum_cast]
  push_cast
  linear_combination hresult

end BernoulliRegular
