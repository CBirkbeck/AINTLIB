module

public import BernoulliRegular.KummerCongruence.VonStaudtClausen

/-!
# Kummer congruences — Voronoi's congruence (Cohen Prop 9.5.20)

Voronoi's elementary congruence for generalized Bernoulli numbers:

  `(a^k − 1) · B_k ≡ k · a^{k−1} · ∑_{j=0}^{p−1} j^{k−1} · ⌊ja/p⌋ (mod p)`

for `a` coprime to `p`, `k ≥ 2` even with `(p−1) ∤ k` and `p ∤ (k+1)`.

This module exposes the main theorem `voronoi_congruence_mod_p`, built
from three private helpers: the polynomial linear approximation, the
multiplicative permutation of residues, and the per-term binomial mod `p²`
bound. See the umbrella `BernoulliRegular.KummerCongruence` for how this
combines with Step 2 to prove T011 (Kummer's congruence).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

/-! ### Step 3 — Voronoi's congruence and T011 (Kummer's congruence)

**Voronoi's congruence** (Cohen Prop 9.5.20): for `a, p` with `gcd(a, p) = 1`
and `k ≥ 1` with `(p-1) ∤ k`:
  `(a^k - 1) · B_k ≡ k · a^{k-1} · ∑_{j=1}^{p-1} j^{k-1} · ⌊ja/p⌋ (mod p)`
as elements of `ℤ_[p]` (where `B_k` is `p`-integral by vSC generic).

**Proof**: permutation argument `{ja mod p : j ∈ [0, p-1]} = [0, p-1]`
combined with the binomial expansion
`(ja mod p)^k ≡ (ja)^k - k·(ja)^{k-1}·p·⌊ja/p⌋ (mod p²)`,
summed over `j`. After invoking Faulhaber to express `∑ j^k` in terms of
`B_k · p + p² · (integer)`, the mod-`p` form follows by canceling common
factors. See Cohen §9.5.4 or Washington §5.4.

**T011 (Kummer's congruence)** follows from Voronoi: for `m ≡ n (mod p-1)`,
a primitive root `a` gives `a^m ≡ a^n (mod p)`, `S_m ≡ S_n (mod p)`, so
the Voronoi RHSs for `m` and `n` are congruent mod `p`. Dividing by
`m · n` (p-units when p ∤ m·n) gives `B_m/m ≡ B_n/n (mod p)`.
-/

/-- **Voronoi polynomial identity** (helper): in any commutative ring `R`,
for `k ≥ 1` and any `x y : R`,
  `(x - p·y)^k = x^k - k · x^{k-1} · p · y + p² · z`
for some explicit `z : R`. The `z` is the tail of the binomial expansion
(terms with `i ≥ 2`), each of which carries a factor of `p^i ≥ p²`. -/
lemma voronoi_sub_pow_linear_approx {R : Type*} [CommRing R]
    (p : R) {k : ℕ} (hk : 1 ≤ k) (x y : R) :
    ∃ z : R,
      (x - p * y) ^ k = x ^ k - (k : R) * x ^ (k - 1) * p * y + p ^ 2 * z := by
  -- Induction on k. Base case k=1 trivial; inductive step multiplies by (x - p·y).
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · -- k = 1.
      subst hn; refine ⟨0, ?_⟩; push_cast; ring
    · -- k = n + 1 with n ≥ 1.
      have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      obtain ⟨z, hz⟩ := ih hn_pos
      -- Witness: z·x + n·x^(n-1)·y² - p·y·z.
      refine ⟨z * x + (n : R) * x ^ (n - 1) * y * y - p * y * z, ?_⟩
      have h_pow_shift : x ^ (n - 1) * x = x ^ n := by
        rw [← pow_succ]; congr 1; omega
      have h_lhs : (x - p * y) ^ (n + 1) =
          (x ^ n - (n : R) * x ^ (n - 1) * p * y + p ^ 2 * z) * (x - p * y) := by
        rw [pow_succ, hz]
      rw [h_lhs, show (n + 1 - 1 : ℕ) = n from by omega, pow_succ x n,
        show ((n + 1 : ℕ) : R) = (n : R) + 1 from by push_cast; ring]
      linear_combination -((n : R) * p * y) * h_pow_shift

/-- **Voronoi permutation** (helper): if `a` is coprime to `p` (odd prime),
then multiplication by `a` permutes residues mod `p`. Hence for any function
`f : ℕ → R` (where `R` is an additive commutative monoid),
  `∑_{j < p} f((j * a) % p) = ∑_{j < p} f(j)`.

Proof via `Finset.sum_nbij'` with bijection `j ↦ (j * a) % p` and inverse
`j ↦ (j * b) % p` where `b = (a : ZMod p)⁻¹.val` is the modular inverse. -/
lemma voronoi_permutation
    {p : ℕ} [hp : Fact p.Prime] {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ j ∈ Finset.range p, f ((j * a) % p) = ∑ j ∈ Finset.range p, f j := by
  have hp : Nat.Prime p := hp.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  -- Modular inverse of a: use unitOfCoprime.
  have ha_coprime_p : Nat.Coprime a p :=
    Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr ha_coprime)
  set b : ℕ := ((a : ZMod p)⁻¹).val with hb_def
  -- Key: (a * b) ≡ 1 (mod p) as elements of ZMod p.
  have ha_unit : IsUnit ((a : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ha_coprime_p
  have hab : ((a : ZMod p) * (a : ZMod p)⁻¹) = 1 :=
    ZMod.mul_inv_of_unit _ ha_unit
  have hb_zmod : ((b : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := by
    rw [hb_def, ZMod.natCast_val, ZMod.cast_id]
  -- Forward bijection: i ↦ (i * a) % p. Inverse: j ↦ (j * b) % p.
  refine Finset.sum_nbij' (fun i => (i * a) % p) (fun j => (j * b) % p) ?_ ?_ ?_ ?_ ?_
  · intros i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ hp.pos
  · intros j _; simp only [Finset.mem_range]; exact Nat.mod_lt _ hp.pos
  · intros i hi
    simp only [Finset.mem_range] at hi
    rw [show ((i * a) % p * b) % p = (i * a * b) % p by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]]
    have h_zmod : ((i * a * b : ℕ) : ZMod p) = (i : ZMod p) := by
      push_cast; rw [hb_zmod]
      rw [show ((i : ZMod p) * (a : ZMod p) * (a : ZMod p)⁻¹) =
        (i : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) from by ring, hab, mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod, Nat.mod_eq_of_lt hi]
  · intros j hj
    simp only [Finset.mem_range] at hj
    rw [show ((j * b) % p * a) % p = (j * b * a) % p by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]]
    have h_zmod : ((j * b * a : ℕ) : ZMod p) = (j : ZMod p) := by
      push_cast; rw [hb_zmod]
      rw [show ((j : ZMod p) * (a : ZMod p)⁻¹ * (a : ZMod p)) =
        (j : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) from by ring, hab, mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod, Nat.mod_eq_of_lt hj]
  · intros i _; dsimp only

/-- **Voronoi sum identity mod p²** (helper): in `ℤ_[p]`, for `k ≥ 1`,
`a` coprime to `p`,
  `(a^k - 1) · ∑_{j<p} j^k - k · a^{k-1} · p · ∑_{j<p} j^{k-1} · ⌊ja/p⌋ ∈ p²·ℤ_p`.

This is obtained by summing the binomial identity
`((j·a) mod p)^k = (j·a - p·⌊ja/p⌋)^k ≡ (j·a)^k - k·(j·a)^{k-1}·p·⌊ja/p⌋ (mod p²)`
and using that `j ↦ (j·a) mod p` is a permutation. -/
lemma voronoi_sum_mod_p_sq
    {p : ℕ} [hp : Fact p.Prime]
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_pos : 0 < k) :
    ∃ W : ℤ_[p],
      (((a : ℤ_[p]) ^ k - 1) * ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) -
          (k : ℤ_[p]) * ((a : ℤ_[p]) ^ (k - 1)) * (p : ℤ_[p]) *
            ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℤ_[p])) =
        (p : ℤ_[p]) ^ 2 * W := by
  -- Per-term bound from voronoi_sub_pow_linear_approx.
  -- For each j < p: define r_j := (j*a) % p, q_j := (j*a) / p, so j*a = p*q_j + r_j
  -- in ℕ, hence (r_j : ℤ_p) = (j*a : ℤ_p) - p · q_j.
  -- Then r_j^k = (j*a - p*q_j)^k = (j*a)^k - k · (j*a)^(k-1) · p · q_j + p² · z_j.
  -- Summing, using permutation, gives the identity.
  -- Choose per-term z_j: a function of j.
  have hp_prime : Nat.Prime p := hp.out
  -- Helper: `(j * a : ℤ_[p]) = p · q_j + r_j` where r_j = (j*a) % p, q_j = (j*a) / p.
  have h_div_mod : ∀ j : ℕ,
      ((j * a : ℕ) : ℤ_[p]) = ((j * a / p : ℕ) : ℤ_[p]) * (p : ℤ_[p]) +
        ((((j * a) % p : ℕ)) : ℤ_[p]) := fun j => by
    rw [show ((j * a : ℕ) : ℤ_[p]) = (((j * a / p) * p + (j * a) % p : ℕ) : ℤ_[p]) from by
      rw [← (Nat.div_add_mod' _ _).symm]]
    push_cast; ring
  -- Per-j witness: apply voronoi_sub_pow_linear_approx to
  -- x = (j*a : ℤ_p), y = (j*a/p : ℤ_p), p = (p : ℤ_p).
  choose wj hwj using (fun (j : ℕ) (_hj : j ∈ Finset.range p) =>
    voronoi_sub_pow_linear_approx (R := ℤ_[p])
      (p := (p : ℤ_[p])) (k := k) hk_pos ((j * a : ℕ) : ℤ_[p])
      (((j * a / p : ℕ)) : ℤ_[p]))
  -- Now: (r_j : ℤ_p)^k = ((j*a) - p * (j*a/p))^k = (j*a)^k - k*(j*a)^(k-1)*p*(j*a/p) + p²*wj.
  -- For this we need to show (((j*a) % p : ℕ) : ℤ_p) = (j*a : ℤ_p) - p*(j*a/p : ℤ_p).
  have h_rj_eq : ∀ j : ℕ, (((((j * a) % p : ℕ)) : ℤ_[p])) =
      ((j * a : ℕ) : ℤ_[p]) - (p : ℤ_[p]) * (((j * a / p : ℕ)) : ℤ_[p]) := fun j => by
    linear_combination -h_div_mod j
  -- Per-j binomial identity:
  have h_per_j : ∀ (j : ℕ) (hj : j ∈ Finset.range p),
      (((((j * a) % p : ℕ)) : ℤ_[p])) ^ k =
        ((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * wj j hj := fun j hj => by rw [h_rj_eq j]; exact hwj j hj
  -- Sum over j ∈ range p.
  -- Let S₁ := ∑ j^k (ℕ form → ℤ_p)
  -- Let S₁' := ∑ ((j*a) % p)^k
  -- By permutation (voronoi_permutation), S₁ = S₁' (as ℤ_p elements).
  -- ∑ (j*a)^k = a^k · ∑ j^k = a^k · S₁.
  -- ∑ (j*a)^(k-1) · (j*a/p) = a^(k-1) · ∑ j^(k-1) · (j*a/p) = a^(k-1) · S₂.
  -- ∑ (LHS of h_per_j) = S₁'
  -- ∑ (RHS of h_per_j) = a^k·S₁ - k·a^(k-1)·p·S₂ + p²·∑wj.
  -- So: S₁ = a^k·S₁ - k·a^(k-1)·p·S₂ + p²·W.
  -- Rearranging: (a^k - 1)·S₁ - k·a^(k-1)·p·S₂ = -p²·W + (0 - 0) = -p²·W.
  -- Final witness assembled below, after `w` is defined.
  -- Step A: cast the permutation from ∑ ((j*a) % p)^k to ∑ j^k as ℤ_p element.
  have h_perm : ((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ) : ℤ_[p]) =
      ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) := by
    congr 1; exact voronoi_permutation ha_coprime (fun n : ℕ => n ^ k)
  -- Step B: sum the per-j binomial identity over j ∈ range p in ℤ_p.
  -- Define a total function w : ℕ → ℤ_[p] extending wj.
  set w : ℕ → ℤ_[p] := fun j => if h : j ∈ Finset.range p then wj j h else 0 with hw_def
  have hw_eq : ∀ (j : ℕ) (hj : j ∈ Finset.range p), w j = wj j hj := fun j hj => by
    change (if h : j ∈ Finset.range p then wj j h else 0) = wj j hj; simp [hj]
  -- Final witness: -∑ w j.
  set W_sum : ℤ_[p] := ∑ j ∈ Finset.range p, w j with hW_sum
  refine ⟨-W_sum, ?_⟩
  have h_sum_binom : (((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ)) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hw_eq j hj, Nat.cast_pow]
    exact h_per_j j hj
  -- Combine Step A and Step B: the sum form using (j*a) ℤ_p terms.
  have h_sum_ℤp : ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    rw [← h_perm, h_sum_binom]
  -- Now factor: (j*a)^k = a^k · j^k, and (j*a)^(k-1) = a^(k-1) · j^(k-1).
  have h_ja_pow : ∀ j : ℕ, ((j * a : ℕ) : ℤ_[p]) ^ k =
      ((a : ℤ_[p])) ^ k * ((j : ℕ) : ℤ_[p]) ^ k := fun j => by push_cast; ring
  have h_ja_pow_sub1 : ∀ j : ℕ, ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) =
      ((a : ℤ_[p])) ^ (k - 1) * ((j : ℕ) : ℤ_[p]) ^ (k - 1) := fun j => by push_cast; ring
  -- Rewrite RHS of h_sum_ℤp term-by-term using h_ja_pow, h_ja_pow_sub1.
  have h_sum_rewrite :
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) =
      ∑ j ∈ Finset.range p,
        ((a : ℤ_[p]) ^ k * ((j : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j : ℕ) : ℤ_[p]) ^ (k - 1) * (((j * a / p : ℕ)) : ℤ_[p])) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h_ja_pow j, h_ja_pow_sub1 j]; ring
  rw [h_sum_rewrite] at h_sum_ℤp
  -- Split into three separate sums.
  have h_three :
      ∑ j ∈ Finset.range p,
        ((a : ℤ_[p]) ^ k * ((j : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j : ℕ) : ℤ_[p]) ^ (k - 1) * (((j * a / p : ℕ)) : ℤ_[p])) +
        (p : ℤ_[p]) ^ 2 * w j) =
      (a : ℤ_[p]) ^ k * (∑ j ∈ Finset.range p, ((j : ℕ) : ℤ_[p]) ^ k) -
      (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
        (∑ j ∈ Finset.range p,
          ((j : ℕ) : ℤ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℤ_[p])) +
      (p : ℤ_[p]) ^ 2 * W_sum := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1; rw [hW_sum, Finset.mul_sum]
  -- And cast the natural-number sums to ℤ_p.
  have h_cast1 : (∑ j ∈ Finset.range p, ((j : ℕ) : ℤ_[p]) ^ k) =
      ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) := by push_cast; rfl
  have h_cast2 : (∑ j ∈ Finset.range p,
        ((j : ℕ) : ℤ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℤ_[p])) =
      ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℤ_[p]) := by push_cast; rfl
  rw [h_three, h_cast1, h_cast2] at h_sum_ℤp
  -- Now h_sum_ℤp : ∑ j^k = a^k·∑ j^k - k·a^(k-1)·p·S₂ + p²·W_attach.
  -- Goal: (a^k - 1)·∑ j^k - k·a^(k-1)·p·S₂ = p²·(-W_attach).
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
theorem voronoi_congruence_mod_p
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_two : 2 ≤ k) (hk_even : Even k) (_hk_coprime : ¬ (p - 1) ∣ k)
    (h_p_not_dvd_kPlus : ¬ (p : ℕ) ∣ (k + 1))
    (h_below_k : ∀ j, j ≤ k → ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) *
            ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hk_pos : 0 < k := by omega
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- Step 1 (ℤ_p, from voronoi_sum_mod_p_sq):
  --   (a^k - 1)·S₁ - k·a^(k-1)·p·S₂ = p²·W   where
  --   S₁ := ∑ j^k (in ℤ_p),
  --   S₂ := ∑ j^(k-1)·⌊ja/p⌋ (in ℤ_p).
  obtain ⟨W, hW⟩ := voronoi_sum_mod_p_sq ha_coprime hk_pos
  -- Step 2 (ℚ_p, from sum_range_pow_sub_p_mul_bernoulli_weighted):
  --   (k+1)·(S₁ - p·B_k) = p²·W'
  obtain ⟨W', hW'⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even
    (fun j hj hj_two hj_even =>
      p_mul_bernoulli_mem_padicInt_restricted hp_odd hj_two hj_even
        (fun j' hj' => h_below_k j' (Nat.le_trans hj' hj.le)))
  -- Modular inverse of (k+1).
  have hkp1_unit : IsUnit ((k + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_kPlus
  set u : ℤ_[p] := (hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hu_def
  have hu_mul : ((k + 1 : ℕ) : ℤ_[p]) * u = 1 := by
    change ((hkp1_unit.unit * hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  have hu_mul_Qp : ((k + 1 : ℕ) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul
  -- Witness: z = W - (a^k - 1) · u · W'.
  refine ⟨W - ((a : ℤ_[p]) ^ k - 1) * u * W', ?_⟩
  -- Introduce abbreviations for the sums (cleaner working in ℚ_[p]).
  set S1 : ℚ_[p] := ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ k with hS1_def
  set S2 : ℚ_[p] :=
    ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℚ_[p]) with hS2_def
  -- hW in ℚ_[p] form (cast and reindex sums).
  have hW_Q : ((a : ℚ_[p]) ^ k - 1) * S1 -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * (p : ℚ_[p]) * S2 =
      (p : ℚ_[p]) ^ 2 * ((W : ℤ_[p]) : ℚ_[p]) := by
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hW
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, PadicInt.coe_one] at this
    rw [hS1_def, hS2_def]
    push_cast at this
    exact this
  -- From hW': divide by (k+1) to get S1 - p·B_k = u·p²·W'.
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
  -- From h_S1_sub: S1 = p·B_k + u·p²·W'. Substitute into hW_Q.
  have hS1_eq : S1 = (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) +
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    linear_combination h_S1_sub
  rw [hS1_eq] at hW_Q
  -- Align the goal's S2 form.
  have hS2_cast : ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) = S2 := by
    rw [hS2_def]; push_cast; rfl
  -- Now hW_Q: (a^k - 1)·(p·B_k + u·p²·W') - k·a^(k-1)·p·S2 = p²·W.
  -- Factor p, then divide: (a^k - 1)·B_k - k·a^(k-1)·S2 = p·(W - (a^k - 1)·u·W').
  have hX : ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * S2 =
      (p : ℚ_[p]) * (((W : ℤ_[p]) : ℚ_[p]) -
        ((a : ℚ_[p]) ^ k - 1) * ((u : ℤ_[p]) : ℚ_[p]) * ((W' : ℤ_[p]) : ℚ_[p])) :=
    mul_left_cancel₀ hpQ_ne (by linear_combination hW_Q)
  rw [hS2_cast]; push_cast; linear_combination hX


end BernoulliRegular
