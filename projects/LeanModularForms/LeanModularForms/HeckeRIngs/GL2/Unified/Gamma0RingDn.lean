/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0

/-!
# Ring-side Hecke elements `D_n` in `𝕋(Γ₀(N))`

This file is the **ring layer** of the ring-first Hecke-operator architecture: it defines,
purely inside the Hecke ring `𝕋 (Gamma0_pair N) ℤ` (commutative by Shimura Prop 3.8 for
`Γ₀(N)`, via the Atkin–Lehner anti-involution), the elements whose images under the
character-space ring homomorphisms *are* the classical Hecke operators:

* `heckeRingDp p`     — the prime class `Γ₀(N)·diag(1,p)·Γ₀(N)` (defined for **all** `p > 0`,
  including the bad primes `p ∣ N`);
* `heckeRingSpp p`    — the scalar class `Γ₀(N)·diag(p,p)·Γ₀(N)` for `p ∤ N`, and `0` for
  `p ∣ N` (the scalar matrix `diag(p,p)` does not lie in `Δ₀(N)` when `p ∣ N`; the junk
  value `0` mirrors the vanishing of the diamond operator `⟨p⟩` there);
* `heckeRingDppow p r` — the prime-power element defined by the Diamond–Shurman
  recurrence `D_{p^{r+2}} = D_p·D_{p^{r+1}} − (p·S_p)·D_{p^r}`, which for `p ∣ N`
  degenerates (since `S_p = 0`) to `D_{p^r} = D_p^r`;
* `heckeRingDn n`    — the composite element, assembled multiplicatively over the prime
  factorisation of `n` by `minFac`-peeling, with **genuine** bad-prime factors.

The structural identities — commutativity (free), the per-prime product formula
`D_{p^r}·D_{p^s} = ∑_{i ≤ min(r,s)} (p·S_p)^i · D_{p^{r+s−2i}}`, and coprime
multiplicativity `D_m·D_n = D_{mn}` — are **pure commutative algebra**: they are proven
below for an arbitrary commutative ring (the `Formal*` sections) and then instantiated at
`𝕋 (Gamma0_pair N) ℤ`.  No operators, coset combinatorics, or analytic input appear.
The operator-level counterparts (`heckeT_n_comm`, `heckeT_n_mul_coprime`, …) are then
*transported* along `heckeRingHomCharSpace` and glued over the character direct sum,
replacing their former self-contained induction cascades.

## Main definitions

* `HeckeRing.GL2.Unified.heckeRingDp`
* `HeckeRing.GL2.Unified.heckeRingSpp`
* `HeckeRing.GL2.Unified.heckeRingDppow`
* `HeckeRing.GL2.Unified.heckeRingDn`
* `HeckeRing.GL2.Unified.heckeRingSn` — the composite scalar class `S_d` (multiplicative
  in `d`; vanishes unless `d` is coprime to `N`), the ring-side avatar of `d^{k-2}·⟨d⟩`.

## Main results

* `heckeRingDppow_mul`  — the per-prime product formula (Chebyshev-style algebra).
* `heckeRingDn_mul_coprime` — `D_{mn} = D_m · D_n` for coprime `m, n`.

## Implementation notes

The formal commutative algebra is stated generically over `[CommRing R]` and then
instantiated at `𝕋 (Gamma0_pair N) ℤ`, which carries both a global `Ring` instance and a
(non-instance) `CommRing` structure `instCommRing_Gamma0`; proving the algebra generically
avoids ever mixing the two elaboration paths. The pure-`ℕ` divisor-combinatorics helpers are
reproduced from the operator layer `HeckeT_n.lean` because this file does not import it.
-/

namespace HeckeRing.GL2.Unified

open HeckeRing HeckeRing.GLn

section FormalChebyshev

variable {R : Type*} [CommRing R]

private theorem formal_D_mul_d (D S : R) (d : ℕ → R)
    (hrec : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) (m : ℕ) (hm : 0 < m) :
    D * d m = d (m + 1) + S * d (m - 1) := by
  grind

private theorem formal_ppow_mul (D S : R) (d : ℕ → R) (h0 : d 0 = 1) (h1 : d 1 = D)
    (hrec : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) :
    ∀ r s : ℕ, r ≤ s →
      d r * d s = ∑ i ∈ Finset.range (r + 1), S ^ i * d (r + s - 2 * i) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s hrs
    match r, ih with
    | 0, _ => simp [h0]
    | 1, _ =>
      rw [h1, formal_D_mul_d D S d hrec s (by omega),
        Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_mul, pow_one,
        show 1 + s - 2 * 0 = s + 1 by omega, show 1 + s - 2 * 1 = s - 1 by omega]
    | (r + 2), ih =>
      have key : ∀ i ∈ Finset.range (r + 2),
          D * (S ^ i * d (r + 1 + s - 2 * i)) =
            S ^ i * d (r + 2 + s - 2 * i) + S ^ (i + 1) * d (r + s - 2 * i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have h := formal_D_mul_d D S d hrec (r + 1 + s - 2 * i) (by omega)
        rw [show r + 1 + s - 2 * i + 1 = r + 2 + s - 2 * i by omega,
          show r + 1 + s - 2 * i - 1 = r + s - 2 * i by omega] at h
        linear_combination S ^ i * h
      have hL : d (r + 2) * d s = D * (d (r + 1) * d s) - S * (d r * d s) := by
        linear_combination d s * hrec r
      rw [hL, ih (r + 1) (by omega) s (by omega), ih r (by omega) s (by omega),
        Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib]
      have hshift : S * ∑ i ∈ Finset.range (r + 1), S ^ i * d (r + s - 2 * i) =
          ∑ i ∈ Finset.range (r + 1), S ^ (i + 1) * d (r + s - 2 * i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hshift, Finset.sum_range_succ (fun i ↦ S ^ (i + 1) * d (r + s - 2 * i)) (r + 1),
        Finset.sum_range_succ (fun i ↦ S ^ i * d (r + 2 + s - 2 * i)) (r + 2),
        show r + 2 + s - 2 * (r + 2) = r + s - 2 * (r + 1) by omega]
      ring

end FormalChebyshev

section FormalPeel

variable {R : Type*} [Monoid R]

/-- The `minFac`-peeling product: `peelProd f n = f p v * peelProd f (n / p^v)` where
`p = minFac n` and `v = p`-adic valuation of `n`, with `peelProd f 0 = peelProd f 1 = 1`. -/
noncomputable def peelProd (f : ℕ → ℕ → R) (n : ℕ) : R :=
  if _h : n ≤ 1 then 1
  else
    let p := n.minFac
    let v := n.factorization p
    f p v * peelProd f (n / p ^ v)
termination_by n
decreasing_by
  have hp := Nat.minFac_prime (by lia : n ≠ 1)
  exact Nat.div_lt_self (by lia) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by lia) (Nat.minFac_dvd n)).ne' hp.one_lt)

@[simp] theorem peelProd_zero (f : ℕ → ℕ → R) : peelProd f 0 = 1 := by
  rw [peelProd]; simp

@[simp] theorem peelProd_one (f : ℕ → ℕ → R) : peelProd f 1 = 1 := by
  rw [peelProd]; simp

/-- Unfolding equation for `peelProd` at `1 < n`: peels off the leading `minFac` block. -/
theorem peelProd_peel (f : ℕ → ℕ → R) (n : ℕ) (hn : 1 < n) : peelProd f n = f n.minFac
    (n.factorization n.minFac) * peelProd f (n / n.minFac ^ n.factorization n.minFac) := by
  rw [peelProd, dif_neg (by omega : ¬ n ≤ 1)]

/-- `peelProd` over a prime power is a single block. -/
theorem peelProd_ppow (f : ℕ → ℕ → R) {p : ℕ} (hp : Nat.Prime p) (v : ℕ)
    (hv : 0 < v) : peelProd f (p ^ v) = f p v := by
  rw [peelProd_peel f _ (Nat.one_lt_pow hv.ne' hp.one_lt), hp.pow_minFac hv.ne',
    Nat.factorization_pow_self hp, Nat.div_self (pow_pos hp.pos v), peelProd_one, mul_one]

end FormalPeel

section FormalPeelComm

variable {R : Type*} [CommMonoid R]

private theorem peelProd_eq_factorization_prod (f : ℕ → ℕ → R) :
    ∀ {n : ℕ}, n ≠ 0 → peelProd f n = n.factorization.prod fun p k ↦ f p k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0
    rcases (Nat.one_le_iff_ne_zero.mpr hn0).lt_or_eq with h1 | h1
    · have hp : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
      have hmem : n.minFac ∈ n.factorization.support := by
        simp [Nat.support_factorization, Nat.mem_primeFactors, hp, n.minFac_dvd, hn0]
      have hlt : n / n.minFac ^ n.factorization n.minFac < n :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow
          (hp.factorization_pos_of_dvd hn0 n.minFac_dvd).ne' hp.one_lt)
      rw [peelProd_peel f n h1, ih _ hlt (Nat.ordCompl_pos _ hn0).ne',
        Nat.factorization_ordCompl, Finsupp.mul_prod_erase _ _ _ hmem]
    · simp [← h1]

/-- **`peelProd` is multiplicative on coprime arguments**: for coprime `m, n` and any block
map `f`, `peelProd f (m * n) = peelProd f m * peelProd f n`. -/
theorem peelProd_mul_coprime (f : ℕ → ℕ → R) (m n : ℕ) (hcop : Nat.Coprime m n) :
    peelProd f (m * n) = peelProd f m * peelProd f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hcop
    simp [hcop]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hcop
    simp [hcop]
  rw [peelProd_eq_factorization_prod f (Nat.mul_ne_zero hm hn),
    peelProd_eq_factorization_prod f hm, peelProd_eq_factorization_prod f hn,
    Nat.factorization_mul_of_coprime hcop,
    Finsupp.prod_add_index_of_disjoint hcop.disjoint_primeFactors]

end FormalPeelComm

section FormalTable

variable {R : Type*} [CommRing R]

private lemma factorization_coprime_mul_pow_self {p g c : ℕ} (hp : Nat.Prime p) (hpg : ¬p ∣ g) :
    (g * p ^ c).factorization p = c := by
  simp [Nat.factorization_mul_apply_of_coprime (hp.coprime_pow_of_not_dvd hpg),
    Nat.factorization_eq_zero_of_not_dvd hpg, Nat.Prime.factorization_pow hp]

private lemma factorization_pow_mul_self {p j d : ℕ} (hp : Nat.Prime p) (hd_pos : 0 < d)
    (hpd : ¬p ∣ d) : (p ^ j * d).factorization p = j := by
  simp [Nat.factorization_mul (pow_pos hp.pos j).ne' hd_pos.ne',
    hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hpd]

private lemma pow_mul_mem_gcd_divisors {p m n g' c j d' : ℕ} (hgcd_eq : m.gcd n = g' * p ^ c)
    (hg'_pos : 0 < g') (hpc_pos : 0 < p ^ c) (hd' : d' ∈ g'.divisors) (hj_le : j ≤ c) :
    p ^ j * d' ∈ (m.gcd n).divisors := by
  rw [hgcd_eq, Nat.mem_divisors]
  exact ⟨mul_comm (p ^ j) d' ▸
    Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd') (pow_dvd_pow p hj_le),
    (Nat.mul_pos hg'_pos hpc_pos).ne'⟩

private lemma ordCompl_mem_divisors_of_dvd_mul_pow {p g' c d : ℕ} (hp : Nat.Prime p)
    (hg'_pos : 0 < g') (hp_not_dvd_g' : ¬p ∣ g')
    (hd_dvd_gpc : d ∣ g' * p ^ c) :
    d / p ^ d.factorization p ∈ g'.divisors := by
  have hordCompl_gpc : g' * p ^ c / p ^ (g' * p ^ c).factorization p = g' := by
    rw [mul_comm, Nat.ordCompl_pow_mul_of_not_dvd c hp hp_not_dvd_g']
  rw [Nat.mem_divisors]
  refine ⟨?_, hg'_pos.ne'⟩
  simpa only [hordCompl_gpc] using Nat.ordCompl_dvd_ordCompl_of_dvd hd_dvd_gpc p

private lemma gcd_eq_gcd_ordCompl_mul_pow_min {p va vb m' n' m n : ℕ}
    (hp : Nat.Prime p) (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n') :
    Nat.gcd m n = Nat.gcd m' n' * p ^ min va vb := by
  have hpa_cop_m' : Nat.Coprime (p ^ va) m' := (hp.coprime_pow_of_not_dvd hp_not_dvd_m').symm
  have hpa_cop_n' : Nat.Coprime (p ^ va) n' := (hp.coprime_pow_of_not_dvd hp_not_dvd_n').symm
  have hm'_cop_pb : Nat.Coprime m' (p ^ vb) := hp.coprime_pow_of_not_dvd hp_not_dvd_m'
  have hgcd_pp : Nat.gcd (p ^ va) (p ^ vb) = p ^ min va vb := by
    grind [Nat.gcd_eq_left, Nat.gcd_eq_right, pow_dvd_pow, min_eq_left, min_eq_right]
  rw [hm_eq, hn_eq, hpa_cop_m'.mul_gcd _,
      Nat.Coprime.gcd_mul_right_cancel_right _ hpa_cop_n'.symm,
      Nat.Coprime.gcd_mul_left_cancel_right _ hm'_cop_pb.symm, hgcd_pp, mul_comm]

private lemma mn_div_pjd_eq {p va vb m' n' m n d' j : ℕ} (hp : Nat.Prime p)
    (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n')
    (hd'_dvd_m' : d' ∣ m') (hd'_dvd_n' : d' ∣ n') (_hd'_pos : 0 < d')
    (_hm'_pos : 0 < m') (_hn'_pos : 0 < n') (hj_le : j ≤ min va vb) :
    m * n / (p ^ j * d' * (p ^ j * d')) =
        p ^ (min va vb + max va vb - 2 * j) * (m' * n' / (d' * d')) ∧
      Nat.Coprime (p ^ (min va vb + max va vb - 2 * j)) (m' * n' / (d' * d')) := by
  have hdd_dvd : d' * d' ∣ m' * n' := Nat.mul_dvd_mul hd'_dvd_m' hd'_dvd_n'
  set r := va + vb - 2 * j with hr_def
  have hr_eq : min va vb + max va vb - 2 * j = r := by rw [min_add_max]
  have hmn_div_eq : m * n / (p ^ j * d' * (p ^ j * d')) =
      p ^ r * (m' * n' / (d' * d')) := by
    rw [hm_eq, hn_eq]
    have h1 : p ^ va * m' * (p ^ vb * n') = p ^ (va + vb) * (m' * n') := by
      rw [pow_add]
      ring
    have h2 : p ^ j * d' * (p ^ j * d') = p ^ (2 * j) * (d' * d') := by
      rw [two_mul, pow_add]
      ring
    rw [h1, h2, show va + vb = 2 * j + r by omega, pow_add, mul_assoc,
        Nat.mul_div_mul_left _ _ (pow_pos hp.pos (2 * j)), Nat.mul_div_assoc _ hdd_dvd]
  have hp_not_dvd_quot : ¬p ∣ (m' * n' / (d' * d')) := fun h ↦
    hp.not_dvd_mul hp_not_dvd_m' hp_not_dvd_n' (h.trans (Nat.div_dvd_of_dvd hdd_dvd))
  exact ⟨hr_eq ▸ hmn_div_eq,
    hr_eq ▸ (hp.coprime_iff_not_dvd.mpr hp_not_dvd_quot).pow_left r⟩

variable (dblk sblk : ℕ → ℕ → R)

private lemma formal_table_summand {p : ℕ} (hp : Nat.Prime p) (va vb m' n' m n j d' : ℕ)
    (hm'_pos : 0 < m') (hn'_pos : 0 < n')
    (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n')
    (hd' : d' ∈ (m'.gcd n').divisors) (hj_le : j ≤ min va vb) :
    ((p : ℤ) ^ j • (peelProd sblk (p ^ j) *
        peelProd dblk (p ^ (min va vb + max va vb - 2 * j)))) *
      ((d' : ℤ) • (peelProd sblk d' * peelProd dblk (m' * n' / (d' * d')))) =
    ((p ^ j * d' : ℕ) : ℤ) •
      (peelProd sblk (p ^ j * d') * peelProd dblk (m * n / (p ^ j * d' * (p ^ j * d')))) := by
  have hd'_dvd_g' : d' ∣ m'.gcd n' := Nat.dvd_of_mem_divisors hd'
  have hd'_dvd_m' : d' ∣ m' := hd'_dvd_g'.trans (Nat.gcd_dvd_left m' n')
  have hd'_dvd_n' : d' ∣ n' := hd'_dvd_g'.trans (Nat.gcd_dvd_right m' n')
  have hd'_pos : 0 < d' :=
    Nat.pos_of_ne_zero fun h ↦ (Nat.mem_divisors.mp hd').2
      (Nat.eq_zero_of_zero_dvd (h ▸ hd'_dvd_g'))
  have hp_not_dvd_d' : ¬p ∣ d' := fun h ↦ hp_not_dvd_m' (h.trans hd'_dvd_m')
  have hcop_S : Nat.Coprime (p ^ j) d' := (hp.coprime_iff_not_dvd.mpr hp_not_dvd_d').pow_left j
  obtain ⟨hidx, hcop_D⟩ := mn_div_pjd_eq hp hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n'
    hd'_dvd_m' hd'_dvd_n' hd'_pos hm'_pos hn'_pos hj_le
  rw [smul_mul_smul_comm, hidx, peelProd_mul_coprime dblk _ _ hcop_D,
      peelProd_mul_coprime sblk _ _ hcop_S, Nat.cast_mul, Nat.cast_pow]
  ring_nf

private lemma formal_table_div_sum {p : ℕ} (hp : Nat.Prime p) (va vb m' n' m n : ℕ)
    (hm'_pos : 0 < m') (hn'_pos : 0 < n') (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n')
    (hgcd_eq : Nat.gcd m n = Nat.gcd m' n' * p ^ min va vb) :
    (∑ j ∈ Finset.range (min va vb + 1),
        (p : ℤ) ^ j • (peelProd sblk (p ^ j) *
          peelProd dblk (p ^ (min va vb + max va vb - 2 * j)))) *
      (∑ d ∈ (Nat.gcd m' n').divisors.attach,
        (d.val : ℤ) • (peelProd sblk d.val *
          peelProd dblk (m' * n' / (d.val * d.val)))) =
    ∑ d ∈ (Nat.gcd m n).divisors.attach,
      (d.val : ℤ) • (peelProd sblk d.val *
        peelProd dblk (m * n / (d.val * d.val))) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  set c := min va vb
  set g' := m'.gcd n'
  have hg'_pos : 0 < g' :=
    Nat.pos_of_ne_zero fun h ↦ absurd (Nat.eq_zero_of_gcd_eq_zero_left h) hm'_pos.ne'
  have hpc_pos : 0 < p ^ c := pow_pos hp.pos c
  have hp_not_dvd_g' : ¬p ∣ g' := fun h ↦ hp_not_dvd_m' (h.trans (Nat.gcd_dvd_left m' n'))
  refine Finset.sum_bij'
    (fun (x : ℕ × {d // d ∈ g'.divisors})
        (hx : x ∈ Finset.range (c + 1) ×ˢ g'.divisors.attach) ↦
      ⟨p ^ x.1 * x.2.val, ?_⟩)
    (fun (d : {d // d ∈ (m.gcd n).divisors}) (_ : d ∈ (m.gcd n).divisors.attach) ↦
      ((d.val.factorization p), ⟨d.val / p ^ (d.val.factorization p), ?_⟩))
    ?_ ?_ ?_ ?_ ?_
  case refine_1 =>
    exact pow_mul_mem_gcd_divisors hgcd_eq hg'_pos hpc_pos x.2.prop
      (Nat.lt_add_one_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hx).1))
  case refine_2 =>
    exact ordCompl_mem_divisors_of_dvd_mul_pow hp hg'_pos hp_not_dvd_g'
      (hgcd_eq ▸ Nat.dvd_of_mem_divisors d.prop : ↑d ∣ g' * p ^ c)
  case refine_3 => exact fun _ _ ↦ Finset.mem_attach _ _
  case refine_4 =>
    rintro ⟨d, hd⟩ -
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_attach, and_true]
    have hd_dvd_gpc : d ∣ g' * p ^ c := hgcd_eq ▸ Nat.dvd_of_mem_divisors hd
    have hgpc_ne : g' * p ^ c ≠ 0 := (Nat.mul_pos hg'_pos hpc_pos).ne'
    have hd_ne : d ≠ 0 := ne_zero_of_dvd_ne_zero hgpc_ne hd_dvd_gpc
    exact Nat.lt_succ_of_le (factorization_coprime_mul_pow_self (c := c) hp hp_not_dvd_g' ▸
      (Nat.factorization_le_iff_dvd hd_ne hgpc_ne).mpr hd_dvd_gpc p)
  case refine_5 =>
    rintro ⟨j, ⟨d', hd'⟩⟩ -
    have hd'_pos : 0 < d' := Nat.pos_of_ne_zero fun h ↦
      hg'_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ Nat.dvd_of_mem_divisors hd'))
    have hfact : (p ^ j * d').factorization p = j :=
      factorization_pow_mul_self hp hd'_pos
        (fun h ↦ hp_not_dvd_g' (dvd_trans h (Nat.dvd_of_mem_divisors hd')))
    ext1
    · exact hfact
    · exact Subtype.ext (by simp only [hfact, Nat.mul_div_cancel_left d' (pow_pos hp.pos j)])
  case refine_6 =>
    rintro ⟨d, hd⟩ -
    exact Subtype.ext (Nat.ordProj_mul_ordCompl_eq_self d p)
  case refine_7 =>
    rintro ⟨j, ⟨d', hd'⟩⟩ hmem
    exact formal_table_summand dblk sblk hp va vb m' n' m n j d' hm'_pos hn'_pos
      hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n' hd'
      (Nat.lt_add_one_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hmem).1))

private theorem formal_table_noncoprime
    (hppow : ∀ (p : ℕ), Nat.Prime p → ∀ r s : ℕ, r ≤ s →
      peelProd dblk (p ^ r) * peelProd dblk (p ^ s) =
        ∑ i ∈ Finset.range (r + 1),
          (p : ℤ) ^ i • (peelProd sblk (p ^ i) * peelProd dblk (p ^ (r + s - 2 * i))))
    (g : ℕ) (m n : ℕ) [NeZero m] [NeZero n] (hg : Nat.gcd m n = g) (hg1 : g ≠ 1)
    (ih : ∀ g', g' < g → ∀ (m' n' : ℕ), [NeZero m'] → [NeZero n'] → Nat.gcd m' n' = g' →
      peelProd dblk m' * peelProd dblk n' =
        ∑ d ∈ (Nat.gcd m' n').divisors.attach,
          (d.val : ℤ) • (peelProd sblk d.val *
            peelProd dblk (m' * n' / (d.val * d.val)))) :
    peelProd dblk m * peelProd dblk n =
      ∑ d ∈ (Nat.gcd m n).divisors.attach,
        (d.val : ℤ) • (peelProd sblk d.val *
          peelProd dblk (m * n / (d.val * d.val))) := by
  have hg_pos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · exact absurd ((Nat.gcd_eq_zero_iff.mp hg)).1 (NeZero.ne m)
    · exact h
  set p := g.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by lia)
  have hp_dvd_m : p ∣ m := dvd_trans (hg ▸ Nat.minFac_dvd g) (Nat.gcd_dvd_left m n)
  have hp_dvd_n : p ∣ n := dvd_trans (hg ▸ Nat.minFac_dvd g) (Nat.gcd_dvd_right m n)
  set va := m.factorization p
  set vb := n.factorization p
  have ha_pos : 0 < va := hp.factorization_pos_of_dvd (NeZero.ne m) hp_dvd_m
  have hb_pos : 0 < vb := hp.factorization_pos_of_dvd (NeZero.ne n) hp_dvd_n
  set m' := m / p ^ va
  set n' := n / p ^ vb
  have hm'_pos : 0 < m' :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) (Nat.ordProj_dvd m p)) (pow_pos hp.pos va)
  have hn'_pos : 0 < n' :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) (Nat.ordProj_dvd n p)) (pow_pos hp.pos vb)
  haveI : NeZero m' := ⟨hm'_pos.ne'⟩
  haveI : NeZero n' := ⟨hn'_pos.ne'⟩
  have hp_not_dvd_m' : ¬p ∣ m' := Nat.not_dvd_ordCompl hp (NeZero.ne m)
  have hp_not_dvd_n' : ¬p ∣ n' := Nat.not_dvd_ordCompl hp (NeZero.ne n)
  have hm_eq : m = p ^ va * m' := (Nat.mul_div_cancel' (Nat.ordProj_dvd m p)).symm
  have hn_eq : n = p ^ vb * n' := (Nat.mul_div_cancel' (Nat.ordProj_dvd n p)).symm
  have hgcd_eq : Nat.gcd m n = Nat.gcd m' n' * p ^ min va vb :=
    gcd_eq_gcd_ordCompl_mul_pow_min hp hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n'
  set g' := Nat.gcd m' n'
  have hg'_lt : g' < g := by
    rw [← hg, hgcd_eq]
    refine lt_mul_of_one_lt_right (Nat.pos_of_ne_zero fun hg'0 ↦ ?_)
      (Nat.one_lt_pow (by omega) hp.one_lt)
    exact hm'_pos.ne' (Nat.eq_zero_of_gcd_eq_zero_left hg'0)
  have hcop_m : Nat.Coprime (p ^ va) m' := (hp.coprime_pow_of_not_dvd hp_not_dvd_m').symm
  have hcop_n : Nat.Coprime (p ^ vb) n' := (hp.coprime_pow_of_not_dvd hp_not_dvd_n').symm
  have hDm : peelProd dblk m = peelProd dblk (p ^ va) * peelProd dblk m' := by
    rw [hm_eq, peelProd_mul_coprime dblk _ _ hcop_m]
  have hDn : peelProd dblk n = peelProd dblk (p ^ vb) * peelProd dblk n' := by
    rw [hn_eq, peelProd_mul_coprime dblk _ _ hcop_n]
  have hppow_minmax : peelProd dblk (p ^ va) * peelProd dblk (p ^ vb) =
      peelProd dblk (p ^ min va vb) * peelProd dblk (p ^ max va vb) := by
    rcases le_or_gt va vb with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h.le, max_eq_left h.le, mul_comm]
  rw [hDm, hDn, mul_mul_mul_comm, hppow_minmax,
      hppow p hp (min va vb) (max va vb) (min_le_max),
      ih g' (hg ▸ hg'_lt) m' n' rfl]
  exact formal_table_div_sum dblk sblk hp va vb m' n' m n hm'_pos hn'_pos
    hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n' hgcd_eq

private theorem formal_table
    (hppow : ∀ (p : ℕ), Nat.Prime p → ∀ r s : ℕ, r ≤ s →
      peelProd dblk (p ^ r) * peelProd dblk (p ^ s) =
        ∑ i ∈ Finset.range (r + 1),
          (p : ℤ) ^ i • (peelProd sblk (p ^ i) * peelProd dblk (p ^ (r + s - 2 * i))))
    (m n : ℕ) [NeZero m] [NeZero n] :
    peelProd dblk m * peelProd dblk n =
      ∑ d ∈ (Nat.gcd m n).divisors.attach,
        (d.val : ℤ) • (peelProd sblk d.val *
          peelProd dblk (m * n / (d.val * d.val))) := by
  suffices H : ∀ g, ∀ (m n : ℕ), [NeZero m] → [NeZero n] → Nat.gcd m n = g →
      peelProd dblk m * peelProd dblk n =
        ∑ d ∈ (Nat.gcd m n).divisors.attach,
          (d.val : ℤ) • (peelProd sblk d.val *
            peelProd dblk (m * n / (d.val * d.val))) by
    exact H (Nat.gcd m n) m n rfl
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro m n _ _ hg
  by_cases hg1 : g = 1
  · subst hg1
    rw [Finset.sum_attach _ fun d : ℕ ↦
        (d : ℤ) • (peelProd sblk d * peelProd dblk (m * n / (d * d))), hg, Nat.divisors_one,
      Finset.sum_singleton, Nat.cast_one, one_smul, Nat.one_mul, Nat.div_one, peelProd_one,
      one_mul, ← peelProd_mul_coprime dblk m n hg]
  · exact formal_table_noncoprime dblk sblk hppow g m n hg hg1
      (fun g' hlt m' n' _ _ h ↦ ih g' hlt m' n' h)

end FormalTable

variable {N : ℕ} [NeZero N]

/-- The ring-side prime generator: the single double coset `D_p = Γ₀(N)·diag(1,p)·Γ₀(N)`.
Defined for every `p > 0`, including bad primes `p ∣ N`. -/
noncomputable def heckeRingDp (p : ℕ) (hp : 0 < p) : 𝕋 (Gamma0_pair N) ℤ :=
  T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp) 1

/-- The ring-side scalar generator: the single scalar double coset `T(p,p)` for `p ∤ N`,
and `0` for `p ∣ N` (where `diag(p,p) ∉ Δ₀(N)`; the vanishing mirrors `⟨p⟩ = 0`). -/
noncomputable def heckeRingSpp (p : ℕ) (hp : Nat.Prime p) : 𝕋 (Gamma0_pair N) ℤ :=
  if hpN : Nat.Coprime p N then
    T_single (Gamma0_pair N) ℤ (T_diag_Gamma0 N (fun _ : Fin 2 ↦ p) (fun _ ↦ hp.pos)
      (by rwa [Int.gcd_natCast_natCast])) 1
  else 0

@[simp] theorem heckeRingSpp_of_not_coprime (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) : heckeRingSpp (N := N) p hp = 0 :=
  dif_neg hpN

/-- The ring-side prime-power element, defined by the Diamond–Shurman recurrence
`D_{p^0} = 1`, `D_{p^1} = D_p`, and
`D_{p^{r+2}} = D_p · D_{p^{r+1}} − (p·S_p) · D_{p^r}`.
For `p ∣ N` the scalar term vanishes and the recurrence degenerates to `D_{p^r} = D_p^r`. -/
noncomputable def heckeRingDppow (p : ℕ) (hp : Nat.Prime p) : ℕ → 𝕋 (Gamma0_pair N) ℤ
  | 0 => 1
  | 1 => heckeRingDp p hp.pos
  | r + 2 =>
    heckeRingDp p hp.pos * heckeRingDppow p hp (r + 1) -
      ((p : ℤ) • heckeRingSpp p hp) * heckeRingDppow p hp r

@[simp] theorem heckeRingDppow_zero (p : ℕ) (hp : Nat.Prime p) :
    heckeRingDppow (N := N) p hp 0 = 1 := rfl

@[simp] theorem heckeRingDppow_one (p : ℕ) (hp : Nat.Prime p) :
    heckeRingDppow (N := N) p hp 1 = heckeRingDp p hp.pos := rfl

/-- The `r + 2` case of the recurrence: `D_{p^{r+2}} = D_p · D_{p^{r+1}} − (p · S_p) · D_{p^r}`. -/
theorem heckeRingDppow_succ_succ (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    heckeRingDppow (N := N) p hp (r + 2) = heckeRingDp p hp.pos * heckeRingDppow p hp (r + 1) -
      ((p : ℤ) • heckeRingSpp p hp) * heckeRingDppow p hp r := rfl

/-- For a bad prime `p ∣ N` the recurrence degenerates: `D_{p^r} = D_p^r`. -/
theorem heckeRingDppow_eq_pow_of_not_coprime (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (r : ℕ) : heckeRingDppow (N := N) p hp r = heckeRingDp p hp.pos ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r _ih0 ih1 =>
    rw [heckeRingDppow_succ_succ, heckeRingSpp_of_not_coprime p hp hpN,
      smul_zero, zero_mul, sub_zero, ih1, ← pow_succ']

/-- **Per-prime product formula** (Shimura 3.24(3) at level `Γ₀(N)`, ring side): for
`r ≤ s`,
`D_{p^r} · D_{p^s} = ∑_{i=0}^{r} (p·S_p)^i · D_{p^{r+s−2i}}`.
Instantiates the formal Chebyshev identity in the commutative ring `𝕋 (Gamma0_pair N) ℤ`.
For `p ∣ N` both sides collapse to `D_p^{r+s}`. -/
theorem heckeRingDppow_mul (p : ℕ) (hp : Nat.Prime p) (r s : ℕ) (hrs : r ≤ s) :
    heckeRingDppow (N := N) p hp r * heckeRingDppow p hp s =
      ∑ i ∈ Finset.range (r + 1), ((p : ℤ) • heckeRingSpp p hp) ^ i * heckeRingDppow p hp (r + s - 2 * i) := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact formal_ppow_mul (heckeRingDp p hp.pos) ((p : ℤ) • heckeRingSpp p hp)
    (heckeRingDppow p hp) rfl rfl (heckeRingDppow_succ_succ p hp) r s hrs

/-- The composite ring element `D_n`, assembled by `minFac`-peeling over the prime
factorisation of `n` — with **genuine** factors at bad primes `p ∣ N`
(`D_{p^v} = D_p^v`). `D_0 = D_1 = 1`. -/
noncomputable def heckeRingDn (n : ℕ) : 𝕋 (Gamma0_pair N) ℤ :=
  peelProd (R := 𝕋 (Gamma0_pair N) ℤ)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingDppow p hp v else 1) n

@[simp] theorem heckeRingDn_zero : heckeRingDn (N := N) 0 = 1 := peelProd_zero _

@[simp] theorem heckeRingDn_one : heckeRingDn (N := N) 1 = 1 := peelProd_one _

/-- On a prime power, the composite assembly agrees with the prime-power element. -/
theorem heckeRingDn_ppow (p : ℕ) (hp : Nat.Prime p) (v : ℕ) :
    heckeRingDn (N := N) (p ^ v) = heckeRingDppow p hp v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  rw [heckeRingDn, peelProd_ppow _ hp v hv, dif_pos hp]

/-- Peeling step for `heckeRingDn`: for `1 < n`, expresses `D_n` as `D_{p^v} * D_{n/p^v}`
where `p = n.minFac` and `v` is the `p`-adic valuation of `n`. -/
theorem heckeRingDn_peel (n : ℕ) (hn : 1 < n) : heckeRingDn (N := N) n =
    heckeRingDppow n.minFac (Nat.minFac_prime (by omega : n ≠ 1))
        (n.factorization n.minFac) * heckeRingDn (n / n.minFac ^ n.factorization n.minFac) := by
  grind [heckeRingDn, peelProd_peel]

/-- **Coprime multiplicativity** (ring side): `D_{mn} = D_m · D_n` for coprime `m, n`. -/
theorem heckeRingDn_mul_coprime (m n : ℕ) (hmn : Nat.Coprime m n) :
    heckeRingDn (N := N) (m * n) = heckeRingDn m * heckeRingDn n := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact peelProd_mul_coprime _ m n hmn

/-- The composite scalar class `S_d`: multiplicative over the factorisation of `d`,
with `S_{p^v} = S_p^v`. Vanishes (some factor is `0`) unless `d` is coprime to `N`.
Ring-side avatar of the operator `d ↦ d^{k-2}·⟨d⟩`. -/
noncomputable def heckeRingSn (d : ℕ) : 𝕋 (Gamma0_pair N) ℤ :=
  peelProd (R := 𝕋 (Gamma0_pair N) ℤ)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingSpp p hp ^ v else 1) d

@[simp] theorem heckeRingSn_one : heckeRingSn (N := N) 1 = 1 := peelProd_one _

/-- The composite scalar class vanishes as soon as `d` shares a factor with `N`:
some prime-power block is `S_p^v = 0^v = 0`. -/
theorem heckeRingSn_eq_zero_of_not_coprime :
    ∀ d : ℕ, d ≠ 0 → ¬ Nat.Coprime d N → heckeRingSn (N := N) d = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd0 hdN
    have hd1 : d ≠ 1 := fun h ↦ hdN (h ▸ Nat.coprime_one_left N)
    have hd2 : 1 < d := by omega
    set q := d.minFac with hq_def
    have hq : Nat.Prime q := Nat.minFac_prime hd1
    set v := d.factorization q with hv_def
    have hv_pos : 0 < v :=
      hq.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd d)
    have hpeel : heckeRingSn (N := N) d =
        heckeRingSpp q hq ^ v * heckeRingSn (d / q ^ v) := by
      rw [heckeRingSn, peelProd_peel _ d hd2, dif_pos hq]
      rfl
    by_cases hqN : Nat.Coprime q N
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
        (fun h ↦ hdN h : Nat.gcd d N ≠ 1)
      have hpN : p ∣ N := hpdvd.trans (Nat.gcd_dvd_right d N)
      have hpq : p ≠ q := by
        rintro rfl
        exact (hp.coprime_iff_not_dvd.mp hqN) hpN
      have hp_quot : p ∣ d / q ^ v := by
        rcases hp.dvd_mul.mp
            ((Nat.mul_div_cancel' (Nat.ordProj_dvd d q)).symm ▸
             hpdvd.trans (Nat.gcd_dvd_left d N)) with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)) hpq
        · exact h
      rw [hpeel, ih _
        (Nat.div_lt_self (by omega) (Nat.one_lt_pow hv_pos.ne' hq.one_lt))
        (Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd d q))
          (pow_pos hq.pos v)).ne'
        (fun hcop ↦
          (hp.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left hp_quot hcop)) hpN),
        mul_zero]
    · rw [hpeel, heckeRingSpp_of_not_coprime q hq hqN, zero_pow hv_pos.ne', zero_mul]

/-- On a prime power, the composite scalar class agrees with the power of the prime scalar:
`S_{p^v} = S_p^v`. -/
theorem heckeRingSn_ppow (p : ℕ) (hp : Nat.Prime p) (v : ℕ) :
    heckeRingSn (N := N) (p ^ v) = heckeRingSpp p hp ^ v := by
  cases v <;> simp_all [heckeRingSn, peelProd_ppow _ hp _ (Nat.succ_pos _)]

/-- The per-prime product formula in `D_n`/`S_n` form: `D_{p^r} * D_{p^s} = ∑_{i=0}^{r} p^i • (S_{p^i} * D_{p^{r+s−2i}})` for `r ≤ s` (Shimura 3.24(3)). -/
theorem heckeRingDn_ppow_mul (p : ℕ) (hp : Nat.Prime p) (r s : ℕ) (hrs : r ≤ s) :
    heckeRingDn (N := N) (p ^ r) * heckeRingDn (p ^ s) = ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (heckeRingSn (p ^ i) * heckeRingDn (p ^ (r + s - 2 * i))) := by
  rw [heckeRingDn_ppow p hp r, heckeRingDn_ppow p hp s, heckeRingDppow_mul p hp r s hrs]
  simp only [heckeRingDn_ppow p hp, heckeRingSn_ppow p hp, smul_pow, smul_mul_assoc]

/-- **General multiplication table** (ring-side Shimura 3.24 at level `Γ₀(N)`): for
`m, n > 0`,
`D_m · D_n = ∑_{d ∣ gcd m n} d • (S_d · D_{mn/d²})`.
The bad-prime divisors `d` with `gcd(d, N) > 1` contribute `0` (since `S_d = 0` there), so the
sum over *all* divisors of `gcd m n` is correct as stated.  Instantiates the formal table
`formal_table` with the concrete `peelProd`-assembled families `heckeRingDn`, `heckeRingSn`,
whose per-prime blocks satisfy the Chebyshev product law `heckeRingDn_ppow_mul`. -/
theorem heckeRingDn_mul (m n : ℕ) [NeZero m] [NeZero n] :
    heckeRingDn (N := N) m * heckeRingDn n = ∑ d ∈ (Nat.gcd m n).divisors.attach,
      (d.val : ℤ) • (heckeRingSn d.val * heckeRingDn (m * n / (d.val * d.val))) := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact formal_table
    (fun p v ↦ if hp : Nat.Prime p then heckeRingDppow p hp v else 1)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingSpp p hp ^ v else 1)
    heckeRingDn_ppow_mul m n

end HeckeRing.GL2.Unified
