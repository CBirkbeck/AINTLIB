import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Route 2A — the discriminant lemma (Silverman V.1.1, Leaf 5)

The arithmetic finish of Route 2A: from `det(rπ−s|E[ℓ]) ≡ deg(rπ−s)` for the **separable** cases
(`p ∤ s`, Silverman III.5.5), the Weil-pairing route delivers `deg(rπ−s) = q·r² − t·rs + s² ≥ 0` for
all `(r,s)` with `p ∤ s`. This file lifts that to **all** `(r,s)`:

  if `Q(r,s) := q·r² − t·rs + s² ≥ 0` for every `(r,s)` with `p ∤ s`, then `Q ≥ 0` everywhere.

The mechanism is the **discriminant**: `Q ≥ 0` on the `p`-coprime-denominator sublattice forces
`t² ≤ 4q` (the Hasse inequality), whence `Q` is positive semi-definite. The proof is purely
arithmetic — no elliptic-curve content — and uses no real analysis: a balanced remainder makes
`(2qr − ts)² ≤ q²` for a chosen `s = ℓⁿ` (`ℓ ≠ p` prime), and `(4q − t²)ℓ^{2n}` then races below
`−q²`, contradicting the `≥ −q²` lower bound from `Q ≥ 0`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, V.1.1 / Lemma 1.2 (deg is a positive
definite quadratic form ⟹ `|t| ≤ 2√q`).
-/

namespace HasseWeil.WeilPairing

/-- **Balanced remainder.** For `0 < q` and any `a`, there is `r` with `|a − 2qr| ≤ q`
(the nearest-integer approximation of `a/(2q)`). -/
theorem exists_int_balanced {q : ℤ} (hq : 0 < q) (a : ℤ) : ∃ r : ℤ, |a - 2 * q * r| ≤ q := by
  have hm : (0 : ℤ) < 2 * q := by linarith
  refine ⟨(a + q) / (2 * q), ?_⟩
  have h0 : 0 ≤ (a + q) % (2 * q) := Int.emod_nonneg _ (ne_of_gt hm)
  have h1 : (a + q) % (2 * q) < 2 * q := Int.emod_lt_of_pos _ hm
  have hd : (a + q) % (2 * q) + 2 * q * ((a + q) / (2 * q)) = a + q :=
    Int.emod_add_mul_ediv (a + q) (2 * q)
  rw [abs_le]
  constructor <;> linarith [hd, h0, h1]

/-- **The discriminant lemma (Silverman V.1.1).** If the quadratic form `Q(r,s) = q·r² − t·rs + s²`
(with `0 < q`) is non-negative on every `(r,s)` whose `s` is coprime to a prime `p`, then it is
non-negative on **all** `(r,s)`.

Step 1 forces `t² ≤ 4q` (a contradiction otherwise, via a `p`-coprime witness `s = ℓⁿ`); step 2 is
the positive-semidefiniteness `4q·Q = (2qr − ts)² + (4q − t²)s² ≥ 0`. -/
theorem qf_nonneg_of_nonneg_on_coprime {q t : ℤ} (hq : 0 < q) {p : ℕ} (hp : p.Prime)
    (h : ∀ r s : ℤ, ¬ (p : ℤ) ∣ s → 0 ≤ q * r ^ 2 - t * r * s + s ^ 2) :
    ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2 := by
  -- Step 1: t² ≤ 4q.
  have hdisc : t ^ 2 ≤ 4 * q := by
    by_contra hcon
    push Not at hcon                       -- 4 * q < t ^ 2
    obtain ⟨ℓ, hℓ_ge, hℓ_prime⟩ := Nat.exists_infinite_primes (p + 1)
    have hℓp : ℓ ≠ p := by omega
    have h1ℓ : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ_prime.one_lt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, q < (ℓ : ℤ) ^ n := pow_unbounded_of_one_lt q h1ℓ
    set s : ℤ := (ℓ : ℤ) ^ n with hsdef
    have hs_pos : 0 < s := lt_trans hq hn
    have hps : ¬ (p : ℤ) ∣ s := by
      rw [hsdef]
      intro hdvd
      have hnat : p ∣ ℓ ^ n := by exact_mod_cast hdvd
      exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ_prime).mp (hp.dvd_of_dvd_pow hnat)).symm
    obtain ⟨r, hbal⟩ := exists_int_balanced hq (t * s)
    have hQ : 0 ≤ q * r ^ 2 - t * r * s + s ^ 2 := h r s hps
    have h4qQ : 0 ≤ 4 * q * (q * r ^ 2 - t * r * s + s ^ 2) :=
      mul_nonneg (by linarith) hQ
    have hbsq : (2 * q * r - t * s) ^ 2 ≤ q ^ 2 := by
      have hb := abs_le.mp hbal
      nlinarith [hb.1, hb.2]
    have htlt : 4 * q - t ^ 2 ≤ -1 := by linarith
    have hmul : (4 * q - t ^ 2) * s ^ 2 ≤ (-1) * s ^ 2 :=
      mul_le_mul_of_nonneg_right htlt (sq_nonneg s)
    have hs2gt : q ^ 2 < s ^ 2 := by nlinarith [hn, hq, hs_pos]
    have key : 4 * q * (q * r ^ 2 - t * r * s + s ^ 2)
        = (2 * q * r - t * s) ^ 2 + (4 * q - t ^ 2) * s ^ 2 := by ring
    nlinarith [h4qQ, key, hbsq, hmul, hs2gt]
  -- Step 2: positive semidefiniteness `4q·Q = (2qr − ts)² + (4q − t²)s² ≥ 0`.
  intro r s
  nlinarith [sq_nonneg (2 * q * r - t * s),
    mul_nonneg (by linarith : (0 : ℤ) ≤ 4 * q - t ^ 2) (sq_nonneg s), hq]

/-- **The discriminant lemma, coprime-in-BOTH-coordinates form** (reviewer round-23, Route B).
If the quadratic form `Q(r,s) = q·r² − t·rs + s²` (with `0 < q`) is non-negative on every `(r,s)` whose
**both** coordinates are coprime to a prime `p` (`p ∤ r` and `p ∤ s`), then it is non-negative on
**all** `(r,s)`.

This weakens the hypothesis of `qf_nonneg_of_nonneg_on_coprime` (which assumes `≥ 0` on the larger
set `{p ∤ s}`) to the smaller set `{p ∤ r ∧ p ∤ s}` — exactly the locus on which the Weil-pairing
pencil scaling is available **without** the inseparable `p ∣ r'` geometric input.

Step 1 forces `t² ≤ 4q` by the reviewer's **explicit** negative witness — no density / CRT /
balanced-remainder argument: if `Δ := t² − 4q > 0`, set `C := q − t + 1`, `m := p·(|C| + 1)`,
`r := m·t + 1`, `s := 2·m·q + 1`.  Then `p ∣ m` makes `r ≡ s ≡ 1 (mod p)`, so `p ∤ r, s`, while the
`ring` identity `Q(m·t+1, 2·m·q+1) = (4q − t²)(q·m² + m) + (q − t + 1) = −Δ·(q·m² + m) + C` is
`< 0` (since `Δ·(q·m² + m) ≥ q·m² + m ≥ |C| + 1 > C`), contradicting `Q ≥ 0`.  Step 2 reuses the
positive-semidefiniteness `4q·Q = (2qr − ts)² + (4q − t²)s² ≥ 0`. -/
theorem qf_nonneg_of_nonneg_on_coprime_both {q t : ℤ} (hq : 0 < q) {p : ℕ} (hp : p.Prime)
    (h : ∀ r s : ℤ, ¬ (p : ℤ) ∣ r → ¬ (p : ℤ) ∣ s →
      0 ≤ q * r ^ 2 - t * r * s + s ^ 2) :
    ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2 := by
  -- Step 1: t² ≤ 4q, by the reviewer's explicit prime-to-`p` negative witness.
  have hdisc : t ^ 2 ≤ 4 * q := by
    by_contra hcon
    push Not at hcon                       -- 4 * q < t ^ 2
    have hΔ : (1 : ℤ) ≤ t ^ 2 - 4 * q := by linarith
    set C : ℤ := q - t + 1 with hCdef
    set m : ℤ := (p : ℤ) * (|C| + 1) with hmdef
    have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have habsC : (0 : ℤ) ≤ |C| := abs_nonneg C
    have hCle : C ≤ |C| := le_abs_self C
    have hm_ge : |C| + 1 ≤ m := by rw [hmdef]; nlinarith [habsC, hp2]
    have hm_pos : 0 < m := by linarith [habsC]
    have hpm : (p : ℤ) ∣ m := ⟨|C| + 1, rfl⟩
    set r : ℤ := m * t + 1 with hrdef
    set s : ℤ := 2 * m * q + 1 with hsdef
    -- `r ≡ 1 (mod p)`: if `p ∣ r` then `p ∣ (r − m·t) = 1`, impossible for a prime.
    have hpr : ¬ (p : ℤ) ∣ r := by
      intro hdvd
      have hd1 : (p : ℤ) ∣ (r - m * t) := dvd_sub hdvd (hpm.mul_right t)
      rw [hrdef, add_sub_cancel_left] at hd1
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd1) with h1 | h1 <;>
        · rw [h1] at hp2; norm_num at hp2
    -- `s ≡ 1 (mod p)`: same, with `s − 2·m·q = 1`.
    have hps : ¬ (p : ℤ) ∣ s := by
      intro hdvd
      have hd1 : (p : ℤ) ∣ (s - 2 * m * q) := dvd_sub hdvd ((hpm.mul_left 2).mul_right q)
      rw [hsdef, add_sub_cancel_left] at hd1
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd1) with h1 | h1 <;>
        · rw [h1] at hp2; norm_num at hp2
    have hQ : 0 ≤ q * r ^ 2 - t * r * s + s ^ 2 := h r s hpr hps
    -- The reviewer's `ring` identity at `(r,s) = (m·t+1, 2·m·q+1)`.
    have hkey : q * r ^ 2 - t * r * s + s ^ 2
        = (4 * q - t ^ 2) * (q * m ^ 2 + m) + (q - t + 1) := by
      rw [hrdef, hsdef]; ring
    have hqm : |C| + 1 ≤ q * m ^ 2 + m := by nlinarith [hm_ge, hm_pos, hq, sq_nonneg m]
    have hbound : (4 * q - t ^ 2) * (q * m ^ 2 + m) + (q - t + 1) < 0 := by
      have hΔpos : 0 < q * m ^ 2 + m := by linarith [habsC, hqm]
      nlinarith [hΔ, hqm, habsC, hCle, hΔpos]
    rw [hkey] at hQ
    linarith [hQ, hbound]
  -- Step 2: positive semidefiniteness `4q·Q = (2qr − ts)² + (4q − t²)s² ≥ 0`.
  intro r s
  nlinarith [sq_nonneg (2 * q * r - t * s),
    mul_nonneg (by linarith : (0 : ℤ) ≤ 4 * q - t ^ 2) (sq_nonneg s), hq]

end HasseWeil.WeilPairing
