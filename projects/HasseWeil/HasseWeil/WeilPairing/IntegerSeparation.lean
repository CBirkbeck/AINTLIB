import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Route 2 endgame — integer separation from per-`ℓ` congruences (Silverman V.2.3.1, Step 7)

This file ships **Step 7** of the round-17 Weil-pairing route to the Hasse bound: the purely
arithmetic *integer-separation* lemma that lifts a family of mod-`ℓ` congruences (one per auxiliary
prime `ℓ ≠ p`) to an equality of integers.

The whole Weil-pairing content of Route 2 — the determinant–degree congruence
`det(ψ | E[ℓ]) ≡ deg ψ (mod ℓ)` — feeds into this lemma as the per-`ℓ` hypothesis.  Concretely,
once the finite-level pairing gives `deg(rπ − s) ≡ qr² − t·rs + s² (mod ℓ)` for every prime `ℓ ≠ p`,
`int_eq_of_congr_all_primes_ne` yields the **integer** identity `deg(rπ − s) = qr² − t·rs + s²`,
which (being a value of `deg`) is `≥ 0` — closing Leaf 1.

This isolates the Weil pairing as the single residual: everything *downstream* of the per-`ℓ`
determinant congruence is this self-contained arithmetic, with **no** elliptic-curve content.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, V.2.3.1 (the integer equality `det = deg`
is pinned by reducing modulo infinitely many `ℓ`).
-/

namespace HasseWeil.WeilPairing

/-- **An integer divisible by every prime `ℓ ≠ p` is zero.**

The arithmetic core of the Route-2 endgame: a nonzero integer has only finitely many prime
divisors, but there are infinitely many primes `≠ p`, so if every such prime divides `D` then
`D = 0`.  (Witness: choose a prime `ℓ ≥ max(|D|+1, p+1)`; it is `≠ p` and exceeds `|D|`, yet
`ℓ ∣ D` forces `ℓ ≤ |D|` when `D ≠ 0`.) -/
theorem int_eq_zero_of_dvd_all_primes_ne {D : ℤ} {p : ℕ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (ℓ : ℤ) ∣ D) : D = 0 := by
  by_contra hD
  obtain ⟨ℓ, hℓ_ge, hℓ_prime⟩ := Nat.exists_infinite_primes (max (D.natAbs + 1) (p + 1))
  have hℓ_ne : ℓ ≠ p := by
    have : p < ℓ := lt_of_lt_of_le (Nat.lt_succ_self p) (le_trans (le_max_right _ _) hℓ_ge)
    omega
  have hdvd : (ℓ : ℤ) ∣ D := h ℓ hℓ_prime hℓ_ne
  have hdvd_nat : ℓ ∣ D.natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_natCast] at h2
  have hle : ℓ ≤ D.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hdvd_nat
  have hgt : D.natAbs < ℓ :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hℓ_ge)
  omega

/-- **Integer equality from mod-`ℓ` congruences for all primes `ℓ ≠ p`.**

If `A ≡ B (mod ℓ)` (as elements of `ZMod ℓ`) for every prime `ℓ ≠ p`, then `A = B` as integers.
This is the Route-2 endgame: with `A = deg(rπ − s)` and `B = qr² − t·rs + s²`, the per-`ℓ`
determinant–degree congruence from the finite-level Weil pairing forces the integer identity. -/
theorem int_eq_of_congr_all_primes_ne {A B : ℤ} {p : ℕ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (A : ZMod ℓ) = (B : ZMod ℓ)) : A = B := by
  have hsub : A - B = 0 := by
    apply int_eq_zero_of_dvd_all_primes_ne (p := p)
    intro ℓ hℓ hℓne
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hc := h ℓ hℓ hℓne
    have h0 : ((A - B : ℤ) : ZMod ℓ) = 0 := by rw [Int.cast_sub, hc, sub_self]
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  omega

end HasseWeil.WeilPairing
