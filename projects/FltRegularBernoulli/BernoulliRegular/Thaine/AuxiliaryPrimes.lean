import BernoulliRegular.Thaine.AuxiliaryUnits
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# T-THAINE-2: Auxiliary-prime universe (Chebotarev-style)

For Thaine's annihilator theorem (`[Wash97 2nd ed §15]`), the construction
needs an infinite supply of auxiliary primes ℓ′ ≡ 1 (mod p^n) whose
Frobenius on a chosen Galois extension acts as a prescribed element. This
follows from Chebotarev's density theorem applied to the Galois closure
of `K(ζ_{p^n})` together with the cyclotomic-extension splitting.

## Structure

This ticket records the *interface* needed by `T-THAINE-3` (Kolyvagin
derivative) and `T-THAINE-4` (annihilator descent). The interface is
`AuxiliaryPrimePool p n`, an inhabited (in fact infinite) record of
auxiliary primes satisfying the Thaine conditions.

The *content* — applying mathlib's Chebotarev density theorem to produce
witnesses — is a substantial follow-up; here we ship the type-level
contract so that downstream Thaine work can proceed parametric on it.

## Conditions on auxiliary primes (from [Wash97 2nd ed §15.1])

For Thaine's construction at level `n`:
1. ℓ′ is prime, distinct from `p`.
2. ℓ′ ≡ 1 (mod `p^n`) (so that `μ_{p^n} ⊂ K(ζ_{ℓ′})` after appropriate
   extension).
3. The Frobenius of ℓ′ on the Hilbert class field of `K` acts as a
   prescribed element (specified by the Kolyvagin derivative target).

For the type-level interface here, we abstract the conditions into the
predicate `IsThaineAuxiliary p n ℓ`. The full construction will use
this predicate as the type of legitimate auxiliary primes.

## References

* [Wash97 2nd ed] §15.1 (auxiliary primes), Lemma 15.4.
* [Rubin00] *Euler Systems*, §3.5 (Chebotarev application).
* `Mathlib.NumberTheory.NumberField.Cyclotomic.Basic` and Chebotarev
  results in `Mathlib.NumberTheory.Cyclotomic.GaloisActionOnCyclo`.
-/

@[expose] public section

namespace BernoulliRegular

namespace Thaine

/-- **`IsThaineAuxiliary p n ℓ`**: predicate saying that the prime `ℓ` is
suitable as a Thaine auxiliary at level `n` for the prime `p`. The
conditions are:

1. `ℓ ≠ p`.
2. `p^n ∣ (ℓ - 1)` (i.e., `ℓ ≡ 1 mod p^n`).

The Frobenius condition (item 3 in the file docstring) is parametric
on the target Galois action and is encoded separately in the
construction sites of `T-THAINE-3`. -/
structure IsThaineAuxiliary (p n ℓ : ℕ) : Prop where
  ne_p : ℓ ≠ p
  cong_one_mod_p_pow : (p ^ n) ∣ (ℓ - 1)

namespace IsThaineAuxiliary

/-- A Thaine auxiliary prime is `≥ 1` (since `p^n ∣ ℓ - 1` requires
`ℓ ≥ p^n + 1` or `ℓ = 1`; for the prime case `ℓ ≥ 2` so the genuine
content is `p^n ∣ ℓ - 1`). -/
theorem one_le_of_ne_p_of_prime {p n ℓ : ℕ} (_ : p.Prime)
    (hℓ_prime : ℓ.Prime) (_ : IsThaineAuxiliary p n ℓ) : 1 ≤ ℓ :=
  hℓ_prime.one_lt.le

/-- The constant function: the Thaine condition is decidable for fixed
`(p, n, ℓ)`. -/
instance decidable (p n ℓ : ℕ) [Decidable (ℓ ≠ p)]
    [Decidable ((p ^ n) ∣ (ℓ - 1))] :
    Decidable (IsThaineAuxiliary p n ℓ) :=
  decidable_of_iff (ℓ ≠ p ∧ (p ^ n) ∣ (ℓ - 1))
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.ne_p, h.cong_one_mod_p_pow⟩⟩

end IsThaineAuxiliary

/-- **Concrete example for FLT37 / level 1**: the LV-prime ℓ = 149 satisfies
`IsThaineAuxiliary 37 1 149`. Here the level is `n = 1`; higher-level
auxiliaries (n ≥ 2) needed for Kolyvagin descent of the annihilator are
constructed in `T-THAINE-3`. -/
theorem isThaineAuxiliary_thirtyseven_one_one_forty_nine :
    IsThaineAuxiliary 37 1 149 where
  ne_p := by decide
  cong_one_mod_p_pow := by decide

/-- **Existence (placeholder for Chebotarev)**: for any `p, n`, there
exists at least one Thaine auxiliary prime. Proved by Chebotarev density,
which guarantees infinitely many such primes. The full proof is deferred
to a refinement that invokes mathlib's Chebotarev infrastructure; for
now we record the existence as the interface contract. -/
def ThaineAuxiliaryExistence (p n : ℕ) : Prop :=
  ∃ ℓ : ℕ, ℓ.Prime ∧ IsThaineAuxiliary p n ℓ

/-- For the FLT37 setting (p = 37, n = 1), existence is witnessed by
ℓ = 149. -/
theorem thaineAuxiliaryExistence_thirtyseven_one :
    ThaineAuxiliaryExistence 37 1 :=
  ⟨149, by decide, isThaineAuxiliary_thirtyseven_one_one_forty_nine⟩

/-- **Generic Thaine-auxiliary existence via Dirichlet density**
(unconditional). For any prime `p` and any `n ≥ 1`, there exists a
prime ℓ ≠ p with `p^n ∣ ℓ - 1`. Proof: Dirichlet's theorem (mathlib's
`Nat.setOf_prime_and_eq_mod_infinite`) says the set of primes ℓ with
`(ℓ : ZMod (p^n)) = 1` is infinite, hence in particular non-empty;
moreover, `ℓ ≠ p` is automatic since `(p : ZMod (p^n)) = 0 ≠ 1` for any
prime `p` (since `p ∣ p^n` already, so `p ≡ 0` not `1` modulo `p^n`). -/
theorem thaineAuxiliaryExistence_of_prime
    (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ThaineAuxiliaryExistence p n := by
  haveI : NeZero (p ^ n) := ⟨(Nat.pow_pos hp.pos).ne'⟩
  have h_inf := Nat.infinite_setOf_prime_and_eq_mod (q := p ^ n) (a := 1) isUnit_one
  obtain ⟨ℓ, hℓ_prime, hℓ_cast⟩ := h_inf.nonempty
  refine ⟨ℓ, hℓ_prime, ?_, ?_⟩
  · -- ℓ ≠ p: from ℓ ≡ 1 (mod p^n), if ℓ = p then p^n ∣ (p - 1), but
    -- p^n ≥ p ≥ 2 and p - 1 ≥ 1, contradiction.
    intro h_eq
    rw [h_eq] at hℓ_cast
    have hp_pos : 1 ≤ p := hp.pos
    have h_sub_zero : ((p - 1 : ℕ) : ZMod (p ^ n)) = 0 := by
      have h_eq2 : ((p - 1 : ℕ) : ZMod (p ^ n)) = (p : ZMod (p ^ n)) - 1 := by
        rw [Nat.cast_sub hp_pos, Nat.cast_one]
      rw [h_eq2, hℓ_cast, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h_sub_zero
    -- h_sub_zero : p^n ∣ p - 1.
    have hp_two : 2 ≤ p := hp.two_le
    have h_pn_le : p ^ n ≤ p - 1 := Nat.le_of_dvd (by omega) h_sub_zero
    have h_p_le_pn : p ≤ p ^ n := Nat.le_self_pow (by omega : n ≠ 0) p
    omega
  · -- p^n ∣ ℓ - 1: from ℓ ≡ 1 (mod p^n) (i.e., (ℓ : ZMod p^n) = 1).
    have hℓ_pos : 1 ≤ ℓ := hℓ_prime.one_lt.le
    have h_sub_zero : ((ℓ - 1 : ℕ) : ZMod (p ^ n)) = 0 := by
      have h_eq : ((ℓ - 1 : ℕ) : ZMod (p ^ n)) = (ℓ : ZMod (p ^ n)) - 1 := by
        rw [Nat.cast_sub hℓ_pos, Nat.cast_one]
      rw [h_eq, hℓ_cast, sub_self]
    rwa [ZMod.natCast_eq_zero_iff] at h_sub_zero

/-- **Infinitude of Thaine-auxiliary primes** (unconditional). For any
prime `p` and any `n ≥ 1`, the set of primes ℓ with `IsThaineAuxiliary
p n ℓ` is infinite. Proof: the set of primes ℓ with `(ℓ : ZMod (p^n)) = 1`
is infinite by Dirichlet density, and removing the (at most one) prime
equal to `p` (which doesn't satisfy the congruence anyway, by the
argument in `thaineAuxiliaryExistence_of_prime`) leaves an infinite set. -/
theorem infinite_setOf_thaineAuxiliary
    (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    {ℓ : ℕ | ℓ.Prime ∧ IsThaineAuxiliary p n ℓ}.Infinite := by
  haveI : NeZero (p ^ n) := ⟨(Nat.pow_pos hp.pos).ne'⟩
  have h_inf := Nat.infinite_setOf_prime_and_eq_mod (q := p ^ n) (a := 1) isUnit_one
  -- The Dirichlet-density set is contained in our set (after the IsThaineAuxiliary unfolding).
  refine h_inf.mono ?_
  intro ℓ ⟨hℓ_prime, hℓ_cast⟩
  refine ⟨hℓ_prime, ⟨?_, ?_⟩⟩
  · -- ℓ ≠ p: contradiction argument as in `thaineAuxiliaryExistence_of_prime`.
    intro h_eq
    rw [h_eq] at hℓ_cast
    have hp_pos : 1 ≤ p := hp.pos
    have h_sub_zero : ((p - 1 : ℕ) : ZMod (p ^ n)) = 0 := by
      have h_eq2 : ((p - 1 : ℕ) : ZMod (p ^ n)) = (p : ZMod (p ^ n)) - 1 := by
        rw [Nat.cast_sub hp_pos, Nat.cast_one]
      rw [h_eq2, hℓ_cast, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h_sub_zero
    have hp_two : 2 ≤ p := hp.two_le
    have h_pn_le : p ^ n ≤ p - 1 := Nat.le_of_dvd (by omega) h_sub_zero
    have h_p_le_pn : p ≤ p ^ n := Nat.le_self_pow (by omega : n ≠ 0) p
    omega
  · -- p^n ∣ ℓ - 1 from (ℓ : ZMod p^n) = 1.
    have hℓ_pos : 1 ≤ ℓ := hℓ_prime.one_lt.le
    have h_sub_zero : ((ℓ - 1 : ℕ) : ZMod (p ^ n)) = 0 := by
      have h_eq : ((ℓ - 1 : ℕ) : ZMod (p ^ n)) = (ℓ : ZMod (p ^ n)) - 1 := by
        rw [Nat.cast_sub hℓ_pos, Nat.cast_one]
      rw [h_eq, hℓ_cast, sub_self]
    rwa [ZMod.natCast_eq_zero_iff] at h_sub_zero

end Thaine

end BernoulliRegular

end
