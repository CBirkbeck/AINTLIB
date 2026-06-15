module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot

/-!
# Canonical `pthSymbolAtPrime` and explicit Galois action

This file gives a *canonical* version of `pthSymbolAtPrime` that uses the
canonical primitive `p`-th root of unity `canonicalResidueZetaP q` instead of
`Classical.choose`. The canonical choice is Galois-equivariant in a precise
sense (see `canonicalResidueZetaP_val_galois_compat`), so the Galois-action
transformation of the residue symbol takes the explicit form

```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) = (a : ZMod p) * pthSymbolAtPrime_canonical α q.
```

This eliminates the opaque unit factor `c : (ZMod p)ˣ` that appears in the
existence-form `pthSymbolAtPrime_galoisAction_exists_unit`.

## Main definitions and theorems

* `pthSymbolAtPrime_canonical α q` — the residue symbol defined using the
  canonical primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`.
* `pthSymbolAtPrime_canonical_galoisAction` — the explicit Galois-action
  transformation with factor `(a : ZMod p)`.
* `pthSymbolAtPrime_eq_canonical_up_to_unit` — the canonical and
  `Classical.choose`-based versions agree up to a unit factor in `(ZMod p)ˣ`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Step 1 — units-level Galois compatibility

The compatibility statement
`canonicalResidueZetaP_val_galois_compat` is at the level of underlying ring
elements; lifting it to the level of units is mechanical via `Units.ext`. -/

/-- Units-level Galois compatibility: the image of the canonical residue zeta
at `q` under the unit-version of `cyclotomicGaloisQuotientEquiv` equals the
canonical residue zeta at `σ_a • q` raised to the `a.val` power (as a unit). -/
theorem canonicalResidueZetaP_units_galois_compat
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Units.mapEquiv
        ((cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q) :
          (𝓞 K ⧸ q) ≃* (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q))
        (canonicalResidueZetaP (p := p) (K := K) q) =
      (canonicalResidueZetaP (p := p) (K := K)
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)) ^ (a : ZMod p).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  apply Units.ext
  -- Reduce to underlying ring elements.
  change (cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q
      ((canonicalResidueZetaP (p := p) (K := K) q) : 𝓞 K ⧸ q) :
        𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) =
      ((canonicalResidueZetaP (p := p) (K := K)
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)) ^ (a : ZMod p).val :
            (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)ˣ).val
  rw [Units.val_pow_eq_pow_val]
  exact canonicalResidueZetaP_val_galois_compat a q

/-! ### Step 2 — `pthSymbolAtPrime_canonical` definition

Like `pthSymbolAtPrime`, this is `0` whenever the preconditions fail. In the
"good" case (`q ≠ ⊥`, maximal, `α ∉ q`, `p ∣ Nq − 1`, `(p : 𝓞 K) ∉ q`) it
equals `primeExponent` with the *canonical* primitive `p`-th root, eliminating
the `Classical.choose`. -/

/-- The canonical `p`-th-power residue symbol at a prime, using
`canonicalResidueZetaP q` as the primitive `p`-th root. The hypothesis
`(p : 𝓞 K) ∉ q` is what guarantees a primitive `p`-th root exists in the
residue field; if it fails the symbol is `0`. -/
noncomputable def pthSymbolAtPrime_canonical (α : 𝓞 K) (q : Ideal (𝓞 K)) :
    ZMod p := by
  classical
  by_cases hbot : q = ⊥
  · exact 0
  haveI : NeZero q := ⟨hbot⟩
  by_cases hmax : q.IsMaximal
  · by_cases hα : α ∈ q
    · exact 0
    by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
    · by_cases hp_in : (p : 𝓞 K) ∈ q
      · exact 0
      · haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        haveI : q.IsMaximal := hmax
        haveI : q.IsPrime := hmax.isPrime
        exact Reflection.ResidueSymbol.PowerResidue.primeExponent q
          (canonicalResidueZetaP (p := p) (K := K) q)
          (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
          hdiv α hα
    · exact 0
  · exact 0

/-- Symbol vanishes at the bottom ideal. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_eq_bot (α : 𝓞 K) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α (⊥ : Ideal (𝓞 K)) = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_pos rfl]

/-- Symbol vanishes when `α ∈ q`. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_mem
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∈ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_pos hmax, dif_pos hα]

/-- Symbol vanishes when `(p : 𝓞 K) ∈ q`. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_p_mem
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∈ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_pos hmax, dif_neg hα, dif_pos hdiv, dif_pos hp_in]

/-- Symbol vanishes for non-maximal `q ≠ ⊥`. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal
    (α : 𝓞 K) {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : ¬ q.IsMaximal) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_neg hmax]

/-- Symbol vanishes when `p ∤ Nq − 1`. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_not_dvd
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : ¬ p ∣ Fintype.card (𝓞 K ⧸ q) - 1) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_pos hmax, dif_neg hα, dif_neg hdiv]

/-- Symbol vanishes unconditionally at a nonzero maximal prime containing
`(p)`. If the numerator lies in the prime this is the usual numerator-zero
case; otherwise the definition reaches either the non-divisibility branch or
the explicit `(p) ∈ q` branch. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_p_mem_uncond
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hp_in : (p : 𝓞 K) ∈ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  by_cases hα : α ∈ q
  · exact pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα
  by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
  · exact pthSymbolAtPrime_canonical_eq_zero_of_p_mem hbot hmax hα hdiv hp_in
  · exact pthSymbolAtPrime_canonical_eq_zero_of_not_dvd hbot hmax hα hdiv

/-- **Symbol vanishes at primes with `Ideal.absNorm q = p`.** For any prime
ideal `q` of `𝓞 K` whose absolute norm equals `p`, the canonical symbol
vanishes at every `α ∉ q`. The hypothesis `Ideal.absNorm q = p` gives
`Fintype.card (𝓞 K ⧸ q) = p`, hence `p ∤ p - 1` (a basic prime fact),
which feeds `pthSymbolAtPrime_canonical_eq_zero_of_not_dvd`.

In cyclotomic `K = ℚ(ζ_p)`, the unique prime `λ = (1 - ζ_p)` above `p`
has `Nλ = p`, so this discharges the symbol at `λ` unconditionally on `α`
(modulo `α ∉ λ`, which is automatic for hyperprimary η). -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_absNorm_eq_p
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q)
    (hN : Ideal.absNorm q = p) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  refine pthSymbolAtPrime_canonical_eq_zero_of_not_dvd hbot hmax hα ?_
  -- Goal: ¬ p ∣ Fintype.card (𝓞 K ⧸ q) - 1.
  -- From `Ideal.absNorm q = p`, `Fintype.card (𝓞 K ⧸ q) = p`, so `... - 1 = p - 1`.
  -- Then `p ∤ p - 1` since `p ≥ 2`.
  have hp_prime : p.Prime := Fact.out
  have h_card : Fintype.card (𝓞 K ⧸ q) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [h_card]
  intro hp_div
  -- `p ∣ p - 1` in ℕ-truncated subtraction. For `p ≥ 2`, `p - 1 < p`, so `p ∣ p - 1`
  -- forces `p - 1 = 0`, i.e., `p = 1`, contradicting primality.
  have hp_le : p ≤ p - 1 := Nat.le_of_dvd (by
    rcases Nat.eq_zero_or_pos (p - 1) with h0 | hpos
    · -- p - 1 = 0 means p ≤ 1. Combined with p ≥ 2 from primality, contradiction.
      exfalso
      have hp_ge_two : 2 ≤ p := hp_prime.two_le
      omega
    · exact hpos) hp_div
  have hp_ge_two : 2 ≤ p := hp_prime.two_le
  omega

/-- Symbol vanishes unconditionally at a nonzero maximal prime of absolute
norm `p`. If the numerator belongs to the prime this is immediate; otherwise
use the norm-`p` non-divisibility branch. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_absNorm_eq_p_uncond
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hN : Ideal.absNorm q = p) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  by_cases hα : α ∈ q
  · exact pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα
  · exact pthSymbolAtPrime_canonical_eq_zero_of_absNorm_eq_p hbot hmax hα hN

/-- In the "good" case (all preconditions met, including `(p : 𝓞 K) ∉ q`),
the canonical symbol unfolds to `primeExponent` with the canonical zeta. -/
theorem pthSymbolAtPrime_canonical_eq_primeExponent
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : NeZero q := ⟨hbot⟩
    haveI : q.IsMaximal := hmax
    haveI : q.IsPrime := hmax.isPrime
    pthSymbolAtPrime_canonical (p := p) (K := K) α q =
      Reflection.ResidueSymbol.PowerResidue.primeExponent q
        (canonicalResidueZetaP (p := p) (K := K) q)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in) hdiv α hα := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_pos hmax, dif_neg hα, dif_pos hdiv, dif_neg hp_in]

/-! ### Step 2b — algebraic API: `_one`, `_mul`, `_pow`, `_pow_p_eq_zero`

Mirrors the API for non-canonical `pthSymbolAtPrime` (`_one`, `_mul`, `_pow`,
`_pow_p_eq_zero`). The canonical version is well-behaved for the same reasons:
in the bad branches everything is `0`; in the good branch the same canonical
ζ is used for both sides, so the lemmas reduce to `primeExponent_one`,
`primeExponent_mul`, `primeExponent_pow` from `Reflection/ResidueSymbol/Basic.lean`. -/

/-- **Residue-is-p-th-power ⟹ symbol vanishes**: when the residue of `α`
in `(𝓞 K / q)ˣ` is a p-th power, the canonical p-th-power residue symbol
vanishes. This is the local residue-field statement used when a numerator is
known to be a local `p`-th power at the relevant prime. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_residue_isPow
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∉ q)
    (h_pow : ∃ y : (𝓞 K ⧸ q)ˣ,
      Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα = y ^ p) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  haveI hmax' : q.IsMaximal := hmax
  haveI : q.IsPrime := hmax.isPrime
  letI : Field (𝓞 K ⧸ q) := Ideal.Quotient.field q
  rw [pthSymbolAtPrime_canonical_eq_primeExponent hbot hmax hα hdiv hp_in]
  unfold Reflection.ResidueSymbol.PowerResidue.primeExponent
  exact Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent_eq_zero_of_isPow
    _ (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in) hdiv h_pow

/-- Multiplicativity of the canonical residue symbol in `α`. For `q` a maximal
non-zero ideal of `𝓞 K` and `α, β ∉ q`, the canonical symbol satisfies
`pthSymbolAtPrime_canonical (α * β) q =
  pthSymbolAtPrime_canonical α q + pthSymbolAtPrime_canonical β q`. -/
theorem pthSymbolAtPrime_canonical_mul
    {α β : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) (hβ : β ∉ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (α * β) q =
      pthSymbolAtPrime_canonical (p := p) (K := K) α q +
        pthSymbolAtPrime_canonical (p := p) (K := K) β q := by
  haveI : NeZero q := ⟨hbot⟩
  haveI hqK_prime : q.IsPrime := hmax.isPrime
  have hαβ : α * β ∉ q := fun h => (hqK_prime.mem_or_mem h).elim hα hβ
  simp only [pthSymbolAtPrime_canonical, dif_neg hbot, dif_pos hmax, dif_neg hαβ,
    dif_neg hα, dif_neg hβ]
  split_ifs with hdiv hp_in
  · simp
  · -- Good case: apply primeExponent_mul.
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : q.IsMaximal := hmax
    exact Reflection.ResidueSymbol.PowerResidue.primeExponent_mul q
      (canonicalResidueZetaP (p := p) (K := K) q)
      (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
      hdiv hα hβ hαβ
  · simp

/-- The canonical symbol vanishes at `1`. Follows from multiplicativity:
`s(1·1) = s(1) + s(1)` forces `s(1) = 0`. -/
theorem pthSymbolAtPrime_canonical_one
    {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (1 : 𝓞 K) q = 0 := by
  haveI hqp : q.IsPrime := hmax.isPrime
  have h1 : (1 : 𝓞 K) ∉ q := hqp.one_notMem
  have h := pthSymbolAtPrime_canonical_mul (p := p) (K := K)
    (α := (1 : 𝓞 K)) (β := 1) hbot hmax h1 h1
  rw [one_mul] at h
  linear_combination -h

/-- The canonical symbol of `α^n` is `n · symbol α q` in `ZMod p`. By induction
using `pthSymbolAtPrime_canonical_mul`. -/
theorem pthSymbolAtPrime_canonical_pow
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) (n : ℕ) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (α ^ n) q =
      (n : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  haveI hqp : q.IsPrime := hmax.isPrime
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact pthSymbolAtPrime_canonical_one (p := p) (K := K) hbot hmax
  | succ k ih =>
    have hpow : α ^ k ∉ q := fun h => hα (hqp.mem_of_pow_mem k h)
    rw [pow_succ, pthSymbolAtPrime_canonical_mul (p := p) (K := K) hbot hmax hpow hα,
      ih]
    push_cast; ring

/-- **Unconditional vanishing at `α^p`** (any prime ideal): the canonical
symbol of any `p`-th-power input vanishes in `ZMod p`, regardless of
whether `α ∈ q` or `q` is maximal. Cases:
* `q = ⊥`: symbol = 0.
* `q ≠ ⊥` not maximal: symbol = 0.
* `q` maximal, `α ∈ q`: `α^p ∈ q`, symbol = 0 by in-prime vanishing.
* `q` maximal, `α ∉ q`: `(p : ZMod p) = 0` via the multiplicative form. -/
theorem pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond
    (α : 𝓞 K) (q : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (α ^ p) q = 0 := by
  by_cases hbot : q = ⊥
  · subst hbot; exact pthSymbolAtPrime_canonical_eq_zero_of_eq_bot _
  by_cases hmax : q.IsMaximal
  · by_cases hα : α ∈ q
    · -- α ∈ q ⟹ α^p ∈ q, vanishing by in-prime case.
      have hα_pow : α ^ p ∈ q := by
        have hp_pos : 0 < p := (Fact.out : p.Prime).pos
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0) with ⟨k, hk⟩
        rw [hk, pow_succ]
        exact Ideal.mul_mem_left _ _ hα
      exact pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα_pow
    · -- α ∉ q: existing lemma applies.
      rw [pthSymbolAtPrime_canonical_pow (p := p) (K := K) hbot hmax hα p,
        ZMod.natCast_self, zero_mul]
  · exact pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax

/-- **Vanishing at a `p`-th power.** The canonical symbol of any `p`-th-power
input is `0` in `ZMod p`, since `(p : ZMod p) = 0`. -/
theorem pthSymbolAtPrime_canonical_pow_p_eq_zero
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (α ^ p) q = 0 := by
  rw [pthSymbolAtPrime_canonical_pow (p := p) (K := K) hbot hmax hα p,
    ZMod.natCast_self, zero_mul]

/-! ### Step 2c — bidirectional vanishing iff and congruence helpers -/

/-- The canonical symbol equals `0` iff in the "good case" (all preconditions
met) the underlying `primeExponent` is `0`. The "good case" itself is the
conjunction of the five preconditions; outside of it, the symbol is `0` by
definition. -/
theorem pthSymbolAtPrime_canonical_eq_zero_iff
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : NeZero q := ⟨hbot⟩
    haveI : q.IsMaximal := hmax
    haveI : q.IsPrime := hmax.isPrime
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 ↔
      Reflection.ResidueSymbol.PowerResidue.primeExponent q
        (canonicalResidueZetaP (p := p) (K := K) q)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in) hdiv α hα = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  rw [pthSymbolAtPrime_canonical_eq_primeExponent hbot hmax hα hdiv hp_in]

/-- In the good case, canonical symbol-vanishing is equivalent to the residue
class of the numerator being a `p`-th power in the residue field. -/
theorem pthSymbolAtPrime_canonical_eq_zero_iff_residue_isPow
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∉ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 ↔
      ∃ y : (𝓞 K ⧸ q)ˣ,
        Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα = y ^ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  haveI hmax' : q.IsMaximal := hmax
  haveI : q.IsPrime := hmax.isPrime
  letI : Field (𝓞 K ⧸ q) := Ideal.Quotient.field q
  rw [pthSymbolAtPrime_canonical_eq_zero_iff hbot hmax hα hdiv hp_in]
  change
    Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
        (canonicalResidueZetaP (p := p) (K := K) q)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
        hdiv
        (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα) = 0 ↔
      ∃ y : (𝓞 K ⧸ q)ˣ,
        Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα = y ^ p
  exact Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent_eq_zero_iff_isPow
    (canonicalResidueZetaP (p := p) (K := K) q)
    (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
    hdiv (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα)

/-- If the canonical symbol vanishes in the good case, then the residue class of
the numerator is a `p`-th power in the residue field. -/
theorem residue_isPow_of_pthSymbolAtPrime_canonical_eq_zero
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∉ q)
    (h : pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0) :
    ∃ y : (𝓞 K ⧸ q)ˣ,
      Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα = y ^ p :=
  (pthSymbolAtPrime_canonical_eq_zero_iff_residue_isPow
    hbot hmax hα hdiv hp_in).mp h

/-- Congruence: equal arguments give equal symbols. (A `congr`-style helper for
when the equality is non-definitional.) -/
theorem pthSymbolAtPrime_canonical_eq_of_eq
    {α α' : 𝓞 K} {q q' : Ideal (𝓞 K)} (hα : α = α') (hq : q = q') :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q =
      pthSymbolAtPrime_canonical (p := p) (K := K) α' q' := by
  subst hα; subst hq; rfl

/-! ### Step 3 — explicit Galois action

The canonical zeta is Galois-equivariant up to a `(.val)`-power exponent
(`canonicalResidueZetaP_val_galois_compat`). Combined with
`primeExponent_ringEquiv` and `primeExponent_zeta_pow`, this gives the
explicit form:

```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) = (a : ZMod p) * pthSymbolAtPrime_canonical α q.
```

The proof is the chain
`primeExponent σq canonicalZetaSigmaQ (σα) =`
`(a.val : ZMod p) * primeExponent σq (canonicalZetaSigmaQ^a.val) (σα)`
`  [primeExponent_zeta_pow]`
`= (a.val : ZMod p) * primeExponent σq (Units.mapEquiv σ_q canonicalZetaQ) (σα)`
`  [units_galois_compat]`
`= (a.val : ZMod p) * primeExponent q canonicalZetaQ α [primeExponent_ringEquiv]`. -/

/-- **Explicit Galois action of `pthSymbolAtPrime_canonical`.**

For `α ∈ 𝓞 K`, `q ⊂ 𝓞 K` a non-`⊥` maximal ideal with `α ∉ q` and
`(p : 𝓞 K) ∉ q`, and `a` a Galois automorphism, the canonical residue
symbol satisfies the explicit transformation

```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) = (a : ZMod p) * pthSymbolAtPrime_canonical α q.
```

The factor `(a : ZMod p)` is the genuine cyclotomic-character value, in
contrast to the opaque unit factor `c : (ZMod p)ˣ` that appears in the
existence-form `pthSymbolAtPrime_galoisAction_exists_unit`. -/
theorem pthSymbolAtPrime_canonical_galoisAction
    (a : CyclotomicUnitDelta p) (α : 𝓞 K)
    {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a q) =
      (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  classical
  haveI hp_ne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  haveI hbot_q' : NeZero (cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
    ⟨cyclotomicGaloisConjugate_ne_bot a hbot⟩
  haveI hmax_q' :
      (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal :=
    cyclotomicGaloisConjugate_isMaximal a q
  haveI hprime_q' : (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsPrime :=
    hmax_q'.isPrime
  haveI hprime_q : q.IsPrime := hmax.isPrime
  -- σ_a α ∉ σ_a • q.
  have hα' : cyclotomicRingOfIntegersEquiv (p := p) K a α ∉
      cyclotomicGaloisConjugate (p := p) (K := K) a q :=
    (notMem_cyclotomicGaloisConjugate_iff a).mpr hα
  -- σ_a • q ≠ ⊥.
  have hbot_q'_ne : cyclotomicGaloisConjugate (p := p) (K := K) a q ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hbot
  -- (p : 𝓞 K) ∉ σ_a • q (uses fixedness of ℕ-cast under σ_a).
  have hp_in' : (p : 𝓞 K) ∉ cyclotomicGaloisConjugate (p := p) (K := K) a q := by
    intro hp_in_conj
    apply hp_in
    have h_fix : cyclotomicRingOfIntegersEquiv (p := p) K a (p : 𝓞 K) = (p : 𝓞 K) := by
      change (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom (p : 𝓞 K) = (p : 𝓞 K)
      rw [map_natCast]
    rw [← h_fix] at hp_in_conj
    exact (mem_cyclotomicGaloisConjugate_iff a).mp hp_in_conj
  -- |𝓞K/σq| = |𝓞K/q|, hence p divides also at σq.
  have h_card_q'q :
      Fintype.card
        (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) =
        Fintype.card (𝓞 K ⧸ q) :=
    cyclotomicGaloisConjugate_quotient_card_eq a hbot
  have hdiv' : p ∣ Fintype.card
      (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) - 1 := by
    rw [h_card_q'q]; exact hdiv
  -- Unfold both sides via good-case lemmas.
  rw [pthSymbolAtPrime_canonical_eq_primeExponent hbot_q'_ne hmax_q' hα' hdiv' hp_in']
  rw [pthSymbolAtPrime_canonical_eq_primeExponent hbot hmax hα hdiv hp_in]
  -- Now both sides are concrete `primeExponent` values.
  -- Define abbreviations.
  set ζq : (𝓞 K ⧸ q)ˣ := canonicalResidueZetaP (p := p) (K := K) q
  set ζσq : (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)ˣ :=
    canonicalResidueZetaP (p := p) (K := K)
      (cyclotomicGaloisConjugate (p := p) (K := K) a q)
  have hζq : IsPrimitiveRoot ζq p :=
    canonicalResidueZetaP_isPrimitiveRoot hbot hp_in
  have hζσq : IsPrimitiveRoot ζσq p :=
    canonicalResidueZetaP_isPrimitiveRoot hbot_q'_ne hp_in'
  -- The mul-equiv induced by σ_a on quotients.
  set φ_mul : (𝓞 K ⧸ q) ≃*
      (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
    (cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q).toMulEquiv
  -- σ_a-image of canonicalZetaQ as a unit.
  set ζq_img : (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)ˣ :=
    Units.mapEquiv φ_mul ζq
  -- The image is a primitive p-th root.
  have hζq_img : IsPrimitiveRoot ζq_img p :=
    hζq.map_of_injective
      (Units.map_injective
        (f := ((cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q) :
            (𝓞 K ⧸ q) →* (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)))
        (cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q).injective)
  -- Step (a): primeExponent_ringEquiv: exponent at σq with ζq_img on (σα)
  --                                = exponent at q with ζq on α.
  have h_ringEquiv :
      Reflection.ResidueSymbol.PowerResidue.primeExponent
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)
          ζq_img hζq_img hdiv'
          (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' =
      Reflection.ResidueSymbol.PowerResidue.primeExponent q ζq hζq hdiv α hα :=
    primeExponent_ringEquiv (p := p) (R := 𝓞 K)
      (q := q) (q' := cyclotomicGaloisConjugate (p := p) (K := K) a q)
      (cyclotomicRingOfIntegersEquiv (p := p) K a) rfl
      h_card_q'q hζq hdiv hdiv' α hα hα'
  -- Step (b): the σ_a-image equals canonicalZeta_σq^a.val.
  have h_compat : ζq_img = ζσq ^ (a : ZMod p).val :=
    canonicalResidueZetaP_units_galois_compat a q
  -- Step (c): primeExponent_zeta_pow: a.val * exponent at σq with (ζσq^a.val)
  --                                 = exponent at σq with ζσq.
  -- ζσq^a.val is a primitive p-th root because (a.val).Coprime p (a is a unit).
  have ha_val_cop : ((a : ZMod p).val).Coprime p := by
    have hp_prime : Nat.Prime p := Fact.out
    rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
    intro h_dvd
    -- p ∣ a.val ⟹ a.val = 0 (since a.val < p)
    have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
    have ha_zero : (a : ZMod p).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt h_dvd ha_lt
    -- But a.val = 0 ⟹ (a : ZMod p) = 0, contradicting unitness.
    have ha_cast : ((a : ZMod p).val : ZMod p) = (a : ZMod p) :=
      ZMod.natCast_zmod_val (a : ZMod p)
    rw [ha_zero] at ha_cast
    push_cast at ha_cast
    exact a.isUnit.ne_zero ha_cast.symm
  have hζσq_pow : IsPrimitiveRoot (ζσq ^ (a : ZMod p).val) p :=
    hζσq.pow_of_coprime _ ha_val_cop
  have h_zetaPow :
      ((a : ZMod p).val : ZMod p) *
        Reflection.ResidueSymbol.PowerResidue.primeExponent
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)
          (ζσq ^ (a : ZMod p).val) hζσq_pow hdiv'
          (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' =
      Reflection.ResidueSymbol.PowerResidue.primeExponent
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)
          ζσq hζσq hdiv'
          (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' :=
    Reflection.ResidueSymbol.PowerResidue.primeExponent_zeta_pow
      _ hζσq hdiv' hζσq_pow _ hα'
  -- Now substitute h_compat into h_ringEquiv to get a statement involving
  -- ζσq ^ a.val on the LHS (matching h_zetaPow). Proof-irrelevant `congr`
  -- absorbs the change in `IsPrimitiveRoot` proof.
  have h_ringEquiv' :
      Reflection.ResidueSymbol.PowerResidue.primeExponent
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)
          (ζσq ^ (a : ZMod p).val) hζσq_pow hdiv'
          (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' =
      Reflection.ResidueSymbol.PowerResidue.primeExponent q ζq hζq hdiv α hα := by
    have h_re := h_ringEquiv
    revert hζq_img h_re
    rw [h_compat]
    intros
    congr 1
  -- Combine: substitute h_ringEquiv' into h_zetaPow.
  rw [h_ringEquiv'] at h_zetaPow
  -- h_zetaPow : (a.val : ZMod p) * primeExponent q ζq α =
  --             primeExponent σq ζσq (σα).
  -- Goal: primeExponent σq ζσq (σα) = (a : ZMod p) * primeExponent q ζq α.
  rw [← h_zetaPow]
  -- Just need (a.val : ZMod p) = (a : ZMod p).
  congr 1
  exact ZMod.natCast_zmod_val (a : ZMod p)

/-! ### Step 3b — corollaries of the explicit Galois action

Variants and consequences of `pthSymbolAtPrime_canonical_galoisAction`:
* `_galoisAction_iff` — the equation is an iff (one of three equivalent forms).
* `_galoisAction_one` — at the identity element of the Galois group, the action
  is trivial: it amounts to `pthSymbolAtPrime_canonical α q`.
* `_compose_galois` — composing two Galois actions multiplies the factors.
-/

/-- **Equivalent "subtraction form" of the Galois action equation.**

The Galois transformation `symbol(σα, σq) = a · symbol(α, q)` is logically
equivalent to its `_ - _ = 0` form `symbol(σα, σq) - a · symbol(α, q) = 0`,
which is sometimes more convenient for combining with other vanishing
identities. -/
theorem pthSymbolAtPrime_canonical_galoisAction_iff
    (a : CyclotomicUnitDelta p) (α : 𝓞 K) (q : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a q) =
      (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α q ↔
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a q) -
      (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 :=
  ⟨fun h => by rw [h, sub_self], fun h => by linear_combination h⟩

/-- **The identity Galois element acts trivially.**

For the unit `1 ∈ CyclotomicUnitDelta p`, both sides of the Galois action
equation reduce to `pthSymbolAtPrime_canonical α q`: the LHS via
`cyclotomicGaloisConjugate_one` and `cyclotomicRingOfIntegersEquiv_one_apply`,
the RHS via `(1 : ZMod p) * x = x`. -/
theorem pthSymbolAtPrime_canonical_galoisAction_one (α : 𝓞 K)
    {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K (1 : CyclotomicUnitDelta p) α)
        (cyclotomicGaloisConjugate (p := p) (K := K)
          (1 : CyclotomicUnitDelta p) q) =
      pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  have h := pthSymbolAtPrime_canonical_galoisAction (p := p) (K := K)
    (1 : CyclotomicUnitDelta p) α hbot hmax hα hp_in hdiv
  -- `(1 : CyclotomicUnitDelta p) → (ZMod p)` evaluates to `1`.
  have h1 : ((1 : CyclotomicUnitDelta p) : ZMod p) = 1 := by
    push_cast
    rfl
  rw [h1, one_mul] at h
  exact h

/-- **Composition of two Galois actions multiplies the factors.**

For `a, b ∈ CyclotomicUnitDelta p` and a "good" pair `(α, q)`, applying
`σ_a` after `σ_b` to both arguments multiplies the symbol by `(a * b : ZMod p)`.
This is just two applications of `pthSymbolAtPrime_canonical_galoisAction`,
combined via `cyclotomicRingOfIntegersEquiv_mul_apply` and
`cyclotomicGaloisConjugate_mul`. -/
theorem pthSymbolAtPrime_canonical_compose_galois
    (a b : CyclotomicUnitDelta p) (α : 𝓞 K)
    {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a
          (cyclotomicRingOfIntegersEquiv (p := p) K b α))
        (cyclotomicGaloisConjugate (p := p) (K := K) a
          (cyclotomicGaloisConjugate (p := p) (K := K) b q)) =
      (a : ZMod p) * (b : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  -- Compatibility witnesses for the inner application of (b, q).
  haveI hp_ne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hbot_b : cyclotomicGaloisConjugate (p := p) (K := K) b q ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot b hbot
  have hmax_b : (cyclotomicGaloisConjugate (p := p) (K := K) b q).IsMaximal :=
    cyclotomicGaloisConjugate_isMaximal b q
  have hα_b : cyclotomicRingOfIntegersEquiv (p := p) K b α ∉
      cyclotomicGaloisConjugate (p := p) (K := K) b q :=
    (notMem_cyclotomicGaloisConjugate_iff b).mpr hα
  -- Card preservation, hence divisibility.
  have h_card_b :
      Fintype.card (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) b q) =
        Fintype.card (𝓞 K ⧸ q) :=
    cyclotomicGaloisConjugate_quotient_card_eq b hbot
  have hdiv_b : p ∣ Fintype.card
      (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) b q) - 1 := by
    rw [h_card_b]; exact hdiv
  -- `(p : 𝓞 K) ∉ σ_b • q`, by fixedness of ℕ-cast under σ_b.
  have hp_in_b : (p : 𝓞 K) ∉ cyclotomicGaloisConjugate (p := p) (K := K) b q := by
    intro h_in
    apply hp_in
    have h_fix : cyclotomicRingOfIntegersEquiv (p := p) K b (p : 𝓞 K) =
        (p : 𝓞 K) := by
      change (cyclotomicRingOfIntegersEquiv (p := p) K b).toRingHom (p : 𝓞 K) =
        (p : 𝓞 K)
      rw [map_natCast]
    rw [← h_fix] at h_in
    exact (mem_cyclotomicGaloisConjugate_iff b).mp h_in
  -- Apply the Galois action with `a` to `(σ_b α, σ_b • q)`.
  have h_a := pthSymbolAtPrime_canonical_galoisAction (p := p) (K := K)
    a (cyclotomicRingOfIntegersEquiv (p := p) K b α)
    hbot_b hmax_b hα_b hp_in_b hdiv_b
  -- Apply the Galois action with `b` to `(α, q)`.
  have h_b := pthSymbolAtPrime_canonical_galoisAction (p := p) (K := K)
    b α hbot hmax hα hp_in hdiv
  -- Substitute h_b into h_a.
  rw [h_b, ← mul_assoc] at h_a
  exact h_a

/-! ### Step 4 — compatibility with `pthSymbolAtPrime`

The canonical and `Classical.choose`-based versions agree up to a unit factor
in `(ZMod p)ˣ`. Concretely: `Classical.choose hroot` is some primitive `p`-th
root of unity in `(𝓞 K ⧸ q)ˣ`, and `canonicalResidueZetaP q` is another. By
`IsPrimitiveRoot.isPrimitiveRoot_iff'` the two differ by an `n`-th power for
some `n.Coprime p`, and the residue exponents are related by multiplication
by `(n : ZMod p)`. -/

/-- Compatibility: when both `pthSymbolAtPrime` and
`pthSymbolAtPrime_canonical` are in the "good" case (preconditions met,
including `(p : 𝓞 K) ∉ q`), they agree up to a unit factor in `(ZMod p)ˣ`. -/
theorem pthSymbolAtPrime_eq_canonical_up_to_unit
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1) :
    ∃ c : (ZMod p)ˣ,
      pthSymbolAtPrime (p := p) α q =
        c.val * pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  classical
  haveI hp_ne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  haveI : q.IsMaximal := hmax
  haveI : q.IsPrime := hmax.isPrime
  -- The good-case unfolding of `pthSymbolAtPrime` requires a primitive root.
  have hroot : ∃ ζ : (𝓞 K ⧸ q)ˣ, IsPrimitiveRoot ζ p :=
    exists_isPrimitiveRoot_of_not_mem_p hbot hp_in
  -- Unfold pthSymbolAtPrime_canonical via the good-case lemma.
  rw [pthSymbolAtPrime_canonical_eq_primeExponent hbot hmax hα hdiv hp_in]
  -- Unfold pthSymbolAtPrime via its good-case branches.
  unfold pthSymbolAtPrime
  rw [dif_neg hbot, dif_pos hmax, dif_neg hα, dif_pos hdiv, dif_pos hroot]
  -- Now: (Classical.choose hroot) is a primitive p-th root, and
  -- canonicalResidueZetaP q is another. They differ by an n-th power
  -- for some n.Coprime p.
  set ζ_class : (𝓞 K ⧸ q)ˣ := hroot.choose with hζ_class_def
  set ζ_canon : (𝓞 K ⧸ q)ˣ := canonicalResidueZetaP (p := p) (K := K) q
    with hζ_canon_def
  have hζ_class : IsPrimitiveRoot ζ_class p := hroot.choose_spec
  have hζ_canon : IsPrimitiveRoot ζ_canon p :=
    canonicalResidueZetaP_isPrimitiveRoot hbot hp_in
  -- Get n such that ζ_class = ζ_canon ^ n with n.Coprime p.
  obtain ⟨n, hn_lt, hn_cop, hn_eq⟩ :=
    (hζ_canon.isPrimitiveRoot_iff' (k := p)).mp hζ_class
  have hn_unit : IsUnit ((n : ZMod p)) := by
    rw [ZMod.isUnit_iff_coprime]; exact hn_cop
  -- The factor `c` is `(n : ZMod p)⁻¹`. Reasoning:
  -- `primeExponent_zeta_pow` says
  --   `(n : ZMod p) * primeExponent (ζ_canon^n) ... = primeExponent ζ_canon ...`.
  -- Since `ζ_class = ζ_canon^n`, the LHS factor `primeExponent (ζ_canon^n) ...`
  -- agrees with `primeExponent ζ_class ...` (proof-irrelevant), so
  --   `(n : ZMod p) * primeExponent ζ_class ... = primeExponent ζ_canon ...`.
  -- Hence `primeExponent ζ_class ... = (n : ZMod p)⁻¹ * primeExponent ζ_canon ...`.
  refine ⟨hn_unit.unit⁻¹, ?_⟩
  -- ζ_canon^n is a primitive p-th root.
  have hζ_pow : IsPrimitiveRoot (ζ_canon ^ n) p :=
    hζ_canon.pow_of_coprime _ hn_cop
  -- Apply primeExponent_zeta_pow.
  have h_pow_eq :
      (n : ZMod p) *
        Reflection.ResidueSymbol.PowerResidue.primeExponent q
          (ζ_canon ^ n) hζ_pow hdiv α hα =
      Reflection.ResidueSymbol.PowerResidue.primeExponent q
          ζ_canon hζ_canon hdiv α hα :=
    Reflection.ResidueSymbol.PowerResidue.primeExponent_zeta_pow
      _ hζ_canon hdiv hζ_pow α hα
  -- Use ζ_class = ζ_canon^n (i.e., hn_eq : ζ_canon^n = ζ_class) to swap into
  -- ζ_class form. The IsPrimitiveRoot proof is propositionally irrelevant
  -- once the value is fixed.
  have h_swap :
      Reflection.ResidueSymbol.PowerResidue.primeExponent q
          (ζ_canon ^ n) hζ_pow hdiv α hα =
      Reflection.ResidueSymbol.PowerResidue.primeExponent q
          ζ_class hζ_class hdiv α hα := by
    revert hζ_pow
    rw [hn_eq]
    intros
    congr 1
  rw [h_swap] at h_pow_eq
  -- h_pow_eq : (n : ZMod p) * primeExponent ζ_class ... = primeExponent ζ_canon ...
  -- Goal:      primeExponent ζ_class ... = (hn_unit.unit⁻¹).val * primeExponent ζ_canon ...
  have hc_val : (hn_unit.unit⁻¹).val = ((n : ZMod p))⁻¹ := by
    have : (hn_unit.unit⁻¹).val * hn_unit.unit.val = 1 := hn_unit.unit.inv_val
    have hu_val : hn_unit.unit.val = (n : ZMod p) := rfl
    rw [hu_val] at this
    exact eq_inv_of_mul_eq_one_left this
  rw [hc_val]
  have hn_ne_zero : ((n : ZMod p)) ≠ 0 := hn_unit.ne_zero
  rw [eq_inv_mul_iff_mul_eq₀ hn_ne_zero]
  linear_combination h_pow_eq

/-! ### Step 5 — vanishing-bridge lemmas between the two versions

When `pthSymbolAtPrime_canonical α q = 0`, the corresponding
`pthSymbolAtPrime α q = 0` as well (via the unit factor `c`), and conversely
since the unit factor is invertible. These bridge "vanishing on the canonical
side" and "vanishing on the non-canonical side" without needing to know what
the unit factor is. -/

/-- **Vanishing transfers from canonical to non-canonical.**

If `pthSymbolAtPrime_canonical α q = 0` (in the good case), then
`pthSymbolAtPrime α q = 0` too, by the multiplicative compatibility. -/
theorem pthSymbolAtPrime_eq_zero_of_canonical_eq_zero
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (h : pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0) :
    pthSymbolAtPrime (p := p) α q = 0 := by
  obtain ⟨c, hc⟩ := pthSymbolAtPrime_eq_canonical_up_to_unit
    hbot hmax hα hp_in hdiv
  rw [hc, h, mul_zero]

/-- **Vanishing transfers from non-canonical to canonical.**

The reverse implication: since the unit factor `c` is invertible,
`pthSymbolAtPrime α q = 0` forces `pthSymbolAtPrime_canonical α q = 0`. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_pthSymbolAtPrime_eq_zero
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (h : pthSymbolAtPrime (p := p) α q = 0) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  obtain ⟨c, hc⟩ := pthSymbolAtPrime_eq_canonical_up_to_unit
    hbot hmax hα hp_in hdiv
  rw [hc] at h
  -- `c.val * x = 0` and `c.val` is a unit ⟹ `x = 0`.
  have hc_ne : c.val ≠ 0 := c.ne_zero
  exact (mul_eq_zero.mp h).resolve_left hc_ne

/-- **Vanishing iff between the two versions.** Combines both transfer
directions. -/
theorem pthSymbolAtPrime_canonical_eq_zero_iff_pthSymbolAtPrime_eq_zero
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 ↔
      pthSymbolAtPrime (p := p) α q = 0 :=
  ⟨pthSymbolAtPrime_eq_zero_of_canonical_eq_zero hbot hmax hα hp_in hdiv,
    pthSymbolAtPrime_canonical_eq_zero_of_pthSymbolAtPrime_eq_zero
      hbot hmax hα hp_in hdiv⟩

end Furtwaengler

end BernoulliRegular
