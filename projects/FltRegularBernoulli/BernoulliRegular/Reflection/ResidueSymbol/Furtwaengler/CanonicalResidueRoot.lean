module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Int

/-!
# Canonical primitive `p`-th root of unity in `(𝓞 K ⧸ q)ˣ`

For `K = ℚ(ζ_p)` cyclotomic and a maximal ideal `q ⊂ 𝓞 K` with
`(p : 𝓞 K) ∉ q`, the canonical primitive `p`-th root of unity in
`(𝓞 K ⧸ q)ˣ` is the residue of the canonical primitive `p`-th root
`cyclotomicZetaInteger K ∈ 𝓞 K`.

This avoids the `Classical.choose` obstacle in
`pthSymbolAtPrime`: the canonical choice is fixed by the cyclotomic
Galois action, hence the c.2 transformation
`pthSymbolAtPrime (σ_a α) (σ_a • q) = ? · pthSymbolAtPrime α q`
has unit factor `c = 1` unconditionally.

## Main definitions and theorems

* `canonicalResidueZetaP q hp_in_q` — the canonical primitive `p`-th
  root in `(𝓞 K ⧸ q)ˣ`, defined when `(p : 𝓞 K) ∉ q` (and `q` maximal).
* `canonicalResidueZetaP_isPrimitiveRoot` — primitivity: it is a
  primitive `p`-th root of unity.
* `cyclotomicRingOfIntegersEquiv_apply_zetaInteger` — Galois compatibility:
  `σ_a` acts on `cyclotomicZetaInteger` by raising to the `a.val` power.
* `canonicalResidueZetaP_galois_compat` — the canonical residue zeta at
  `σ_a • q` is the image of the canonical residue zeta at `q` under the
  quotient ring iso induced by `σ_a`, raised to the `a.val` power.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Step 1 — coprimality of `absNorm q` with `p`

If `q` is a maximal ideal of `𝓞 K` with `(p : 𝓞 K) ∉ q`, then
`(absNorm q).Coprime p`. The proof uses the Dedekind structure: the
prime `q.under ℤ` is `⟨ℓ⟩` for some rational prime `ℓ`, and
`absNorm q` is a power of `ℓ`. Since `p ∉ q` and `q` is prime, the
underlying prime is not `p`, so the coprimality follows.
-/

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [Fact p.Prime] in
/-- If `(p : 𝓞 K) ∉ q`, then the absolute norm of the rational prime
under `q` is not `p`. -/
theorem absNorm_under_ne_of_not_mem
    {q : Ideal (𝓞 K)}
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    Ideal.absNorm (q.under ℤ) ≠ p := by
  intro h
  -- absNorm (q.under ℤ) = p ⟹ p ∈ q via cast_mem_ideal_iff.
  apply hp_not_in_q
  have : ((Ideal.absNorm (q.under ℤ) : ℤ) : 𝓞 K) ∈ q := by
    rw [Int.cast_mem_ideal_iff]
  rw [h] at this
  exact_mod_cast this

omit [IsCyclotomicExtension {p} ℚ K] in
/-- If `(p : 𝓞 K) ∉ q` for a maximal `q ≠ ⊥`, then
`(absNorm q).Coprime p`. -/
theorem coprime_absNorm_p_of_not_mem
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    (Ideal.absNorm q).Coprime p := by
  haveI : NeZero q := ⟨hq_ne_bot⟩
  -- The under-prime is a prime number ≠ p.
  have h_under_prime : (Ideal.absNorm (q.under ℤ)).Prime :=
    Nat.absNorm_under_prime q
  have h_under_ne_p : Ideal.absNorm (q.under ℤ) ≠ p :=
    absNorm_under_ne_of_not_mem hp_not_in_q
  -- absNorm q is a power of absNorm (q.under ℤ) (via inertiaDeg).
  have h_under_dvd : Ideal.absNorm (q.under ℤ) ∣ Ideal.absNorm q :=
    Int.absNorm_under_dvd_absNorm q
  have h_norm_pow : Ideal.absNorm q =
      Ideal.absNorm (q.under ℤ) ^
        ((Ideal.span ({(Ideal.absNorm (q.under ℤ) : ℤ)} : Set ℤ)).inertiaDeg q) := by
    have := Ideal.absNorm_eq_pow_inertiaDeg
      (R := 𝓞 K) (P := q) (p := (Ideal.absNorm (q.under ℤ) : ℤ))
      (Nat.prime_iff_prime_int.mp h_under_prime)
    simpa using this
  -- p is prime, and the under-prime ≠ p, so they're coprime.
  have hp_prime : Nat.Prime p := Fact.out
  have h_cop_under_p : (Ideal.absNorm (q.under ℤ)).Coprime p := by
    rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
    intro h_p_dvd
    -- p ∣ absNorm (q.under ℤ), both prime ⟹ equal. But we have ≠.
    exact h_under_ne_p
      ((Nat.prime_dvd_prime_iff_eq hp_prime h_under_prime).mp h_p_dvd).symm
  -- absNorm q = (under)^k, so coprime to p iff (under).Coprime p.
  rw [h_norm_pow]
  exact h_cop_under_p.pow_left _

/-! ### Step 2 — canonical residue ζ_p definition and primitivity

We define the canonical primitive `p`-th root of unity in `(𝓞 K ⧸ q)ˣ`
as the residue of the canonical primitive `p`-th root of unity
`cyclotomicZetaInteger K ∈ 𝓞 K`. Primitivity follows from
`IsPrimitiveRoot.idealQuotient_mk` once coprimality is established.
-/

/-- Canonical residue primitive `p`-th root in `𝓞 K ⧸ q`. This is the
"underlying" element; the unit version is `canonicalResidueZetaP`. -/
noncomputable def canonicalResidueZetaPRing
    (q : Ideal (𝓞 K)) : 𝓞 K ⧸ q :=
  Ideal.Quotient.mk q (cyclotomicZetaInteger (p := p) K)

/-- Canonical residue primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. Defined
as the residue of `cyclotomicZetaInteger K`, which is a primitive
`p`-th root of unity in `𝓞 K`, hence a unit. The image inherits the
unit structure from the surjective ring hom. -/
noncomputable def canonicalResidueZetaP
    (q : Ideal (𝓞 K)) : (𝓞 K ⧸ q)ˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- ζ_p ∈ 𝓞 K is a unit. Its image under the ring hom is also a unit.
  let hζ_unit : IsUnit (cyclotomicZetaInteger (p := p) K) :=
    (cyclotomicZetaInteger_isPrimitiveRoot (p := p) (K := K)).isUnit
      (Fact.out : p.Prime).ne_zero
  ((Ideal.Quotient.mk q).isUnit_map hζ_unit).unit

@[simp] theorem canonicalResidueZetaP_val
    (q : Ideal (𝓞 K)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((canonicalResidueZetaP (p := p) (K := K) q) : 𝓞 K ⧸ q) =
      Ideal.Quotient.mk q (cyclotomicZetaInteger (p := p) K) := by
  rfl

/-- **Primitivity (underlying ring element form).**
For maximal `q` with `(p : 𝓞 K) ∉ q`, the residue of
`cyclotomicZetaInteger K` is a primitive `p`-th root in `𝓞 K ⧸ q`. -/
theorem canonicalResidueZetaPRing_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaPRing (p := p) (K := K) q) p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hq_ne_bot⟩
  -- Use IsPrimitiveRoot.idealQuotient_mk.
  -- Need: absNorm q ≠ 1 (q ≠ ⊤, automatic from prime) and Coprime.
  have habs_ne_one : Ideal.absNorm q ≠ 1 := by
    intro h
    rw [Ideal.absNorm_eq_one_iff] at h
    exact hq.ne_top h
  have hcop : (Ideal.absNorm q).Coprime p :=
    coprime_absNorm_p_of_not_mem hq_ne_bot hp_not_in_q
  exact (cyclotomicZetaInteger_isPrimitiveRoot (p := p) (K := K)).idealQuotient_mk
    habs_ne_one hcop

/-- **Primitivity (unit form).**
For maximal `q` with `(p : 𝓞 K) ∉ q`, the canonical residue zeta is a
primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. -/
theorem canonicalResidueZetaP_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaP (p := p) (K := K) q) p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Use coe_units_iff to reduce to the underlying ring element.
  rw [← IsPrimitiveRoot.coe_units_iff]
  rw [canonicalResidueZetaP_val]
  exact canonicalResidueZetaPRing_isPrimitiveRoot hq_ne_bot hp_not_in_q

/-- **Existence corollary.** For maximal `q` with `(p : 𝓞 K) ∉ q`, there
exists a primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. This bridges the
`Classical.choose` precondition of `pthSymbolAtPrime`. -/
theorem exists_isPrimitiveRoot_of_not_mem_p
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    ∃ ζ : (𝓞 K ⧸ q)ˣ, IsPrimitiveRoot ζ p :=
  ⟨canonicalResidueZetaP (p := p) (K := K) q,
    canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q⟩

/-! ### Step 2b — basic API around primitivity

Convenience lemmas immediately derived from `IsPrimitiveRoot`:
`pow_eq_one`, `ne_one`, `orderOf_eq`, plus a `zpow` form and the
inverse-as-power identity `ζ⁻¹ = ζ ^ (p - 1)`.
-/

/-- The canonical residue zeta raised to the `p`-th power is `1`. -/
theorem canonicalResidueZetaP_pow_eq_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaP (p := p) (K := K) q ^ p = 1 :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_eq_one

/-- The canonical residue zeta is not `1`. Uses `1 < p` from primality. -/
theorem canonicalResidueZetaP_ne_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaP (p := p) (K := K) q ≠ 1 :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).ne_one
    (Fact.out : p.Prime).one_lt

/-- The canonical residue zeta has order exactly `p` in `(𝓞 K ⧸ q)ˣ`. -/
theorem canonicalResidueZetaP_orderOf_eq
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    orderOf (canonicalResidueZetaP (p := p) (K := K) q) = p :=
  ((canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).eq_orderOf).symm

/-- The canonical residue zeta raised to a power `l` equals `1` iff `p ∣ l`. -/
theorem canonicalResidueZetaP_pow_eq_one_iff
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) (l : ℕ) :
    canonicalResidueZetaP (p := p) (K := K) q ^ l = 1 ↔ p ∣ l :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_eq_one_iff_dvd l

/-- Integer-power version: `ζ ^ (p : ℤ) = 1`. -/
theorem canonicalResidueZetaP_zpow_eq_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaP (p := p) (K := K) q ^ (p : ℤ) = 1 :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).zpow_eq_one

/-- The inverse equals the `(p - 1)`-th power. Uses `ζ ^ p = 1` together with
`ζ ^ p = ζ * ζ ^ (p - 1)`. -/
theorem canonicalResidueZetaP_inv
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    (canonicalResidueZetaP (p := p) (K := K) q)⁻¹ =
      canonicalResidueZetaP (p := p) (K := K) q ^ (p - 1) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpow := canonicalResidueZetaP_pow_eq_one hq_ne_bot hp_not_in_q
  -- ζ * ζ^(p-1) = ζ^p = 1, so ζ⁻¹ = ζ^(p-1).
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  have h_eq : canonicalResidueZetaP (p := p) (K := K) q *
      canonicalResidueZetaP (p := p) (K := K) q ^ (p - 1) =
      canonicalResidueZetaP (p := p) (K := K) q ^ p := by
    rw [← pow_succ', Nat.sub_one_add_one hp_pos.ne']
  rw [h_eq, hpow]

/-- `ζ⁻¹` is also a primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`. -/
theorem canonicalResidueZetaP_inv_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaP (p := p) (K := K) q)⁻¹ p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).inv

/-- For `i` coprime to `p`, the `i`-th power of the canonical residue zeta is
also a primitive `p`-th root. Specialising `IsPrimitiveRoot.pow_of_coprime`. -/
theorem canonicalResidueZetaP_pow_isPrimitiveRoot
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) {i : ℕ} (hi : i.Coprime p) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (canonicalResidueZetaP (p := p) (K := K) q ^ i) p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_of_coprime i hi

/-- The canonical residue zeta has finite order. -/
theorem canonicalResidueZetaP_isOfFinOrder
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    IsOfFinOrder (canonicalResidueZetaP (p := p) (K := K) q) :=
  (canonicalResidueZetaP_isPrimitiveRoot hq_ne_bot hp_not_in_q).isOfFinOrder
    (Fact.out : p.Prime).ne_zero

/-- `ζ ^ p = 1` at the underlying ring level. -/
theorem canonicalResidueZetaPRing_pow_eq_one
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    canonicalResidueZetaPRing (p := p) (K := K) q ^ p = 1 :=
  (canonicalResidueZetaPRing_isPrimitiveRoot hq_ne_bot hp_not_in_q).pow_eq_one

/-! ### Step 3 — Galois compatibility of canonical zeta

The cyclotomic Galois action `σ_a` on `𝓞 K` acts on
`cyclotomicZetaInteger` by raising to the `a.val` power.
Concretely, `σ_a • ζ = ζ^a.val` (Mathlib's `cyclotomicSigmaOfUnit_smul_zetaInteger`).
This translates to the residue level via the quotient ring iso.
-/

/-- The action of `cyclotomicRingOfIntegersEquiv K a` on
`cyclotomicZetaInteger K` is exact exponentiation by `a.val`. This is
just the unfolding of the Galois action on a fixed element of `K`. -/
theorem cyclotomicRingOfIntegersEquiv_apply_zetaInteger
    (a : CyclotomicUnitDelta p) :
    cyclotomicRingOfIntegersEquiv (p := p) K a (cyclotomicZetaInteger (p := p) K) =
      cyclotomicZetaInteger (p := p) K ^ (a : ZMod p).val := by
  -- Unfolding cyclotomicRingOfIntegersEquiv reduces to the smul lemma.
  change cyclotomicSigmaOfUnit (p := p) K a • cyclotomicZetaInteger (p := p) K = _
  exact cyclotomicSigmaOfUnit_smul_zetaInteger (p := p) (K := K) a

/-- The quotient ring iso induced by `σ_a` sends the canonical residue
zeta at `q` to the `a.val`-th power of the canonical residue zeta at
`σ_a • q`. This is the residue-level version of
`cyclotomicRingOfIntegersEquiv_apply_zetaInteger`.

This is the core compatibility used to make the c.2 `pthSymbolAtPrime`
Galois transformation unconditional with unit factor `c = 1` (after
inverting the `a.val` exponent). -/
theorem canonicalResidueZetaP_val_galois_compat
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q
      ((canonicalResidueZetaP (p := p) (K := K) q) : 𝓞 K ⧸ q) =
    ((canonicalResidueZetaP (p := p) (K := K)
      (cyclotomicGaloisConjugate (p := p) (K := K) a q)) :
      𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) ^ (a : ZMod p).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Both sides unfold to the same residue: σ_a (ζ_p) = ζ_p^a.val.
  rw [canonicalResidueZetaP_val, canonicalResidueZetaP_val]
  rw [cyclotomicGaloisQuotientEquiv_mk]
  -- Now LHS: Ideal.Quotient.mk (σ_a • q) (σ_a (ζ_p)).
  -- RHS: (Ideal.Quotient.mk (σ_a • q) ζ_p)^a.val.
  -- Use that σ_a (ζ_p) = ζ_p^a.val and map_pow.
  rw [cyclotomicRingOfIntegersEquiv_apply_zetaInteger]
  rw [map_pow]

/-- Existence of primitive `p`-th root at the conjugate prime, derived from
the canonical residue zeta. -/
theorem exists_isPrimitiveRoot_at_galois_conjugate
    (a : CyclotomicUnitDelta p)
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne_bot : q ≠ ⊥)
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    ∃ ζ : (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)ˣ,
      IsPrimitiveRoot ζ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a q
  refine exists_isPrimitiveRoot_of_not_mem_p
    (cyclotomicGaloisConjugate_ne_bot a hq_ne_bot) ?_
  -- Need: (p : 𝓞 K) ∉ σ_a • q.
  -- Strategy: σ_a (p) = p (since p ∈ ℚ ⊂ K is fixed by Galois),
  -- and σ_a is a ring isomorphism so σ_a (p) ∈ σ_a • q ↔ p ∈ q.
  intro hp_in_conj
  apply hp_not_in_q
  -- Show σ_a (p : 𝓞 K) = (p : 𝓞 K).
  have h_fix : cyclotomicRingOfIntegersEquiv (p := p) K a (p : 𝓞 K) = (p : 𝓞 K) := by
    -- p is a natural number, hence fixed by any ring hom.
    change (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom (p : 𝓞 K) = (p : 𝓞 K)
    rw [map_natCast]
  -- Apply mem_cyclotomicGaloisConjugate_iff with α = (p : 𝓞 K).
  rw [← h_fix] at hp_in_conj
  exact (mem_cyclotomicGaloisConjugate_iff a).mp hp_in_conj

/-- The canonical residue zeta squared equals `ζ^2`. -/
theorem canonicalResidueZetaP_sq
    (q : Ideal (𝓞 K)) :
    (canonicalResidueZetaP (p := p) (K := K) q) ^ 2 =
      (canonicalResidueZetaP (p := p) (K := K) q) *
        (canonicalResidueZetaP (p := p) (K := K) q) := by
  rw [sq]

end Furtwaengler

end BernoulliRegular
