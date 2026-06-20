module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import BernoulliRegular.FLT37.Eichler.StickelbergerPrimeRelation

/-!
# Splitting of a rational prime `ℓ ≡ 1 mod p` in `K = ℚ(ζ_p)` (Gauss-sum factorisation, leaf 4·i)

This file is sub-leaf **(i)** of the **K-side order-`p` Gauss-sum prime
factorisation** (Washington, *Introduction to Cyclotomic Fields*, GTM 83,
Thm 6.10 — the Stickelberger congruence). The K-side factorisation is what
discharges the principality hypothesis `h` of
`stickelbergerOrbitIdeal_isPrincipal_of_under_eq`
(`FLT37/Eichler/StickelbergerPrimeRelation.lean`), the last open input of the
Stickelberger annihilation chain (leaf 4 → general Stickelberger annihilation →
Herbrand bound, Case-I).

## What is established here

Fix `K = ℚ(ζ_p)` (`IsCyclotomicExtension {p} ℚ K`) and a rational prime `ℓ ≠ p`.
For a prime ideal `𝔮 ⊂ 𝓞 K` lying over `(ℓ)`:

* `ramificationIdx_eq_one_of_ne` : `e(𝔮 | ℓ) = 1` — `ℓ` is **unramified** in `K`
  (since `ℓ ∤ p`), specialising mathlib's
  `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`.
* `inertiaDeg_eq_orderOf` : `f(𝔮 | ℓ) = orderOf (ℓ : ZMod p)` — the residual
  degree is the multiplicative order of `ℓ` mod `p`, specialising mathlib's
  `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`.
* `inertiaDeg_eq_one_of_natCast_eq_one` : when `ℓ ≡ 1 (mod p)` (i.e.
  `(ℓ : ZMod p) = 1`), `f(𝔮 | ℓ) = 1` — `ℓ` **splits completely**.
* `ncard_primesOver_eq_sub_one_of_natCast_eq_one` : when `ℓ ≡ 1 (mod p)` there
  are exactly `p - 1` primes of `𝓞 K` above `(ℓ)` — the fundamental identity
  `g · e · f = [K : ℚ] = p - 1` with `e = f = 1`.

These are the splitting / prime-count inputs that the Stickelberger ideal
factorisation `Ideal.span {g(χ)^?} = ∏_a (σ_a 𝔮₀)^{e_a}` builds on: the
character `χ : (ZMod ℓ)ˣ → μ_p ⊂ K` of order `p` exists precisely because the
residue field at `𝔮₀` is `𝔽_ℓ` (inertia degree `1`), and the orbit product
ranges over the `p - 1` conjugate primes `σ_a 𝔮₀`.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.1 (splitting of primes in
  cyclotomic fields), §6.2 (Stickelberger, Thm 6.10).
* Mathlib `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`,
  `ramificationIdx_eq_of_not_dvd`,
  `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`.
-/

@[expose] public section

noncomputable section

open NumberField Ideal

namespace BernoulliRegular

namespace FLT37

namespace Eichler

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

local notation3 "𝓵" => (Ideal.span {(ℓ : ℤ)})

/-! ### Unramifiedness and residual degree of `ℓ ≠ p` in `K = ℚ(ζ_p)` -/

/-- **Unramifiedness.** A rational prime `ℓ ≠ p` is unramified in `K = ℚ(ζ_p)`:
every prime `𝔮` of `𝓞 K` above `(ℓ)` has ramification index `1`.

Specialises `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd` with
cyclotomic level `m = p` and residue prime `ℓ`, using `ℓ ∤ p` (both prime,
`ℓ ≠ p`). -/
theorem ramificationIdx_eq_one_of_ne
    (hne : ℓ ≠ p) (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver 𝓵] :
    Ideal.ramificationIdx 𝓵 𝔮 = 1 := by
  have hndvd : ¬ ℓ ∣ p := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hℓ.out hp.out).mp h)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h𝓵ne : 𝓵 ≠ ⊥ := by simpa using hℓ.out.ne_zero
  rw [ramificationIdx_eq_ramificationIdx' 𝓵 𝔮 h𝓵ne]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
    (p := ℓ) (K := K) (P := 𝔮) (m := p) hndvd

/-- **Residual degree = order of `ℓ` mod `p`.** For a prime `𝔮` of `𝓞 K` above
`(ℓ)` with `ℓ ≠ p`, the inertia (residual) degree `f(𝔮 | ℓ)` equals the
multiplicative order of `(ℓ : ZMod p)`.

Specialises `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd` with cyclotomic
level `m = p` and residue prime `ℓ`. -/
theorem inertiaDeg_eq_orderOf
    (hne : ℓ ≠ p) (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver 𝓵] :
    Ideal.inertiaDeg 𝓵 𝔮 = orderOf (ℓ : ZMod p) := by
  have hndvd : ¬ ℓ ∣ p := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hℓ.out hp.out).mp h)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h𝓵ne' : 𝓵 ≠ ⊥ := by simpa using hℓ.out.ne_zero
  haveI h𝔮ne : 𝔮 ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot h𝓵ne' 𝔮
  haveI : 𝔮.IsMaximal := (inferInstance : 𝔮.IsPrime).isMaximal h𝔮ne
  rw [inertiaDeg_eq_inertiaDeg' 𝓵 𝔮]
  exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
    (p := ℓ) (K := K) (P := 𝔮) (m := p) hndvd

/-! ### `ℓ ≡ 1 mod p`: complete splitting -/

/-- If `ℓ ≡ 1 (mod p)` (i.e. `(ℓ : ZMod p) = 1`) then `ℓ ≠ p`: otherwise
`(ℓ : ZMod p) = (p : ZMod p) = 0 ≠ 1`. -/
theorem ne_of_natCast_eq_one_mod (hℓ1 : (ℓ : ZMod p) = 1) : ℓ ≠ p := by
  rintro rfl
  haveI : Nontrivial (ZMod ℓ) := by
    haveI : Fact (1 < ℓ) := ⟨hℓ.out.one_lt⟩
    infer_instance
  exact zero_ne_one (by rw [← ZMod.natCast_self ℓ]; exact hℓ1)

/-- **Complete splitting (residual degree `1`).** When `ℓ ≡ 1 (mod p)`, i.e.
`(ℓ : ZMod p) = 1`, every prime `𝔮` of `𝓞 K` above `(ℓ)` has residual degree
`1`. Equivalently, `ℓ` splits completely in `K = ℚ(ζ_p)` and the residue field at
`𝔮` is `𝔽_ℓ = ZMod ℓ`, which is what carries the order-`p` residue character
`χ : (ZMod ℓ)ˣ → μ_p ⊂ K` whose Gauss sum the Stickelberger factorisation
analyses. -/
theorem inertiaDeg_eq_one_of_natCast_eq_one
    (hℓ1 : (ℓ : ZMod p) = 1) (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver 𝓵] :
    Ideal.inertiaDeg 𝓵 𝔮 = 1 := by
  have hne : ℓ ≠ p := ne_of_natCast_eq_one_mod hℓ1
  rw [inertiaDeg_eq_orderOf (K := K) hne 𝔮, hℓ1, orderOf_one]

/-- The ideal `(ℓ)` of `ℤ` is nonzero. -/
theorem span_ell_ne_bot : (𝓵 : Ideal ℤ) ≠ ⊥ := by
  simpa using hℓ.out.ne_zero

instance span_ell_isMaximal : (𝓵 : Ideal ℤ).IsMaximal :=
  Int.ideal_span_isMaximal_of_prime ℓ

/-- **Prime count under complete splitting.** When `ℓ ≡ 1 (mod p)` there are
exactly `p - 1` primes of `𝓞 K` lying above `(ℓ)`.

This is the Galois fundamental identity `g · e · f = #Gal(K/ℚ) = [K : ℚ] = p - 1`
with `e = 1` (`ramificationIdx_eq_one_of_ne`) and `f = 1`
(`inertiaDeg_eq_one_of_natCast_eq_one`), so `g = p - 1`. The `p - 1` conjugate
primes `σ_a 𝔮₀` (`a ∈ (ZMod p)ˣ`) are exactly the factors of the Stickelberger
orbit ideal `∏_a (σ_a 𝔮₀)^{e_a}`. -/
theorem ncard_primesOver_eq_sub_one_of_natCast_eq_one
    (hℓ1 : (ℓ : ZMod p) = 1) :
    (Ideal.primesOver 𝓵 (𝓞 K)).ncard = p - 1 := by
  have hne : ℓ ≠ p := ne_of_natCast_eq_one_mod hℓ1
  have hndvd : ¬ ℓ ∣ p := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hℓ.out hp.out).mp h)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  -- The Galois fundamental identity: `g · (e · f) = #Gal(K/ℚ)`.
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := 𝓵) (B := 𝓞 K) (G := Gal(K / ℚ))
  -- `e = 1`: ramification index of `ℓ` in `K` is `1`.
  have he : (𝓵 : Ideal ℤ).ramificationIdxIn (𝓞 K) = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
      (p := ℓ) (K := K) (m := p) hndvd
  -- `f = 1`: residual degree of `ℓ` in `K` is `orderOf (ℓ : ZMod p) = 1`.
  have hf : (𝓵 : Ideal ℤ).inertiaDegIn (𝓞 K) = 1 := by
    rw [IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
        (p := ℓ) (K := K) (m := p) hndvd, hℓ1, orderOf_one]
  -- `#Gal(K/ℚ) = [K : ℚ] = φ(p) = p - 1`.
  have hcard : Nat.card (Gal(K / ℚ)) = p - 1 := by
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (n := p) K
        (Polynomial.cyclotomic.irreducible_rat hp.out.pos),
      Nat.totient_prime hp.out]
  rw [he, hf, mul_one, mul_one, hcard] at hfund
  exact hfund

/-! ## Sub-leaves (ii) + (iii): the algebraic Gauss-sum setup over `L = ℚ(ζ_{pℓ})`

We now build the order-`p` multiplicative character `χ : (ZMod ℓ)ˣ → μ_p` and its
Gauss sum, over the carrier field `L` with `IsCyclotomicExtension {p * ℓ} ℚ L`
(`= ℚ(ζ_p, ζ_ℓ) = ℚ(ζ_{pℓ})`). This is the smallest field containing both:

* a primitive `p`-th root of unity `μ_p ∈ 𝓞 L` (the values of `χ` lie in
  `⟨μ_p⟩ = μ_p ⊂ 𝓞 L`), and
* a primitive `ℓ`-th root of unity `ζ_ℓ ∈ 𝓞 L` (carrying the standard primitive
  additive character `ψ` of `ZMod ℓ`).

Both are extracted as powers of the distinguished primitive `(p ℓ)`-th root
`zeta (p ℓ)` via `IsPrimitiveRoot.pow`. We work directly in `𝓞 L` (a domain), so
the Gauss sum `gaussSum χ ψ ∈ 𝓞 L` is an algebraic integer and its ideal is
defined.

The carrier `K = ℚ(ζ_p)` embeds into `L` (`IsCyclotomicExtension {p} ℚ` is the
`union_left` restriction of `{p, ℓ}`, equivalently `p ∣ p ℓ`); the **descent**
sub-leaf (v) below relates the `𝓞 L`-ideal of the Gauss sum back to a `𝓞 K`-ideal
via the relative norm / `Ideal.map` of `K ⊂ L`. -/

section GaussSumSetup

variable {p : ℕ} [hp : Fact p.Prime]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
variable {L : Type u} [Field L] [NumberField L] [IsCyclotomicExtension {p * ℓ} ℚ L]

local instance : NeZero (p * ℓ) := ⟨Nat.mul_ne_zero hp.out.ne_zero hℓ.out.ne_zero⟩

/-- The distinguished primitive `(p ℓ)`-th root of unity in `𝓞 L`. -/
noncomputable def zetaPL : 𝓞 L :=
  (IsCyclotomicExtension.zeta_spec (p * ℓ) ℚ L).toInteger

lemma zetaPL_isPrimitiveRoot :
    IsPrimitiveRoot (zetaPL (p := p) (ℓ := ℓ) (L := L)) (p * ℓ) := by
  simpa [zetaPL] using
    (IsCyclotomicExtension.zeta_spec (p * ℓ) ℚ L).toInteger_isPrimitiveRoot

/-- The primitive `p`-th root of unity `μ_p = ζ_{pℓ}^ℓ ∈ 𝓞 L`, the target of the
order-`p` multiplicative character `χ`. -/
noncomputable def muP : 𝓞 L := zetaPL (p := p) (ℓ := ℓ) (L := L) ^ ℓ

/-- `μ_p = ζ_{pℓ}^ℓ` is a primitive `p`-th root of unity. -/
lemma muP_isPrimitiveRoot :
    IsPrimitiveRoot (muP (p := p) (ℓ := ℓ) (L := L)) p := by
  have hpos : 0 < p * ℓ := Nat.mul_pos hp.out.pos hℓ.out.pos
  simpa [muP] using
    (zetaPL_isPrimitiveRoot (p := p) (ℓ := ℓ) (L := L)).pow hpos (by ring)

/-- The primitive `ℓ`-th root of unity `ζ_ℓ = ζ_{pℓ}^p ∈ 𝓞 L`, carrying the
standard additive character `ψ` of `ZMod ℓ`. -/
noncomputable def zetaL : 𝓞 L := zetaPL (p := p) (ℓ := ℓ) (L := L) ^ p

/-- `ζ_ℓ = ζ_{pℓ}^p` is a primitive `ℓ`-th root of unity. -/
lemma zetaL_isPrimitiveRoot :
    IsPrimitiveRoot (zetaL (p := p) (ℓ := ℓ) (L := L)) ℓ := by
  have hpos : 0 < p * ℓ := Nat.mul_pos hp.out.pos hℓ.out.pos
  simpa [zetaL] using
    (zetaPL_isPrimitiveRoot (p := p) (ℓ := ℓ) (L := L)).pow hpos rfl

/-- `ζ_ℓ ^ ℓ = 1`, the data needed to build the additive character `ψ`. -/
lemma zetaL_pow_ell :
    zetaL (p := p) (ℓ := ℓ) (L := L) ^ ℓ = 1 :=
  (zetaL_isPrimitiveRoot (p := p) (ℓ := ℓ) (L := L)).pow_eq_one

/-! ### (ii) The standard primitive additive character `ψ` of `ZMod ℓ` -/

local instance : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

/-- **(ii) additive character.** The standard primitive additive character
`ψ : AddChar (ZMod ℓ) (𝓞 L)`, `ψ(a) = ζ_ℓ^a`, built from the primitive `ℓ`-th
root of unity `ζ_ℓ ∈ 𝓞 L`. This is the `ψ` of the Gauss sum `gaussSum χ ψ`. -/
noncomputable def addCharL : AddChar (ZMod ℓ) (𝓞 L) :=
  AddChar.zmodChar ℓ (zetaL_pow_ell (p := p) (ℓ := ℓ) (L := L))

@[simp] lemma addCharL_apply (a : ZMod ℓ) :
    addCharL (p := p) (ℓ := ℓ) (L := L) a = zetaL (p := p) (ℓ := ℓ) (L := L) ^ a.val :=
  rfl

/-- **(ii) primitivity of `ψ`.** The additive character `ψ = addCharL` is
primitive, since `ζ_ℓ` is a primitive `ℓ`-th root of unity
(`AddChar.zmodChar_primitive_of_primitive_root`). -/
lemma addCharL_isPrimitive :
    (addCharL (p := p) (ℓ := ℓ) (L := L)).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root ℓ
    (zetaL_isPrimitiveRoot (p := p) (ℓ := ℓ) (L := L))

lemma addCharL_ne_one :
    addCharL (p := p) (ℓ := ℓ) (L := L) ≠ 1 := by
  have hprim := addCharL_isPrimitive (p := p) (ℓ := ℓ) (L := L)
  have h1 : (1 : ZMod ℓ) ≠ 0 := by
    haveI : Fact (1 < ℓ) := ⟨hℓ.out.one_lt⟩
    exact one_ne_zero
  -- `mulShift ψ 1 = ψ`, and primitivity gives `mulShift ψ 1 ≠ 1`.
  have hne := hprim h1
  rwa [AddChar.mulShift_one] at hne

/-! ### (ii) The order-`p` multiplicative character `χ` -/

/-- `p ∣ ℓ - 1` packaged in the `Fintype.card`-shape required by
`MulChar.exists_mulChar_orderOf`: `p ∣ Fintype.card (ZMod ℓ) - 1`. -/
lemma p_dvd_card_sub_one (hℓ1 : (ℓ : ZMod p) = 1) :
    p ∣ Fintype.card (ZMod ℓ) - 1 := by
  rw [ZMod.card]
  -- `(ℓ : ZMod p) = 1` says `p ∣ ℓ - 1`.
  have hle : 1 ≤ ℓ := hℓ.out.one_le
  have : ((ℓ - 1 : ℕ) : ZMod p) = 0 := by
    push_cast [hle]
    rw [hℓ1]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- **(ii) existence of the order-`p` character.** When `ℓ ≡ 1 (mod p)` there is
a multiplicative character `χ : MulChar (ZMod ℓ) (𝓞 L)` of order exactly `p`,
whose values lie in `μ_p ⊂ 𝓞 L`. Produced by `MulChar.exists_mulChar_orderOf`
from `p ∣ ℓ - 1` (`p_dvd_card_sub_one`) and the primitive `p`-th root of unity
`μ_p ∈ 𝓞 L` (`muP_isPrimitiveRoot`). -/
lemma exists_mulCharL_orderOf (hℓ1 : (ℓ : ZMod p) = 1) :
    ∃ χ : MulChar (ZMod ℓ) (𝓞 L), orderOf χ = p :=
  MulChar.exists_mulChar_orderOf (ZMod ℓ)
    (p_dvd_card_sub_one (p := p) (ℓ := ℓ) hℓ1)
    (muP_isPrimitiveRoot (p := p) (ℓ := ℓ) (L := L))

/-! ### (iii) The Gauss-sum product relation and its ideal form

We fix an order-`p` character `χ` and assemble the product relation
`g(χ) · g(χ⁻¹) = χ(-1) · ℓ` (with `χ(-1) = 1` when `p ≠ 2`) and its
ideal-theoretic shadow `(g(χ)) · (g(χ⁻¹)) = (ℓ)` in `𝓞 L` (the unit `χ(-1)` is
absorbed). -/

variable {χ : MulChar (ZMod ℓ) (𝓞 L)} (hχord : orderOf χ = p)

omit hℓ [NumberField L] in
include hχord in
/-- `χ ≠ 1`: its order is the prime `p ≥ 2`, hence `> 1`. -/
lemma mulCharL_ne_one : χ ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hχord
  exact hp.out.ne_one hχord.symm

omit [NumberField L] in
/-- `χ(-1)` is a unit (in fact a square root of `1`): `χ(-1)·χ(-1) = χ(1) = 1`. -/
lemma mulCharL_neg_one_isUnit : IsUnit (χ (-1)) :=
  IsUnit.of_mul_eq_one (χ (-1)) <| by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]

omit [NumberField L] [IsCyclotomicExtension {p * ℓ} ℚ L] in
include hχord in
/-- `χ(-1) = 1` when `p ≠ 2`: a character of odd order `p` sends `-1 ↦ 1`
(`MulChar.val_neg_one_eq_one_of_odd_order`). -/
lemma mulCharL_neg_one (hp2 : p ≠ 2) : χ (-1) = 1 :=
  MulChar.val_neg_one_eq_one_of_odd_order
    (hp.out.odd_of_ne_two hp2) (hχord ▸ pow_orderOf_eq_one χ)

include hχord in
/-- **(iii) Gauss-sum product relation.** For an order-`p` character `χ` over
`𝓞 L` and the primitive additive character `ψ`,

  `g(χ) · g(χ⁻¹) = χ(-1) · ℓ`   (in `𝓞 L`).

This is mathlib's `gaussSum_mul_gaussSum_pow_orderOf_sub_one`, which gives
`g(χ) · g(χ^{p-1}) = χ(-1) · #(ZMod ℓ)`, rewritten using `χ^{p-1} = χ⁻¹` and
`#(ZMod ℓ) = ℓ`. (When `p ≠ 2` the factor `χ(-1) = 1`, see `mulCharL_neg_one`.) -/
lemma gaussSumL_mul_inv :
    gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) *
        gaussSum χ⁻¹ (addCharL (p := p) (ℓ := ℓ) (L := L)) =
      χ (-1) * (ℓ : 𝓞 L) := by
  have hψ := addCharL_isPrimitive (p := p) (ℓ := ℓ) (L := L)
  have hχ1 := mulCharL_ne_one (p := p) (ℓ := ℓ) (L := L) hχord
  -- `χ^{p-1} = χ⁻¹`.
  have hinv : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos, pow_orderOf_eq_one]
  have hmain :=
    gaussSum_mul_gaussSum_pow_orderOf_sub_one (R := ZMod ℓ) (R' := 𝓞 L) hχ1 hψ
  rw [hinv, ZMod.card] at hmain
  exact hmain

include hχord in
/-- **(iii) ideal form.** In `𝓞 L`,

  `(g(χ)) · (g(χ⁻¹)) = (ℓ)`,

the product of the principal ideals generated by the two Gauss sums equals the
principal ideal generated by `ℓ`. This is the ideal-theoretic shadow of
`gaussSumL_mul_inv` (the unit `χ(-1)` is absorbed by `span_singleton`).
It pins down the **total** valuation `v_𝔓(g(χ)) + v_𝔓(g(χ⁻¹)) = v_𝔓(ℓ)` at every
prime `𝔓` of `𝓞 L` above `ℓ` — the constraint that the Stickelberger digit-sum
formula (iv) refines into the individual valuations. -/
lemma gaussSumL_ideal_mul_inv :
    Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)) *
        Ideal.span ({gaussSum χ⁻¹ (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)) =
      Ideal.span ({(ℓ : 𝓞 L)} : Set (𝓞 L)) := by
  rw [Ideal.span_singleton_mul_span_singleton,
    gaussSumL_mul_inv (p := p) (ℓ := ℓ) (L := L) hχord]
  -- `χ(-1)·ℓ` and `ℓ` are associates: `χ(-1)` is a unit.
  obtain ⟨u, hu⟩ := mulCharL_neg_one_isUnit (χ := χ)
  rw [← hu, ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
    Ideal.top_mul]

/-! ### (iv-b) foundational leaves: `g(χ) ≡ 0 mod 𝔓` and the `v + v⁻¹` relation

These two leaves are the entry point of the **Stickelberger congruence** (Washington
Thm 6.10, Lemma 6.1). The first establishes the **lower bound** `v_𝔓(g(χ)) ≥ 1`
for every prime `𝔓 | ℓ` of `𝓞 L`: since `ζ_ℓ ≡ 1 mod 𝔓` (the residue field has
characteristic `ℓ`, where the only `ℓ`-th root of unity is `1`), every additive
character value `ψ(a) = ζ_ℓ^a ≡ 1`, so `g(χ) ≡ ∑_a χ(a) = 0 mod 𝔓`.

The second is the exact analogue, on the `ℓ`-side of `L = ℚ(ζ_{pℓ})`, of the
above-`p` relation `primeAbovePExponent_add_inv_eq_pred`
(`GaussSum/PrimeFactorization/Valuation.lean`): from the ideal identity
`(g(χ))·(g(χ⁻¹)) = (ℓ)` (`gaussSumL_ideal_mul_inv`) and the fact that `ℓ` ramifies
in `L = ℚ(ζ_{pℓ})` with index `e(𝔓|ℓ) = ℓ - 1` (since `ℓ ∥ pℓ`, the `ℓ`-part of the
cyclotomic level is `ℓ^1`), the two Gauss-sum valuations sum to `ℓ - 1`:

  `v_𝔓(g(χ)) + v_𝔓(g(χ⁻¹)) = ℓ - 1`. -/

/-- The residue field `𝓞 L ⧸ 𝔓` of a prime `𝔓` above `(ℓ)` has characteristic
`ℓ`. Built from `CharP (ℤ ⧸ (ℓ)) ℓ ≅ ZMod ℓ` transported along the (injective)
residue extension `ℤ ⧸ (ℓ) → 𝓞 L ⧸ 𝔓` (which exists because the ramification
index `e(𝔓|ℓ) ≠ 0`). -/
lemma charP_quotient_of_liesOver_ell (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    CharP (𝓞 L ⧸ 𝔓) ℓ := by
  have hℓ0 : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using hℓ.out.ne_zero
  haveI : NeZero (Ideal.ramificationIdx (Ideal.span {(ℓ : ℤ)}) 𝔓) :=
    ⟨Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
      (R := ℤ) (S := 𝓞 L) (p := Ideal.span {(ℓ : ℤ)}) 𝔓 hℓ0⟩
  letI : Algebra (ℤ ⧸ (Ideal.span {(ℓ : ℤ)})) (𝓞 L ⧸ 𝔓) :=
    Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero (Ideal.span {(ℓ : ℤ)}) 𝔓
  haveI : CharP (ℤ ⧸ (Ideal.span {(ℓ : ℤ)})) ℓ :=
    charP_of_injective_ringHom
      (f := (Int.quotientSpanNatEquivZMod ℓ).symm.toRingHom)
      (Int.quotientSpanNatEquivZMod ℓ).symm.injective ℓ
  exact charP_of_injective_algebraMap' (ℤ ⧸ (Ideal.span {(ℓ : ℤ)})) ℓ

/-- **`ζ_ℓ ≡ 1 mod 𝔓`** for every prime `𝔓` of `𝓞 L` above `(ℓ)`: the primitive
`ℓ`-th root of unity `ζ_ℓ ∈ 𝓞 L` is congruent to `1` modulo `𝔓`. In the residue
field (characteristic `ℓ`) the freshman's dream gives
`(ζ̄_ℓ - 1)^ℓ = ζ̄_ℓ^ℓ - 1 = 0`, and a field has no nonzero nilpotents, so
`ζ̄_ℓ = 1`. This is the key local fact behind `g(χ) ≡ 0 mod 𝔓`. -/
lemma zetaL_sub_one_mem_of_liesOver_ell (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    zetaL (p := p) (ℓ := ℓ) (L := L) - 1 ∈ 𝔓 := by
  haveI : CharP (𝓞 L ⧸ 𝔓) ℓ := charP_quotient_of_liesOver_ell (ℓ := ℓ) (L := L) 𝔓
  set ζbar : 𝓞 L ⧸ 𝔓 := Ideal.Quotient.mk 𝔓 (zetaL (p := p) (ℓ := ℓ) (L := L)) with hζbar
  have hpow : ζbar ^ ℓ = 1 := by
    rw [hζbar, ← map_pow, zetaL_pow_ell (p := p) (ℓ := ℓ) (L := L), map_one]
  have hsubpow : (ζbar - 1) ^ ℓ = 0 := by
    calc
      (ζbar - 1) ^ ℓ = ζbar ^ ℓ - 1 := by
        simpa using
          (sub_pow_char_of_commute ℓ (Commute.one_right ζbar) :
            (ζbar - 1) ^ ℓ = ζbar ^ ℓ - 1 ^ ℓ)
      _ = 0 := by rw [hpow, sub_self]
  have hsub : ζbar - 1 = 0 := eq_zero_of_pow_eq_zero hsubpow
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← hζbar, hsub]

include hχord in
/-- **(iv-b) lower bound `v_𝔓(g(χ)) ≥ 1`.** For an order-`p` character `χ` over
`𝓞 L` and every prime `𝔓` of `𝓞 L` above `(ℓ)`, the Gauss sum
`g(χ) = ∑_a χ(a)·ζ_ℓ^a` lies in `𝔓`.

Proof (Washington Lemma 6.1): modulo `𝔓` we have `ζ_ℓ ≡ 1`
(`zetaL_sub_one_mem_of_liesOver_ell`), hence each summand `χ(a)·ζ_ℓ^{a} ≡ χ(a)`,
so `g(χ) ≡ ∑_a χ(a) = 0` because `χ ≠ 1` is a nontrivial multiplicative character
(`MulChar.sum_eq_zero_of_ne_one`). This is the first half of the Stickelberger
congruence: it gives the strict positivity `v_𝔓(g(χ)) ≥ 1` underlying the digit
formula `v_𝔓(g(χ)) = ⟨b⟩ ∈ {1, …, p-1}`. -/
lemma gaussSumL_mem_prime_of_liesOver_ell (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) ∈ 𝔓 := by
  have hχ1 := mulCharL_ne_one (p := p) (ℓ := ℓ) (L := L) hχord
  have hζ1 : Ideal.Quotient.mk 𝔓 (zetaL (p := p) (ℓ := ℓ) (L := L)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk 𝔓), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact zetaL_sub_one_mem_of_liesOver_ell (p := p) (ℓ := ℓ) (L := L) 𝔓
  rw [← Ideal.Quotient.eq_zero_iff_mem, gaussSum, map_sum]
  -- Each summand `χ(a)·ζ_ℓ^{a.val} ≡ χ(a)` mod 𝔓 (since `ζ_ℓ ≡ 1`), so the sum
  -- collapses to `∑_a mk(χ a) = mk(∑_a χ a) = mk 0 = 0`.
  have hterm : ∀ a : ZMod ℓ,
      Ideal.Quotient.mk 𝔓
          (χ a * addCharL (p := p) (ℓ := ℓ) (L := L) a) =
        Ideal.Quotient.mk 𝔓 (χ a) := by
    intro a
    rw [addCharL_apply, map_mul, map_pow, hζ1, one_pow, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← map_sum,
    MulChar.sum_eq_zero_of_ne_one hχ1, map_zero]

include hχord in
/-- Both Gauss sums `g(χ)` and `g(χ⁻¹)` are nonzero elements of the domain
`𝓞 L`, since their product `g(χ)·g(χ⁻¹) = χ(-1)·ℓ` is nonzero (`χ(-1)` is a unit,
`ℓ ≠ 0`). -/
lemma gaussSumL_ne_zero_and_inv :
    gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 ∧
      gaussSum χ⁻¹ (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 := by
  have hmul := gaussSumL_mul_inv (p := p) (ℓ := ℓ) (L := L) hχord
  obtain ⟨u, hu⟩ := mulCharL_neg_one_isUnit (χ := χ)
  rw [← hu] at hmul
  have hprod_ne :
      gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) *
          gaussSum χ⁻¹ (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 := by
    rw [hmul]
    exact mul_ne_zero u.ne_zero (show (ℓ : 𝓞 L) ≠ 0 by exact_mod_cast hℓ.out.ne_zero)
  exact ⟨fun h => hprod_ne (by rw [h, zero_mul]),
    fun h => hprod_ne (by rw [h, mul_zero])⟩

include hχord in
/-- The principal ideal of `g(χ)` is nonzero. -/
lemma gaussSumL_span_ne_bot :
    Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)) ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr
    (gaussSumL_ne_zero_and_inv (p := p) (ℓ := ℓ) (L := L) hχord).1

include hχord in
/-- The principal ideal of `g(χ⁻¹)` is nonzero. -/
lemma gaussSumL_inv_span_ne_bot :
    Ideal.span ({gaussSum χ⁻¹ (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)) ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr
    (gaussSumL_ne_zero_and_inv (p := p) (ℓ := ℓ) (L := L) hχord).2

include hχord in
/-- **(iv-b) the `v_𝔓 + v_𝔓∘inv = ℓ - 1` relation.** For an order-`p` character
`χ` over `𝓞 L` and every prime `𝔓` of `𝓞 L` above `(ℓ)`, the `𝔓`-adic
multiplicities of the two Gauss sums sum to `ℓ - 1`:

  `count_𝔓 (g(χ)) + count_𝔓 (g(χ⁻¹)) = ℓ - 1`.

This is the `ℓ`-side of `L = ℚ(ζ_{pℓ})` analogue of the above-`p` relation
`primeAbovePExponent_add_inv_eq_pred`. Proof: the product ideal `(g(χ))·(g(χ⁻¹))`
equals `(ℓ)` (`gaussSumL_ideal_mul_inv`), whose `𝔓`-multiplicity is the
ramification index `e(𝔓|ℓ) = ℓ - 1` (`IsCyclotomicExtension.Rat.ramificationIdx_eq`
with `pℓ = ℓ^1 · p`, `ℓ ∤ p`); then `normalizedFactors_mul` splits the count
additively. With `gaussSumL_mem_prime_of_liesOver_ell` (each count `≥ 1`), this
pins the two valuations into the window `[1, ℓ - 2]` — the constraint refined by
the Stickelberger digit formula (iv). -/
lemma gaussSumL_count_add_inv_eq_sub_one
    (hℓp : ¬ ℓ ∣ p) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓 +
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum χ⁻¹ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓 = ℓ - 1 := by
  haveI : NeZero (p * ℓ) := ⟨Nat.mul_ne_zero hp.out.ne_zero hℓ.out.ne_zero⟩
  set Iχ : Ideal (𝓞 L) :=
    Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)) with hIχ
  set Iχinv : Ideal (𝓞 L) :=
    Ideal.span ({gaussSum χ⁻¹ (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)) with hIχinv
  have hIχ_ne : Iχ ≠ ⊥ := gaussSumL_span_ne_bot (p := p) (ℓ := ℓ) (L := L) hχord
  have hIχinv_ne : Iχinv ≠ ⊥ := gaussSumL_inv_span_ne_bot (p := p) (ℓ := ℓ) (L := L) hχord
  -- The product ideal `Iχ * Iχinv = (ℓ)`, whose `𝔓`-multiplicity is `e(𝔓|ℓ) = ℓ - 1`.
  have hℓmap :
      Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) =
        Ideal.span ({(ℓ : 𝓞 L)} : Set (𝓞 L)) := by
    simpa using Ideal.map_span (algebraMap ℤ (𝓞 L)) ({(ℓ : ℤ)} : Set ℤ)
  have hℓmap_ne_bot :
      Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [hℓmap]
    exact Ideal.span_singleton_eq_bot.not.mpr
      (show (ℓ : 𝓞 L) ≠ 0 by exact_mod_cast hℓ.out.ne_zero)
  have h𝔓_ne_bot : 𝔓 ≠ ⊥ := by
    have hℓ0 : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by simpa using hℓ.out.ne_zero
    exact ne_bot_of_liesOver_of_ne_bot hℓ0 𝔓
  -- `e(𝔓|ℓ) = ℓ - 1` for `L = ℚ(ζ_{pℓ})`: write `pℓ = ℓ^1 · p`, `ℓ ∤ p`.
  have hram : Ideal.ramificationIdx (Ideal.span {(ℓ : ℤ)}) 𝔓 = ℓ - 1 := by
    rw [ramificationIdx_eq_ramificationIdx' (Ideal.span {(ℓ : ℤ)}) 𝔓 (by simpa using hℓ.out.ne_zero)]
    have := IsCyclotomicExtension.Rat.ramificationIdx_eq
      (n := p * ℓ) (m := p) (p := ℓ) (k := 0) (K := L) (P := 𝔓) (by ring) hℓp
    simpa using this
  have hcount_ell :
      (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({(ℓ : 𝓞 L)} : Set (𝓞 L)))).count 𝔓 = ℓ - 1 := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        (R := ℤ) (S := 𝓞 L) (p := Ideal.span {(ℓ : ℤ)}) (P := 𝔓)
        hℓmap_ne_bot inferInstance h𝔓_ne_bot, hℓmap] at hram
    exact hram
  have hmuleq : Iχ * Iχinv = Ideal.span ({(ℓ : 𝓞 L)} : Set (𝓞 L)) :=
    gaussSumL_ideal_mul_inv (p := p) (ℓ := ℓ) (L := L) hχord
  -- Split the count of the product additively.
  have hsplit :
      (UniqueFactorizationMonoid.normalizedFactors (Iχ * Iχinv)).count 𝔓 =
        (UniqueFactorizationMonoid.normalizedFactors Iχ).count 𝔓 +
          (UniqueFactorizationMonoid.normalizedFactors Iχinv).count 𝔓 := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hIχ_ne hIχinv_ne, Multiset.count_add]
  rw [hmuleq, hcount_ell] at hsplit
  omega

include hχord in
/-- **(iv-b) lower bound in `count` form: `1 ≤ count_𝔓 (g(χ))`.** The `count`-language
restatement of `gaussSumL_mem_prime_of_liesOver_ell`, in the exact shape consumed by
the digit-sum predicates `StickelbergerDigitSumValuation` /
`SinglePrimePowerValuation`: for every prime `𝔓 | ℓ`, the multiplicity of `𝔓` in the
factorisation of `(g(χ))` is at least `1`.

Proof: `g(χ) ∈ 𝔓` (`gaussSumL_mem_prime_of_liesOver_ell`) gives
`span {g(χ)} ≤ 𝔓`, hence `𝔓 ∈ normalizedFactors (span {g(χ)})`
(`mem_normalizedFactors_iff`, `𝔓` prime), i.e. `count ≥ 1`
(`Multiset.one_le_count_iff_mem`). Combined with
`gaussSumL_count_add_inv_eq_sub_one` this pins each Gauss-sum count into
`[1, ℓ - 2]`. -/
lemma one_le_gaussSumL_count_of_liesOver_ell (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    1 ≤ (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓 := by
  rw [Multiset.one_le_count_iff_mem,
    Ideal.mem_normalizedFactors_iff
      (gaussSumL_span_ne_bot (p := p) (ℓ := ℓ) (L := L) hχord)]
  refine ⟨inferInstance, ?_⟩
  rw [Ideal.span_singleton_le_iff_mem]
  exact gaussSumL_mem_prime_of_liesOver_ell (p := p) (ℓ := ℓ) (L := L) hχord 𝔓

/-! ### (v) Jacobi-sum route: `g(χ)^p ∈ K`-ideal data

The descent (v) is cleanest via the Jacobi-sum identity
`gaussSum_pow_eq_prod_jacobiSum`: for `χ` of order `p`,

  `g(χ)^p = χ(-1) · ℓ · ∏_{i=1}^{p-2} J(χ, χ^i)`,

and **each Jacobi sum `J(χ, χ^i) ∈ ℤ[μ_p] ⊆ 𝓞 K`** lives already in `K = ℚ(ζ_p)`
(`jacobiSum_mem_algebraAdjoin_of_pow_eq_one`). Hence `g(χ)^p` is, up to the unit
`χ(-1) = 1` and the rational integer `ℓ`, a product of elements of `𝓞 K`. This is
what lets the `p`-th power of the Gauss-sum ideal descend to a `K`-ideal without
the full `𝓞 L → 𝓞 K` norm bookkeeping. -/

include hχord in
/-- **(v) Jacobi-sum product formula for `g(χ)^p`.** For `χ` of order `p`,

  `g(χ)^p = χ(-1) · ℓ · ∏_{i ∈ [1, p-2]} J(χ, χ^i)`   (in `𝓞 L`).

Specialises `gaussSum_pow_eq_prod_jacobiSum` (with `orderOf χ = p`,
`#(ZMod ℓ) = ℓ`). The Jacobi-sum factors are the `K`-rational pieces of the
descent. -/
lemma gaussSumL_pow_eq_prod_jacobiSum :
    gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) ^ p =
      χ (-1) * (ℓ : 𝓞 L) *
        ∏ i ∈ Finset.Ico 1 (p - 1), jacobiSum χ (χ ^ i) := by
  have hψ := addCharL_isPrimitive (p := p) (ℓ := ℓ) (L := L)
  have hge : 2 ≤ orderOf χ := by rw [hχord]; exact hp.out.two_le
  have h := gaussSum_pow_eq_prod_jacobiSum hge hψ
  rw [hχord, ZMod.card] at h
  exact h

omit hp hℓ [NumberField L] [IsCyclotomicExtension {p * ℓ} ℚ L] in
include hχord in
/-- `χ^k ≠ 1` whenever `0 < k < p`: the order of `χ` is exactly `p`, so no smaller
positive power can be trivial (`pow_ne_one_of_lt_orderOf`). This is the
nontriviality side-condition feeding the Jacobi-sum recursion. -/
lemma mulCharL_pow_ne_one {k : ℕ} (hk0 : k ≠ 0) (hkp : k < p) : χ ^ k ≠ 1 := by
  rw [← hχord] at hkp
  exact pow_ne_one_of_lt_orderOf hk0 hkp

include hχord in
/-- **(iv-b2, Step 1) Jacobi-sum recursion for the Gauss sums.** For `χ` of order
`p` and `0 < j < p`,

  `g(χ^j) · J(χ^{j-1}, χ) = g(χ^{j-1}) · g(χ)`   (in `𝓞 L`).

This is the multiplicative recursion that drives the induction `j ↦ v_{𝔓₀}(g(χ^j))`
behind the Stickelberger congruence (`SinglePrimePowerValuation`). It specialises
mathlib's `jacobiSum_mul_nontrivial` (`g(χ'·φ)·J(χ',φ) = g(χ')·g(φ)`) with
`χ' = χ^{j-1}`, `φ = χ`, using `χ^{j-1}·χ = χ^j ≠ 1` (since `0 < j < p`, so
`χ^j ≠ 1` by `mulCharL_pow_ne_one`). Passing to ideals (`Ideal.span`) it gives the
valuation recursion `v_𝔓(g(χ^j)) + v_𝔓(J(χ^{j-1},χ)) = v_𝔓(g(χ^{j-1})) + v_𝔓(g(χ))`,
the additive backbone of the digit recursion. -/
lemma gaussSumL_mul_eq_jacobiSum_mul {j : ℕ} (hj0 : j ≠ 0) (hjp : j < p) :
    gaussSum (χ ^ j) (addCharL (p := p) (ℓ := ℓ) (L := L)) *
        jacobiSum (χ ^ (j - 1)) χ =
      gaussSum (χ ^ (j - 1)) (addCharL (p := p) (ℓ := ℓ) (L := L)) *
        gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) := by
  -- `χ^j ≠ 1` for `0 < j < p`.
  have hχj : χ ^ j ≠ 1 := mulCharL_pow_ne_one (p := p) (ℓ := ℓ) (L := L) hχord hj0 hjp
  -- `χ^{j-1} * χ = χ^j`, so the product character is `χ^j ≠ 1`.
  have hmul_eq : χ ^ (j - 1) * χ = χ ^ j := by
    rw [← pow_succ, Nat.sub_one_add_one hj0]
  have hne : χ ^ (j - 1) * χ ≠ 1 := hmul_eq ▸ hχj
  have h := jacobiSum_mul_nontrivial (R := 𝓞 L) hne (addCharL (p := p) (ℓ := ℓ) (L := L))
  rwa [hmul_eq] at h

omit [IsCyclotomicExtension {p * ℓ} ℚ L] in
/-- `(ℓ : 𝓞 L) ≠ 0` packaged as `(Fintype.card (ZMod ℓ) : 𝓞 L) ≠ 0`, the shape
required by `gaussSum_ne_zero_of_nontrivial` / `jacobiSum_mem_*`. -/
lemma card_zmod_ell_ne_zero : (Fintype.card (ZMod ℓ) : 𝓞 L) ≠ 0 := by
  rw [ZMod.card]
  exact_mod_cast hℓ.out.ne_zero

include hχord in
/-- **Nonvanishing of `g(χ^k)` for nontrivial powers.** For `χ` of order `p` and
`0 < k < p`, the Gauss sum `g(χ^k)` is a nonzero element of `𝓞 L`. This is
`gaussSum_ne_zero_of_nontrivial` applied to the nontrivial character `χ^k`
(`mulCharL_pow_ne_one`) and the primitive `ψ`, with `(#(ZMod ℓ) : 𝓞 L) = ℓ ≠ 0`.
It is what lets the recursion `gaussSumL_mul_eq_jacobiSum_mul` pass to ideal /
`normalizedFactors` form. -/
lemma gaussSumL_pow_ne_zero {k : ℕ} (hk0 : k ≠ 0) (hkp : k < p) :
    gaussSum (χ ^ k) (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 :=
  gaussSum_ne_zero_of_nontrivial (card_zmod_ell_ne_zero (ℓ := ℓ) (L := L))
    (mulCharL_pow_ne_one (p := p) (ℓ := ℓ) (L := L) hχord hk0 hkp)
    (addCharL_isPrimitive (p := p) (ℓ := ℓ) (L := L))

include hχord in
/-- **(iv-b2, Step 1, ideal form) count-additive recursion at a prime `𝔓₀ | ℓ`.**
Taking `𝔓₀`-adic multiplicities (`normalizedFactors.count`) in the multiplicative
recursion `g(χ^j)·J(χ^{j-1},χ) = g(χ^{j-1})·g(χ)`
(`gaussSumL_mul_eq_jacobiSum_mul`), the Gauss-sum and Jacobi-sum valuations satisfy

  `v_{𝔓₀}(g(χ^j)) + v_{𝔓₀}(J(χ^{j-1},χ)) = v_{𝔓₀}(g(χ^{j-1})) + v_{𝔓₀}(g(χ))`,

for `0 < j-1` and `j < p` (so `χ^{j-1}`, `χ^j` and `χ` are nontrivial and the
Gauss sums nonzero, `gaussSumL_pow_ne_zero`; the Jacobi sum is nonzero since the
product of the two nonzero Gauss sums equals it times the nonzero `g(χ^j)`).
This is the additive backbone of the digit induction: combined with the digit
recursion `⟨(j-1)b₀⟩ + ⟨b₀⟩ - ⟨j b₀⟩ = (carry)` and the Jacobi carry valuation
`v_{𝔓₀}(J(χ^{j-1},χ)) = (carry)`, it yields `v_{𝔓₀}(g(χ^j)) = ⟨j b₀⟩`. -/
lemma gaussSumL_count_recursion {j : ℕ} (hj1 : 1 < j) (hjp : j < p)
    (𝔓₀ : Ideal (𝓞 L)) [𝔓₀.IsPrime] [𝔓₀.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum (χ ^ j) (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓₀ +
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({jacobiSum (χ ^ (j - 1)) χ} : Set (𝓞 L)))).count 𝔓₀ =
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum (χ ^ (j - 1)) (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓₀ +
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓₀ := by
  have hj0 : j ≠ 0 := by omega
  -- The three Gauss sums are nonzero.
  have hgj : gaussSum (χ ^ j) (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 :=
    gaussSumL_pow_ne_zero (p := p) (ℓ := ℓ) (L := L) hχord hj0 hjp
  have hgj1 : gaussSum (χ ^ (j - 1)) (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 :=
    gaussSumL_pow_ne_zero (p := p) (ℓ := ℓ) (L := L) hχord (by omega) (by omega)
  have hg1 : gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 :=
    (gaussSumL_ne_zero_and_inv (p := p) (ℓ := ℓ) (L := L) hχord).1
  -- The Jacobi sum is nonzero: `g(χ^j)·J = g(χ^{j-1})·g(χ) ≠ 0`.
  have hrec := gaussSumL_mul_eq_jacobiSum_mul (p := p) (ℓ := ℓ) (L := L) hχord hj0 hjp
  have hJ : jacobiSum (χ ^ (j - 1)) χ ≠ 0 := by
    intro hJ0
    rw [hJ0, mul_zero] at hrec
    exact (mul_ne_zero hgj1 hg1) hrec.symm
  -- `span` of products = product of spans; `normalizedFactors_mul` splits the count.
  have hcount_lhs :
      (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({gaussSum (χ ^ j) (addCharL (p := p) (ℓ := ℓ) (L := L)) *
            jacobiSum (χ ^ (j - 1)) χ} : Set (𝓞 L)))).count 𝔓₀ =
        (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({gaussSum (χ ^ j) (addCharL (p := p) (ℓ := ℓ) (L := L))} :
              Set (𝓞 L)))).count 𝔓₀ +
          (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({jacobiSum (χ ^ (j - 1)) χ} : Set (𝓞 L)))).count 𝔓₀ := by
    rw [← Ideal.span_singleton_mul_span_singleton,
      UniqueFactorizationMonoid.normalizedFactors_mul
        (Ideal.span_singleton_eq_bot.not.mpr hgj)
        (Ideal.span_singleton_eq_bot.not.mpr hJ), Multiset.count_add]
  have hcount_rhs :
      (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({gaussSum (χ ^ (j - 1)) (addCharL (p := p) (ℓ := ℓ) (L := L)) *
            gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)))).count 𝔓₀ =
        (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({gaussSum (χ ^ (j - 1)) (addCharL (p := p) (ℓ := ℓ) (L := L))} :
              Set (𝓞 L)))).count 𝔓₀ +
          (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
              Set (𝓞 L)))).count 𝔓₀ := by
    rw [← Ideal.span_singleton_mul_span_singleton,
      UniqueFactorizationMonoid.normalizedFactors_mul
        (Ideal.span_singleton_eq_bot.not.mpr hgj1)
        (Ideal.span_singleton_eq_bot.not.mpr hg1), Multiset.count_add]
  rw [← hcount_lhs, ← hcount_rhs, hrec]

include hχord in
/-- **Nonvanishing of the Jacobi sum `J(χ, χ^i)`.** For `χ` of order `p`,
`0 < i` and `i + 1 < p`, the Jacobi sum `J(χ, χ^i)` is a nonzero element of `𝓞 L`.
Proof: `gaussSum_mul_gaussSum = g(χ)·g(χ^i)` factors as `g(χ^{i+1})·J(χ,χ^i)`
(`jacobiSum_mul_nontrivial`, `χ·χ^i = χ^{i+1} ≠ 1`); the left side is nonzero
(both `g(χ)` and `g(χ^i)` are nonzero, `gaussSumL_pow_ne_zero`), so `J ≠ 0`. -/
lemma jacobiSumL_ne_zero {i : ℕ} (hi0 : i ≠ 0) (hi1 : i + 1 < p) :
    jacobiSum χ (χ ^ i) ≠ 0 := by
  have hχsucc : χ * χ ^ i ≠ 1 := by
    have : χ * χ ^ i = χ ^ (i + 1) := by rw [pow_succ, mul_comm]
    rw [this]
    exact mulCharL_pow_ne_one (p := p) (ℓ := ℓ) (L := L) hχord (by omega) hi1
  have h := jacobiSum_mul_nontrivial (R := 𝓞 L) hχsucc (addCharL (p := p) (ℓ := ℓ) (L := L))
  have hg : gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L)) *
      gaussSum (χ ^ i) (addCharL (p := p) (ℓ := ℓ) (L := L)) ≠ 0 :=
    mul_ne_zero (gaussSumL_ne_zero_and_inv (p := p) (ℓ := ℓ) (L := L) hχord).1
      (gaussSumL_pow_ne_zero (p := p) (ℓ := ℓ) (L := L) hχord hi0 (by omega))
  intro hJ0
  rw [hJ0, mul_zero] at h
  exact hg h.symm

/-- **Abstract telescoping helper.** If `g J : ℕ → ℕ` satisfy the single-step
recursion `g (m+1) + J m = g m + g 1` for all `1 ≤ m < N`, then for `1 ≤ n ≤ N`,

  `g n + Σ_{i=1}^{n-1} J i = n · g 1`.

Pure `ℕ`-arithmetic induction, decoupled from the heavy `normalizedFactors.count`
terms it is applied to in `gaussSumL_count_pow_telescope`. -/
private lemma telescope_count_aux {N : ℕ} (g J : ℕ → ℕ)
    (hstep : ∀ m, 1 ≤ m → m + 1 ≤ N → g (m + 1) + J m = g m + g 1) :
    ∀ n, 1 ≤ n → n ≤ N → g n + ∑ i ∈ Finset.Ico 1 n, J i = n * g 1 := by
  intro n hn1 hnN
  induction n, hn1 using Nat.le_induction with
  | base => simp
  | succ m hm1 ih =>
    have ihm := ih (by omega)
    rw [Finset.sum_Ico_succ_top hm1, ← add_assoc,
      add_right_comm (g (m + 1)) _ (J m), hstep m hm1 hnN, Nat.succ_mul]
    omega

include hχord in
/-- **(iv-b2, telescoped form) Gauss-sum power valuation as a digit sum minus
Jacobi carries.** For `χ` of order `p`, `0 < n < p`, and any prime `𝔓₀ | ℓ` of
`𝓞 L`, the `𝔓₀`-multiplicity of `g(χ^n)` is the telescoped relation

  `v_{𝔓₀}(g(χ^n)) + Σ_{i=1}^{n-1} v_{𝔓₀}(J(χ, χ^i)) = n · v_{𝔓₀}(g(χ))`.

This is the count/valuation shadow of mathlib's
`gaussSum_pow_eq_prod_jacobiSum_aux` (`g(χ)^n = g(χ^n)·∏_{i∈[1,n)} J(χ,χ^i)`):
the LHS factor counts split additively (`normalizedFactors_mul`, all factors
nonzero by `gaussSumL_pow_ne_zero` / `jacobiSumL_ne_zero`), and the `n`-th power
on the right multiplies the count of `g(χ)` by `n`
(`normalizedFactors_pow` / `count_pow`). Together with the base value
`v_{𝔓₀}(g(χ)) = ⟨b₀⟩` and the carry valuations `v_{𝔓₀}(J(χ,χ^i)) = p·[carry_i]`,
this pins every `v_{𝔓₀}(g(χ^n)) = ⟨n b₀⟩` (`SinglePrimePowerValuation`), since
`Σ carries = (n·⟨b₀⟩ - ⟨n b₀⟩)/p` by `stickelbergerDigit_add_carry`. -/
lemma gaussSumL_count_pow_telescope {n : ℕ} (hn1 : 1 ≤ n) (hnp : n < p)
    (𝔓₀ : Ideal (𝓞 L)) [𝔓₀.IsPrime] [𝔓₀.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum (χ ^ n) (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓₀ +
      ∑ i ∈ Finset.Ico 1 n, (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({jacobiSum χ (χ ^ i)} : Set (𝓞 L)))).count 𝔓₀ =
      n * (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count 𝔓₀ := by
  -- `gcount m := v_{𝔓₀}(g(χ^m))`, `Jcount i := v_{𝔓₀}(J(χ,χ^i))`.
  let gcount : ℕ → ℕ := fun m =>
    (UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({gaussSum (χ ^ m) (addCharL (p := p) (ℓ := ℓ) (L := L))} :
        Set (𝓞 L)))).count 𝔓₀
  let Jcount : ℕ → ℕ := fun i =>
    (UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({jacobiSum χ (χ ^ i)} : Set (𝓞 L)))).count 𝔓₀
  -- `gcount 1 = v_{𝔓₀}(g(χ))` (rewriting `χ^1 = χ`).
  have hg1eq : gcount 1 = (UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
        Set (𝓞 L)))).count 𝔓₀ := by simp only [gcount, pow_one]
  -- The single-step recursion `gcount (m+1) + Jcount m = gcount m + gcount 1`,
  -- for `1 ≤ m`, `m + 1 ≤ p - 1` (from `gaussSumL_count_recursion` + `jacobiSum_comm`).
  have step : ∀ m, 1 ≤ m → m + 1 ≤ p - 1 →
      gcount (m + 1) + Jcount m = gcount m + gcount 1 := by
    intro m hm1 hmp1
    have hrec := gaussSumL_count_recursion (p := p) (ℓ := ℓ) (L := L) hχord
      (j := m + 1) (by omega) (by omega) 𝔓₀
    have hJcomm : Jcount m =
        (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({jacobiSum (χ ^ (m + 1 - 1)) χ} : Set (𝓞 L)))).count 𝔓₀ := by
      simp only [Jcount, Nat.add_sub_cancel, jacobiSum_comm]
    rw [hJcomm, hg1eq]
    exact hrec
  -- Apply the abstract telescoping helper with `N = p - 1`.
  have := telescope_count_aux (N := p - 1) gcount Jcount step n hn1 (by omega)
  rw [hg1eq] at this
  exact this

include hχord in
/-- **(v) `K`-rationality of the Jacobi-sum factors.** For `χ` of order `p`, each
Jacobi sum `J(χ, χ^i)` lies in `ℤ[μ_p] = Algebra.adjoin ℤ {μ_p} ⊆ 𝓞 L`. Since
`μ_p` is a primitive `p`-th root of unity, `ℤ[μ_p]` is (the image of) `𝓞 K` for
`K = ℚ(ζ_p)`: this is the precise sense in which the Gauss-sum `p`-th power
descends to `K`. Specialises `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`
(`χ^p = 1`, `(χ^i)^p = 1`, `μ_p` primitive `p`-th root). -/
lemma jacobiSumL_mem_algebraAdjoin (i : ℕ) :
    jacobiSum χ (χ ^ i) ∈ Algebra.adjoin ℤ {muP (p := p) (ℓ := ℓ) (L := L)} := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hχp : χ ^ p = 1 := hχord ▸ pow_orderOf_eq_one χ
  have hχip : (χ ^ i) ^ p = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hχp, one_pow]
  exact jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχp hχip
    (muP_isPrimitiveRoot (p := p) (ℓ := ℓ) (L := L))

end GaussSumSetup

/-! ## Sub-leaves (iv) + (v): precise decomposition of the deep core

The remaining content of the K-side Gauss-sum factorisation (Washington Thm 6.10)
is the **Stickelberger congruence** (iv) — the digit-sum valuation of `g(χ)` —
together with the **descent** (v) from `L = ℚ(ζ_{pℓ})` to `K = ℚ(ζ_p)`. Both are
stated below as explicit named hypotheses (`def … : Prop`), each with a complete
docstring decomposing it into dischargeable sub-leaves. None is an axiom; each is
a parametric predicate that the final factorisation theorem consumes and that the
analytic work must discharge.

### The overall target it feeds

The goal (discharging `h` of `stickelbergerOrbitIdeal_isPrincipal_of_under_eq`)
is, for the chosen prime `𝔮₀ ⊂ 𝓞 K` above `ℓ`:

  `(g(χ)^p) = ∏_{a ∈ (ZMod p)ˣ} (σ_a 𝔮₀)^{e_a}`   (as ideals of `𝓞 K`),

with Stickelberger exponents `e_a = ` (a base-`p` digit-sum of `a`). The chain is:

1. **(iv) digit-sum valuation** — `v_𝔓(g(χ)) = s(a(𝔓))` for each prime `𝔓 | ℓ` of
   `𝓞 L`, where `a(𝔓) ∈ (ZMod p)ˣ` indexes `𝔓` (via the order-`p` residue
   character / Frobenius) and `s(a)` is the digit-sum. THE deep theorem.
2. **(v) descent** — push the `𝓞 L`-ideal `(g(χ)^p)` (whose factorisation over
   primes `𝔓 | ℓ` is read off from (iv)) down to the `𝓞 K`-ideal
   `∏_a (σ_a 𝔮₀)^{e_a}`, using that primes of `𝓞 L` above `ℓ` lie over primes of
   `𝓞 K` above `ℓ` with the cyclotomic Galois action compatible, and that
   `g(χ)^p` is (iii)/(v-Jacobi) a `K`-rational quantity up to `(ℓ)`.
-/

section DeepCoreDecomposition

universe v

variable (p : ℕ) [hp : Fact p.Prime]
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
variable (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (L : Type v) [Field L] [NumberField L] [IsCyclotomicExtension {p * ℓ} ℚ L]

local instance : NeZero (p * ℓ) := ⟨Nat.mul_ne_zero hp.out.ne_zero hℓ.out.ne_zero⟩
local instance : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

/-- **The Stickelberger digit** `⟨b⟩` for the order-`p` Gauss sum, the fixed
target value of the deep valuation theorem (iv). For a character of order exactly
`p` over the completely-split residue field `ZMod ℓ` (`ℓ ≡ 1 mod p`), the
`𝔓`-adic valuation of `g(χ)` at the prime `𝔓 = σ_b 𝔓₀` is the canonical
representative `(b : ZMod p).val ∈ {1, …, p-1}` of the indexing unit `b`. This is
the Stickelberger element coefficient `θ_p` read at `σ_{b⁻¹}` (cf.
`Stickelberger/Integrality.lean`'s `stickelbergerScaled`, whose `σ_{b⁻¹}`
coefficient is `(b : ZMod p).val`). -/
def stickelbergerDigit (b : (ZMod p)ˣ) : ℕ := ((b : ZMod p)).val

/-- **Digit-carry recursion (`ZMod p` arithmetic).** For `x y : ZMod p`, the base-`p`
digits satisfy

  `⟨x⟩ + ⟨y⟩ = ⟨x + y⟩ + p · c`,   `c = if p ≤ ⟨x⟩ + ⟨y⟩ then 1 else 0 ∈ {0, 1}`.

This is the pure-arithmetic carry identity underlying the Stickelberger digit
recursion: combined with the Gauss-sum valuation recursion
(`gaussSumL_count_recursion`) and the Jacobi carry valuation
`v_{𝔓₀}(J(χ^{j-1},χ)) = p · c` (with `x = (j-1)b₀`, `y = b₀`, `x + y = j b₀`), it
forces `v_{𝔓₀}(g(χ^j)) = ⟨j b₀⟩`. Proved from `ZMod.val_add` (`(x+y).val =
(x.val + y.val) % p`) and `ZMod.val_lt` (each digit `< p`, so the quotient is
`0` or `1`). -/
theorem stickelbergerDigit_add_carry (x y : ZMod p) :
    (x : ZMod p).val + (y : ZMod p).val =
      (x + y : ZMod p).val + p * (if p ≤ x.val + y.val then 1 else 0) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hxlt : x.val < p := ZMod.val_lt x
  have hylt : y.val < p := ZMod.val_lt y
  by_cases hle : p ≤ x.val + y.val
  · rw [if_pos hle, ZMod.val_add_val_of_le hle]
    omega
  · rw [if_neg hle, ZMod.val_add_of_lt (by omega)]
    omega

/-! ### Refined decomposition of (iv-b): the exact digit-sum valuation

The foundational leaves above (in the `GaussSumSetup` section) have discharged the
two *bounds* on the per-prime valuation `v_𝔓(g(χ))`, for every prime `𝔓 | ℓ` of
`𝓞 L`:

* **lower bound** `v_𝔓(g(χ)) ≥ 1` — `gaussSumL_mem_prime_of_liesOver_ell`
  (`g(χ) ∈ 𝔓` since `ζ_ℓ ≡ 1 mod 𝔓` and `∑_t χ(t) = 0`);
* **complementary sum** `v_𝔓(g(χ)) + v_𝔓(g(χ⁻¹)) = ℓ - 1` —
  `gaussSumL_count_add_inv_eq_sub_one` (from `(g(χ))(g(χ⁻¹)) = (ℓ)` and the
  ramification `e(𝔓|ℓ) = ℓ - 1`).

What remains for (iv-b) is the **exact value**. The classical elementary route
(Washington Thm 6.10) is the **Frobenius/Galois-twist descent** through a *single*
base prime `𝔓₀`, decomposed below into three named predicates. The arithmetic
backbone is the action of the cyclotomic Galois group on the Gauss sum:

  `Gal(L/ℚ) ≅ (ZMod p)ˣ × (ZMod ℓ)ˣ`,

with the `(ZMod p)ˣ`-factor `σ_a` (acting `ζ_p ↦ ζ_p^a`, fixing `ζ_ℓ`) permuting
the `p - 1` primes `𝔓_a := σ_a 𝔓₀` above `ℓ` *transitively*, and acting on the
`μ_p`-valued character by `σ_a(χ(t)) = χ(t)^a`, hence on the Gauss sum (whose `ψ`
is `σ_a`-fixed) by

  `σ_a(g(χ)) = ∑_t χ(t)^a · ψ(t) = g(χ^a)`.

Therefore `v_{𝔓_a}(g(χ)) = v_{𝔓₀}(σ_a⁻¹ g(χ)) = v_{𝔓₀}(g(χ^{a⁻¹}))`, so the entire
per-prime valuation vector is governed by the *single-prime power-character valuation*
`j ↦ v_{𝔓₀}(g(χ^j))`. The Stickelberger content is that this single function is the
digit `⟨·⟩`. -/

/-- **(iv-b1) Galois twist — `σ_a(g(χ)) = g(χ^a)`.** The action on the Gauss sum
of the cyclotomic Galois automorphism `σ_a` (`ζ_p ↦ ζ_p^a`, `ζ_ℓ` fixed) sends
`g(χ)` to `g(χ^a)`. *Discharger:* `MulChar.ringHomComp` + `gaussSum_ringHomComp`
(`gaussSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (gaussSum χ ψ)`) with
`f = σ_a` restricted to `𝓞 L`, using that `σ_a` fixes `ζ_ℓ` (so `ψ.ringHomComp σ_a
= ψ`) and acts as the `a`-th power on `μ_p ∋ χ(t)` (so `χ.ringHomComp σ_a = χ^a`).
This is the mechanism that ties the orbit valuations together; it requires the
`Gal(L/ℚ) ≅ (ZMod p)ˣ × (ZMod ℓ)ˣ` factorisation and the `μ_p`-power action of the
`(ZMod p)ˣ`-factor. -/
def GaussSumGaloisTwist : Prop :=
  ∀ (χ : MulChar (ZMod ℓ) (𝓞 L)), orderOf χ = p →
    ∀ a : (ZMod p)ˣ, ∃ σ : 𝓞 L ≃+* 𝓞 L,
      (Ideal.span ({gaussSum (χ ^ (a : ZMod p).val)
          (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L))) =
        Ideal.map σ (Ideal.span ({gaussSum χ
          (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)))

/-- **(iv-b2) THE deepest sub-leaf: single-prime power-character valuation
(Stickelberger congruence proper).**

For a *fixed* base prime `𝔓₀` of `𝓞 L` above `ℓ` and the order-`p` character `χ`
(indexed so that `v_{𝔓₀}(g(χ)) = 1`), the `𝔓₀`-adic valuation of the power-character
Gauss sum `g(χ^j)` is the digit:

  `v_{𝔓₀}(g(χ^j)) = ⟨j·b₀⟩ = ((j·b₀ : ZMod p)).val`   for `j ∈ (ZMod p)ˣ`,

where `b₀` is the index of `𝔓₀`. **This is the irreducible classical core** of
Stickelberger's theorem (Washington Thm 6.10 / Lemma 6.1–6.2), with *no mathlib
support* (mathlib has Gauss/Jacobi sums but neither the Stickelberger congruence
nor Gross–Koblitz). Its elementary proof is the congruence

  `g(χ^j) ≡ unit · π^{⟨j·b₀⟩} (mod 𝔓₀^{⟨j·b₀⟩+1})`,   `π = ζ_ℓ - 1`,  `v_{𝔓₀}(π)=1`,

proved by induction on `j` via the Jacobi-sum recursion combined with the digit
recursion and the carry-count valuation of `J(χ^{j-1}, χ)`.

#### Reduction achieved (proven infrastructure in `GaussSumSetup`)

The induction's *structural* backbone is now fully proved and axiom-clean:

* **Jacobi-sum recursion** `g(χ^j)·J(χ^{j-1},χ) = g(χ^{j-1})·g(χ)` —
  `gaussSumL_mul_eq_jacobiSum_mul`;
* **count-additive single step**
  `v_{𝔓₀}(g(χ^j)) + v_{𝔓₀}(J(χ^{j-1},χ)) = v_{𝔓₀}(g(χ^{j-1})) + v_{𝔓₀}(g(χ))` —
  `gaussSumL_count_recursion`;
* **telescoped power valuation**
  `v_{𝔓₀}(g(χ^n)) + Σ_{i=1}^{n-1} v_{𝔓₀}(J(χ,χ^i)) = n·v_{𝔓₀}(g(χ))` —
  `gaussSumL_count_pow_telescope` (`0 < n < p`);
* **digit-carry arithmetic** `⟨x⟩+⟨y⟩ = ⟨x+y⟩ + p·[carry]` —
  `stickelbergerDigit_add_carry`;
* **base/bounds** `1 ≤ v_{𝔓₀}(g(χ))` (`one_le_gaussSumL_count_of_liesOver_ell`) and
  `v_{𝔓₀}(g(χ)) + v_{𝔓₀}(g(χ⁻¹)) = ℓ - 1` (`gaussSumL_count_add_inv_eq_sub_one`).

Setting `d := v_{𝔓₀}(g(χ))` and `b₀ := (d : ZMod p)` (`b₀` is a unit since
`1 ≤ d ≤ ℓ-2` and `p ∣ ℓ-1`), the telescope + `stickelbergerDigit_add_carry`
reduce the target `v_{𝔓₀}(g(χ^n)) = ⟨n·b₀⟩` to the *single* irreducible input:

  **(Jacobi carry valuation)** `v_{𝔓₀}(J(χ, χ^i)) = p · [⟨i·d⟩ + ⟨d⟩ ≥ p]`
  for `1 ≤ i < p-1`,

i.e. the per-step Jacobi sum is a `𝔓₀`-unit in the no-carry case and has
`𝔓₀`-valuation exactly `p` in the carry case. This is Stickelberger's congruence
proper (Washington Lemma 6.2 / Gross–Koblitz), with no mathlib support: its proof
needs the Teichmüller expansion `χ(t) ≡ t^{-d(ℓ-1)/p}` and the congruence
`g(χ) ≡ -π^d/d! (mod 𝔓₀^{d+1})`, `π = ζ_ℓ - 1`, i.e. the ℓ-adic Gamma /
factorial machinery — a separate development. -/
def SinglePrimePowerValuation : Prop :=
  ∀ (χ : MulChar (ZMod ℓ) (𝓞 L)), orderOf χ = p →
    ∀ (𝔓₀ : Ideal (𝓞 L)), 𝔓₀.IsPrime → 𝔓₀.LiesOver (Ideal.span {(ℓ : ℤ)}) →
      ∃ b₀ : (ZMod p)ˣ, ∀ j : (ZMod p)ˣ,
        (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({gaussSum (χ ^ (j : ZMod p).val)
            (addCharL (p := p) (ℓ := ℓ) (L := L))} : Set (𝓞 L)))).count 𝔓₀ =
          ((j * b₀ : (ZMod p)ˣ) : ZMod p).val

/-- **(iv) Stickelberger digit-sum valuation — THE deep theorem (Gross–Koblitz /
Washington Thm 6.10).**

For an order-`p` multiplicative character `χ : (ZMod ℓ)ˣ → μ_p ⊂ 𝓞 L`, and each
prime `𝔓` of `𝓞 L` lying above `ℓ`, the `𝔓`-adic valuation of the Gauss sum
`g(χ)` equals the **base-`p` digit-sum** `s` attached to the residue character at
`𝔓`:

  `v_𝔓( g(χ) ) = s(𝔓)`.

Concretely (Washington §6.2): label the primes `𝔓` of `𝓞 L` above `ℓ` by the
elements `t ∈ (ZMod p)ˣ` (the Frobenius / decomposition data, since `Gal(L/ℚ)`
acts transitively with `Gal` of the residue extension cyclic), and let `χ_𝔓` be
the order-`p` residue power character. Then

  `v_𝔓(g(χ)) = ∑_{j} ⟨t · p^j / (q-1)⟩ · (q-1)/p`   (the Stickelberger sum),

equivalently the number of base-`p` digits prescribed by the Stickelberger
element. This is the unique input with **no mathlib support** (mathlib has Gauss
sums and Jacobi sums but neither the Stickelberger congruence nor the
Gross–Koblitz formula); the repo's `GaussSum/PrimeFactorization/Valuation.lean`
is specific to primes **above `p`** and is not reusable here.

#### Sub-leaves of (iv) (the ordered decomposition the analytic proof must follow)

The two *bounds* are **already proved** (foundational leaves, `GaussSumSetup`):

* **lower bound** `v_𝔓(g(χ)) ≥ 1` — `gaussSumL_mem_prime_of_liesOver_ell`;
* **complementary sum** `v_𝔓(g(χ)) + v_𝔓(g(χ⁻¹)) = ℓ - 1` —
  `gaussSumL_count_add_inv_eq_sub_one`.

The *exact value* decomposes (named predicates above) as:

* **(iv-b1) Galois twist** `σ_a(g(χ)) = g(χ^a)` — `GaussSumGaloisTwist`.
  *Discharger:* `gaussSum_ringHomComp` + the `Gal(L/ℚ) ≅ (ZMod p)ˣ × (ZMod ℓ)ˣ`
  factorisation (the `(ZMod p)ˣ`-factor acts as `μ_p`-power on `χ`-values, fixes
  `ζ_ℓ` hence `ψ`).
* **(iv-b2) Single-prime power valuation** `v_{𝔓₀}(g(χ^j)) = ⟨j b₀⟩` —
  `SinglePrimePowerValuation`. **THE deepest sub-leaf** (Stickelberger congruence
  proper, no mathlib support); see its docstring for the Jacobi-recursion /
  binomial-Teichmüller proof.
* **(iv-b3) Orbit assembly** (iv-b1)+(iv-b2) ⟹ this predicate — `OrbitAssembly`.
  *Discharger:* `normalizedFactors` `count` transport under the automorphism
  `σ_a` + reindexing; bookkeeping, no analytic content.

The predicate below is the *output* of (iv): the full per-prime valuation vector,
the precise datum (v) consumes.

**Non-vacuity.** The statement is *not* "there exists some `s` with
`count 𝔓 = s`" (which would be trivially true); it is the genuine assertion that
the per-prime multiplicities, read across the Galois orbit of a fixed prime
`𝔓₀ | ℓ`, follow the **specific Stickelberger digit pattern**
`stickelbergerDigit` (below). Pinning that the multiplicity at `σ_b 𝔓₀` equals the
prescribed digit `⟨b⟩` *is* Stickelberger's theorem; the existential is only over
the choice of base prime `𝔓₀` and the orbit-indexing bijection (sub-leaf iv-a),
while the digit values are fixed data. -/
def StickelbergerDigitSumValuation : Prop :=
  ∀ (χ : MulChar (ZMod ℓ) (𝓞 L)), orderOf χ = p →
    -- there is a base prime `𝔓₀ | ℓ` of `𝓞 L` and a `(ZMod p)ˣ`-indexing
    -- `idx` of (a subfamily of) the primes above `ℓ` — sub-leaf (iv-a) —
    ∃ (idx : (ZMod p)ˣ → Ideal (𝓞 L)),
      (∀ b, (idx b).IsPrime ∧ (idx b).LiesOver (Ideal.span {(ℓ : ℤ)})) ∧
      -- such that the multiplicity of `idx b` in the factorisation of `(g(χ))`
      -- equals the prescribed Stickelberger digit `⟨b⟩` — sub-leaves (iv-b,c).
      ∀ b : (ZMod p)ˣ, (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSum χ (addCharL (p := p) (ℓ := ℓ) (L := L))} :
          Set (𝓞 L)))).count (idx b) = stickelbergerDigit p b

/-- **(iv-b3) Orbit assembly: (iv-b1)+(iv-b2) ⟹ `StickelbergerDigitSumValuation`.**
The per-prime valuation vector `v_{𝔓_a}(g(χ)) = ⟨a⁻¹ b₀⟩` (suitably indexed)
follows from the single-prime values `v_{𝔓₀}(g(χ^j)) = ⟨j b₀⟩` (iv-b2,
`SinglePrimePowerValuation`) transported across the orbit by the Galois twist
`σ_a(g(χ)) = g(χ^a)` (iv-b1, `GaussSumGaloisTwist`):
`v_{𝔓_a}(g(χ)) = v_{𝔓₀}(g(χ^{a⁻¹})) = ⟨a⁻¹ b₀⟩`. *Discharger:* `Ideal.map` /
`normalizedFactors` transport under the ring automorphism `σ_a` (the `count` is
preserved by `σ_a`, cf. `stickelbergerOrbitIdeal_galAction`) + the reindexing
`b ↦ b·b₀⁻¹` (a bijection of `(ZMod p)ˣ` matching `idx b := σ_{b·b₀⁻¹}⁻¹ 𝔓₀`).
This is bookkeeping over (iv-b1,2), not fresh analytic content. -/
def OrbitAssembly : Prop :=
  GaussSumGaloisTwist p ℓ L → SinglePrimePowerValuation p ℓ L →
    StickelbergerDigitSumValuation p ℓ L

/-- **(v) Descent `𝓞 L → 𝓞 K` of the Gauss-sum `p`-th power.**

Given the per-prime valuations from (iv), the principal ideal `(g(χ)^p)` of
`𝓞 L` descends to the Stickelberger orbit ideal `∏_a (σ_a 𝔮₀)^{e_a}` of `𝓞 K`:

  for the chosen prime `𝔮₀ ⊂ 𝓞 K` above `ℓ`, there is an exponent vector
  `e : (ZMod p)ˣ → ℕ` (the Stickelberger digit-sums) and a generator `γ ∈ 𝓞 K`
  with `(γ) = ∏_a (σ_a 𝔮₀)^{e a}` — i.e. the orbit ideal is **principal**.

This is exactly the hypothesis `h` consumed by
`stickelbergerOrbitIdeal_isPrincipal_of_under_eq`.

#### Sub-leaves of (v) (ordered)

* **(v-a) `g(χ)^p ∈ K` up to `(ℓ)`.** By `gaussSumL_pow_eq_prod_jacobiSum` and
  `jacobiSumL_mem_algebraAdjoin`, `g(χ)^p = χ(-1)·ℓ·∏ J(χ,χ^i)` with each
  `J(χ,χ^i) ∈ ℤ[μ_p] = 𝓞 K`. *Discharger:* the two (v)-Jacobi lemmas above
  (already proved) + identification `Algebra.adjoin ℤ {μ_p} = 𝓞 K`-image. **The
  Jacobi-sum route makes this the clean entry point and avoids the relative-norm
  bookkeeping flagged in the brief.**
* **(v-b) Prime correspondence `𝔓 | ℓ` in `𝓞 L` ↔ `𝔮 | ℓ` in `𝓞 K`.** Each
  prime `𝔮` of `𝓞 K` above `ℓ` has a unique prime `𝔓` of `𝓞 L` above it (since
  `[L:K] = ℓ - 1` and `ℓ` splits completely in `K`, totally ramified-free here),
  with `e(𝔓|𝔮)·f(𝔓|𝔮)` controlled. *Discharger:* `Ideal.primesOver` /
  `Ideal.under` API + sub-leaf (i) splitting counts.
* **(v-c) Exponent transport.** Combine (iv) per-`𝔓` valuations with (v-b) to get
  the per-`𝔮` valuations `v_𝔮(g(χ)^p ∩ 𝓞 K) = e_a`, and assemble
  `(γ) = ∏_a (σ_a 𝔮₀)^{e a}` via `Ideal.prod_normalizedFactors_eq_self`.
  *Discharger:* Dedekind-domain factorisation API (cf.
  `gaussSum_ideal_factorisation` in `CyclotomicEmbedding.lean`).

The predicate below is the descent conclusion in the exact form
`stickelbergerOrbitIdeal_isPrincipal_of_under_eq` expects: principality of the
orbit ideal for the **specific Stickelberger digit-sum exponent vector**
`stickelbergerDigit` (the `e` produced by (iv)), at a prime `𝔮₀ | ℓ` of `𝓞 K`.

This is a genuine (non-vacuous) `IsPrincipal` claim about a *fixed* ideal: it is
false for a generic exponent vector and true exactly because the digit-sums are
the Gauss-sum valuations (the hypothesis `StickelbergerDigitSumValuation`). It is
the principal-generator output (`γ = g(χ)^p` descended to `K`, up to `(ℓ)`) that
discharges `h` of `stickelbergerOrbitIdeal_isPrincipal_of_under_eq`. -/
def GaussSumDescentToK : Prop :=
  StickelbergerDigitSumValuation p ℓ L →
    ∀ (𝔮₀ : Ideal (𝓞 K)) [𝔮₀.IsPrime],
      𝔮₀.LiesOver (Ideal.span {(ℓ : ℤ)}) →
      (stickelbergerOrbitIdeal (p := p) (K := K) (stickelbergerDigit p) 𝔮₀).IsPrincipal

end DeepCoreDecomposition

end Eichler

end FLT37

end BernoulliRegular

end
