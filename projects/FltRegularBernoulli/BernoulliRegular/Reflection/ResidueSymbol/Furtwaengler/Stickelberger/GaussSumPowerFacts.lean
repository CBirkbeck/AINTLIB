module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Stickelberger-style prime factorisation of `g(χ_q)^p` (REF-18c2c)

This file develops the Stickelberger-type theorem for the residue Gauss sum
`g(χ_q, ψ_q)` raised to its character order. The classical statement
(Ireland–Rosen Thm 14.5) gives the explicit prime factorisation of
`g(χ_q)^p` in `𝓞_{K(ζ_{Nq})}`, with exponents controlled by the
Stickelberger weight. We work in stages:

1. **Galois invariance of `g(χ)^n`** (this commit).
   For χ a multiplicative character of order dividing `n`, and a ring hom
   `σ : R' →+* R'` that *fixes* χ (`σ ∘ χ = χ`) and shifts the additive
   character ψ by some `a ∈ Rˣ` (`σ ∘ ψ = AddChar.mulShift ψ a`), the `n`-th
   power `g(χ, ψ)^n` is fixed by `σ`. Proof: `g(χ, AddChar.mulShift ψ a)^n` is
   `(χ a)⁻ⁿ · g(χ, ψ)^n` by `gaussSum_mulShift` raised to `n`, and
   `(χ a)^n = (χ^n) a = 1 a = 1` because `χ^n = 1`.

2. **Application to residue Gauss sums** (this commit).
   For `χ_q` of order `p` (residue character) and any Galois automorphism
   `σ` fixing `K = ℚ(ζ_p)` pointwise (so `σ ∘ χ_q = χ_q`), `g(χ_q, ψ_q)^p`
   is fixed by `σ`.

3. **Prime factorisation via Stickelberger weight** (deferred).
   The actual Stickelberger formula `g(χ_q)^p = q^{p-1} · ∏ σ_a^{?}`
   requires the explicit Galois-orbit computation and Jacobi-sum
   factorisation. This is the core of REF-18c2c and is left for follow-up
   commits.

The Galois-invariance step is small but essential: it shows that
`g(χ_q, ψ_q)^p` *descends* from the larger ring `R' = K(ζ_{Nq})` to the
fixed field of the appropriate Galois group, which in our application
will be `K = ℚ(ζ_p)`. This is the key feature exploited by the
Stickelberger formula's prime factorisation.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

variable {R : Type*} [CommRing R] [Fintype R]
variable {R' : Type*} [CommRing R']

/-- **Galois invariance of `g(χ)^n` for characters of order dividing `n`.**

If χ : MulChar R R' has `χ^n = 1`, and σ : R' →+* R' is a ring hom that
fixes χ (i.e., `σ ∘ χ = χ`) and shifts ψ by a unit `a` (i.e.,
`σ ∘ ψ = AddChar.mulShift ψ a`), then σ fixes the `n`-th power of `g(χ, ψ)`. -/
theorem gaussSum_pow_invariant_of_pow_eq_one
    (χ : MulChar R R') (ψ : AddChar R R') {n : ℕ}
    (hχn : χ ^ n = 1)
    (σ : R' →+* R') (a : Rˣ)
    (hσχ : χ.ringHomComp σ = χ)
    (hσψ : σ.toMonoidHom.compAddChar ψ = AddChar.mulShift ψ a) :
    σ ((gaussSum χ ψ) ^ n) = (gaussSum χ ψ) ^ n := by
  rw [map_pow, gaussSum_ringHomComp, hσχ, hσψ]
  -- Goal: (gaussSum χ (AddChar.mulShift ψ a))^n = (gaussSum χ ψ)^n.
  have hmul : χ ↑a * gaussSum χ (AddChar.mulShift ψ a) = gaussSum χ ψ :=
    gaussSum_mulShift χ ψ a
  have hpow : (χ ↑a) ^ n * (gaussSum χ (AddChar.mulShift ψ a)) ^ n =
      (gaussSum χ ψ) ^ n := by
    rw [← mul_pow, hmul]
  have hχa_n : (χ ↑a) ^ n = 1 := by
    rw [← MulChar.pow_apply_coe χ n a, hχn, MulChar.one_apply_coe]
  rw [← hpow, hχa_n, one_mul]

/-- **Application: residue Gauss sum to the `p`-th power is Galois-invariant.**

For the residue character `χ_q` (order `p`) and any ring hom σ : R' →+* R'
fixing it and shifting ψ_q by some unit `a`, the `p`-th power of the
residue Gauss sum is fixed by σ. -/
theorem residueGaussSum_pow_p_invariant
    {k : Type*} [Field k] [Fintype k]
    [IsDomain R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (psi_q : AddChar k R')
    (hχ_pow_p : residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R ^ p = 1)
    (σ : R' →+* R') (a : kˣ)
    (hσχ : (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R).ringHomComp σ =
      residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
    (hσψ : σ.toMonoidHom.compAddChar psi_q = AddChar.mulShift psi_q a) :
    σ ((residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p) =
      (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p :=
  gaussSum_pow_invariant_of_pow_eq_one _ _ hχ_pow_p σ a hσχ hσψ

/-- The residue character has order dividing `p`: `χ_q^p = 1` as a `MulChar`.

This is the input the Galois invariance lemma needs. The proof goes by
extensionality: on units `↑u`, `MulChar.pow_apply_coe` reduces to
`(residueMulChar (↑u))^p`, which we already know is `1`. On non-units
(only `0` for a field), both sides are `0` by `MulChar.map_nonunit`. -/
theorem residueMulChar_pow_eq_one_mulChar
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommMonoidWithZero R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ p = 1 := by
  ext x
  rw [MulChar.pow_apply_coe, residueMulChar_pow_eq_one, MulChar.one_apply_coe]

/-- The order of the residue character is exactly `p`: it is `≤ p` (since
`χ^p = 1`) and `≠ 1` (it is non-trivial), hence equals `p` because `p` is
prime. -/
theorem orderOf_residueMulChar
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    orderOf (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) = p :=
  orderOf_eq_prime
    (residueMulChar_pow_eq_one_mulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
    (residueMulChar_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R)

/-- **Jacobi-sum chain identity for the residue Gauss sum.**

For the residue character `χ_q` (order `p`) and a primitive additive
character `ψ_q`, the `p`-th power of `g(χ_q, ψ_q)` factorises as a product
of Jacobi sums:
$$g(\chi_q, \psi_q)^p = \chi_q(-1) \cdot \#k \cdot \prod_{i=1}^{p-2}
  J(\chi_q, \chi_q^i).$$

This is mathlib's `gaussSum_pow_eq_prod_jacobiSum` specialised to the
residue setup, using `orderOf_residueMulChar = p`. The Jacobi sums on
the right live in the smaller subring spanned by `μ_p ⊆ R'` (since each
`J(χ, χ^i)` is a sum of products of values of χ in `μ_p`); this
prepares the descent of `g(χ_q)^p` into `K` (the smaller field of the
intended cyclotomic application). -/
theorem residueGaussSum_pow_p_eq_prod_jacobiSum
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive) :
    (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p =
      (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) (-1) *
        Fintype.card k *
        ∏ i ∈ Finset.Ico 1 (p - 1),
          jacobiSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
            ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i) := by
  have h_order : orderOf (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) = p :=
    orderOf_residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
  have h_ge_two : 2 ≤ orderOf (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) := by
    rw [h_order]; exact hp.out.two_le
  have key := gaussSum_pow_eq_prod_jacobiSum h_ge_two hpsi
  rw [h_order] at key
  exact key

/-- For `i` with `1 ≤ i ≤ p - 1`, the `i`-th power of the residue character
is non-trivial (since `orderOf χ_q = p`). -/
theorem residueMulChar_pow_ne_one
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {i : ℕ} (hi₁ : 1 ≤ i) (hi₂ : i ≤ p - 1) :
    (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i ≠ 1 := by
  intro h
  have h_order : orderOf (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) = p :=
    orderOf_residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
  have h_dvd : orderOf (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ∣ i :=
    orderOf_dvd_of_pow_eq_one h
  rw [h_order] at h_dvd
  have hp_pos : 0 < p := hp.out.pos
  have hi_lt : i < p := lt_of_le_of_lt hi₂ (Nat.sub_lt hp_pos Nat.one_pos)
  have hi_le := Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.one_pos hi₁) h_dvd
  omega

/-- **Bilinear identity for residue Jacobi sums.** For `1 ≤ i ≤ p - 2`,
`g(χ_q^{i+1}, ψ_q) · J(χ_q, χ_q^i) = g(χ_q, ψ_q) · g(χ_q^i, ψ_q)`.

This is the residue specialisation of mathlib's `jacobiSum_mul_nontrivial`,
expressing the Jacobi sum as a "Gauss sum quotient":
`J(χ, χ^i) = g(χ) · g(χ^i) / g(χ^{i+1})` (in the field case). -/
theorem residueJacobiSum_mul_gaussSum_eq
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (psi_q : AddChar k R')
    {i : ℕ} (hi₁ : 1 ≤ i) (hi₂ : i ≤ p - 2) :
    gaussSum ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ (i + 1)) psi_q *
        jacobiSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
          ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i) =
      residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q *
        gaussSum ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i) psi_q := by
  have h_χχi_ne : residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R *
      (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i ≠ 1 := by
    rw [← pow_succ']
    apply residueMulChar_pow_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R
      (by omega) (by omega)
  have key := jacobiSum_mul_nontrivial h_χχi_ne psi_q
  -- key : g(χ * χ^i) · J = g(χ) · g(χ^i)
  rw [← pow_succ'] at key
  exact key

/-- **Jacobi-sum norm relation for the residue character.** For
`1 ≤ i ≤ p - 2`, the product `J(χ_q, χ_q^i) · J(χ_q⁻¹, χ_q^{-i}) = #k`.

Specialisation of mathlib's `jacobiSum_mul_jacobiSum_inv`, applicable
once the target field `R'` has characteristic distinct from the residue
field's characteristic (which holds when `R'` extends `K = ℚ(ζ_p)` in
characteristic 0). -/
theorem residueJacobiSum_mul_inv
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [Field R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (h_char : ringChar R' ≠ ringChar k)
    {i : ℕ} (hi₁ : 1 ≤ i) (hi₂ : i ≤ p - 2) :
    jacobiSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
        ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i) *
      jacobiSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)⁻¹
        ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i)⁻¹ =
        Fintype.card k := by
  have hp_pos : 0 < p := hp.out.pos
  have h_χ_ne : residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R ≠ 1 :=
    residueMulChar_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R
  have hi_lt_p : i ≤ p - 1 := le_trans hi₂ (Nat.sub_le_sub_left (by omega) p)
  have h_χi_ne : (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i ≠ 1 :=
    residueMulChar_pow_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R hi₁ hi_lt_p
  have h_χχi_ne : residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R *
      (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i ≠ 1 := by
    rw [← pow_succ']
    apply residueMulChar_pow_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R (by omega) (by omega)
  exact jacobiSum_mul_jacobiSum_inv h_char h_χ_ne h_χi_ne h_χχi_ne

/-- **Conjugate-pair relation for the residue Gauss sum.** For `χ_q` of
order `p` and `ψ_q` primitive, `g(χ_q, ψ_q) · g(χ_q^{p-1}, ψ_q) = χ_q(-1) · #k`.

This is the residue specialisation of mathlib's
`gaussSum_mul_gaussSum_pow_orderOf_sub_one`, using `orderOf χ_q = p`.
For `p` odd, `χ_q^{p-1} = χ_q^{-1}`, so this is the standard "norm
relation" `g(χ) · g(χ⁻¹) = χ(-1) · #k`. -/
theorem residueGaussSum_mul_gaussSum_pow_p_sub_one
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive) :
    (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) *
      gaussSum ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ (p - 1)) psi_q =
        (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) (-1) *
          Fintype.card k := by
  have h_order : orderOf (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) = p :=
    orderOf_residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
  have key := gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (residueMulChar_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R) hpsi
  rw [h_order] at key
  exact key

/-!
### Subring descent: `J(χ_q, χ_q^i)` lies in `Subring.closure {ζ_R}`

Each Jacobi sum `J(χ_q, χ_q^i) = -∑_x χ_q(x) χ_q^i(1-x)` is a finite ℤ-linear
combination of products of values of `χ_q`. Since `χ_q` takes values in
`{0} ∪ μ_p`, all of which lie in the subring `ℤ[ζ_R]` generated by `ζ_R`,
each Jacobi sum lies in this subring. This formalises the descent of
`g(χ_q)^p = χ_q(-1) · #k · ∏ J(χ_q, χ_q^i)` from the ambient ring `R'` to
the smaller subring `Subring.closure {ζ_R}` — which is `ℤ[ζ_p]` in the
intended cyclotomic application, and equals `𝓞_K` for `K = ℚ(ζ_p)`.
-/

/-!
### q-adic valuation of `g(χ_q)` (REF-18c2c2 — abstract form)

The classical Stickelberger argument proves `g(χ_q) ∈ P` for `P` a prime
ideal of `𝓞_{R'}` above the rational prime `q`, by reducing the Gauss
sum modulo `P` and using that `ζ_q ≡ 1 (mod P)` plus the vanishing of
non-trivial character sums.

We package this as a clean abstract lemma: if any ideal `I ⊆ R'` contains
`ψ(x) - 1` for all `x : R`, then it contains `gaussSum χ ψ` (for `χ ≠ 1`).
The concrete instantiation `I = P, ψ_q(x) - 1 = (ζ_q^{Tr(x)} - 1) ∈ P`
is the content of a later subticket since it requires concrete cyclotomic
extension scaffolding.
-/

/-- **Abstract form of REF-18c2c2.** For a non-trivial multiplicative
character `χ` and an additive character `ψ` that is "constantly 1 mod `I`"
(i.e., `ψ(x) - 1 ∈ I` for all `x`), the Gauss sum lies in `I`.

The proof splits `g(χ, ψ) = ∑ χ(x) (ψ(x) - 1) + ∑ χ(x)`. The second sum
vanishes because `χ ≠ 1` (via `MulChar.sum_eq_zero_of_ne_one`); the first
is in `I` because each summand is (by closure under R'-multiplication). -/
theorem gaussSum_mem_ideal_of_addChar_sub_one_mem
    {R : Type*} [CommRing R] [Fintype R]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {χ : MulChar R R'} (hχ : χ ≠ 1) (ψ : AddChar R R')
    {I : Ideal R'} (h : ∀ x : R, ψ x - 1 ∈ I) :
    gaussSum χ ψ ∈ I := by
  have h_split : gaussSum χ ψ = ∑ x, χ x * (ψ x - 1) + ∑ x, χ x := by
    unfold gaussSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_sub, mul_one, sub_add_cancel]
  rw [h_split, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]
  exact Ideal.sum_mem _ (fun x _ => Ideal.mul_mem_left _ _ (h x))

/-- **Algebraic helper for the concrete instantiation of REF-18c2c2.**
If `x - 1 ∈ I`, then `x^n - 1 ∈ I` for all `n`. Useful when verifying the
hypothesis of `gaussSum_mem_ideal_of_addChar_sub_one_mem` for the concrete
additive character `ψ_q(x) = ζ_q^{Tr(x)}`: assuming `ζ_q - 1 ∈ P` (the
cyclotomic ramification fact for `P` above `q`), this gives
`ψ_q(x) - 1 = ζ_q^{Tr(x)} - 1 ∈ P` for all `x`. -/
theorem pow_sub_one_mem_of_sub_one_mem
    {R : Type*} [CommRing R] (x : R) (n : ℕ)
    {I : Ideal R} (h : x - 1 ∈ I) :
    x ^ n - 1 ∈ I := by
  obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one x n
  rw [hc]
  exact Ideal.mul_mem_right _ _ h

/-- **Residue Gauss sum specialisation of REF-18c2c2.** If `ψ_q` of a
`StickelbergerSetup` is "constantly 1 mod `I`" on the residue field `k`,
then `g(χ_q) ∈ I`.

In the intended cyclotomic application, `I = P` is a prime ideal of `𝓞_{R'}`
above the rational prime `q`. The hypothesis `ψ_q(x) - 1 ∈ P` for all `x`
follows from `ζ_q ≡ 1 (mod P)`, which is the standard cyclotomic
ramification fact `(ζ_q - 1)^{q-1} ∼ q`. Establishing this for a concrete
`R' = K(ζ_q)` is a separate subticket (it needs ring-of-integers
infrastructure not yet in scope). -/
theorem residueGaussSum_mem_ideal_of_psi_sub_one_mem
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'}
    {I : Ideal R'} (h : ∀ x : k, psi_q x - 1 ∈ I) :
    residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q ∈ I :=
  gaussSum_mem_ideal_of_addChar_sub_one_mem
    (residueMulChar_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R) psi_q h

/-- **Galois compatibility of `residueMulChar`.** For a ring hom
`σ : R' →+* R'` that sends `ζ_R` to `ζ_R^a`, post-composition of the
residue MulChar with `σ` equals the `a`-th power character:
`σ ∘ residueMulChar = (residueMulChar)^a`.

This identifies how a Galois automorphism `σ` (concretely `σ_a` sending
`ζ_R ↦ ζ_R^a`) permutes the residue character among its powers. Combined
with `gaussSum_ringHomComp` (REF-18c2b), it gives the input REF-18c2c3
needs for the Galois orbit assembly: `σ_a(g(χ_q)) = g(χ_q^a, σ_a · ψ_q)`
after suitable adjustment. -/
theorem residueMulChar_ringHomComp_pow_eq
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R') (a : ℕ)
    (hσ : σ ((zeta_R : R'ˣ) : R') = ((zeta_R : R'ˣ) : R') ^ a) :
    (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R).ringHomComp σ =
      (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ a := by
  ext x
  rw [MulChar.ringHomComp_apply, MulChar.pow_apply_coe,
      residueMulChar_apply_unit, σ.map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

/-!
### Galois orbit of `g(χ_q)` (REF-18c2c3 — abstract form)

Combining `residueGaussSum_ringHomComp` (REF-18c2b) with the character
compatibility `residueMulChar_ringHomComp_pow_eq` above gives the
*abstract Galois orbit identity*: for any ring hom `σ : R' →+* R'`
sending `ζ_R ↦ ζ_R^a`,

  `σ(g(χ_q, ψ_q)) = g(χ_q^a, σ ∘ ψ_q)`.

In the concrete cyclotomic application (`R' = K(ζ_q)` and σ_a the
Galois automorphism with `ζ_q ↦ ζ_q^a`), the additive character
transforms as `(σ_a · ψ_q)(x) = ψ_q(a·x)`; the substitution `y = a·x`
then converts the right-hand side into a multiple of `g(χ_q^a, ψ_q)`
controlled by `χ_q^a(a^{-1})`. That refinement requires the concrete
trace formula `ψ_q(x) = ζ_q^{Tr(x)}` and is deferred to REF-18c2c4
together with the prime-ideal factorisation work.
-/

/-- **Abstract form of REF-18c2c3** (Galois orbit of `residueGaussSum`).
For any ring hom `σ : R' →+* R'` sending `ζ_R ↦ ζ_R^a`,
`σ(g(χ_q, ψ_q)) = gaussSum (χ_q^a) (σ ∘ ψ_q)`.

This is the basic Galois transformation rule. The key inputs are
`residueGaussSum_ringHomComp` (REF-18c2b) and
`residueMulChar_ringHomComp_pow_eq` (above). -/
theorem residueGaussSum_ringHomComp_pow_eq
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (psi_q : AddChar k R')
    (σ : R' →+* R') (a : ℕ)
    (hσ : σ ((zeta_R : R'ˣ) : R') = ((zeta_R : R'ˣ) : R') ^ a) :
    σ (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) =
      gaussSum
        ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ a)
        (σ.toMonoidHom.compAddChar psi_q) := by
  rw [residueGaussSum_ringHomComp,
      residueMulChar_ringHomComp_pow_eq zeta_q hzeta_q hdiv zeta_R hzeta_R σ a hσ]

/-- Each value of `residueMulChar` lies in `Subring.closure {(ζ_R : R')}`,
the subring generated by the chosen primitive `p`-th root of unity. -/
theorem residueMulChar_apply_mem_closure
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (x : k) :
    residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R x ∈
      Subring.closure {((zeta_R : R'ˣ) : R')} := by
  by_cases hx : IsUnit x
  · obtain ⟨xu, rfl⟩ := hx
    rw [residueMulChar_apply_unit]
    exact Subring.pow_mem _
      (Subring.subset_closure (Set.mem_singleton _)) _
  · rw [MulChar.map_nonunit _ hx]
    exact Subring.zero_mem _

/-- Each value of `(residueMulChar)^i` lies in `Subring.closure {(ζ_R : R')}`. -/
theorem residueMulChar_pow_apply_mem_closure
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (i : ℕ) (y : k) :
    ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i) y ∈
      Subring.closure {((zeta_R : R'ˣ) : R')} := by
  by_cases hy : IsUnit y
  · obtain ⟨yu, rfl⟩ := hy
    rw [MulChar.pow_apply_coe]
    exact Subring.pow_mem _
      (residueMulChar_apply_mem_closure zeta_q hzeta_q hdiv zeta_R hzeta_R _) _
  · rw [MulChar.map_nonunit _ hy]
    exact Subring.zero_mem _

/-- Each Jacobi sum `J(χ_q, χ_q^i)` lies in `Subring.closure {(ζ_R : R')}`. -/
theorem residueJacobiSum_mem_closure
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (i : ℕ) :
    jacobiSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
        ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i) ∈
      Subring.closure {((zeta_R : R'ˣ) : R')} := by
  unfold jacobiSum
  apply Subring.sum_mem
  intro x _
  apply Subring.mul_mem
  · exact residueMulChar_apply_mem_closure zeta_q hzeta_q hdiv zeta_R hzeta_R x
  · exact residueMulChar_pow_apply_mem_closure zeta_q hzeta_q hdiv zeta_R hzeta_R i (1 - x)

/-- **Subring descent.** `g(χ_q, ψ_q)^p` lies in `Subring.closure {(ζ_R : R')}`,
provided `ψ_q` is primitive (so the Jacobi-sum chain identity applies).

In the intended cyclotomic application with `R' = K(ζ_{Nq})` and
`zeta_R ∈ K = ℚ(ζ_p)`, the closure equals `ℤ[ζ_p] = 𝓞_K`, so
`g(χ_q, ψ_q)^p ∈ 𝓞_K` — the key descent that REF-18c2d will exploit. -/
theorem residueGaussSum_pow_p_mem_closure
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive) :
    (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p ∈
      Subring.closure {((zeta_R : R'ˣ) : R')} := by
  rw [residueGaussSum_pow_p_eq_prod_jacobiSum zeta_q hzeta_q hdiv zeta_R hzeta_R hpsi]
  apply Subring.mul_mem
  · apply Subring.mul_mem
    · exact residueMulChar_apply_mem_closure zeta_q hzeta_q hdiv zeta_R hzeta_R (-1)
    · exact natCast_mem _ _
  · apply Subring.prod_mem
    intro i _
    exact residueJacobiSum_mem_closure zeta_q hzeta_q hdiv zeta_R hzeta_R i

/-- Generic lemma: if `y` is integral over `ℤ` and `x ∈ Subring.closure {y}`,
then `x` is integral over `ℤ`. The integral closure is itself a subring,
containing `y`, hence contains `Subring.closure {y}`. -/
private theorem isIntegral_of_mem_closure_singleton
    {R' : Type*} [CommRing R'] {y : R'} (hy : IsIntegral ℤ y)
    {x : R'} (hx : x ∈ Subring.closure {y}) :
    IsIntegral ℤ x := by
  refine Subring.closure_induction
    (p := fun x _ => IsIntegral ℤ x) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    exact hz ▸ hy
  · exact isIntegral_zero
  · exact isIntegral_one
  · exact fun _ _ _ _ ha hb => ha.add hb
  · exact fun _ _ ha => ha.neg
  · exact fun _ _ _ _ ha hb => ha.mul hb

/-- **Algebraic-integer corollary for Jacobi sums.** `J(χ_q, χ_q^i)` is
integral over `ℤ`. Follows from `residueJacobiSum_mem_closure` together
with `IsPrimitiveRoot.isIntegral` for `ζ_R`. -/
theorem residueJacobiSum_isIntegral
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (i : ℕ) :
    IsIntegral ℤ
      (jacobiSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
        ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ i)) :=
  isIntegral_of_mem_closure_singleton
    ((IsPrimitiveRoot.coe_units_iff.mpr hzeta_R).isIntegral hp.out.pos)
    (residueJacobiSum_mem_closure zeta_q hzeta_q hdiv zeta_R hzeta_R i)

/-- **Algebraic-integer corollary for `g(χ_q)^p`.** `g(χ_q, ψ_q)^p` is an
algebraic integer (integral over `ℤ`).

Combines the Subring descent (`residueGaussSum_pow_p_mem_closure`) with
the fact that `ζ_R` is integral over `ℤ`. In the intended cyclotomic
application with `K = ℚ(ζ_p)`, this combined with `g(χ_q)^p ∈ K`
(provable via Galois invariance) gives `g(χ_q)^p ∈ 𝓞_K`. -/
theorem residueGaussSum_pow_p_isIntegral
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive) :
    IsIntegral ℤ
      ((residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p) :=
  isIntegral_of_mem_closure_singleton
    ((IsPrimitiveRoot.coe_units_iff.mpr hzeta_R).isIntegral hp.out.pos)
    (residueGaussSum_pow_p_mem_closure zeta_q hzeta_q hdiv zeta_R hzeta_R hpsi)

/-!
### Stickelberger weight

The integer-valued exponent appearing in the prime factorisation of
`g(χ_q^a)`: for `1 ≤ a ≤ p - 1`, this is `a · ((Nq - 1) / p)`, which counts
the contribution of the `a`-th Galois conjugate to the q-adic valuation
of the residue Gauss sum. The full Stickelberger formula combines these
weights over all conjugates.
-/

/-- The Stickelberger weight `s(p, Nq, a) := a · ((Nq - 1) / p)`,
the integer exponent for the `a`-th Galois conjugate appearing in the
prime factorisation of `g(χ_q^a)` at `q`. -/
def stickelbergerWeight (p Nq a : ℕ) : ℕ := a * ((Nq - 1) / p)

@[simp]
theorem stickelbergerWeight_zero_arg (p Nq : ℕ) :
    stickelbergerWeight p Nq 0 = 0 :=
  zero_mul _

@[simp]
theorem stickelbergerWeight_one_arg (p Nq : ℕ) :
    stickelbergerWeight p Nq 1 = (Nq - 1) / p :=
  one_mul _

theorem stickelbergerWeight_succ (p Nq a : ℕ) :
    stickelbergerWeight p Nq (a + 1) =
      stickelbergerWeight p Nq a + (Nq - 1) / p := by
  rw [stickelbergerWeight, stickelbergerWeight, Nat.add_mul, one_mul]

/-- When `p ∣ Nq - 1`, the Stickelberger weight satisfies
`p · weight(a) = a · (Nq - 1)`. -/
theorem p_mul_stickelbergerWeight (p Nq a : ℕ) (hdiv : p ∣ Nq - 1) :
    p * stickelbergerWeight p Nq a = a * (Nq - 1) := by
  rw [stickelbergerWeight, Nat.mul_left_comm, Nat.mul_div_cancel' hdiv]

/-!
### `p`-th-power Gauss-sum norm, ideal form

The conjugate-pair relation `g(χ_q) · g(χ_q^{p-1}) = χ_q(-1) · #k` raised
to the `p`-th power, combined with `χ_q(-1)^p = 1`, gives an "ideal-form"
norm: `g(χ_q)^p · g(χ_q^{p-1})^p = (#k)^p`. This is the integer-level
divisibility precursor to the prime-ideal-level Stickelberger formula.
-/

/-- `χ_q(-1)^p = 1` since `χ_q^p = 1` (as a `MulChar`). -/
theorem residueMulChar_neg_one_pow_eq_one
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommMonoidWithZero R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R (-1 : k)) ^ p = 1 := by
  obtain ⟨u, hu⟩ : IsUnit ((-1 : k)) := isUnit_one.neg
  rw [← hu, ← MulChar.pow_apply_coe,
      residueMulChar_pow_eq_one_mulChar zeta_q hzeta_q hdiv zeta_R hzeta_R,
      MulChar.one_apply_coe]

/-- **Ideal-form norm of `g(χ_q)^p`.** Combining the conjugate-pair relation
`g(χ_q) · g(χ_q^{p-1}) = χ_q(-1) · #k` raised to the `p`-th power with
`χ_q(-1)^p = 1`, we get `g(χ_q)^p · g(χ_q^{p-1})^p = (#k)^p`.

This says the ideal `(g(χ_q)^p)` in `𝓞_K` divides `((#k)^p)`, which is a
power of the rational prime under `q`. The full Stickelberger formula
refines this divisibility to an exact prime-ideal factorisation; this
identity is the ring-level precursor. -/
theorem residueGaussSum_pow_p_mul_pow_p_sub_one_eq_card_pow
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive) :
    (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p *
        (gaussSum
          ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ (p - 1)) psi_q) ^ p =
      ((Fintype.card k : R')) ^ p := by
  rw [← mul_pow,
      residueGaussSum_mul_gaussSum_pow_p_sub_one zeta_q hzeta_q hdiv zeta_R hzeta_R hpsi,
      mul_pow,
      residueMulChar_neg_one_pow_eq_one zeta_q hzeta_q hdiv zeta_R hzeta_R, one_mul]

/-!
### Abstract consequences for prime ideal factorisation (REF-18c2c4 — Phase A)

The full Stickelberger prime ideal factorisation requires concrete cyclotomic
ramification machinery (a chosen extension `R'` containing both `μ_p` and
`μ_q`, identification of the prime ideals above `q`, and the ramification fact
`(ζ_q − 1)^{q−1} ∼ q`). Before tackling that infrastructure, we collect the
algebraic consequences that follow purely from the existing abstract API.

These lemmas are useful in the eventual concrete formula and help isolate the
genuinely "cyclotomic-arithmetic" content from the underlying ring theory.
-/

/-- **q-adic ideal containment, raised power.** If the residue Gauss sum lies
in an ideal `I`, then its `n`-th power lies in `I^n`. Direct corollary of
`Ideal.pow_mem_pow`. -/
theorem residueGaussSum_pow_mem_ideal_pow
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'}
    {I : Ideal R'} (h : ∀ x : k, psi_q x - 1 ∈ I) (n : ℕ) :
    (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ n ∈ I ^ n :=
  Ideal.pow_mem_pow
    (residueGaussSum_mem_ideal_of_psi_sub_one_mem
      zeta_q hzeta_q hdiv zeta_R hzeta_R h) n

/-- **Algebraic helper for support analysis.** If `a * b = q^n` for some `n`
and a prime ideal `P` contains `a`, then `P` contains `q`.

This is a pure algebra lemma: any prime in the support of an element
dividing `q^n` must lie above `q`. -/
theorem prime_mem_of_mul_eq_pow {R : Type*} [CommRing R]
    {P : Ideal R} [hP : P.IsPrime] {a b q : R} {n : ℕ}
    (hab : a * b = q ^ n) (ha : a ∈ P) :
    q ∈ P := by
  have hqn : q ^ n ∈ P := hab ▸ Ideal.mul_mem_right b P ha
  rcases n with _ | n
  · rw [pow_zero] at hqn
    exact absurd ((Ideal.eq_top_iff_one P).mpr hqn) hP.ne_top
  · exact hP.mem_of_pow_mem _ hqn

/-- **Support of `g(χ_q)^p` lies above `q`.** Combining the `p`-th-power norm
relation `g(χ_q)^p · g(χ_q^{p-1})^p = (#k)^p` with `prime_mem_of_mul_eq_pow`:
any prime ideal containing `g(χ_q)^p` must contain `#k = q^f`, hence lies
above the rational prime under `q`.

This is the abstract content of "no extraneous prime factors": the only
primes that can appear in the ideal factorisation of `(g(χ_q)^p)` lie above
`q`. The exact exponents are then determined by the Stickelberger weights. -/
theorem residueGaussSum_pow_p_support_above_card
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive)
    {P : Ideal R'} [P.IsPrime]
    (hgauss : (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p ∈ P) :
    ((Fintype.card k : R')) ∈ P :=
  prime_mem_of_mul_eq_pow
    (residueGaussSum_pow_p_mul_pow_p_sub_one_eq_card_pow
      zeta_q hzeta_q hdiv zeta_R hzeta_R hpsi)
    hgauss

/-!
### Cyclotomic ramification (REF-18c2c4 — Phase B)

The classical ramification fact: in any commutative domain `R` containing a
primitive `q`-th root of unity `ζ` (with `q` a rational prime), every prime
ideal `Q` of `R` containing `q` also contains `ζ - 1`.

This is the algebraic content of `(ζ - 1)^{q-1} ∼ q` (the cyclotomic
ramification of `q` in `ℤ[ζ_q]`), formulated at the prime-ideal level.
The proof uses the polynomial identity `Φ_q(1) = q` together with the
factorisation `Φ_q = ∏_{μ primitive} (X - C μ)` and the associate-class
identification of `ζ - 1` with each `ζ^j - 1` for `j` coprime to `q`.

Combined with REF-18c2c2's `gaussSum_mem_ideal_of_addChar_sub_one_mem`,
this gives the concrete instantiation: `g(χ_q) ∈ Q` for `Q` above `q`,
when the additive character `ψ_q` has the form `ψ_q(x) = ζ^{Tr(x)}`.
-/

/-- **Membership preservation under associated elements.** In a commutative
ring, two associated elements lie in the same ideals. -/
private theorem _root_.Associated.mem_ideal_of_mem
    {R : Type*} [CommRing R] {a b : R} (h : Associated a b)
    {I : Ideal R} (ha : a ∈ I) :
    b ∈ I := by
  obtain ⟨u, rfl⟩ := h
  exact Ideal.mul_mem_right (u : R) I ha

/-- **Cyclotomic ramification of a rational prime.** In a domain `R`
containing a primitive `q`-th root of unity `ζ` (with `q` a rational prime),
every prime ideal `Q` of `R` containing `q` also contains `ζ - 1`.

The proof:
1. The identity `Φ_q(1) = q` (from `eval_one_cyclotomic_prime`) combined
   with the factorisation `Φ_q = ∏_{μ primitive} (X - C μ)` (from
   `cyclotomic_eq_prod_X_sub_primitiveRoots`) gives
   `q = ∏_{μ ∈ primitiveRoots q R} (1 - μ)` in `R`.
2. By primality of `Q`, since the product `∏ (1 - μ)` lies in `Q`,
   some factor `1 - μ ∈ Q`.
3. By `IsPrimitiveRoot.isPrimitiveRoot_iff`, that `μ` equals `ζ^a` for
   some `a` coprime to `q`.
4. By `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`,
   `ζ - 1` and `ζ^a - 1` are associated, hence `ζ - 1 ∈ Q`. -/
theorem zeta_sub_one_mem_of_natCast_mem
    {R : Type*} [CommRing R] [IsDomain R]
    {q : ℕ} [hq : Fact q.Prime] {ζ : R} (hζ : IsPrimitiveRoot ζ q)
    {Q : Ideal R} [Q.IsPrime] (hQ : (q : R) ∈ Q) :
    ζ - 1 ∈ Q := by
  have hqpos : 0 < q := hq.out.pos
  -- Step 1: q = ∏_{μ ∈ primitiveRoots q R} (1 - μ) in R
  have hprod : (∏ μ ∈ primitiveRoots q R, ((1 : R) - μ)) = (q : R) := by
    have heval : (Polynomial.cyclotomic q R).eval 1 = (q : R) :=
      Polynomial.eval_one_cyclotomic_prime
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ] at heval
    rw [Polynomial.eval_prod] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
    exact heval
  -- Step 2: ∏ (1 - μ) ∈ Q, so some 1 - μ ∈ Q
  have hprod_mem : (∏ μ ∈ primitiveRoots q R, ((1 : R) - μ)) ∈ Q := hprod ▸ hQ
  obtain ⟨μ, hμ_mem, hμμ⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod_mem
  -- Step 3: μ is a primitive q-th root of unity, hence μ = ζ^a for some a
  have hμ_prim : IsPrimitiveRoot μ q := isPrimitiveRoot_of_mem_primitiveRoots hμ_mem
  have hne : NeZero q := ⟨hq.out.ne_zero⟩
  obtain ⟨a, _, ha_coprime, rfl⟩ := (hζ.isPrimitiveRoot_iff (k := q)).mp hμ_prim
  -- Step 4: 1 - ζ^a ∈ Q ⟹ ζ^a - 1 ∈ Q
  have h_neg : ζ ^ a - 1 ∈ Q := by
    have : ζ ^ a - 1 = -((1 : R) - ζ ^ a) := by ring
    rw [this]
    exact Q.neg_mem hμμ
  -- Step 5: ζ - 1 ∼ ζ^a - 1, so ζ - 1 ∈ Q
  have hassoc : Associated (ζ - 1) (ζ ^ a - 1) :=
    hζ.associated_sub_one_pow_sub_one_of_coprime ha_coprime
  exact hassoc.symm.mem_ideal_of_mem h_neg

/-- **Iterated cyclotomic ramification.** Direct corollary: every power
`ζ^n` of a primitive `q`-th root satisfies `ζ^n - 1 ∈ Q` for any prime
ideal `Q` containing `q`. Combines `zeta_sub_one_mem_of_natCast_mem`
with `pow_sub_one_mem_of_sub_one_mem`. -/
theorem zeta_pow_sub_one_mem_of_natCast_mem
    {R : Type*} [CommRing R] [IsDomain R]
    {q : ℕ} [Fact q.Prime] {ζ : R} (hζ : IsPrimitiveRoot ζ q)
    {Q : Ideal R} [Q.IsPrime] (hQ : (q : R) ∈ Q) (n : ℕ) :
    ζ ^ n - 1 ∈ Q :=
  pow_sub_one_mem_of_sub_one_mem ζ n (zeta_sub_one_mem_of_natCast_mem hζ hQ)

/-- **q-adic containment from cyclotomic additive character.** If the additive
character `ψ_q : k → R'` has the form `ψ_q(x) = ζ^{f(x)}` for some primitive
`q`-th root of unity `ζ ∈ R'` and integer function `f`, then the hypothesis
of `gaussSum_mem_ideal_of_addChar_sub_one_mem` is satisfied for any prime
ideal `Q` of `R'` containing `q`. Hence `g(χ_q, ψ_q) ∈ Q`.

This is the *concrete instantiation* of REF-18c2c2 for the standard
cyclotomic additive character. The hypothesis `h_psi_pow` captures the
trace-formula structure `ψ_q(x) = ζ_q^{Tr(x)}` of the standard primitive
character on a finite field. -/
theorem residueGaussSum_mem_ideal_of_psi_pow_form
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {ζ : R'} (hζ : IsPrimitiveRoot ζ q)
    {psi_q : AddChar k R'}
    (h_psi_pow : ∀ x : k, ∃ n : ℕ, psi_q x = ζ ^ n)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (q : R') ∈ Q) :
    residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q ∈ Q := by
  refine residueGaussSum_mem_ideal_of_psi_sub_one_mem
    zeta_q hzeta_q hdiv zeta_R hzeta_R (fun x => ?_)
  obtain ⟨n, hn⟩ := h_psi_pow x
  rw [hn]
  exact zeta_pow_sub_one_mem_of_natCast_mem hζ hQ n

end Furtwaengler

end BernoulliRegular
