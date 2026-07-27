/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.GaussSum
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Stickelberger
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import Mathlib.NumberTheory.GaussSum


/-!
# K2-1 substantive atom: Gauss-sum Frobenius congruence (REF-18 Phase 2)

This file builds toward Kelly Proposition 9 (the **prime Φ-symbol identity**):

```
(Φ(P) / P')_p = (NP' / P)_p
```

via its substantive atom **K2-1** (Gauss-sum Frobenius congruence):

```
g(χ_P)^{NP'} ≡ (NP'/P)_p · g(χ_P) (mod P')
```

for prime ideals `P, P'` of `𝓞_K` coprime to `(p)` with coprime
rational norms `(NP, NP') = 1`.

## Strategy (per AI reviewer 2026-05-05)

In the residue ring above `P'` (which has characteristic `ℓ` where
`NP' = ℓ ^ f`), raise the Gauss sum termwise to `NP'`:
* The multiplicative character part `χ^{NP'}` is stable because
  `NP' ≡ 1 (mod p)` (so `χ` has order dividing `p` and `χ^{NP'} = χ`).
* The additive character transforms by `ψ ↦ mulShift ψ NP'` (i.e.,
  `t ↦ NP' · t` on the source).
* Pull out the residue symbol `(NP'/P)_p = χ_P(NP')` via
  `gaussSum_mulShift`.

The current file lays the iterated-Frobenius foundation:

```
gaussSum χ ψ ^ p^n = gaussSum (χ^{p^n}) (ψ^{p^n})
```

a generalization of `MulChar.IsQuadratic.gaussSum_frob_iter` (mathlib)
that drops the quadratic hypothesis. From this, with `χ` of order `p`
and `NP' ≡ 1 (mod p)`, the K2-1 congruence follows by combining with
`gaussSum_mulShift` and the substitution argument.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Iterated Frobenius for Gauss sums (general, non-quadratic)

Mathlib only has `MulChar.IsQuadratic.gaussSum_frob_iter`; we need the
non-quadratic version. By induction on the iteration count, applying
`gaussSum_frob` once per step. -/

/-- **Iterated Frobenius for Gauss sums**: for a target ring `R'` of
prime characteristic `p`, `gaussSum χ ψ ^ p^n = gaussSum (χ^{p^n}) (ψ^{p^n})`.
Generalises `MulChar.IsQuadratic.gaussSum_frob_iter` to arbitrary
multiplicative characters. -/
theorem gaussSum_frob_iter
    {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    (p : ℕ) [Fact p.Prime] [CharP R' p]
    (χ : MulChar R R') (ψ : AddChar R R') (n : ℕ) :
    gaussSum χ ψ ^ p ^ n = gaussSum (χ ^ p ^ n) (ψ ^ p ^ n) := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have h_lhs : gaussSum χ ψ ^ p ^ (k + 1) = (gaussSum χ ψ ^ p ^ k) ^ p := by
      rw [← pow_mul, ← pow_succ]
    have h_χ : χ ^ p ^ (k + 1) = (χ ^ p ^ k) ^ p := by
      rw [← pow_mul, ← pow_succ]
    have h_ψ : ψ ^ p ^ (k + 1) = (ψ ^ p ^ k) ^ p := by
      rw [← pow_mul, ← pow_succ]
    rw [h_lhs, ih, gaussSum_frob, ← h_χ, ← h_ψ]

/-! ### Character order p and exponent reduction

For a multiplicative character `χ : MulChar R R'` with `χ^p = 1` (order
dividing `p`), `χ^N = χ^{N mod p}`. In particular, when `N ≡ 1 (mod p)`,
`χ^N = χ`.

This is the second ingredient for K2-1: in the residue ring above `P'`
of characteristic `ℓ`, after iterating Frobenius `f` times we have
`gaussSum χ ψ ^ NP' = gaussSum (χ^{NP'}) (ψ^{NP'})` where `NP' = ℓ ^ f`.
The character part `χ^{NP'}` simplifies to `χ` because `χ` has order
dividing `p` (the *outer* prime) and `NP' ≡ 1 (mod p)` (by hypothesis
that `P'` is a "good" prime for the canonical residue symbol). -/

/-- **Character power reduction modulo character-order**: if `χ^p = 1`,
then `χ^N = χ^{N mod p}`. -/
theorem mulChar_pow_eq_pow_mod
    {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']
    (χ : MulChar R R') (p : ℕ) (hχ_pow : χ ^ p = 1) (N : ℕ) :
    χ ^ N = χ ^ (N % p) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    rw [Nat.mod_zero]
  · -- N = p · (N / p) + (N % p)
    conv_lhs => rw [← Nat.div_add_mod N p]
    rw [pow_add, pow_mul, hχ_pow, one_pow, one_mul]

/-- **Character power = identity at exponent ≡ 1 (mod p)**: if `χ^p = 1`
and `N ≡ 1 (mod p)`, then `χ^N = χ`. -/
theorem mulChar_pow_eq_self_of_modEq_one
    {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']
    (χ : MulChar R R') {p : ℕ} (_hp : 1 < p) (hχ_pow : χ ^ p = 1)
    {N : ℕ} (hN : N % p = 1) :
    χ ^ N = χ := by
  rw [mulChar_pow_eq_pow_mod χ p hχ_pow N, hN, pow_one]

/-! ### K2-1 Gauss-sum Frobenius congruence (combined form)

Combining the three ingredients:
1. **Iterated Frobenius** (`gaussSum_frob_iter`): in a target ring of
   prime characteristic `ℓ`, `g^{ℓ ^ f} = gaussSum (χ^{ℓ ^ f}) (ψ^{ℓ ^ f})`.
2. **Character order reduction** (`mulChar_pow_eq_self_of_modEq_one`):
   if `χ^p = 1` and `N ≡ 1 (mod p)`, then `χ^N = χ`.
3. **AddChar pow = mulShift** (mathlib's `pow_mulShift`):
   `ψ^N = mulShift ψ N`.
4. **mulShift identity** (mathlib's `gaussSum_mulShift`):
   `χ a · gaussSum χ (mulShift ψ a) = gaussSum χ ψ` for unit `a`.

We obtain: `gaussSum χ ψ ^ {ℓ ^ f} = (χ a)⁻¹ · gaussSum χ ψ` in `R'`,
where `a` is the unit cast of `ℓ ^ f` in `R` (the source).

For the K2-1 application: take `R = (𝓞 K)⧸q` (residue field at prime
`q`), `R'` a quotient containing the residue character values mod `P'`
(characteristic `ℓ` = the rational prime under `P'`), `χ = χ_q` the
residue character (order `p` since values lie in `μ_p`), `f` the
residue degree of `P'` (so `NP' = ℓ ^ f`). The hypothesis `NP' ≡ 1
(mod p)` is exactly the "good prime" condition `p ∣ NP' - 1`. -/

/-- **K2-1 Gauss-sum Frobenius congruence (combined form)**.

In a target ring `R'` of prime characteristic `ℓ`, for any `χ : MulChar R R'`
with `χ^p = 1` and any `ψ : AddChar R R'`, given `f : ℕ` with
`(ℓ ^ f) ≡ 1 (mod p)` and the cast of `ℓ ^ f` in `R` is a unit, the `(ℓ ^ f)`-th
power of the Gauss sum equals `(χ a)⁻¹` times the Gauss sum, where `a`
is the unit witness.

This is the substantive Frobenius congruence:
```
g(χ, ψ)^{ℓ ^ f} = (χ(ℓ ^ f))⁻¹ · g(χ, ψ) in R'
```

Mathematical content: in the residue ring above `P'` (char `ℓ`), the
Gauss sum's `NP'`-th power simplifies via Frobenius (iterated `f` times),
character-order reduction (`χ^{NP'} = χ`), and `mulShift` substitution. -/
theorem gaussSum_pow_eq_inv_apply_smul_of_charP
    {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    {p : ℕ} (hp : 1 < p)
    (χ : MulChar R R') (hχ_p : χ ^ p = 1)
    (ψ : AddChar R R')
    (f : ℕ) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : Rˣ) (ha : (a : R) = (ℓ ^ f : ℕ)) :
    χ a * gaussSum χ ψ ^ (ℓ ^ f) = gaussSum χ ψ := by
  -- Apply iterated Frobenius.
  rw [gaussSum_frob_iter ℓ χ ψ f]
  -- Reduce the character power: χ^{ℓ ^ f} = χ.
  rw [mulChar_pow_eq_self_of_modEq_one χ hp hχ_p hN_mod_p]
  -- Convert ψ^{ℓ ^ f} to mulShift ψ (ℓ ^ f).
  rw [AddChar.pow_mulShift]
  -- Convert (ℓ ^ f : ℕ) cast to a unit.
  rw [show (((ℓ ^ f : ℕ) : R) : R) = (a : R) from ha.symm]
  -- Apply gaussSum_mulShift.
  exact gaussSum_mulShift χ ψ a

/-! ### K2-1 specialised to `residueGaussSum`

Combining the general K2-1 atom `gaussSum_pow_eq_inv_apply_smul_of_charP`
with `residueMulChar_pow_p_eq_one`, we get the K2-1 congruence
specialised to `residueGaussSum`. -/

/-- **K2-1 for residueGaussSum**: in a target ring `R'` of prime
characteristic `ℓ`, for the residue Gauss sum `g(χ_q, ψ_q)`, given
`f : ℕ` with `(ℓ ^ f) ≡ 1 (mod p)` and `(ℓ ^ f : ℕ)` lifting to a unit `a`
in the source field `k`:

```
χ_q a · g(χ_q, ψ_q)^{ℓ ^ f} = g(χ_q, ψ_q) in R'.
```

This is Kelly Proposition 9 step 1 specialised to the residue Gauss sum.
The unit hypothesis `IsUnit ((ℓ ^ f : ℕ) : k)` corresponds to the
"coprime rational norms" condition `(NP, NP') = 1` in the K2 statement
(i.e., `q` does not lie above the rational prime `ℓ`). -/
theorem residueGaussSum_pow_eq_inv_apply_smul_of_charP
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 1 < p)
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (psi_q : AddChar k R')
    (f : ℕ) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : kˣ) (ha : (a : k) = (ℓ ^ f : ℕ)) :
    (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) a *
        residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q ^ (ℓ ^ f) =
      residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q := by
  simp only [residueGaussSum]
  exact gaussSum_pow_eq_inv_apply_smul_of_charP hp
    (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
    (residueMulChar_pow_eq_one_mulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)
    psi_q f hN_mod_p a ha

/-! ### `g^{NP'-1} · χ(a) = 1` form

A useful rearrangement of K2-1: from `χ a · g^N = g`, dividing by `g`
(when applicable) gives `χ a · g^{N-1} = 1`. This is the form most
directly relevant to computing the symbol of `g^p` at `P'`:

```
(g^p)^{(NP'-1)/p} = g^{NP'-1} = (χ(a))⁻¹
```

so the canonical residue exponent of `g^p` at `P'` is the negation of
the residue exponent of `a` at `q`. -/

/-- **K2-1 corollary, multiplicative form**: `χ a · g^{ℓ ^ f - 1} · g = g`,
which factors via cancellation to `χ a · g^{ℓ ^ f - 1} · g = g`. We state
the cleaner form: when `ℓ ^ f ≥ 1`, `χ a · g^{ℓ ^ f - 1} · g = g`. -/
theorem gaussSum_pow_sub_one_mul_apply_smul_of_charP
    {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    {p : ℕ} (hp : 1 < p)
    (χ : MulChar R R') (hχ_p : χ ^ p = 1)
    (ψ : AddChar R R')
    {f : ℕ} (hf : 1 ≤ ℓ ^ f) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : Rˣ) (ha : (a : R) = (ℓ ^ f : ℕ)) :
    χ a * gaussSum χ ψ ^ (ℓ ^ f - 1) * gaussSum χ ψ = gaussSum χ ψ := by
  have h := gaussSum_pow_eq_inv_apply_smul_of_charP hp χ hχ_p ψ f hN_mod_p a ha
  -- χ a * g^(ℓ ^ f) = g; rewrite g^(ℓ ^ f) = g^(ℓ ^ f - 1) * g.
  rw [show gaussSum χ ψ ^ (ℓ ^ f) = gaussSum χ ψ ^ (ℓ ^ f - 1) * gaussSum χ ψ from by
    rw [← pow_succ, Nat.sub_add_cancel hf]] at h
  rw [← mul_assoc] at h
  exact h

/-! ### `(g^p)^{(NP'-1)/p}` as a closed form

Since `p ∣ NP' - 1` (i.e. `(ℓ ^ f - 1) ≡ 0 (mod p)`, equivalent to
`ℓ ^ f ≡ 1 (mod p)`), we have `NP' - 1 = p · ((NP'-1)/p)`. Hence
`g^{NP'-1} = (g^p)^{(NP'-1)/p}`. Combined with the K2-1 multiplicative
form, this gives the closed form for the canonical residue exponent
of `g^p` at `P'`:

```
χ a · (g^p)^{(NP'-1)/p} · g = g
```

The factor `(g^p)^{(NP'-1)/p}` is exactly the quantity whose value
modulo `P'` defines the canonical residue exponent of `g^p` at `P'`. -/

/-- **K2-1 closed form for `(g^p)^{(NP'-1)/p}`**: under the K2-1
hypotheses, `χ a · (g^p)^{(ℓ ^ f - 1)/p} · g = g` (the form whose first
factor encodes the canonical residue exponent of `g^p` at `P'`). -/
theorem gaussSum_pow_p_pow_div_mul_apply_smul_of_charP
    {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    {p : ℕ} (hp : 1 < p)
    (χ : MulChar R R') (hχ_p : χ ^ p = 1)
    (ψ : AddChar R R')
    {f : ℕ} (hf : 1 ≤ ℓ ^ f) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : Rˣ) (ha : (a : R) = (ℓ ^ f : ℕ)) :
    χ a * (gaussSum χ ψ ^ p) ^ ((ℓ ^ f - 1) / p) * gaussSum χ ψ =
      gaussSum χ ψ := by
  have h := gaussSum_pow_sub_one_mul_apply_smul_of_charP hp χ hχ_p ψ hf hN_mod_p a ha
  -- Rewrite g^(ℓ ^ f - 1) = (g^p)^((ℓ ^ f - 1)/p) using p | (ℓ ^ f - 1).
  have hp_dvd : p ∣ (ℓ ^ f - 1) := by
    -- ℓ ^ f = p · (ℓ ^ f / p) + (ℓ ^ f % p) =
    -- p · (ℓ ^ f / p) + 1, so ℓ ^ f - 1 = p · (ℓ ^ f / p).
    have h_div_mod : ℓ ^ f = p * (ℓ ^ f / p) + ℓ ^ f % p :=
      (Nat.div_add_mod (ℓ ^ f) p).symm
    refine ⟨ℓ ^ f / p, ?_⟩
    omega
  rw [show gaussSum χ ψ ^ (ℓ ^ f - 1) =
      (gaussSum χ ψ ^ p) ^ ((ℓ ^ f - 1) / p) from by
    rw [← pow_mul, mul_comm, Nat.div_mul_cancel hp_dvd]] at h
  exact h

/-! ### Closed form modulo `g`-invertibility

When `g = gaussSum χ ψ` is invertible in `R'` (e.g., R' is a field where
g ≠ 0), the closed form `χ a · (g^p)^{(NP'-1)/p} · g = g` rearranges to:

```
(g^p)^{(NP'-1)/p} = (χ a)⁻¹ in R'.
```

The LHS is the quantity whose value modulo `P'` (treating `g^p` as
descended to `𝓞_K`) defines the canonical residue exponent of `g^p` at
`P'`. So the canonical residue symbol value `(g^p / P')_p` equals the
discrete log of `(χ a)⁻¹` in the cyclic group of `p`-th roots of unity. -/

/-- **K2-1 closed form (g invertible)**: under the K2-1 hypotheses, if
`g = gaussSum χ ψ` is a unit in `R'`, then `χ a · (g^p)^{(ℓ ^ f - 1)/p} = 1`
in `R'`. (Equivalent to `(g^p)^{(ℓ ^ f - 1)/p} = (χ a)⁻¹` when χ a is a
unit, but stated in the symmetric multiplicative form which doesn't
require χ a's invertibility hypothesis.) -/
theorem gaussSum_pow_p_pow_div_apply_smul_eq_one_of_charP
    {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    {p : ℕ} (hp : 1 < p)
    (χ : MulChar R R') (hχ_p : χ ^ p = 1)
    (ψ : AddChar R R')
    {f : ℕ} (hf : 1 ≤ ℓ ^ f) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : Rˣ) (ha : (a : R) = (ℓ ^ f : ℕ))
    (_hg_ne : gaussSum χ ψ ≠ 0)
    (hg_cancel : ∀ x y : R', x * gaussSum χ ψ = y * gaussSum χ ψ → x = y) :
    χ a * (gaussSum χ ψ ^ p) ^ ((ℓ ^ f - 1) / p) = 1 := by
  have h := gaussSum_pow_p_pow_div_mul_apply_smul_of_charP hp χ hχ_p ψ hf hN_mod_p a ha
  -- h: χ a * (g^p)^((ℓ ^ f - 1)/p) * g = g
  -- Apply hg_cancel: χ a * (g^p)^((ℓ ^ f - 1)/p) = 1.
  apply hg_cancel
  rw [one_mul]
  exact h

/-! ### Field-specialised K2-1 closed form

When `R'` is a field (or any ring with `NoZeroDivisors`), the
cancellation hypothesis is automatic: `g ≠ 0` lets us cancel `g` from
both sides directly. -/

/-- **K2-1 closed form (R' a field with `g ≠ 0`)**: in a target field
`R'` of characteristic `ℓ`, under the K2-1 hypotheses with `g ≠ 0`,

```
χ a · (g^p)^{(ℓ ^ f - 1)/p} = 1 in R'.
```

This is the form best suited for the K2-2 symbol computation in
`R' = 𝓞_K / P'` (a field at prime `P'`). -/
theorem gaussSum_pow_p_pow_div_apply_smul_eq_one_of_charP_field
    {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    [NoZeroDivisors R']
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    {p : ℕ} (hp : 1 < p)
    (χ : MulChar R R') (hχ_p : χ ^ p = 1)
    (ψ : AddChar R R')
    {f : ℕ} (hf : 1 ≤ ℓ ^ f) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : Rˣ) (ha : (a : R) = (ℓ ^ f : ℕ))
    (hg_ne : gaussSum χ ψ ≠ 0) :
    χ a * (gaussSum χ ψ ^ p) ^ ((ℓ ^ f - 1) / p) = 1 :=
  gaussSum_pow_p_pow_div_apply_smul_eq_one_of_charP hp χ hχ_p ψ hf hN_mod_p a ha hg_ne
    (fun _x _y h => mul_right_cancel₀ hg_ne h)

/-! ### Closed form: `(g^p)^{(NP'-1)/p} = (χ a)⁻¹`

When `χ a` is also a unit in `R'`, the cancellation form
`χ a · (g^p)^{(ℓ ^ f - 1)/p} = 1` rearranges to
`(g^p)^{(ℓ ^ f - 1)/p} = (χ a)⁻¹` directly. This is the cleanest form
for connecting K2-1 to the residue symbol computation. -/

/-- **K2-1: `(g^p)^{(NP'-1)/p} · (χ a) = 1`**. Symmetric form: the
invertibility constraint on `χ a` is unnecessary here — the equation
`(g^p)^{(ℓ ^ f - 1)/p} · χ a = 1` holds whenever
`χ a · (g^p)^{(ℓ ^ f - 1)/p} = 1`, since multiplication in `R'` is
commutative. Useful when the consumer wants to identify
`(g^p)^{(NP'-1)/p}` as the multiplicative inverse of `χ a`. -/
theorem gaussSum_pow_p_pow_div_mul_apply_smul_eq_one_of_charP_field
    {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    [NoZeroDivisors R']
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    {p : ℕ} (hp : 1 < p)
    (χ : MulChar R R') (hχ_p : χ ^ p = 1)
    (ψ : AddChar R R')
    {f : ℕ} (hf : 1 ≤ ℓ ^ f) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : Rˣ) (ha : (a : R) = (ℓ ^ f : ℕ))
    (hg_ne : gaussSum χ ψ ≠ 0) :
    (gaussSum χ ψ ^ p) ^ ((ℓ ^ f - 1) / p) * χ a = 1 := by
  have h := gaussSum_pow_p_pow_div_apply_smul_eq_one_of_charP_field
    hp χ hχ_p ψ hf hN_mod_p a ha hg_ne
  rw [mul_comm]; exact h

/-! ### Bundle accessor: K2-1 from `StickelbergerSetup`

`StickelbergerSetup p k R'` packages the data driving the Stickelberger
prime factorisation: a finite field `k`, a target domain `R'` of
characteristic `ℓ`, primitive p-th roots of unity in both, and a
primitive additive character. We expose the K2-1 atom as a bundle
accessor `S.gaussSum_pow_eq_inv_apply_smul`. -/

/-- **Bundle accessor for K2-1**: the substantive Frobenius congruence
for the bundle's Gauss sum, in a target ring of characteristic `ℓ`. -/
theorem StickelbergerSetup.gaussSum_pow_eq_inv_apply_smul
    {p : ℕ} [Fact p.Prime] (hp : 1 < p)
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    (S : StickelbergerSetup p k R')
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP R' ℓ]
    (f : ℕ) (hN_mod_p : (ℓ ^ f) % p = 1)
    (a : kˣ) (ha : (a : k) = (ℓ ^ f : ℕ)) :
    S.residueChar a * S.gaussSum ^ (ℓ ^ f) = S.gaussSum := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact residueGaussSum_pow_eq_inv_apply_smul_of_charP hp
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.psi_q f hN_mod_p a ha

/-! ### Residue field setup: `CharP (𝓞_K ⧸ P') ℓ` for `P'` over `ℓ`

When `P'` is a maximal ideal of `𝓞_K` containing the rational prime `ℓ`,
the residue field `𝓞_K ⧸ P'` has characteristic `ℓ`. -/

/-- **CharP for the residue field at `P'` over `ℓ`**: when `P'` is
maximal and contains the rational prime `ℓ`, the residue field
`𝓞_K ⧸ P'` has characteristic `ℓ`. -/
theorem charP_quotient_of_natPrime_mem
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : (ℓ : 𝓞 K) ∈ P) :
    CharP (𝓞 K ⧸ P) ℓ := by
  haveI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  -- (ℓ : 𝓞 K ⧸ P) = 0
  have h_zero : (ℓ : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P) ℓ]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  -- ringChar divides ℓ
  have h_dvd : ringChar (𝓞 K ⧸ P) ∣ ℓ := ringChar.dvd h_zero
  -- ringChar ≠ 1 (since 𝓞 K ⧸ P is a field, hence nontrivial)
  have h_ne_one : ringChar (𝓞 K ⧸ P) ≠ 1 := CharP.ringChar_ne_one
  -- ringChar = 1 ∨ ringChar = ℓ ⟹ ringChar = ℓ
  have h_eq : ringChar (𝓞 K ⧸ P) = ℓ :=
    Or.resolve_left ((Nat.dvd_prime hℓ).1 h_dvd) h_ne_one
  exact ringChar.of_eq h_eq

/-! ### `phiPrimeGen P`: the Stickelberger generator at prime `P`

For a prime ideal `P` of `𝓞_K`, the Stickelberger ideal equality
`(γ_P) = stickelbergerIdeal P` provides a generator `γ_P ∈ 𝓞_K`.
Classically, this generator is `g(χ_P)^p` (the p-th power of the Gauss
sum), descended from `𝓞_{K(ζ_q)}` to `𝓞_K` via Galois invariance.

We name this `phiPrimeGen` for clarity in the K2-2 chain. The actual
specific value is whatever `StickelbergerIdealEquality.gen` produces;
two different generators differ by a unit, and the symbol identity in
K2-2 holds modulo the unit factor's symbol (which the U-chain handles). -/

/-- **`phiPrimeGen`**: the Stickelberger generator at prime `P` extracted
from a `StickelbergerIdealEquality P` hypothesis. Classically `g(χ_P)^p`,
the Gauss sum descended to `𝓞_K`. -/
noncomputable def phiPrimeGen
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P) : 𝓞 K :=
  h_stick.gen

@[simp] theorem phiPrimeGen_eq_gen
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P) :
    phiPrimeGen h_stick = h_stick.gen := rfl

theorem phiPrimeGen_ne_zero
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P) :
    phiPrimeGen h_stick ≠ 0 :=
  h_stick.gen_ne_zero

theorem phiPrimeGen_span_eq
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P) :
    Ideal.span ({phiPrimeGen h_stick} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P :=
  h_stick.span_gen

/-! ### K2-2c bridge: `residueMulChar` value via `pthSymbolAtPrime_canonical`

For a prime `P` of `𝓞_K`, the residue character `χ_P : MulChar (𝓞_K/P) R'`
(with canonical primitive root `canonicalResidueZetaP P`) and target
primitive root `zeta_R` in `R'`, satisfies:

```
χ_P(α mod P) = zeta_R ^ (pthSymbolAtPrime_canonical α P).val
```

for `α ∈ 𝓞_K` outside `P`, `P` maximal, `p ∤ #(𝓞_K/P) - 1`, `(p : 𝓞_K) ∉ P`.

This is K2-2 step (c): identifies the residue character value at α with
`zeta_R` raised to the canonical residue exponent. -/

/-- **K2-2c bridge**: residueMulChar at canonical zeta equals `zeta_R`
raised to `pthSymbolAtPrime_canonical`. -/
theorem residueMulChar_apply_quotient_canonical_eq_pow_pthSymbol
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [CommRing R']
    (P : Ideal (𝓞 K)) (hbot : P ≠ ⊥) [hmax : P.IsMaximal]
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (hp_in : (p : 𝓞 K) ∉ P)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {α : 𝓞 K} (hα : α ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
        hdiv zeta_R hzeta_R
        ((Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) =
      ((zeta_R : R')) ^
        (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [residueMulChar_apply_quotient (p := p) P
    (canonicalResidueZetaP (p := p) (K := K) P)
    (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
    hdiv zeta_R hzeta_R hα]
  congr 2
  -- Goal: primeExponent P (canonicalZeta P) ... α hα = pthSymbolAtPrime_canonical α P
  exact (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical_eq_primeExponent
    (α := α) (q := P) hbot hmax hα hdiv hp_in).symm

/-! ### Discrete log uniqueness for `finiteFieldExponent`

`finiteFieldExponent` is the discrete log of `finiteFieldUnit hdiv x` in
the cyclic subgroup generated by `zeta`. Uniqueness mod `p` follows from
`zeta` being a primitive `p`-th root.

Specifically: if `zeta^e.val = finiteFieldUnit hdiv x` in `kˣ`, then
`e = finiteFieldExponent zeta hzeta hdiv x`. -/

/-- **Uniqueness of `finiteFieldExponent`**: if `zeta^e.val = x^((#k - 1)/p)`
for `e : ZMod p`, then `e = finiteFieldExponent zeta hzeta hdiv x`. -/
theorem finiteFieldExponent_eq_of_pow_eq
    {k : Type*} [Field k] [Fintype k] {p : ℕ} [Fact p.Prime] [NeZero p]
    {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1)
    {x : kˣ} {e : ZMod p}
    (he : zeta ^ e.val =
      Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv x) :
    e = Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
      zeta hzeta hdiv x := by
  -- Both `zeta^e.val` and `zeta^(finiteFieldExponent ...).val` equal
  -- `finiteFieldUnit hdiv x`, so e.val ≡ (finiteFieldExponent ...).val mod p.
  have h_target := Reflection.ResidueSymbol.PowerResidue.zeta_pow_finiteFieldExponent_val
    hzeta hdiv x
  -- Combine: zeta^e.val = zeta^(finiteFieldExponent ...).val.
  have h_eq : zeta ^ e.val = zeta ^
      (Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
        zeta hzeta hdiv x).val := by
    rw [he, h_target]
  -- p = orderOf zeta (from primitive root)
  have h_order : orderOf zeta = p := hzeta.eq_orderOf.symm
  -- By pow_eq_pow_iff_modEq: e.val ≡ (finiteFieldExponent...).val (mod orderOf zeta)
  rw [pow_eq_pow_iff_modEq, h_order] at h_eq
  -- Goal: e = finiteFieldExponent ... in ZMod p; values are equal mod p.
  have h_val_eq : (e.val : ZMod p) =
      ((Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
          zeta hzeta hdiv x).val : ZMod p) := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr h_eq
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h_val_eq
  exact h_val_eq

/-! ### K2-2 conditional reduction (status)

The full K2-2 theorem combines the foundational atoms above:
* **K2-2a** (`pthSymbolAtPrime_canonical_eq_primeExponent`, existing): unfolds
  `pthSymbolAtPrime_canonical α P'` to `primeExponent P' (canonicalResidueZetaP P')
  ... α hα`, which is `finiteFieldExponent` applied to the unit form of `α`.
* **K2-1** (this file): `χ a · (g^p)^{(NP'-1)/p} = 1` in target ring of char ℓ.
* **K2-2c** (this file, `residueMulChar_apply_quotient_canonical_eq_pow_pthSymbol`):
  `residueMulChar (NP' mod P) at canonicalResidueZetaP P' = (canonicalResidueZetaP P')
  ^ (pthSymbolAtPrime_canonical NP' P).val`.
* **Discrete log uniqueness** (this file, `finiteFieldExponent_eq_of_pow_eq`): if
  `zeta ^ e.val = finiteFieldUnit hdiv x`, then `e = finiteFieldExponent zeta hzeta hdiv x`.

The substantive open content remaining is the **descent atom**: identifying
`(Ideal.Quotient.mk P') (phiPrimeGen)` with the descent of `g(χ_P)^p` to
`𝓞_K`, viewed as an element of `𝓞_K ⧸ P'`. This is the Galois-invariance
descent of the Gauss sum from `𝓞_{K(ζ_q)}` to `𝓞_K`, then reduction by `P'`.

With that descent in place, the K2-2 chain is:
1. `pthSymbolAtPrime_canonical (phiPrimeGen) P' = primeExponent P' ... = e`
   where `e` is determined by
   `(phiPrimeGen mod P')^{(NP'-1)/p} = ζ_{P'}^{e.val}`.
2. By K2-1 + descent:
   `(phiPrimeGen mod P')^{(NP'-1)/p} = (residueMulChar (NP' mod P))⁻¹`.
3. By K2-2c:
   `(residueMulChar (NP' mod P))⁻¹ =
     (canonicalResidueZetaP P')^{-(pthSymbolAtPrime NP' P).val}`.
4. By discrete log uniqueness: `e = -pthSymbolAtPrime NP' P` in `ZMod p`.

All four ingredients are in place; the final conditional theorem only needs
the descent atom as an explicit hypothesis. -/

/-- **Discrete log version with arbitrary target exponent**: if
`finiteFieldUnit ... = canonicalResidueZetaP P'^t.val` for some `t : ZMod p`,
then `pthSymbolAtPrime_canonical γ P' = t`. Strictly more general than
`K2_2_of_descent_pow_eq_general` (which fixes `t = -pthSymbolAtPrime NP' P`). -/
theorem pthSymbolAtPrime_canonical_eq_of_descent_pow_eq
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (γ : 𝓞 K) (hγ_notin_P' : γ ∉ P')
    (t : ZMod p)
    (h_descent :
      letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
      Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv_P'
          (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem
            P' γ hγ_notin_P') =
        canonicalResidueZetaP (p := p) (K := K) P' ^ t.val) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) γ P' = t := by
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  rw [BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical_eq_primeExponent
    hP'_bot hP'_max hγ_notin_P' hdiv_P' hp_in_P']
  simp only [Reflection.ResidueSymbol.PowerResidue.primeExponent]
  exact (finiteFieldExponent_eq_of_pow_eq
    (canonicalResidueZetaP_isPrimitiveRoot (p := p) (K := K) hP'_bot hp_in_P')
    hdiv_P' h_descent.symm).symm

/-- **K2-2 conditional reduction (general form, parametric in γ)**: the
proof of K2-2 doesn't actually need `γ` to be the abstract phiPrimeGen
of a Stickelberger ideal equality — it just needs an element `γ ∈ 𝓞 K`
satisfying the descent identity at `P'`. -/
theorem K2_2_of_descent_pow_eq_general
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (_hP_bot : P ≠ ⊥) [_hP_max : P.IsMaximal]
    (_hp_in_P : (p : 𝓞 K) ∉ P)
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (γ : 𝓞 K) (hγ_notin_P' : γ ∉ P')
    (h_descent :
      letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
      Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv_P'
          (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem
            P' γ hγ_notin_P') =
        canonicalResidueZetaP (p := p) (K := K) P' ^
          (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) γ P' =
      - BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  rw [BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical_eq_primeExponent
    hP'_bot hP'_max hγ_notin_P' hdiv_P' hp_in_P']
  simp only [Reflection.ResidueSymbol.PowerResidue.primeExponent]
  exact (finiteFieldExponent_eq_of_pow_eq
    (canonicalResidueZetaP_isPrimitiveRoot (p := p) (K := K) hP'_bot hp_in_P')
    hdiv_P' h_descent.symm).symm

theorem K2_2_of_descent_pow_eq
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (_hP_bot : P ≠ ⊥) [_hP_max : P.IsMaximal]
    (_hp_in_P : (p : 𝓞 K) ∉ P)
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hphi_notin_P' : phiPrimeGen h_stick ∉ P')
    -- Substantive descent: (phiPrimeGen)^((NP'-1)/p) mod P' = ζ_{P'}^((-s).val)
    -- where s = pthSymbolAtPrime_canonical (NP' : 𝓞 K) P.
    (h_descent :
      letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
      Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv_P'
          (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem
            P' (phiPrimeGen h_stick) hphi_notin_P') =
        canonicalResidueZetaP (p := p) (K := K) P' ^
          (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen h_stick) P' =
      - BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  rw [BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical_eq_primeExponent
    hP'_bot hP'_max hphi_notin_P' hdiv_P' hp_in_P']
  simp only [Reflection.ResidueSymbol.PowerResidue.primeExponent]
  -- Goal: finiteFieldExponent (canonicalZetaP P') ... (quotientUnitOfNotMem P' phi) = -s
  -- Apply discrete log uniqueness with e = -s.
  exact (finiteFieldExponent_eq_of_pow_eq
    (canonicalResidueZetaP_isPrimitiveRoot (p := p) (K := K) hP'_bot hp_in_P')
    hdiv_P' h_descent.symm).symm

end Furtwaengler

end BernoulliRegular

end
