import BernoulliRegular.FLT37.Eichler.CaseII.Section91.ConjNormReassembly

/-!
# [FLT37-CASEII-R2] Washington §9.1 factor-equation extraction (the squared-form → factor step)

This file builds the **factor-equation extraction** of Washington *Introduction to Cyclotomic
Fields* (2nd ed., GTM 83), §9.1 (pp. 170–171): the derivation that turns the **squared form** of the
adjacent factor

  `X² = η'·W^p`,    `X = (ω+ζ^a θ)/(1-ζ^a)`,  `η'` a (real) unit,  `W ∈ K`,

into the **factor equation**

  `X = η_a·ρ_a^p`,    `η_a = η'^{(p+1)/2}` a (real) unit,  `ρ_a = W^{(p+1)/2}/X ∈ K`.

This is the "raising both sides to the `(p+1)/2`th power" step on Washington p. 171.  It is **pure
field algebra** (no ideal theory, no class groups): the squared form is the input, the factor
equation the output, and the bridge is `X^{p+1} = (X²)^{(p+1)/2}`, `X = X^{p+1}/X^p`.

It is the **field-level core** of the factor-equation extraction that, composed with the proven §9.1
reassembly (`CaseIISection91ConjNormReassembly.lean`) and the capstone packaging
(`CaseIISection91DescendedDatum.lean`), supplies the `hfa_pos`/`hfa_neg`/`hfb_pos`/`hfb_neg`
hypotheses of `freeContentCaseIIData37_of_factorEquations`.

## What this file proves (real, axiom-clean Lean — no `sorry`, no `axiom`)

* `washington_factor_of_squared` — the field-algebra core: from `X² = η'·W^p` with `X ≠ 0`, `p` odd,
  produce `X = η_a·ρ_a^p` with `η_a = η'^{(p+1)/2}` (a `Kˣ`-unit, real if `η'` is) and the explicit
  `ρ_a = W^{(p+1)/2}·X⁻¹`.

* `washington_factor_of_squared_pair` — the **conjugate-paired** form (the shape the capstone
  consumes): from the squared form of `X = (ω+ζ^a θ)/(1-ζ^a)` *and* its conjugate
  `X̄ = (ω+ζ^{-a}θ)/(1-ζ^{-a})` with a **common real unit** `η'` and `W̄ = σW`, produce **both**
  factor equations
  ```
  (ω+ζ^a θ)/(1-ζ^a)   = η_a·ρ_a^p,
  (ω+ζ^{-a}θ)/(1-ζ^{-a}) = η_a·(σρ_a)^p,
  ```
  with the **same** real unit `η_a = η'^{(p+1)/2}` and conjugate generators `ρ_a, σρ_a`
  (Washington's `η_a = η_{-a}`, `ρ̄_a = ρ_{-a}`).

## The squared form (Washington p. 170, the input to this file)

Washington derives `X² = η'·W^p` by combining two ideal/class-level facts at the adjacent root `η`:

* **Lemma 9.2** (the *quotient* is a `p`-th power): `α := (X/X̄) = α₁^p` for some `α₁ ∈ K` — this is
  the proven `caseIIRootClassConjFixed37_proven` in its element form (the corrected radical
  `α₀·u` a `p`-th power, with the `-ζ^a` twist in the unit).
* **the B₀-style real-generator argument** (the *product* is a real-unit times a `p`-th power):
  `X·X̄ = η'·(β')^p`, `η'` a real unit, `β'` real — from `(B_a·B_{-a})` principal (σ-fixed, `p∤h⁺`).

Multiplying, `X² = (X·X̄)·(X/X̄) = η'·(β')^p·α₁^p = η'·(β'·α₁)^p`, i.e. `W = β'·α₁`.  The genuine
analytic content (Lemma 9.2 unramifiedness, the B₀-principalization) is proven elsewhere; **this
file is the algebra that converts the resulting squared form into the factor equation.**

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 170–171.
-/

@[expose] public section

noncomputable section

open NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]

/-! ## 1. The squared-form → factor-equation field-algebra core -/

omit [NumberField K] [NumberField.IsCMField K] in
/-- **[SQUARED → FACTOR] The field-algebra core of Washington p. 171.**

Given the squared form `X² = (η' : K)·W^p` (`η' : Kˣ` a unit, `W ∈ K`, `X ≠ 0`) at an **odd** `p`,
there is a `ρ : K` with
```
X = (η' ^ ((p+1)/2) : Kˣ) · ρ ^ p,
```
namely `ρ = W ^ ((p+1)/2) · X⁻¹`.

Proof (Washington's "raise to the `(p+1)/2`th power"): write `k = (p+1)/2`, so `2k = p+1` (`p` odd).
Then `X ^ (p+1) = (X²)^k = (η')^k · (W^k)^p`, and `X = X^{p+1}·(X^p)⁻¹ = (η')^k · (W^k·X⁻¹)^p`. -/
theorem washington_factor_of_squared {p : ℕ} (hp : Odd p) {X W : K} {η' : Kˣ}
    (hX : X ≠ 0) (hsq : X ^ 2 = (η' : K) * W ^ p) :
    X = ((η' ^ ((p + 1) / 2) : Kˣ) : K) * (W ^ ((p + 1) / 2) * X⁻¹) ^ p := by
  obtain ⟨t, ht⟩ := hp
  -- `k = (p+1)/2`, `2k = p+1`.
  set k := (p + 1) / 2 with hk_def
  have h2k : 2 * k = p + 1 := by rw [hk_def, ht]; omega
  -- `X ^ (p+1) = (X²)^k`.
  have hXpow : X ^ (p + 1) = (X ^ 2) ^ k := by rw [← pow_mul, h2k]
  -- `(X²)^k = (η')^k · (W^k)^p`.
  have hRHS : (X ^ 2) ^ k = ((η' ^ k : Kˣ) : K) * (W ^ k) ^ p := by
    rw [hsq, mul_pow, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm k p]
  -- so `X ^ (p+1) = (η')^k · (W^k)^p`.
  have hXp1 : X ^ (p + 1) = ((η' ^ k : Kˣ) : K) * (W ^ k) ^ p := hXpow.trans hRHS
  -- the target RHS `(η')^k · (W^k·X⁻¹)^p = (η')^k · (W^k)^p · (X^p)⁻¹ = X^{p+1}·(X^p)⁻¹ = X`.
  have hXne : (X ^ p) ≠ 0 := pow_ne_zero p hX
  rw [mul_pow, inv_pow, ← mul_assoc, ← hXp1]
  field_simp
  rw [mul_comm, ← pow_succ]

/-- **The factor unit `η_a = η'^{(p+1)/2}` is real when `η'` is real.**  (`σ` commutes with powers.)
-/
theorem washington_factorUnit_real {p : ℕ} {η' : Kˣ}
    (hη' : complexConj K (η' : K) = (η' : K)) :
    complexConj K ((η' ^ ((p + 1) / 2) : Kˣ) : K) = ((η' ^ ((p + 1) / 2) : Kˣ) : K) := by
  rw [Units.val_pow_eq_pow_val, map_pow, hη']

/-! ## 2. The conjugate-paired factor equations (the capstone shape)

The capstone `freeContentCaseIIData37_of_factorEquations` consumes the two factor equations at `±a`
with the **same** real unit `η_a` and the conjugate generators.  Washington derives both from
the **single** squared form via the conjugate-symmetry `η_a = η_{−a}` and `σρ_a = ρ_{−a}`.  We
package that: from the squared form at `X` and its conjugate with a **common real unit** `η'` and
conjugate `W`-witnesses (`σW` for the conjugate), both factor equations hold with the *same* `η_a`
and generators `ρ_a, σρ_a`. -/

/-- **[CONJUGATE-PAIRED FACTOR EQUATIONS] Both `±a` factor equations from the paired squared form.**

Let `Xp = (ω+ζ^a θ)/(1-ζ^a)` and `Xn = (ω+ζ^{−a}θ)/(1-ζ^{−a})` be the adjacent factor and its
conjugate, with `complexConj K Xp = Xn` (real `ω, θ`).  Suppose the **paired squared form** holds
with a
**common real unit** `η'` and a witness `W` for `Xp` whose conjugate `σW` is the witness for `Xn`:
```
Xp² = η'·W^p,        Xn² = η'·(σW)^p,        σ(η') = η',  σ(Xp) = Xn.
```
Then, writing `η_a = η'^{(p+1)/2}` (a **real** unit) and `ρ_a = W^{(p+1)/2}·Xp⁻¹`, **both** factor
equations hold:
```
Xp = η_a·ρ_a^p,        Xn = η_a·(σρ_a)^p,
```
with `σρ_a = (σW)^{(p+1)/2}·Xn⁻¹` the conjugate generator.

This is exactly the `Xp = η_a ρ_a^p`, `Xn = η_a (σρ_a)^p` pair the capstone's
`hfa_pos`/`hfa_neg` consume (after clearing the `(1-ζ^{±a})` denominator). -/
theorem washington_factor_of_squared_pair {p : ℕ} (hp : Odd p) {Xp Xn W : K} {η' : Kˣ}
    (hXp : Xp ≠ 0) (hXn : Xn ≠ 0)
    (hconjX : complexConj K Xp = Xn)
    (hsqp : Xp ^ 2 = (η' : K) * W ^ p)
    (hsqn : Xn ^ 2 = (η' : K) * (complexConj K W) ^ p) :
    Xp = ((η' ^ ((p + 1) / 2) : Kˣ) : K) * (W ^ ((p + 1) / 2) * Xp⁻¹) ^ p ∧
      Xn = ((η' ^ ((p + 1) / 2) : Kˣ) : K) *
        (complexConj K (W ^ ((p + 1) / 2) * Xp⁻¹)) ^ p := by
  refine ⟨washington_factor_of_squared hp hXp hsqp, ?_⟩
  -- The conjugate generator: `σ(W^{(p+1)/2}·Xp⁻¹) = (σW)^{(p+1)/2}·Xn⁻¹`.
  have hconjρ : complexConj K (W ^ ((p + 1) / 2) * Xp⁻¹) =
      (complexConj K W) ^ ((p + 1) / 2) * Xn⁻¹ := by
    rw [map_mul, map_pow, map_inv₀, hconjX]
  rw [hconjρ]
  exact washington_factor_of_squared hp hXn hsqn

end BernoulliRegular.FLT37.Eichler

end

end
