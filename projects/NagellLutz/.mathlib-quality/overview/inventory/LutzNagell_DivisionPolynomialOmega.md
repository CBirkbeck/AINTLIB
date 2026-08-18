# Inventory: `LutzNagell/DivisionPolynomialOmega.lean`

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean`

Extends mathlib's Weierstrass-curve division-polynomial development with the `ω` family of division polynomials, the complement `ψc` of `ψ(n)` in `ψ(2n)`, and the `invar` invariant polynomial, all needed for the `ZSMul` proof. Two local macros `C_simp` and `map_simp` are defined (lines 26-33) for normalising constant-coefficient `C`-pushes and `RingHom`-map-pushes respectively; these are tactic macros, not declarations.

All declarations live in `namespace WeierstrassCurve` with `variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)`. The first block is in a `noncomputable section`.

---

### def invar
- Type: `def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄`
- What: The "invariant" univariate polynomial in `R[X]`, equal to the quotient `(ψ(n-1)²ψ(n+2)+ψ(n-2)ψ(n+1)²+ψ₂²ψ(n)³)/ψ(n+1)ψ(n)ψ(n-1)` for arbitrary `n` modulo the Weierstrass polynomial.
- How: Direct definition as `6X² + b₂X + b₄` using the curve's `b₂`, `b₄` invariants; no proof.
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: []
- Used by: `preΨ₄_add_Ψ₂Sq_sq`, `ω_spec` (in file)
- Visibility: public
- Lines: 45-48 (def, no proof)
- Notes: none

### def ψc
- Type: `def ψc : ℤ → R[X][Y] := compl₂EDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`
- What: The complement of `ψ(n)` in `ψ(2n)`, i.e. the bivariate polynomial sequence whose product with `ψ(n)` gives `ψ(2n)`.
- How: Defined directly via mathlib's `compl₂EDS` applied to the curve's `ψ₂`, `Ψ₃`, `preΨ₄` (with `C` lifting the latter two into `R[X][Y]`); no proof.
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: []
- Used by: `ω_spec`, `two_mul_ω`, `ψc_spec`, `ψc_neg` (in file)
- Visibility: public
- Lines: 50-51 (def, no proof)
- Notes: none

### lemma isEllSequence_ψ
- Type: `lemma isEllSequence_ψ : IsEllSequence W.ψ := IsEllSequence.normEDS`
- What: The `ψ` family of division polynomials forms an elliptic sequence.
- How: Immediate term-mode application of mathlib's `IsEllSequence.normEDS` (the normalised EDS is an elliptic sequence).
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 53 (1-line proof)
- Notes: none

### lemma C_Ψ₃_eq
- Type (signature): `C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2 + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W`
- What: Expresses the constant-lift `C Ψ₃` of the third division polynomial as a bivariate expression in `Ψ₂Sq`, `polynomialX`, `polynomial`, `ψ₂` and the `a₁, a₂` coefficients.
- How: Unfolds all the definitions (`Ψ₃`, `Ψ₂Sq`, `polynomial`, `polynomialX`, `ψ₂`, `polynomialY`, `b₂`, `b₄`, `b₆`, `b₈`, `CC`) with `simp_rw`, pushes `C` through with the `C_simp` macro, then closes by `ring`.
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 55-58 (proof 1 line: `simp_rw …; C_simp; ring`)
- Notes: none

### lemma preΨ₄_add_Ψ₂Sq_sq
- Type: `W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃`
- What: Identity relating the pre-fourth division polynomial plus the square of `Ψ₂Sq` to the product of the invariant and the third division polynomial, all in `R[X]`.
- How: Rewrites `preΨ₄`, `Ψ₂Sq`, `invar`, `Ψ₃` to their definitions, then closes via `linear_combination` using `congr(C $W.b_relation) * X^2` (the lifted `b`-relation `b₂ b₆ - b₄² = ... ` scaled by `X²`) with normalisation `C_simp; ring_nf`.
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `invar`
- Used by: `preΨ₄_add_ψ₂_pow_four` (in file)
- Visibility: public
- Lines: 60-62 (proof 2 lines)
- Notes: hinges on mathlib's `WeierstrassCurve.b_relation`; none

### lemma preΨ₄_add_ψ₂_pow_four
- Type (signature): `C W.preΨ₄ + W.ψ₂ ^ 4 = C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq)`
- What: Bivariate identity expressing the constant-lift of `preΨ₄` plus `ψ₂⁴` as the lift of `invar·Ψ₃` plus a multiple of the Weierstrass `polynomial`.
- How: Rewrites `4 = 2*2`, uses `pow_mul`, `ψ₂_sq` (the square of `ψ₂`), `add_sq`, collapses `C` products via `← C_pow, ← C_add`, then substitutes the previous lemma `preΨ₄_add_Ψ₂Sq_sq`; finishes with `C_simp; ring`.
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `preΨ₄_add_Ψ₂Sq_sq`, `invar`
- Used by: `ω_spec` (in file)
- Visibility: public
- Lines: 64-67 (proof 2 lines)
- Notes: hinges on `preΨ₄_add_Ψ₂Sq_sq` and mathlib's `ψ₂_sq`; none

### lemma φ_mul_ψ
- Type: `lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n`
- What: Identity giving the product `φ(n)·ψ(n)` as `X·ψ(n)³` minus the `invarDenom` of `ψ` at `(1, n)`.
- How: Unfolds `φ` and mathlib's `invarDenom`, then closes by `ring`.
- Hypotheses: `n : ℤ`; `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: []
- Used by: `ω_spec` (in file)
- Visibility: public
- Lines: 69-70 (proof 1 line)
- Notes: none

### def WeierstrassCurve.ω (protected)
- Type (signature, abbreviated): `protected def ω (n : ℤ) : R[X][Y] := redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n * ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃ + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq)) - compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3`
- What: The `ω` family of division polynomials; `ω n` gives the second (`Y`) Jacobian coordinate of scalar multiplication by `n` on the curve.
- How: Direct definition as a combination of mathlib's `redInvarDenom` and `compl₂EDSAux` (built from `ψ₂`, `C Ψ₃`, `C preΨ₄`), the affine polynomials `polynomialX/Y`, `negPolynomial`, the Weierstrass `polynomial`, and `ψ n ^ 3`; no proof.
- Hypotheses: `n : ℤ`; `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ψ` (via `W.ψ`); otherwise mathlib primitives
- Used by: `ω_spec`, `ω_zero`, `ω_one`, `map_ω` (in file)
- Visibility: public (protected)
- Lines: 72-78 (def, no proof)
- Notes: none

### lemma ω_spec
- Type: `lemma ω_spec (n : ℤ) : 2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n`
- What: The defining specification of `ω`: twice `ω(n)` plus the `a₁` and `a₃` correction terms equals the complement `ψc(n)`.
- How: A long rewrite chain unfolding `ψc` and applying mathlib's `compl₂EDS_eq_redInvarNum_sub`, `redInvar_normEDS`, then this file's `preΨ₄_add_ψ₂_pow_four` and `φ_mul_ψ`, mathlib's `invarDenom_eq_redInvarDenom_mul`, then unfolding `ω`, `invar`, `b₂`, `b₄`, `ψ₂`, `polynomialY`, `polynomialX`, `negPolynomial`; closes with `C_simp; ring`.
- Hypotheses: `n : ℤ`; `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ψc`, `preΨ₄_add_ψ₂_pow_four`, `φ_mul_ψ`, `ω` (via `W.ω`), `invar`
- Used by: `two_mul_ω` (in file)
- Visibility: public
- Lines: 82-87 (proof 6 lines)
- Notes: hinges on `preΨ₄_add_ψ₂_pow_four`, `φ_mul_ψ` and mathlib's `compl₂EDS_eq_redInvarNum_sub` / `redInvar_normEDS`; none

### lemma two_mul_ω
- Type: `lemma two_mul_ω (n : ℤ) : 2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3`
- What: Rearrangement of `ω_spec` solving for `2·ω(n)` in terms of `ψc(n)` and the correction terms.
- How: Rewrites backwards through `ω_spec` then closes with `abel`.
- Hypotheses: `n : ℤ`; `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ω_spec`, `ψc` (via statement), `ω` (via `W.ω`)
- Used by: `universal_ω_neg` (in file)
- Visibility: public
- Lines: 89-91 (proof 1 line)
- Notes: none

### lemma ψc_spec
- Type: `lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_compl₂EDS _ _ _ _`
- What: The complement property: `ψ(n)·ψc(n) = ψ(2n)`.
- How: Term-mode application of mathlib's `normEDS_mul_compl₂EDS`.
- Hypotheses: `n : ℤ`; `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ψc` (via statement)
- Used by: unused in file
- Visibility: public
- Lines: 93 (1-line proof)
- Notes: none

### lemma ω_zero
- Type: `@[simp] lemma ω_zero : W.ω 0 = 1 := by simp [ω]`
- What: `ω(0) = 1`.
- How: `simp` unfolding `ω` (the `redInvarDenom`/`compl₂EDSAux` at 0 collapse to give 1).
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ω` (via `W.ω`)
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 95 (1-line proof)
- Notes: none

### lemma ω_one
- Type: `@[simp] lemma ω_one : W.ω 1 = Y := by simp [ω, ψ₂, ← Affine.Y_sub_polynomialY]`
- What: `ω(1) = Y` (the `Y` coordinate).
- How: `simp` unfolding `ω`, `ψ₂`, and rewriting backwards through mathlib's `Affine.Y_sub_polynomialY`.
- Hypotheses: `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ω` (via `W.ω`)
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 96 (1-line proof)
- Notes: none

### lemma ψc_neg
- Type: `@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]`
- What: `ψc` is even: `ψc(-n) = ψc(n)`.
- How: `simp` unfolding `ψc` (mathlib's `compl₂EDS` is even in its index).
- Hypotheses: `n : ℤ`; `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ψc` (via `W.ψc`)
- Used by: `universal_ω_neg` (in file)
- Visibility: public (`@[simp]`)
- Lines: 97 (1-line proof)
- Notes: none

### lemma map_ω
- Type: `@[simp] lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f)`
- What: Naturality of `ω` under a ring homomorphism `f : R →+* S`: the `ω` of the mapped curve equals the map of `ω`.
- How: `simp_rw` pushing the map through every constituent via mathlib's `map_redInvarDenom`, `map_compl₂EDSAux`, `map_polynomial`, `map_polynomialX/Y`, `map_negPolynomial`, `map_ψ₂`, `map_Ψ₃`, `map_preΨ₄`, `map_Ψ₂Sq`, `map_ψ` (after rewriting `ω` and `← coe_mapRingHom`), then a closing `simp`.
- Hypotheses: `n : ℤ`; `f : R →+* S`; `W : WeierstrassCurve R`, with `S` a commutative ring.
- Uses from project: `ω` (via `.ω`)
- Used by: `ω_neg` (in file)
- Visibility: public (`@[simp]`)
- Lines: 109-114 (proof 3 lines)
- Notes: opened `Affine EllSequence in`; relies on the family of mathlib `map_*` lemmas; none

### lemma universal_ω_neg (private)
- Type (signature): `private lemma universal_ω_neg (n : ℤ) : letI W := Universal.curve; W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3`
- What: The negation formula for `ω` proved specifically over the universal Weierstrass curve `Universal.curve`.
- How: Reduces using `mul_cancel_left_mem_nonZeroDivisors` together with `Universal.Poly.two_ne_zero` (so cancelling the factor of `2` is valid over the universal polynomial ring), then `simp_rw` with `left_distrib`, `two_mul_ω`, `ψc_neg`, mathlib's `ψ_neg`, `φ_neg`, and closes with `ring`.
- Hypotheses: `n : ℤ`; specialised to `W := Universal.curve` (the universal curve over the universal polynomial ring).
- Uses from project: `two_mul_ω`, `ψc_neg`, `ω` (via `W.ω`)
- Used by: `ω_neg` (in file)
- Visibility: private
- Lines: 116-120 (proof 3 lines)
- Notes: hinges on mathlib's `mul_cancel_left_mem_nonZeroDivisors`, `Universal.Poly.two_ne_zero` and `two_mul_ω`; none

### lemma ω_neg
- Type: `lemma ω_neg (n : ℤ) : W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3`
- What: The negation formula for `ω` over an arbitrary curve: `ω(-n) = ω(n) + a₁·φ(n)·ψ(n) + a₃·ψ(n)³`.
- How: Transfers the universal case via `← W.map_specialize` (specialising the universal curve to `W`), then rewrites through `map_ω`, the private `universal_ω_neg`, mathlib's `map_φ`, `map_ω`, `map_ψ`, and closes with `simp`.
- Hypotheses: `n : ℤ`; `W : WeierstrassCurve R` over a commutative ring `R`.
- Uses from project: `ω` (via `W.ω`), `map_ω`, `universal_ω_neg`
- Used by: unused in file
- Visibility: public
- Lines: 122-123 (proof 1 line)
- Notes: hinges on `universal_ω_neg`, `map_ω` and mathlib's `map_specialize`; none

---

## File Summary

- **Total declarations: 16** — 3 defs (`invar`, `ψc`, `ω`) / 13 lemmas+theorems (`isEllSequence_ψ`, `C_Ψ₃_eq`, `preΨ₄_add_Ψ₂Sq_sq`, `preΨ₄_add_ψ₂_pow_four`, `φ_mul_ψ`, `ω_spec`, `two_mul_ω`, `ψc_spec`, `ω_zero`, `ω_one`, `ψc_neg`, `map_ω`, `universal_ω_neg`, `ω_neg`) / 0 instances. (Also 2 non-declaration local tactic macros: `C_simp`, `map_simp`.)
- **Key API (used by ≥3 in-file):**
  - `ω` (the def) — used by `ω_spec`, `ω_zero`, `ω_one`, `map_ω`, `two_mul_ω`, `universal_ω_neg`, `ω_neg` (and is the file's central object).
  - `ψc` — used by `ω_spec`, `two_mul_ω`, `ψc_spec`, `ψc_neg`.
  - `invar` — used by `preΨ₄_add_Ψ₂Sq_sq`, `preΨ₄_add_ψ₂_pow_four`, `ω_spec`.
- **Unused decls (within this file):** `isEllSequence_ψ`, `C_Ψ₃_eq`, `ψc_spec`, `ω_zero`, `ω_one`, `ω_neg` (these are public API consumed by other files such as the ZSMul proof, not internally).
- **Decls with `sorry`:** none.
- **Decls with `set_option`:** none.
- **Proofs >50 lines (OVER-50):** none (0).
- **Proofs 30-50 lines:** none (0).
- **Note:** `map_simp` macro (lines 29-33) is defined but appears unused within this file's proof bodies.
