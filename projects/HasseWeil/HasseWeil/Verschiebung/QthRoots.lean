/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.OmegaPullbackCoeff
import HasseWeil.Verschiebung.DivPolyExpand
import HasseWeil.Verschiebung.PurelyInsep
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.ReduceModChar

/-!
# q-th roots for `mulByInt q`'s coordinate generators (Session 3 — explicit construction)

Following the Session 3 finding (`Φ_q ∈ F_p[X^q]` and `ΨSq_q ∈ F_p[X^q]`
in char p with the b-relation, sympy-verified for q ∈ {2, 3, 4, 5}), this
file provides the **polynomial-level q-th-root extractor** and an explicit
witness form for the Frobenius-image membership of `mulByInt_x q`.

## Strategy

Given `f ∈ F_p[X]` with `f ∈ Set.range (Polynomial.expand K q)` (i.e.,
`f = f'(X^q)` for some `f' ∈ F_p[X]`), in char p with q = p^k we have:

```
f^q = (sum c_i X^i)^q = sum c_i^q X^(qi) = sum c_i X^(qi) = expand q f
```

(Frobenius: c_i^q = c_i for c_i ∈ F_p, plus the q-th-power binomial.)

So `f' satisfies (f')^q = expand q f' = f`. Evaluating at `x_gen ∈ K(E)`:

```
f'(x_gen)^q = (f^q evaluated at x_gen) = f(x_gen)
```

Hence `f(x_gen)` has a q-th root in K(E), namely `f'(x_gen)`. Applied to
`f = Φ_q` (which lies in `Polynomial.expand`-range under the b-relation),
we conclude `Φ_q(x_gen)` is a q-th power, so `mulByInt_x q = Φ_q/ΨSq_q`
is a q-th power, so `[q]*x_gen ∈ Im(π*)`.

## What's shipped

* `polyExpandRoot` — the polynomial-level extractor (uses `Classical.choose`
  on the `Set.range` membership witness).
* `polyExpandRoot_spec` — its defining property `expand q (root f) = f`.
* `PolyPowCardEq` — the q-th-power-equals-expand identity for polynomials
  over a finite field. This is `f^q = expand q f`, a structural fact in
  char p with q = #K. It corresponds to mathlib's
  `Polynomial.expand_eq_pow_card` (when the lemma name is verified) or
  follows directly from `add_pow_card_pow` + `FiniteField.pow_card`.

## Status

Witness-parametric on the inputs:

1. `Φ_q ∈ Polynomial.expand`-range (Lean formalisation of the b-relation
   reduction; sympy-verified).
2. `ΨSq_q ∈ Polynomial.expand`-range (same).
3. `PolyPowCardEq K` (mathlib structural fact about finite fields).

Each input has a clear unconditional path; the residual is purely Lean
formalisation of the b-relation reduction (~150 LOC) and tagging the
mathlib structural fact (~10 LOC). Total ~160 LOC remaining for the
unconditional discharge of `mulByInt_x q ∈ Im(π*)`.

The y-coordinate analog (`mulByInt_y q ∈ Im(π*)`) requires bivariate
versions of the same, ~150 LOC.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### Polynomial-side q-th-root extraction -/

/-- **Polynomial-level q-th-root extractor**: if `f ∈ Polynomial.expand K q`-range,
    extract `f'` with `expand K q f' = f` (i.e. `f'(X^q) = f(X)`). -/
noncomputable def polyExpandRoot
    (f : Polynomial K) (hf : f ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K)))) :
    Polynomial K :=
  hf.choose

/-- Defining property: `polyExpandRoot f hf` satisfies `expand q · = f`. -/
theorem polyExpandRoot_spec
    (f : Polynomial K) (hf : f ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K)))) :
    Polynomial.expand K (Fintype.card K) (polyExpandRoot f hf) = f :=
  hf.choose_spec

/-! ### The polynomial Frobenius identity (witness form)

For `f ∈ K[X]` over a finite field `K` of cardinality `q`, the identity
`f^q = expand q f` holds. This is `Polynomial.expand_pow_eq_pow_card` in
mathlib (or follows from `add_pow_card_pow` + `FiniteField.pow_card`).
Held as a hypothesis here pending the precise mathlib lemma name. -/

/-- **Witness form of the polynomial q-th-power identity**: `f^q = expand q f`
    for every `f ∈ K[X]`. Structural fact in char p with q = #K. -/
def PolyPowCardEq (K : Type*) [Field K] [Fintype K] : Prop :=
  ∀ f : Polynomial K, f ^ Fintype.card K = Polynomial.expand K (Fintype.card K) f

/-- **Polynomial Frobenius identity, unconditional**: for `f ∈ K[X]` over a
    finite field `K` of cardinality `q = p^n`, we have `f^q = expand q f`.

    Proof: extract `(p, n)` via `FiniteField.card'`, set up `ExpChar K p`,
    then induct on the polynomial:
    * Sum case: `add_pow_expChar_pow`.
    * Monomial case: `(C a · X^m)^q = C a · X^(mq) = expand q (C a · X^m)`
      using `FiniteField.pow_card a = a`. -/
theorem polyPowCardEq_of_finite : PolyPowCardEq K := by
  obtain ⟨p, hCharP, ⟨n, _hn_pos⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : CharP K p := hCharP
  haveI : Fact p.Prime := ⟨hp_prime⟩
  intro f
  rw [hcard]
  induction f using Polynomial.induction_on' with
  | add p_poly q_poly hp_poly hq_poly =>
    rw [add_pow_expChar_pow, hp_poly, hq_poly, map_add]
  | monomial m a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_pow, ← Polynomial.C_pow, ← hcard,
      show (a : K) ^ Fintype.card K = a from FiniteField.pow_card a,
      map_mul, map_pow, Polynomial.expand_C, Polynomial.expand_X, ← pow_mul]
    ring

/-! ### The q-th root for `Φ_q(x_gen)`, witness form -/

/-- **Witness form**: given `Φ_q ∈ Polynomial.expand q-range` and the
    polynomial Frobenius identity, `Φ_q(x_gen) = π* g` for some
    `g ∈ K(E)` (specifically `g = polyExpandRoot Φ_q hΦ` evaluated at
    `x_gen` via `Polynomial.aeval`).

    Combined with the analogous fact for `ΨSq_q` and division, this would
    give `mulByInt_x q ∈ Im(π*)`. -/
theorem polyExpandRoot_aeval_pow_eq
    (f : Polynomial K) (hf : f ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K))))
    (h_pow : PolyPowCardEq K) (z : W.toAffine.FunctionField) :
    (Polynomial.aeval z (polyExpandRoot f hf)) ^ Fintype.card K =
      Polynomial.aeval z f := by
  -- (aeval z f')^q = aeval z (f'^q) = aeval z (expand q f') = aeval z f
  rw [← map_pow, h_pow (polyExpandRoot f hf), polyExpandRoot_spec]

/-- The natural-number `p` casts to `0` in `K(E)` whenever `CharP K p`, transported
    through the injective `algebraMap K → K(E)`. Shared helper for the char-`p`
    Freshman's-dream and Weierstrass-substitution lemmas below. -/
private theorem natCast_functionField_eq_zero (W : WeierstrassCurve K) (p : ℕ) [CharP K p] :
    (p : W.toAffine.FunctionField) = 0 := by
  have : CharP W.toAffine.FunctionField p :=
    charP_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  exact CharP.cast_eq_zero W.toAffine.FunctionField p

/-! ### b-relation reduction: `Φ_q ∈ Set.range (expand K q)` for q ∈ K

Sympy has verified (`scripts/verify_phi_q_clean.py`, `verify_phi_4.py`)
that `Φ_q ∈ F_p[X^q]` and `ΨSq_q ∈ F_p[X^q]` generically (over the
b-relation) for q = p^k in char p. This section ships the Lean
formalisation, starting with the smallest case q = 2 in char 2. -/

/-- **q = 2 in char 2**: `W.Φ 2 ∈ Set.range (Polynomial.expand K 2)`.
    K-level specialisation of `Φ_two_mem_expand_two_charP` (`DivPolyExpand`). -/
theorem Φ_two_mem_expand_two_char_two
    (W : WeierstrassCurve K) [CharP K 2] :
    W.Φ 2 ∈ Set.range (⇑(Polynomial.expand K 2)) :=
  Φ_two_mem_expand_two_charP W

/-! ### q = 3 in char 3: polynomial-side identities

By sympy verification (`scripts/verify_phi_q_clean.py`), `Φ_3 ∈ K[X³]` and
`ΨSq_3 ∈ K[X³]` after b-relation reduction in char 3.

Structurally simpler for `ΨSq_3 = Ψ₃²`: in char 3, `Ψ₃ = b₂·X³ + b₈`
(since `3·X⁴`, `3b₄·X²`, `3b₆·X` all vanish), so `Ψ₃ = expand 3 (b₂·X + b₈)`
and `ΨSq_3 = (expand 3 (b₂·X + b₈))² = expand 3 ((b₂·X + b₈)²)`. -/

/-- **q = 3 in char 3**: `W.Ψ₃ ∈ Set.range (Polynomial.expand K 3)`.
    K-level specialisation of `Ψ₃_mem_expand_three_charP` (`DivPolyExpand`). -/
theorem Ψ₃_mem_expand_three_char_three
    (W : WeierstrassCurve K) [CharP K 3] :
    W.Ψ₃ ∈ Set.range (⇑(Polynomial.expand K 3)) :=
  Ψ₃_mem_expand_three_charP W

/-- **q = 3 in char 3**: `W.ΨSq 3 ∈ Set.range (Polynomial.expand K 3)`.
    K-level specialisation of `ΨSq_three_mem_expand_three_charP` (`DivPolyExpand`). -/
theorem ΨSq_three_mem_expand_three_char_three
    (W : WeierstrassCurve K) [CharP K 3] :
    W.ΨSq 3 ∈ Set.range (⇑(Polynomial.expand K 3)) :=
  ΨSq_three_mem_expand_three_charP W

/-- **Char-3 b-relation**: `b₈ = b₂·b₆ - b₄²`. K-level specialisation of
    `b_relation_of_charP_three` (`DivPolyExpand`). -/
theorem b_relation_of_char_three
    (W : WeierstrassCurve K) [CharP K 3] :
    W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 :=
  b_relation_of_charP_three W

/-- **q = 3 in char 3**: `W.Φ 3 ∈ Set.range (Polynomial.expand K 3)`.
    K-level specialisation of `Φ_three_mem_expand_three_charP` (`DivPolyExpand`).
    The substantive sympy-derived `linear_combination` multiplier lives at the
    generic CommRing level. -/
theorem Φ_three_mem_expand_three_char_three
    (W : WeierstrassCurve K) [CharP K 3] :
    W.Φ 3 ∈ Set.range (⇑(Polynomial.expand K 3)) :=
  Φ_three_mem_expand_three_charP W

/-! ### Universal x_gen q-th root: from expand-range memberships -/

/-- **Universal x_gen q-th root, witness form**: given that `Φ_q` and
    `ΨSq_q` are q-th-power polynomials (in `Polynomial.expand`-range),
    the q-th root of `(mulByInt W q).pullback x_gen = mulByInt_x q` exists
    in `K(E)`. Specifically, it's `Φ_q'(x_gen) / ΨSq_q'(x_gen)` where
    `Φ_q' = polyExpandRoot Φ_q hΦ` and similarly for `ΨSq_q`. -/
theorem mulByInt_q_pullback_x_gen_qth_root_of_expand_witness
    (h_Φ : (W.Φ ((Fintype.card K : ℕ) : ℤ)) ∈
      Set.range (⇑(Polynomial.expand K (Fintype.card K))))
    (h_ΨSq : (W.ΨSq ((Fintype.card K : ℕ) : ℤ)) ∈
      Set.range (⇑(Polynomial.expand K (Fintype.card K))))
    (hn : ((Fintype.card K : ℕ) : ℤ) ≠ 0) :
    ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) := by
  -- Define g = aeval x_gen Φ' / aeval x_gen ΨSq' where ' means polyExpandRoot.
  -- Then g^q = (aeval x_gen Φ')^q / (aeval x_gen ΨSq')^q
  --         = aeval x_gen (expand q Φ') / aeval x_gen (expand q ΨSq')   (polyPowCardEq)
  --         = aeval x_gen Φ / aeval x_gen ΨSq = mulByInt_x q
  --         = (mulByInt W q).pullback x_gen.
  have h_pow := polyPowCardEq_of_finite (K := K)
  set Φ' := polyExpandRoot (W.Φ ((Fintype.card K : ℕ) : ℤ)) h_Φ
  set ΨSq' := polyExpandRoot (W.ΨSq ((Fintype.card K : ℕ) : ℤ)) h_ΨSq
  have hΦ_root_pow : (Polynomial.aeval (x_gen W) Φ') ^ Fintype.card K =
      Polynomial.aeval (x_gen W) (W.Φ ((Fintype.card K : ℕ) : ℤ)) :=
    polyExpandRoot_aeval_pow_eq W _ h_Φ h_pow (x_gen W)
  have hΨSq_root_pow : (Polynomial.aeval (x_gen W) ΨSq') ^ Fintype.card K =
      Polynomial.aeval (x_gen W) (W.ΨSq ((Fintype.card K : ℕ) : ℤ)) :=
    polyExpandRoot_aeval_pow_eq W _ h_ΨSq h_pow (x_gen W)
  -- Identify aeval x_gen with the algebraMap chain (matches Φ_ff / ΨSq_ff defs).
  have hΦ_aeval : Polynomial.aeval (x_gen W) (W.Φ ((Fintype.card K : ℕ) : ℤ)) =
      Φ_ff W ((Fintype.card K : ℕ) : ℤ) := by
    change Polynomial.aeval
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))
      (W.Φ ((Fintype.card K : ℕ) : ℤ)) = _
    rw [Polynomial.aeval_algebraMap_apply
          (A := W.toAffine.CoordinateRing) (B := W.toAffine.FunctionField),
      Polynomial.aeval_algebraMap_apply
        (A := Polynomial K) (B := W.toAffine.CoordinateRing),
      Polynomial.aeval_X_left_apply]
    rfl
  have hΨSq_aeval : Polynomial.aeval (x_gen W) (W.ΨSq ((Fintype.card K : ℕ) : ℤ)) =
      ΨSq_ff W ((Fintype.card K : ℕ) : ℤ) := by
    change Polynomial.aeval
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))
      (W.ΨSq ((Fintype.card K : ℕ) : ℤ)) = _
    rw [Polynomial.aeval_algebraMap_apply
          (A := W.toAffine.CoordinateRing) (B := W.toAffine.FunctionField),
      Polynomial.aeval_algebraMap_apply
        (A := Polynomial K) (B := W.toAffine.CoordinateRing),
      Polynomial.aeval_X_left_apply]
    rfl
  refine ⟨Polynomial.aeval (x_gen W) Φ' / Polynomial.aeval (x_gen W) ΨSq', ?_⟩
  rw [div_pow, hΦ_root_pow, hΨSq_root_pow, hΦ_aeval, hΨSq_aeval]
  show _ = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))
  rw [mulByInt_pullback_x W ((Fintype.card K : ℕ) : ℤ) hn]
  rfl

/-! ### y_gen wrapper: q-th root from a `mulByInt_y` witness

Symmetric companion of the x_gen version: given a q-th-root for the
function-field element `mulByInt_y W q = ω_q / ψ_q^3`, transport it
through `mulByInt_pullback_y` to a q-th-root of `(mulByInt q).pullback y_gen`.
The substantive content (constructing `mulByInt_y W q ∈ K(E)^q`) reduces
to a bivariate polynomial decomposition for `ω_q` (analog of
`Φ_q ∈ Polynomial.expand`-range), which is character-specific. -/

/-- **y_gen q-th root, witness wrapper**: given a q-th root `g` of
    `mulByInt_y W q` in `K(E)`, conclude that `(mulByInt q).pullback (y_gen W)`
    has the same q-th root. Direct via `mulByInt_pullback_y`. -/
theorem mulByInt_q_pullback_y_gen_qth_root_of_witness
    (h_y : ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K = mulByInt_y W ((Fintype.card K : ℕ) : ℤ))
    (hn : ((Fintype.card K : ℕ) : ℤ) ≠ 0) :
    ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) := by
  obtain ⟨g, hg⟩ := h_y
  refine ⟨g, ?_⟩
  rw [hg]
  show _ = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.root W.toAffine.polynomial))
  rw [mulByInt_pullback_y W ((Fintype.card K : ℕ) : ℤ) hn]

/-- **q = 2 in char 2**: `W.ΨSq 2 ∈ Set.range (Polynomial.expand K 2)`.
    K-level specialisation of `ΨSq_two_mem_expand_two_charP` (`DivPolyExpand`). -/
theorem ΨSq_two_mem_expand_two_char_two
    (W : WeierstrassCurve K) [CharP K 2] :
    W.ΨSq 2 ∈ Set.range (⇑(Polynomial.expand K 2)) :=
  ΨSq_two_mem_expand_two_charP W

/-! ### Y-coefficient of ω₂ for q = 2 in char 2

The basis decomposition `ω 2 = C(A) + C(B) · Y` over `R[X][Y]` has, in
char 2, Y-coefficient `B(X) = a₁ · Ψ₃(X) + ψ₂(X)³` (where `ψ₂ = a₁X + a₃`
in char 2, since `2Y` vanishes).

We show this Y-coefficient lies in `Set.range (Polynomial.expand K 2)`:
the X¹ and X³ terms vanish via the b-relations
`b₂ = a₁² + 4·a₂` (so `b₂ ≡ a₁²` in char 2) and
`b₆ = a₃² + 4·a₆` (so `b₆ ≡ a₃²` in char 2).
The remaining terms `a₁X⁴`, `(a₁b₄ + a₁²a₃)X²`, `a₁b₈ + a₃³` are all
in even powers — explicit q-th-root extractor available. -/

/-- **Y-coefficient of ω₂ in char 2**, defined explicitly as
    `a₁ · Ψ₃ + (a₁X + a₃)³`. The Y-coefficient of `ω 2` in the
    `{1, Y}` basis decomposition over `R[X]`. -/
noncomputable def omega2_Y_coeff_char_two
    (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C W.a₁ * W.Ψ₃ +
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 3

/-- **q = 2 in char 2**: the Y-coefficient of `ω 2` lies in
    `Polynomial.expand K 2`-range. The X¹ coefficient is `a₁(b₆ + a₃²)`,
    which vanishes because `b₆ = a₃²` in char 2 (from `b₆ = a₃² + 4·a₆`).
    The X³ coefficient is `a₁(b₂ + a₁²)`, which vanishes because
    `b₂ = a₁²` in char 2. -/
theorem omega2_Y_coeff_mem_expand_two_char_two
    (W : WeierstrassCurve K) [CharP K 2] :
    omega2_Y_coeff_char_two W ∈ Set.range (⇑(Polynomial.expand K 2)) := by
  refine ⟨Polynomial.C W.a₁ * Polynomial.X ^ 2 +
    Polynomial.C (W.a₁ * W.b₄ + W.a₁ ^ 2 * W.a₃) * Polynomial.X +
    Polynomial.C (W.a₁ * W.b₈ + W.a₃ ^ 3), ?_⟩
  have h_2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h_b2 : W.b₂ = W.a₁ ^ 2 := WeierstrassCurve.b₂_of_char_two W
  have h_b6 : W.b₆ = W.a₃ ^ 2 := WeierstrassCurve.b₆_of_char_two W
  rw [omega2_Y_coeff_char_two, WeierstrassCurve.Ψ₃, h_b2, h_b6]
  simp only [map_add, map_mul, map_pow, Polynomial.expand_C, Polynomial.expand_X]
  have h_2P : (2 : Polynomial K) = 0 := by
    rw [show (2 : Polynomial K) = Polynomial.C 2 from rfl, h_2, Polynomial.C_0]
  have h_6P : (6 : Polynomial K) = 0 := by
    rw [show (6 : Polynomial K) = 2 * 3 from by ring, h_2P, zero_mul]
  linear_combination
    (-Polynomial.C W.a₁ * Polynomial.X * Polynomial.C W.a₃ ^ 2) * h_6P +
    (-Polynomial.C W.a₁ * Polynomial.X ^ 4
      - Polynomial.C W.a₁ * Polynomial.C W.b₄ * Polynomial.X ^ 2
      - Polynomial.C W.a₁ ^ 2 * Polynomial.C W.a₃ * Polynomial.X ^ 2
      - Polynomial.C W.a₁ ^ 3 * Polynomial.X ^ 3) * h_2P

/-! ### X-coefficient of ω₂ and the coupled identity (q=2 char-2)

The X-coefficient `A(X) := (X² + a₁²X + a₁a₃ + a₄)·Ψ₃ + (a₁X + a₃)⁴` of
the basis decomposition `ω 2 = C(A) + C(B)·Y` is **NOT** in
`Polynomial.expand K 2`-range generically. The y-side q-th-root
construction therefore relies on the **coupled identity**:

```
(α + β·y_gen)² = ω 2 / ψ₂³  (in char 2, K(E))
```

with α = α₀, β = α₁. Expanding via `y_gen² = a₁ x_gen y_gen + a₃ y_gen + cubic_x`:
```
α² = α₀² + α₁²·cubic_x + α₁²·ψ₂·y_gen
```

Matching coefficients with `(A + B·y_gen)/ψ₂³`:
* y_gen-side: `α₁²·ψ₂ = B/ψ₂³` ⟹ `α₁² = B/ψ₂⁴` ⟹ requires B ∈ expand-range (✓ shipped).
* 1-side: `α₀² + α₁²·cubic_x = A/ψ₂³` ⟹ `α₀²·ψ₂⁴ = A·ψ₂ + B·cubic_x` (in char 2; sign flips since -B=B).

The coupled-residual `A·ψ₂ + B·cubic_x` must be in expand-range. This is
**non-trivial** — sympy-verified for arbitrary char-2 Weierstrass curves
using the `b_relation_of_char_two` (`b₂·b₆ = b₄²`) identity. -/

/-- **X-coefficient of ω₂ in char 2**, defined explicitly as
    `(X² + a₁²X + a₁a₃ + a₄)·Ψ₃ + (a₁X + a₃)⁴`. The 1-coefficient of
    `ω 2` in the `{1, Y}` basis decomposition over `R[X]`. -/
noncomputable def omega2_X_coeff_char_two
    (W : WeierstrassCurve K) : Polynomial K :=
  (Polynomial.X ^ 2 + Polynomial.C (W.a₁ ^ 2) * Polynomial.X +
      Polynomial.C (W.a₁ * W.a₃) + Polynomial.C W.a₄) * W.Ψ₃ +
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 4

/-- **Cubic part of the Weierstrass equation**: `X³ + a₂·X² + a₄·X + a₆`,
    which equals `Y² + a₁·X·Y + a₃·Y` on the curve. -/
noncomputable def cubic_x (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
    Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆

/-- **The coupled-residual polynomial**:
    `A·ψ₂ + B·cubic_x` where ψ₂ = a₁X + a₃ in char 2.
    Sympy-verified to lie in `Polynomial.expand K 2`-range in char 2. -/
noncomputable def omega2_coupled_residual_char_two
    (W : WeierstrassCurve K) : Polynomial K :=
  omega2_X_coeff_char_two W *
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) +
  omega2_Y_coeff_char_two W * cubic_x W

/-- **The coupled-residual witness polynomial (q=2 char-2)**: the explicit
    polynomial `ω₂_coupled_witness ∈ K[X]` such that, sympy-verified,
    `expand 2 ω₂_coupled_witness = A·ψ₂ + B·cubic_x` in char 2. Provided
    here as a separate definition to enable the structural ship of the
    coupled identity (theorem follow-up). -/
noncomputable def omega2_coupled_witness_char_two
    (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C (W.a₁ * W.a₂ + W.a₃) * Polynomial.X ^ 3 +
  Polynomial.C (W.a₁ ^ 3 * W.a₄ + W.a₁ * W.a₃ ^ 2 + W.a₁ * W.a₆ + W.a₃ * W.a₄) *
    Polynomial.X ^ 2 +
  Polynomial.C (W.a₁ ^ 5 * W.a₆ + W.a₁ ^ 4 * W.a₃ * W.a₄ +
      W.a₁ ^ 3 * W.a₂ * W.a₃ ^ 2 + W.a₁ ^ 3 * W.a₂ * W.a₆ +
      W.a₁ ^ 3 * W.a₄ ^ 2 + W.a₁ ^ 2 * W.a₂ * W.a₃ * W.a₄ +
      W.a₁ ^ 2 * W.a₃ ^ 3 + W.a₁ ^ 2 * W.a₃ * W.a₆ +
      W.a₁ * W.a₂ ^ 2 * W.a₃ ^ 2 + W.a₁ * W.a₂ * W.a₄ ^ 2 +
      W.a₁ * W.a₃ ^ 2 * W.a₄ + W.a₃ * W.a₄ ^ 2) * Polynomial.X +
  Polynomial.C (W.a₁ ^ 3 * W.a₃ ^ 2 * W.a₆ + W.a₁ ^ 3 * W.a₆ ^ 2 +
      W.a₁ ^ 2 * W.a₃ ^ 3 * W.a₄ + W.a₁ * W.a₂ * W.a₃ ^ 4 +
      W.a₁ * W.a₂ * W.a₃ ^ 2 * W.a₆ + W.a₁ * W.a₄ ^ 2 * W.a₆ +
      W.a₂ * W.a₃ ^ 3 * W.a₄ + W.a₃ ^ 5 + W.a₃ ^ 3 * W.a₆ + W.a₃ * W.a₄ ^ 3)

/-- **Multiplier polynomial M(X) for the char-2 coupled identity (q=2)**:
    The sympy-verified polynomial such that
    `omega2_coupled_residual - expand K 2 witness = 2·M(X)`.
    With (2:K)=0, this difference vanishes, giving the identity. -/
noncomputable def omega2_coupled_multiplier_char_two
    (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C (3 * W.a₁) * Polynomial.X ^ 7 +
  Polynomial.C (3 * W.a₁ ^ 3 + W.a₁ * W.a₂ + W.a₃) * Polynomial.X ^ 6 +
  Polynomial.C (W.a₁ ^ 5 + W.a₁ ^ 3 * W.a₂ + 8 * W.a₁ ^ 2 * W.a₃ + 3 * W.a₁ * W.a₄) *
    Polynomial.X ^ 5 +
  Polynomial.C (5 * W.a₁ ^ 4 * W.a₃ + W.a₁ ^ 3 * W.a₄ + 3 * W.a₁ ^ 2 * W.a₂ * W.a₃ +
      7 * W.a₁ * W.a₃ ^ 2 + W.a₁ * W.a₆ + W.a₃ * W.a₄) *
    Polynomial.X ^ 4 +
  Polynomial.C (10 * W.a₁ ^ 3 * W.a₃ ^ 2 + 2 * W.a₁ ^ 3 * W.a₆ +
      4 * W.a₁ ^ 2 * W.a₃ * W.a₄ + 4 * W.a₁ * W.a₂ * W.a₃ ^ 2 +
      4 * W.a₁ * W.a₂ * W.a₆ - W.a₁ * W.a₄ ^ 2 + 2 * W.a₃ ^ 3) *
    Polynomial.X ^ 3 +
  Polynomial.C (-W.a₁ ^ 4 * W.a₃ * W.a₄ + 2 * W.a₁ ^ 3 * W.a₂ * W.a₆ -
      W.a₁ ^ 3 * W.a₄ ^ 2 - W.a₁ ^ 2 * W.a₂ * W.a₃ * W.a₄ +
      9 * W.a₁ ^ 2 * W.a₃ ^ 3 + 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ +
      2 * W.a₁ * W.a₂ ^ 2 * W.a₆ - W.a₁ * W.a₂ * W.a₄ ^ 2 +
      5 * W.a₁ * W.a₃ ^ 2 * W.a₄ + W.a₂ * W.a₃ ^ 3 +
      2 * W.a₂ * W.a₃ * W.a₆ - W.a₃ * W.a₄ ^ 2) *
    Polynomial.X ^ 2 +
  Polynomial.C (W.a₁ ^ 4 * W.a₃ * W.a₆ - W.a₁ ^ 3 * W.a₃ ^ 2 * W.a₄ +
      W.a₁ ^ 3 * W.a₄ * W.a₆ + W.a₁ ^ 2 * W.a₂ * W.a₃ ^ 3 +
      4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * W.a₆ - 2 * W.a₁ ^ 2 * W.a₃ * W.a₄ ^ 2 +
      W.a₁ * W.a₂ * W.a₃ ^ 2 * W.a₄ + 4 * W.a₁ * W.a₂ * W.a₄ * W.a₆ +
      4 * W.a₁ * W.a₃ ^ 4 + 3 * W.a₁ * W.a₃ ^ 2 * W.a₆ -
      W.a₁ * W.a₄ ^ 3 + 2 * W.a₃ ^ 3 * W.a₄) *
    Polynomial.X +
  Polynomial.C (-W.a₁ ^ 2 * W.a₃ ^ 3 * W.a₄ + 2 * W.a₁ * W.a₂ * W.a₃ ^ 2 * W.a₆ +
      2 * W.a₁ * W.a₂ * W.a₆ ^ 2 - W.a₁ * W.a₃ ^ 2 * W.a₄ ^ 2 -
      W.a₁ * W.a₄ ^ 2 * W.a₆ + 2 * W.a₂ * W.a₃ * W.a₄ * W.a₆ -
      W.a₃ * W.a₄ ^ 3)

/-- **The coupled identity (q=2 char-2)**: `A·ψ₂ + B·cubic_x` is in
    `Polynomial.expand K 2`-range, witnessed by `omega2_coupled_witness_char_two`.

    Sympy-verified for arbitrary char-2 Weierstrass curves: substituting the
    b-relations `b₂ = a₁²`, `b₄ = a₁a₃`, `b₆ = a₃²` (char 2), the difference
    `(A·ψ₂ + B·cubic_x) − expand 2 (witness)` is a polynomial multiple of 2,
    hence vanishes in char 2.

    The Lean proof is sketched (sympy-verified with explicit M(X) such that
    diff = 2·M); the formal `ring`-closing step requires careful sequencing
    of `linear_combination` with M-as-coefficient. Shipped as a hypothesis
    here for downstream consumers; full proof TODO with structural M. -/
theorem omega2_coupled_residual_mem_expand_two_char_two_witness
    (W : WeierstrassCurve K) [CharP K 2]
    (h_witness : Polynomial.expand K 2 (omega2_coupled_witness_char_two W) =
      omega2_coupled_residual_char_two W) :
    omega2_coupled_residual_char_two W ∈ Set.range (⇑(Polynomial.expand K 2)) :=
  ⟨omega2_coupled_witness_char_two W, h_witness⟩

/-! ### Route 1: derivative-vanishes proof of expand-range membership

In char 2, `f ∈ Set.range (Polynomial.expand K 2)` iff `f.derivative = 0`
(Frobenius criterion via `Polynomial.expand_contract`). For the coupled
residual `A·ψ₂ + B·cubic_x`, every nonzero coefficient is at an even
degree (sympy-verified, char-2-reduced), so its derivative vanishes. -/

set_option maxHeartbeats 1000000 in
/-- **Derivative of `omega2_coupled_residual_char_two` vanishes in char 2**.
    Direct: the polynomial has only even-degree nonzero coefficients in
    char 2, so its derivative is zero. -/
theorem omega2_coupled_residual_derivative_eq_zero
    (W : WeierstrassCurve K) [CharP K 2] :
    Polynomial.derivative (omega2_coupled_residual_char_two W) = 0 := by
  have h_b2 : W.b₂ = W.a₁ ^ 2 := WeierstrassCurve.b₂_of_char_two W
  have h_b4 : W.b₄ = W.a₁ * W.a₃ := WeierstrassCurve.b₄_of_char_two W
  have h_b6 : W.b₆ = W.a₃ ^ 2 := WeierstrassCurve.b₆_of_char_two W
  rw [omega2_coupled_residual_char_two, omega2_X_coeff_char_two,
      omega2_Y_coeff_char_two, cubic_x, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.b₈, h_b2, h_b4, h_b6]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_pow, Polynomial.derivative_C,
        Polynomial.derivative_X, Polynomial.derivative_ofNat,
        zero_mul, mul_zero, mul_one, zero_add, add_zero, Nat.cast_ofNat]
  reduce_mod_char!
  -- Fully expand C(compound) into products of atomic C(a_i), so ring_nf
  -- can combine all power-products into atomic C(a_i)^k * X^j form.
  simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add,
    Polynomial.C_0, Polynomial.C_1]
  ring_nf
  reduce_mod_char!

/-- **The coupled identity, unconditional (q=2 char-2)**: `A·ψ₂ + B·cubic_x ∈ expand-range`.
    Direct from the derivative-vanishes proof via `Polynomial.expand_contract`. -/
theorem omega2_coupled_residual_mem_expand_two_char_two
    (W : WeierstrassCurve K) [CharP K 2] :
    omega2_coupled_residual_char_two W ∈ Set.range (⇑(Polynomial.expand K 2)) := by
  exact ⟨Polynomial.contract 2 (omega2_coupled_residual_char_two W),
    Polynomial.expand_contract 2 (omega2_coupled_residual_derivative_eq_zero W) (by norm_num)⟩

/-! ### y-coordinate q-th-root (witness-parametric, q=2 char-2)

Construction of `α = α₀ + α₁·y_gen ∈ K(E)` whose square equals
`mulByInt_y W 2`, parametric on the two polynomial-side expand-range
witnesses (B and the coupled-residual). The q-th-root extractors give
explicit polynomial roots `polyExpandRoot B h_B` and `polyExpandRoot (A·ψ₂ + B·cubic_x) h_AB`,
which divided by `ψ₂(x_gen)²` give α₁ and α₀ respectively. -/

/-- **y-coordinate q-th-root coefficient α₁** (witness-parametric, q=2 char-2):
    `α₁ = aeval x_gen (polyExpandRoot B h_B) / ψ₂(x_gen)²`. Note: in this
    formulation, `Fintype.card K = 2` is required for the polyExpandRoot
    extractor to operate on `expand K (Fintype.card K) = expand K 2`. -/
noncomputable def alpha_1_y_qth_root_char_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_card : Fintype.card K = 2)
    (h_B : omega2_Y_coeff_char_two W ∈ Set.range (⇑(Polynomial.expand K 2))) :
    W.toAffine.FunctionField :=
  let h_B' : omega2_Y_coeff_char_two W ∈
      Set.range (⇑(Polynomial.expand K (Fintype.card K))) := h_card ▸ h_B
  Polynomial.aeval (x_gen W) (polyExpandRoot (omega2_Y_coeff_char_two W) h_B') /
    Polynomial.aeval (x_gen W)
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 2

/-- **y-coordinate q-th-root coefficient α₀** (witness-parametric, q=2 char-2):
    `α₀ = aeval x_gen (polyExpandRoot (A·ψ₂ + B·cubic_x) h_AB) / ψ₂(x_gen)²`. -/
noncomputable def alpha_0_y_qth_root_char_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_card : Fintype.card K = 2)
    (h_AB : omega2_coupled_residual_char_two W ∈ Set.range (⇑(Polynomial.expand K 2))) :
    W.toAffine.FunctionField :=
  let h_AB' : omega2_coupled_residual_char_two W ∈
      Set.range (⇑(Polynomial.expand K (Fintype.card K))) := h_card ▸ h_AB
  Polynomial.aeval (x_gen W)
      (polyExpandRoot (omega2_coupled_residual_char_two W) h_AB') /
    Polynomial.aeval (x_gen W)
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 2

/-- **y-coordinate q-th-root** (witness-parametric, q=2 char-2):
    `α = α₀ + α₁·y_gen ∈ K(E)`, parametric on the two expand-range witnesses. -/
noncomputable def y_qth_root_q_eq_2_char_2_of_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_card : Fintype.card K = 2)
    (h_B : omega2_Y_coeff_char_two W ∈ Set.range (⇑(Polynomial.expand K 2)))
    (h_AB : omega2_coupled_residual_char_two W ∈ Set.range (⇑(Polynomial.expand K 2))) :
    W.toAffine.FunctionField :=
  alpha_0_y_qth_root_char_two W h_card h_AB +
    alpha_1_y_qth_root_char_two W h_card h_B * y_gen W

/-- **y-coordinate q-th-root, unconditional (q=2 char-2)**: combines the two
    now-unconditional expand-range memberships (`omega2_Y_coeff_mem_expand_two_char_two`
    and `omega2_coupled_residual_mem_expand_two_char_two`) to produce the
    explicit α = α₀ + α₁·y_gen ∈ K(E). -/
noncomputable def y_qth_root_q_eq_2_char_2
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2) :
    W.toAffine.FunctionField :=
  y_qth_root_q_eq_2_char_2_of_witnesses W h_card
    (omega2_Y_coeff_mem_expand_two_char_two W)
    (omega2_coupled_residual_mem_expand_two_char_two W)

/-! ### Inverse-closure for `(frobeniusIsog W).pullback.range`

The Frobenius pullback range is the q-th-power subfield `K(E)^q ⊆ K(E)`,
hence closed under inverses (and indeed a subfield). This lifts the
Subalgebra structure to a subfield-in-spirit, supplying the structural
fact needed by the generator-reduction step. -/

/-- The Frobenius pullback range is closed under inverses: every q-th
    power has its inverse a q-th power. Direct: `(g⁻¹)^q = (g^q)⁻¹`. -/
theorem frobeniusIsog_pullback_range_inv_mem (f : W.toAffine.FunctionField)
    (hf : f ∈ (frobeniusIsog W).pullback.range) :
    f⁻¹ ∈ (frobeniusIsog W).pullback.range := by
  rw [mem_frobenius_range_iff] at hf ⊢
  obtain ⟨g, hg⟩ := hf
  refine ⟨g⁻¹, ?_⟩
  rw [inv_pow, hg]

/-! ### Generator reduction (witness-parametric)

The structural step from generator-level q-th-root facts to a universal
q-th-root function. We ship it witness-parametric on the load-bearing
fact that K(E) is generated as a K-extension by `{x_gen, y_gen}` (in
fieldRange/IntermediateField form). The two generator-level q-th-roots
are then transported via the closure properties of the Frobenius range. -/

/-- **Generator reduction witness form**: given that `[q]*x_gen` and
    `[q]*y_gen` are in `(frobeniusIsog W).pullback.range`, AND a
    structural witness that the `[q]*`-pullback range is contained in
    the K-subfield generated by these two images, conclude every
    `[q]*z` lies in the Frobenius range. -/
theorem mulByInt_q_pullback_range_subset_frobenius_of_xy_subfield_witness
    (h_x : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) ∈
        (frobeniusIsog W).pullback.range)
    (h_y : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) ∈
        (frobeniusIsog W).pullback.range)
    (h_subfield : ∀ z : W.toAffine.FunctionField,
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈
        (frobeniusIsog W).pullback.range ∨
      (∃ a b c : W.toAffine.FunctionField,
        a ∈ (frobeniusIsog W).pullback.range ∧
        b ∈ (frobeniusIsog W).pullback.range ∧
        c ∈ (frobeniusIsog W).pullback.range ∧
        c ≠ 0 ∧
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z = (a + b) / c)) :
    ∀ z : W.toAffine.FunctionField,
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈
        (frobeniusIsog W).pullback.range := by
  intro z
  rcases h_subfield z with h | ⟨a, b, c, ha, hb, hc, hc_ne, heq⟩
  · exact h
  · rw [heq]
    have hsum : a + b ∈ (frobeniusIsog W).pullback.range :=
      Subalgebra.add_mem _ ha hb
    have hinv : c⁻¹ ∈ (frobeniusIsog W).pullback.range :=
      frobeniusIsog_pullback_range_inv_mem W c hc
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ hsum hinv

/-! ### Wire-up: `(mulByInt W q).pullback (y_gen W) ∈ frobenius range`

Specializes the existing `mulByInt_q_pullback_y_gen_qth_root_of_witness`
with the unconditional polynomial-side data. The remaining content is
the squaring identity `(α₀ + α₁·y_gen)² = mulByInt_y W 2`, which is
parametric here. -/

/-- **y-gen pullback in Frobenius range** (q=2 char-2, witness on
    squaring identity): given the squaring identity for the explicit
    α = α₀ + α₁·y_gen, the y_gen pullback of [2]* lies in Frobenius range. -/
theorem mulByInt_q_pullback_y_gen_mem_range_of_sqrid_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2)
    (h_sqrid : (y_qth_root_q_eq_2_char_2 W h_card) ^ Fintype.card K =
      mulByInt_y W ((Fintype.card K : ℕ) : ℤ))
    (hn : ((Fintype.card K : ℕ) : ℤ) ≠ 0) :
    ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) :=
  mulByInt_q_pullback_y_gen_qth_root_of_witness W
    ⟨y_qth_root_q_eq_2_char_2 W h_card, h_sqrid⟩ hn

/-! ### IntermediateField generator-reduction witness form

The fact that `K(E)` is generated as an IntermediateField over `K` by
`{x_gen, y_gen}`. Since `K(E) = FractionRing(CoordinateRing)` and
`CoordinateRing = K[x_gen, y_gen]/(W.polynomial)`, the structural
identity holds. Shipped here as a hypothesis-form theorem; the
unconditional version requires mathlib's `IsFractionRing` instance for
`Algebra.adjoin K S → IntermediateField.adjoin K S` plus an explicit
proof that `Algebra.adjoin K {x_gen, y_gen}` contains the image of
`CoordinateRing` in `FunctionField`. -/

/-- **IntermediateField generator-reduction witness**: given that
    `K(E) = adjoin K {x_gen, y_gen}` as IntermediateField, the
    `(mulByInt q).pullback.fieldRange` is contained in `(frobeniusIsog).pullback.fieldRange`
    iff `[q]*x_gen ∈ frobenius.fieldRange` and `[q]*y_gen ∈ frobenius.fieldRange`.
    Witness-parametric on the IntermediateField equality. -/
theorem mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_top : (⊤ : IntermediateField K W.toAffine.FunctionField) =
      IntermediateField.adjoin K {x_gen W, y_gen W})
    (h_x : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) ∈
        (frobeniusIsog W).pullback.fieldRange)
    (h_y : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) ∈
        (frobeniusIsog W).pullback.fieldRange) :
    ∀ z : W.toAffine.FunctionField,
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈
        (frobeniusIsog W).pullback.fieldRange := by
  intro z
  -- Every z ∈ K(E) = adjoin K {x_gen, y_gen}, and the pullback is a K-alg hom.
  -- So [q]*z ∈ adjoin K {[q]*x_gen, [q]*y_gen}, both in the target subfield.
  have h_z_mem : z ∈ IntermediateField.adjoin K {x_gen W, y_gen W} := by
    rw [← h_top]; trivial
  -- The pullback is a K-alg hom; image of adjoin K S = adjoin K (image S).
  -- Use AlgHom.fieldRange characterization.
  have h_subfield : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈
      IntermediateField.adjoin K
        {(mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W),
         (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W)} := by
    have h_map : ((mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) ∈
        ((IntermediateField.adjoin K {x_gen W, y_gen W}).map
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback) :=
      ⟨z, h_z_mem, rfl⟩
    rw [IntermediateField.adjoin_map] at h_map
    convert h_map using 2
    simp [Set.image_pair]
  -- Apply IntermediateField.adjoin_le_iff to bound by frobenius range.
  refine IntermediateField.adjoin_le_iff.mpr ?_ h_subfield
  intro f hf
  rcases hf with rfl | rfl
  · exact h_x
  · exact h_y

/-! ### IntermediateField top equality: K(E) = adjoin K {x_gen, y_gen}

Direct mathematical argument: K(E) = FractionRing(CoordinateRing), where
CoordinateRing is generated as a K-algebra by image-of-X = x_gen and
image-of-Y = y_gen. The image of CoordinateRing in K(E) is contained in
`IntermediateField.adjoin K {x_gen, y_gen}` (since both generators are
in it and the IntermediateField is closed under K-algebra ops). Then
since K(E) = FractionRing(CoordinateRing) and IntermediateField is closed
under inverses, the IntermediateField contains all of K(E). -/

/-- **K(E) is generated as IntermediateField over K by x_gen and y_gen,
    witness-parametric form**: given the structural fact that every element of
    `CoordinateRing` maps into the K-subalgebra generated by x_gen and y_gen
    (which holds because CoordinateRing = AdjoinRoot W.polynomial = K[X,Y]/(W)
    is K-algebra-generated by image of X = x_gen and AdjoinRoot.root = y_gen),
    derive that K(E) equals the IntermediateField adjoin via FractionRing
    structure. -/
theorem functionField_eq_intermediateField_adjoin_xy_of_witness
    (W : WeierstrassCurve K)
    (h_alg_top : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈
        Algebra.adjoin K ({x_gen W, y_gen W} : Set _)) :
    (⊤ : IntermediateField K W.toAffine.FunctionField) =
      IntermediateField.adjoin K ({x_gen W, y_gen W} : Set _) := by
  refine le_antisymm ?_ le_top
  intro f _
  obtain ⟨⟨num, den, hden_mem⟩, rfl⟩ := IsLocalization.mk'_surjective
    (M := nonZeroDivisors W.toAffine.CoordinateRing)
    (S := W.toAffine.FunctionField) f
  have h_R_in_adjoin : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈
        IntermediateField.adjoin K ({x_gen W, y_gen W} : Set _) :=
    fun r ↦ IntermediateField.algebra_adjoin_le_adjoin K _ (h_alg_top r)
  have h_num := h_R_in_adjoin num
  have h_den := h_R_in_adjoin den
  show IsLocalization.mk' W.toAffine.FunctionField num ⟨den, hden_mem⟩ ∈ _
  rw [IsFractionRing.mk'_eq_div]
  exact div_mem h_num h_den

/-! ### Unconditional `h_alg_top` discharge

The witness `h_alg_top` to `functionField_eq_intermediateField_adjoin_xy_of_witness`
is a structural fact about `CoordinateRing = AdjoinRoot W.polynomial`: every
element of the coordinate ring is, in `K(E)`, a K-polynomial expression in
the generic point `(x_gen, y_gen)`. The proof is a direct double induction
through `AdjoinRoot.induction_on` (presenting any `r : R` as `mk f p` for
some `p : K[X][Y]`) and `Polynomial.induction_on'` (decomposing `p` into
monomials), with the monomial step handled by `mk_C` / `mk_X` plus
algebra-tower navigation.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.1 (the
function field as the fraction field of the affine coordinate ring of a
plane curve, with x and y as transcendence-base / generators). -/

/-- **Coordinate-ring image lies in `Algebra.adjoin K {x_gen, y_gen}`** —
the unconditional form of the witness `h_alg_top` that
`functionField_eq_intermediateField_adjoin_xy_of_witness` would otherwise
take as a hypothesis. -/
theorem coordinateRing_algebraMap_mem_adjoin_xy
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (r : W.toAffine.CoordinateRing) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈
      Algebra.adjoin K ({x_gen W, y_gen W} : Set _) := by
  induction r using AdjoinRoot.induction_on with | _ p => ?_
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [show AdjoinRoot.mk W.toAffine.polynomial (p + q) =
            AdjoinRoot.mk W.toAffine.polynomial p +
            AdjoinRoot.mk W.toAffine.polynomial q from map_add _ _ _,
        map_add]
    exact add_mem hp hq
  | monomial n a =>
    -- `monomial n a = C a * X^n` in `(K[X])[Y]`; under `mk W.polynomial`,
    -- `C a` becomes `of W.polynomial a` (= ↑a via the K[X]-algebra structure
    -- on R) and `X` becomes `root W.polynomial`. After algebraMap to K(E),
    -- the image is `(algebraMap K[X] KE) a · (y_gen W)^n`. The first factor
    -- lies in `Algebra.adjoin K {x_gen W}` (image of `aeval (x_gen W)`); the
    -- second is `y_gen W`-power, already in the adjoin's generator set.
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_mul, map_pow]
    -- Goal: (algebraMap R KE) ((algebraMap K[X] R) a) *
    --       ((algebraMap R KE) (AdjoinRoot.root W.poly))^n ∈
    --       Algebra.adjoin K {x_gen W, y_gen W}
    refine mul_mem ?_ (pow_mem ?_ _)
    · -- First factor: `algebraMap R KE ((algebraMap K[X] R) a) ∈ adjoin K {x_gen, y_gen}`.
      -- By IsScalarTower, this equals `algebraMap K[X] KE a`. Strategy: use a from
      -- structural induction on `a : K[X]` itself; the K-coefficients land in K ⊆ adjoin
      -- and the powers of X land on x_gen W ∈ adjoin generators.
      induction a using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [map_add, map_add]
        exact add_mem hp hq
      | monomial m k =>
        -- `algebraMap K[X] R (C k * X^m) = (algebraMap K R) k * (algebraMap K[X] R X)^m`
        -- → `algebraMap R KE (...) = algebraMap K KE k * (x_gen W)^m`. K-multiple of
        -- a power of x_gen, in `Algebra.adjoin K {x_gen, y_gen}`.
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
            map_mul, map_pow]
        refine mul_mem ?_ (pow_mem ?_ _)
        · -- algebraMap R KE (algebraMap K[X] R (C k)) is the image of K, in subalgebra.
          show (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
              ((algebraMap K[X] W.toAffine.CoordinateRing) (Polynomial.C k)) ∈ _
          have h_const : (algebraMap K[X] W.toAffine.CoordinateRing) (Polynomial.C k) =
              algebraMap K W.toAffine.CoordinateRing k :=
            (IsScalarTower.algebraMap_apply K K[X] W.toAffine.CoordinateRing k).symm
          rw [h_const, ← IsScalarTower.algebraMap_apply K
            W.toAffine.CoordinateRing W.toAffine.FunctionField k]
          exact Subalgebra.algebraMap_mem _ k
        · -- algebraMap R KE (algebraMap K[X] R X) = x_gen W
          show (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
              ((algebraMap K[X] W.toAffine.CoordinateRing) Polynomial.X) ∈ _
          exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · -- Second factor: `algebraMap R KE (AdjoinRoot.root W.poly) = y_gen W`,
      -- a generator of the adjoin.
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

/-- **K(E) = adjoin K {x_gen, y_gen}** (unconditional). Composes the
witness-parametric form with `coordinateRing_algebraMap_mem_adjoin_xy`. -/
theorem functionField_eq_intermediateField_adjoin_xy
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] :
    (⊤ : IntermediateField K W.toAffine.FunctionField) =
      IntermediateField.adjoin K ({x_gen W, y_gen W} : Set _) :=
  functionField_eq_intermediateField_adjoin_xy_of_witness W
    (coordinateRing_algebraMap_mem_adjoin_xy W)

/-! ### Squaring identity opener (q=2 char-2)

Three stepping-stone lemmas toward the squaring identity
`(α₀ + α₁·y_gen)² = mulByInt_y W 2` in char 2:

1. `char_two_sq_basis_form` — `(a + b·y)² = a² + b²·y²` in char 2 (cross
   term vanishes).
2. `y_gen_sq_weierstrass_char_two` — Weierstrass equation specialized
   to char 2: `y_gen² = a₁·x_gen·y_gen + a₃·y_gen + cubic_x(x_gen)`.
3. `alpha_squared_basis_form` — combined: `(α₀ + α₁·y_gen)² =
   (α₀² + α₁²·cubic_x) + α₁²·ψ₂·y_gen` in char 2.

Tomorrow's session combines these with Session 14's coupled identity
to identify the result with `mulByInt_y W 2`. -/

/-- **Char-2 freshman's dream for `a + b·y`**: `(a + b·y)² = a² + b²·y²`
    in char 2. The cross term `2·a·b·y` vanishes. -/
theorem char_two_sq_basis_form (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    [CharP K 2] (a b : W.toAffine.FunctionField) :
    (a + b * y_gen W) ^ 2 = a ^ 2 + b ^ 2 * y_gen W ^ 2 := by
  have h_2 : (2 : W.toAffine.FunctionField) = 0 := natCast_functionField_eq_zero W 2
  ring_nf
  linear_combination (a * b * y_gen W) * h_2

/-- **Weierstrass equation at the generic point in char 2**: `y_gen² =
    a₁·x_gen·y_gen + a₃·y_gen + cubic_x(x_gen)`. Direct from
    `generic_equation` (the Weierstrass equation at the generic point)
    plus char-2 sign collapse. -/
theorem y_gen_sq_weierstrass_char_two (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 2] :
    (y_gen W) ^ 2 =
      algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W * y_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃ * y_gen W +
      (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) := by
  -- generic_equation: (W_KE W).toAffine.Equation (x_gen W) (y_gen W)
  -- This unfolds to the polynomial equation y² + a₁xy + a₃y - (x³ + a₂x² + a₄x + a₆) = 0
  have h_eq := generic_equation W
  rw [Affine.equation_iff'] at h_eq
  -- h_eq : y_gen² + a₁ * x_gen * y_gen + a₃ * y_gen - (x_gen³ + a₂*x_gen² + a₄*x_gen + a₆) = 0
  -- (with algebraMap K K(E) for the a_i values, since we're in W_KE = W.map (algebraMap K K(E)))
  -- In char 2, - = +, so y² = a₁xy + a₃y + (x³ + a₂x² + a₄x + a₆).
  have h_2 : (2 : W.toAffine.FunctionField) = 0 := natCast_functionField_eq_zero W 2
  -- W_KE's coefficients are algebraMap K K(E) of W's coefficients.
  show _ = _
  have h_a1 : (W_KE W).a₁ = algebraMap K W.toAffine.FunctionField W.a₁ := rfl
  have h_a2 : (W_KE W).a₂ = algebraMap K W.toAffine.FunctionField W.a₂ := rfl
  have h_a3 : (W_KE W).a₃ = algebraMap K W.toAffine.FunctionField W.a₃ := rfl
  have h_a4 : (W_KE W).a₄ = algebraMap K W.toAffine.FunctionField W.a₄ := rfl
  have h_a6 : (W_KE W).a₆ = algebraMap K W.toAffine.FunctionField W.a₆ := rfl
  rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h_eq
  linear_combination h_eq -
    (y_gen W * algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      y_gen W * algebraMap K W.toAffine.FunctionField W.a₃) * h_2

/-- **α-squared basis form** (q=2 char-2): combined char-2 squaring
    + Weierstrass substitution. -/
theorem alpha_squared_basis_form (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 2] (a b : W.toAffine.FunctionField) :
    (a + b * y_gen W) ^ 2 =
      a ^ 2 + b ^ 2 * (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W * y_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃ * y_gen W +
        (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) := by
  rw [char_two_sq_basis_form, y_gen_sq_weierstrass_char_two]

/-! ### α₁ and α₀ component identities

`α₁² = aeval x_gen B / (aeval x_gen ψ₂_poly)^4` and
`α₀² = aeval x_gen (A·ψ₂ + B·cubic_x) / (aeval x_gen ψ₂_poly)^4`,
both via `polyExpandRoot_aeval_pow_eq` applied at q = 2. -/

/-- **α₁ squared identity (q=2 char-2)**: simpler statement using
    `Fintype.card K`, sidestepping the dependent rewriting of `h_card`. -/
theorem alpha_1_y_qth_root_pow_card_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2)
    (h_B' : omega2_Y_coeff_char_two W ∈
      Set.range (⇑(Polynomial.expand K (Fintype.card K)))) :
    (Polynomial.aeval (x_gen W) (polyExpandRoot _ h_B')) ^ Fintype.card K =
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W) :=
  polyExpandRoot_aeval_pow_eq W _ h_B' (polyPowCardEq_of_finite (K := K)) (x_gen W)

/-- **α₀ squared identity (q=2 char-2)**: simpler statement using
    `Fintype.card K`. -/
theorem alpha_0_y_qth_root_pow_card_eq
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2)
    (h_AB' : omega2_coupled_residual_char_two W ∈
      Set.range (⇑(Polynomial.expand K (Fintype.card K)))) :
    (Polynomial.aeval (x_gen W) (polyExpandRoot _ h_AB')) ^ Fintype.card K =
      Polynomial.aeval (x_gen W) (omega2_coupled_residual_char_two W) :=
  polyExpandRoot_aeval_pow_eq W _ h_AB' (polyPowCardEq_of_finite (K := K)) (x_gen W)

/-! ### ω₂ basis decomposition in K[X][Y] (q=2 char-2)

Sympy-verified (`scripts/verify_omega2_basis.py`): in char 2, mathlib's
`W.ω 2` equals `C(A) + C(B)·Y` as a bivariate polynomial in `K[X][Y]`,
where `Y` here is the outer `Polynomial.X` and A, B are the K[X]
polynomials defined in Sessions 8, 9.

The proof uses `redInvarDenom_two = 1`, `complEDSAux₂_two = 0` (mathlib),
char-2 reductions of the integer multipliers via `reduce_mod_char!`,
and `ring` for the final polynomial identity.

Shipped here as a witness-parametric named hypothesis (`OmegaTwoBasisHolds W`)
to enable the downstream squaring identity composition. The unconditional
proof of `OmegaTwoBasisHolds W` is a substantive bivariate identity in
`K[X][Y]` (~50 LOC follow-up). -/

/-- **The basis decomposition hypothesis (q=2 char-2)**: in K[X][Y],
    `W.ω 2 = C(A) + C(B) · Polynomial.X` where Polynomial.X is the
    Y-variable. Sympy-verified (`scripts/verify_omega2_basis.py`). -/
def OmegaTwoBasisHolds (W : WeierstrassCurve K) : Prop :=
  W.ω 2 = Polynomial.C (omega2_X_coeff_char_two W) +
    Polynomial.C (omega2_Y_coeff_char_two W) * Polynomial.X

set_option maxHeartbeats 1000000 in
/-- **Unconditional basis decomposition of ω₂ in char 2**: the bivariate
    polynomial `W.ω 2` in `K[X][Y]` decomposes as `C(A) + C(B)·Y` after
    char-2 reductions (mathlib's `redInvarDenom_two`, `complEDSAux₂_two`,
    plus `reduce_mod_char!` for the integer-multiplier cancellations). -/
theorem omegaTwoBasisHolds_char_two
    (W : WeierstrassCurve K) [CharP K 2] :
    OmegaTwoBasisHolds W := by
  have h_b2 : W.b₂ = W.a₁ ^ 2 := WeierstrassCurve.b₂_of_char_two W
  have h_b4 : W.b₄ = W.a₁ * W.a₃ := WeierstrassCurve.b₄_of_char_two W
  have h_b6 : W.b₆ = W.a₃ ^ 2 := WeierstrassCurve.b₆_of_char_two W
  unfold OmegaTwoBasisHolds omega2_X_coeff_char_two omega2_Y_coeff_char_two
  rw [WeierstrassCurve.ω, redInvarDenom_two, complEDSAux₂_two,
      WeierstrassCurve.ψ_two, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₈,
      h_b2, h_b4, h_b6]
  unfold WeierstrassCurve.ψ₂ WeierstrassCurve.Affine.negPolynomial
    WeierstrassCurve.Affine.polynomial WeierstrassCurve.Affine.polynomialX
    WeierstrassCurve.Affine.polynomialY
  reduce_mod_char!
  simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add,
    Polynomial.C_0, Polynomial.C_1]
  ring_nf

/-! ### ω_ff at the generic point: K(E)-level basis decomposition

Bridge from `omegaTwoBasisHolds_char_two` (bivariate identity in K[X][Y])
to the K(E)-level statement `ω_ff W 2 = aeval x_gen A + aeval x_gen B · y_gen`.
Apply `algebraMap CR KE ∘ mk W` to both sides of the bivariate identity. -/

/-- **K(E)-level basis decomposition (q=2 char-2)**: at the generic point,
    `ω_ff W 2 = aeval x_gen A + aeval x_gen B · y_gen` in `K(E)` (char 2),
    derived from the bivariate identity `omegaTwoBasisHolds_char_two`. -/
theorem omega_ff_two_basis_decomp_char_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2] :
    ω_ff W 2 =
      Polynomial.aeval (x_gen W) (omega2_X_coeff_char_two W) +
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W) * y_gen W := by
  -- ω_ff W 2 = algebraMap CR KE (mk W (W.ω 2)).
  -- By omegaTwoBasisHolds, W.ω 2 = C(A) + C(B) · X (Y-variable).
  unfold ω_ff
  rw [omegaTwoBasisHolds_char_two W]
  -- mk W is a ring hom; algebraMap CR KE is also.
  -- Apply map_add, map_mul to push through.
  simp only [map_add, map_mul]
  -- Now both sides should match up to identifying the components.
  -- Component 1: algebraMap CR KE (mk W (C A)) = aeval x_gen A.
  -- Component 2: algebraMap CR KE (mk W (C B)) = aeval x_gen B.
  -- Component 3: algebraMap CR KE (mk W X) = y_gen W (X here is Y-variable).
  -- Helper: algebraMap (Polynomial K) KE p = aeval (x_gen W) p, via the
  -- pattern from MulByIntPullback.lean:401 (aeval_algebraMap_apply twice).
  have h_alg_eq_aeval : ∀ p : Polynomial K,
      algebraMap (Polynomial K) W.toAffine.FunctionField p =
      Polynomial.aeval (x_gen W) p := fun p ↦ by
    show algebraMap (Polynomial K) W.toAffine.FunctionField p =
      Polynomial.aeval (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) p
    rw [Polynomial.aeval_algebraMap_apply (A := W.toAffine.CoordinateRing)
          (B := W.toAffine.FunctionField),
        Polynomial.aeval_algebraMap_apply (A := Polynomial K)
          (B := W.toAffine.CoordinateRing),
        Polynomial.aeval_X_left_apply, ← IsScalarTower.algebraMap_apply]
  have h_C_A : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C (omega2_X_coeff_char_two W))) =
      Polynomial.aeval (x_gen W) (omega2_X_coeff_char_two W) := by
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing
        (omega2_X_coeff_char_two W)) = _
    rw [← IsScalarTower.algebraMap_apply]
    exact h_alg_eq_aeval _
  have h_C_B : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C (omega2_Y_coeff_char_two W))) =
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W) := by
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing
        (omega2_Y_coeff_char_two W)) = _
    rw [← IsScalarTower.algebraMap_apply]
    exact h_alg_eq_aeval _
  have h_X_y : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (Affine.CoordinateRing.mk W.toAffine Polynomial.X) = y_gen W := by
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.root W.toAffine.polynomial) = _
    rfl
  rw [h_C_A, h_C_B, h_X_y]

/-- **ψ_ff W 2 in char 2 equals aeval x_gen (a₁X + a₃)**.
    Direct from ψ_two + char-2 simplification of ψ₂ = polynomialY. -/
theorem psi_ff_two_eq_aeval_char_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2] :
    ψ_ff W 2 = Polynomial.aeval (x_gen W)
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) := by
  unfold ψ_ff
  rw [WeierstrassCurve.ψ_two]
  unfold WeierstrassCurve.ψ₂ WeierstrassCurve.Affine.polynomialY
  -- ψ₂ = C(C 2)·Y + C(C a₁ * X + C a₃). In char 2, C(C 2) = 0.
  -- mk W (0·Y + C(C a₁ * X + C a₃)) = algebraMap (Poly K) CR (C a₁ * X + C a₃)
  reduce_mod_char!
  -- Now ψ₂ should be C(C a₁ * X + C a₃) (constant in Y).
  simp only [Polynomial.C_0, zero_mul, zero_add]
  -- mk W (C p) = algebraMap (Poly K) CR p; then algebraMap CR KE = aeval x_gen p
  show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
    (algebraMap (Polynomial K) W.toAffine.CoordinateRing
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃)) = _
  rw [← IsScalarTower.algebraMap_apply]
  show algebraMap (Polynomial K) W.toAffine.FunctionField
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) =
    Polynomial.aeval (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃)
  rw [Polynomial.aeval_algebraMap_apply (A := W.toAffine.CoordinateRing)
        (B := W.toAffine.FunctionField),
      Polynomial.aeval_algebraMap_apply (A := Polynomial K)
        (B := W.toAffine.CoordinateRing),
      Polynomial.aeval_X_left_apply, ← IsScalarTower.algebraMap_apply]

/-! ### Final composition: squaring identity

Combines all the axiom-clean component pieces shipped across Sessions
7-19 to close the squaring identity:
`(α₀ + α₁·y_gen)² = mulByInt_y W 2` in K(E) with char 2. -/

/-- **Y-coefficient match (q=2 char-2, witness-parametric)**:
    `α₁² · ψ₂(x_gen) = aeval x_gen B / ψ₂(x_gen)^3` in K(E),
    parametric on the squaring identity for the polyExpandRoot
    extractor (which is `polyExpandRoot_aeval_pow_eq` at q = 2). -/
theorem alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2)
    (h_psi_ne : Polynomial.aeval (x_gen W)
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ≠ 0)
    (h_polyRoot_sq :
      (Polynomial.aeval (x_gen W)
        (polyExpandRoot (omega2_Y_coeff_char_two W)
          (h_card ▸ omega2_Y_coeff_mem_expand_two_char_two W : _))) ^ 2 =
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W)) :
    (alpha_1_y_qth_root_char_two W h_card
        (omega2_Y_coeff_mem_expand_two_char_two W)) ^ 2 *
      Polynomial.aeval (x_gen W)
        (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) =
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W) /
      Polynomial.aeval (x_gen W)
        (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 3 := by
  unfold alpha_1_y_qth_root_char_two
  rw [div_pow, h_polyRoot_sq]
  field_simp

/-- **Polynomial-level constant-coefficient identity (q=2 char-2)**:
    multiply both sides of the constant-coefficient match by ψ_gen^4 to
    eliminate field inverses. Keeps `aeval x_gen (omega2_coupled_residual_char_two W)`
    as an opaque term and uses its definitional unfolding + char-2
    cancellation of `2·B·cubic_x`. -/
theorem alpha_0_sq_polynomial_match_char_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2)
    (h_psi_ne : Polynomial.aeval (x_gen W)
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ≠ 0)
    (h_polyRoot_sq_alpha_0 :
      (Polynomial.aeval (x_gen W)
        (polyExpandRoot (omega2_coupled_residual_char_two W)
          (h_card ▸ omega2_coupled_residual_mem_expand_two_char_two W : _))) ^ 2 =
      Polynomial.aeval (x_gen W) (omega2_coupled_residual_char_two W))
    (h_polyRoot_sq_alpha_1 :
      (Polynomial.aeval (x_gen W)
        (polyExpandRoot (omega2_Y_coeff_char_two W)
          (h_card ▸ omega2_Y_coeff_mem_expand_two_char_two W : _))) ^ 2 =
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W)) :
    ((alpha_0_y_qth_root_char_two W h_card
        (omega2_coupled_residual_mem_expand_two_char_two W)) ^ 2 +
      (alpha_1_y_qth_root_char_two W h_card
        (omega2_Y_coeff_mem_expand_two_char_two W)) ^ 2 *
      Polynomial.aeval (x_gen W) (cubic_x W)) *
      Polynomial.aeval (x_gen W)
        (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 4 =
      Polynomial.aeval (x_gen W) (omega2_X_coeff_char_two W) *
      Polynomial.aeval (x_gen W)
        (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) := by
  unfold alpha_0_y_qth_root_char_two alpha_1_y_qth_root_char_two
  rw [div_pow, div_pow, h_polyRoot_sq_alpha_0, h_polyRoot_sq_alpha_1]
  -- Keep aeval x_gen (omega2_coupled_residual_char_two W) opaque; use the
  -- definitional unfolding aeval (A·ψ + B·cubic) = aeval A · aeval ψ + aeval B · aeval cubic
  -- as a single rewrite.
  have h_residual : Polynomial.aeval (x_gen W) (omega2_coupled_residual_char_two W) =
      Polynomial.aeval (x_gen W) (omega2_X_coeff_char_two W) *
        Polynomial.aeval (x_gen W)
          (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) +
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W) *
        Polynomial.aeval (x_gen W) (cubic_x W) := by
    unfold omega2_coupled_residual_char_two
    rw [map_add, map_mul, map_mul]
  rw [h_residual]
  have h_2 : (2 : W.toAffine.FunctionField) = 0 := natCast_functionField_eq_zero W 2
  field_simp
  linear_combination
    (Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W) *
      Polynomial.aeval (x_gen W) (cubic_x W)) * h_2

/-- **Squaring identity (q=2 char-2, witness-parametric)**: the explicit
    `α = α₀ + α₁·y_gen` squares to `mulByInt_y W 2`. -/
theorem y_qth_root_squared_eq_mulByInt_y_two_of_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2)
    (h_psi_ne : Polynomial.aeval (x_gen W)
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ≠ 0)
    (h_polyRoot_sq_alpha_0 :
      (Polynomial.aeval (x_gen W)
        (polyExpandRoot (omega2_coupled_residual_char_two W)
          (h_card ▸ omega2_coupled_residual_mem_expand_two_char_two W : _))) ^ 2 =
      Polynomial.aeval (x_gen W) (omega2_coupled_residual_char_two W))
    (h_polyRoot_sq_alpha_1 :
      (Polynomial.aeval (x_gen W)
        (polyExpandRoot (omega2_Y_coeff_char_two W)
          (h_card ▸ omega2_Y_coeff_mem_expand_two_char_two W : _))) ^ 2 =
      Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W)) :
    (y_qth_root_q_eq_2_char_2 W h_card) ^ 2 = mulByInt_y W 2 := by
  unfold y_qth_root_q_eq_2_char_2 y_qth_root_q_eq_2_char_2_of_witnesses
  rw [char_two_sq_basis_form, y_gen_sq_weierstrass_char_two]
  have h_Y := alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness W h_card h_psi_ne
    h_polyRoot_sq_alpha_1
  have h_const := alpha_0_sq_polynomial_match_char_two W h_card h_psi_ne
    h_polyRoot_sq_alpha_0 h_polyRoot_sq_alpha_1
  unfold mulByInt_y
  rw [omega_ff_two_basis_decomp_char_two, psi_ff_two_eq_aeval_char_two]
  -- Bind names.
  set ψ : W.toAffine.FunctionField := Polynomial.aeval (x_gen W)
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃)
  set A' : W.toAffine.FunctionField :=
    Polynomial.aeval (x_gen W) (omega2_X_coeff_char_two W)
  set B' : W.toAffine.FunctionField :=
    Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W)
  set C' : W.toAffine.FunctionField :=
    Polynomial.aeval (x_gen W) (cubic_x W)
  set α₀ := alpha_0_y_qth_root_char_two W h_card
    (omega2_coupled_residual_mem_expand_two_char_two W)
  set α₁ := alpha_1_y_qth_root_char_two W h_card
    (omega2_Y_coeff_mem_expand_two_char_two W)
  -- Bridge: ψ = a₁·x_gen + a₃ (after aeval distributes over the polynomial sum).
  have h_psi_form : ψ = algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃ := by
    show Polynomial.aeval (x_gen W) (Polynomial.C W.a₁ * Polynomial.X +
        Polynomial.C W.a₃) = _
    simp [Polynomial.aeval_C, Polynomial.aeval_X]
  -- Convert h_const to a clean polynomial form: (α₀² + α₁²·C')·ψ³ = A'.
  have h_const' : (α₀ ^ 2 + α₁ ^ 2 * C') * ψ ^ 3 = A' := by
    have h2 : (α₀ ^ 2 + α₁ ^ 2 * C') * ψ ^ 3 * ψ = A' * ψ := by
      linear_combination h_const
    exact mul_right_cancel₀ h_psi_ne h2
  -- Convert h_Y to the clean polynomial form: α₁²·ψ⁴ = B'.
  have h_Y' : α₁ ^ 2 * ψ ^ 4 = B' := by
    have h : α₁ ^ 2 * ψ * ψ ^ 3 = B' / ψ ^ 3 * ψ ^ 3 := by rw [h_Y]
    rw [div_mul_cancel₀ _ (pow_ne_zero 3 h_psi_ne)] at h
    linear_combination h
  -- Now refactor LHS of goal: a₁·x·y + a₃·y + cubic = ψ·y + cubic (using h_psi_form).
  rw [show algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W * y_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃ * y_gen W +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆) = ψ * y_gen W + C' from by
    rw [h_psi_form]
    show _ = (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) * y_gen W +
        Polynomial.aeval (x_gen W) (cubic_x W)
    unfold cubic_x
    simp [Polynomial.aeval_C, Polynomial.aeval_X, map_add, map_mul, map_pow]
    ring]
  -- Goal: α₀² + α₁²·(ψ·y_gen + C') = (A' + B'·y_gen) / ψ³
  rw [eq_div_iff (pow_ne_zero 3 h_psi_ne)]
  linear_combination h_const' + y_gen W * h_Y'

/-! ### y-side cubing identity scaffold (q=3 char-3)

The q=3 char=3 analog of Sessions 14-25's squaring identity work.
Stepping-stone lemmas toward the cubing identity
`(α₀ + α₁·y_gen)^3 = mulByInt_y W 3` in char 3:

1. `char_three_cube_basis_form` — `(a + b·y)^3 = a^3 + b^3·y^3` in
   char 3 (Frobenius/Freshman's dream — cross terms `3·a²·b·y` and
   `3·a·b²·y²` vanish via `(3 : K(E)) = 0`).

2. `y_gen_sq_weierstrass_char_three` — Weierstrass equation specialised
   to char 3: `y_gen² = -a₁·x_gen·y_gen - a₃·y_gen + cubic_x(x_gen)`.

3. `y_gen_cubed_weierstrass_char_three` — combined: `y_gen^3` expressed
   in `{1, y_gen}` basis via two Y² substitutions:
   `y_gen^3 = (ψ_2² + cubic_x)·y_gen + ψ_2·cubic_x` (the form is
   char-independent over the {1, y} basis after substitution).

These will be combined with the polynomial-side identities
(`Φ_three_mem_expand_three_char_three`,
`ΨSq_three_mem_expand_three_char_three`) to produce the full cubing
identity, structurally analogous to Sessions 14-25's squaring arc but
with cube root instead of square root. -/

/-- **Char-3 freshman's dream for `a + b·y`**: `(a + b·y)^3 = a^3 + b^3·y^3`
    in char 3. The cross terms `3·a²·b·y` and `3·a·b²·y²` vanish because
    `(3 : K(E)) = 0`. q=3 analog of `char_two_sq_basis_form`. -/
theorem char_three_cube_basis_form (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] (a b : W.toAffine.FunctionField) :
    (a + b * y_gen W) ^ 3 = a ^ 3 + b ^ 3 * y_gen W ^ 3 := by
  have h_3 : (3 : W.toAffine.FunctionField) = 0 := natCast_functionField_eq_zero W 3
  ring_nf
  linear_combination (a ^ 2 * b * y_gen W + a * b ^ 2 * y_gen W ^ 2) * h_3

/-- **Char-5 freshman's dream for `a + b·y`**: `(a + b·y)^5 = a^5 + b^5·y^5`
    in char 5. The four cross terms (coefficients C(5,k) ∈ {5, 10, 10, 5})
    all vanish via `(5 : K(E)) = 0`. q=5 analog of `char_three_cube_basis_form`. -/
theorem char_five_quintic_basis_form (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 5] (a b : W.toAffine.FunctionField) :
    (a + b * y_gen W) ^ 5 = a ^ 5 + b ^ 5 * y_gen W ^ 5 := by
  have h_5 : (5 : W.toAffine.FunctionField) = 0 := natCast_functionField_eq_zero W 5
  ring_nf
  linear_combination
    (a ^ 4 * b * y_gen W + 2 * a ^ 3 * b ^ 2 * y_gen W ^ 2 +
      2 * a ^ 2 * b ^ 3 * y_gen W ^ 3 + a * b ^ 4 * y_gen W ^ 4) * h_5


/-- **Weierstrass equation at the generic point in char 3**:
    `y_gen² = -a₁·x_gen·y_gen - a₃·y_gen + cubic_x(x_gen)`.
    Direct from `generic_equation` — no char-specific sign collapse since
    `-1 ≠ 1` in char 3 (unlike char 2). -/
theorem y_gen_sq_weierstrass_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] :
    (y_gen W) ^ 2 =
      -(algebraMap K W.toAffine.FunctionField W.a₁) * x_gen W * y_gen W -
      algebraMap K W.toAffine.FunctionField W.a₃ * y_gen W +
      (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) := by
  have h_eq := generic_equation W
  rw [Affine.equation_iff'] at h_eq
  have h_a1 : (W_KE W).a₁ = algebraMap K W.toAffine.FunctionField W.a₁ := rfl
  have h_a2 : (W_KE W).a₂ = algebraMap K W.toAffine.FunctionField W.a₂ := rfl
  have h_a3 : (W_KE W).a₃ = algebraMap K W.toAffine.FunctionField W.a₃ := rfl
  have h_a4 : (W_KE W).a₄ = algebraMap K W.toAffine.FunctionField W.a₄ := rfl
  have h_a6 : (W_KE W).a₆ = algebraMap K W.toAffine.FunctionField W.a₆ := rfl
  rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h_eq
  linear_combination h_eq

/-- **Weierstrass equation at the generic point in char 5**:
    `y_gen² = -a₁·x_gen·y_gen - a₃·y_gen + cubic_x(x_gen)`.
    Same form as char 3 (any char ≠ 2). -/
theorem y_gen_sq_weierstrass_char_five (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 5] :
    (y_gen W) ^ 2 =
      -(algebraMap K W.toAffine.FunctionField W.a₁) * x_gen W * y_gen W -
      algebraMap K W.toAffine.FunctionField W.a₃ * y_gen W +
      (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) := by
  have h_eq := generic_equation W
  rw [Affine.equation_iff'] at h_eq
  have h_a1 : (W_KE W).a₁ = algebraMap K W.toAffine.FunctionField W.a₁ := rfl
  have h_a2 : (W_KE W).a₂ = algebraMap K W.toAffine.FunctionField W.a₂ := rfl
  have h_a3 : (W_KE W).a₃ = algebraMap K W.toAffine.FunctionField W.a₃ := rfl
  have h_a4 : (W_KE W).a₄ = algebraMap K W.toAffine.FunctionField W.a₄ := rfl
  have h_a6 : (W_KE W).a₆ = algebraMap K W.toAffine.FunctionField W.a₆ := rfl
  rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h_eq
  linear_combination h_eq

/-- **Weierstrass-cubing of `y_gen` in char 5**: `y_gen^3` in `{1, y_gen}`
    basis. Same form as char 3:
    `y_gen^3 = (ψ_2² + cubic_x)·y_gen - ψ_2·cubic_x`. -/
theorem y_gen_cubed_weierstrass_char_five (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 5] :
    (y_gen W) ^ 3 =
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) * y_gen W -
      (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
      (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) := by
  have h := y_gen_sq_weierstrass_char_five W
  linear_combination
    (y_gen W -
      (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃)) * h

/-- **Weierstrass-cubing of `y_gen` in char 3**: `y_gen^3` expressed in
    `{1, y_gen}` basis after two applications of the Weierstrass relation
    `y² = -ψ_2·y + cubic_x`:
    `y_gen^3 = (ψ_2² + cubic_x)·y_gen - ψ_2·cubic_x`
    where `ψ_2 = a₁·x_gen + a₃` and `cubic_x = x³ + a₂·x² + a₄·x + a₆`.

    q=3 char=3 analog of `y_gen_sq_weierstrass_char_two`'s role for q=2. -/
theorem y_gen_cubed_weierstrass_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] :
    (y_gen W) ^ 3 =
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) * y_gen W -
      (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
      (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) := by
  have h := y_gen_sq_weierstrass_char_three W
  -- h : y² = -a₁·x·y - a₃·y + cubic_x = -ψ_2·y + cubic_x
  -- want: y³ = (ψ_2² + cubic_x)·y - ψ_2·cubic_x
  -- linear_combination (y - ψ_2) · h closes via the chain:
  --   y · y² = y³ (substitute h once); then y² in result is substituted again via h.
  linear_combination
    (y_gen W -
      (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃)) * h

/-! ### ω_3 X/Y basis coefficients (q=3 char-3 scaffold)

q=3 char=3 analogs of `omega2_X_coeff_char_two` and
`omega2_Y_coeff_char_two`. Sympy-extracted in
`scripts/verify_omega_3_coefficients.py`: the Y⁰ coefficient (degree 13
in X) and Y¹ coefficient (degree 12 in X, starting with `2·X¹²`) of
`W.ω 3` in `K[X][Y]` after reducing modulo `Y² ≡ -a₁XY - a₃Y + cubic_x`
(char-3 Weierstrass) and mod 3.

The defs below extract the **raw** Y⁰ and Y¹ coefficients of the
bivariate polynomial `W.ω 3` in `K[X][Y]` (before Weierstrass reduction).
The sympy-verified **reduced** forms are larger, encompassing the
Y²-and-higher contributions; the eventual basis decomposition theorem
bridges raw → reduced via `mk W` (the Affine.CoordinateRing quotient).

These defs are axiom-clean by construction (just `Polynomial.coeff`).
The substantive content — the `OmegaThreeBasisHolds` theorem
(structural analog of `omegaTwoBasisHolds_char_two`) — is queued. -/

/-- **Raw Y⁰ coefficient of `W.ω 3`** in `K[X]`: the constant-in-Y term
    of the bivariate polynomial `W.ω 3 ∈ K[X][Y]`. After Weierstrass
    reduction, this combines with higher-Y-degree contributions to form
    the {1, Y} basis Y⁰ coefficient (sympy-extracted, deg 13 in X). -/
noncomputable def omega_3_X_coeff_char_three (W : WeierstrassCurve K) :
    Polynomial K :=
  Polynomial.coeff (W.ω 3) 0

/-- **Raw Y¹ coefficient of `W.ω 3`** in `K[X]`: the Y-degree-1 term
    of the bivariate polynomial `W.ω 3 ∈ K[X][Y]`. After Weierstrass
    reduction, this combines with higher-Y-degree contributions to form
    the {1, Y} basis Y¹ coefficient (sympy-extracted, deg 12 in X
    starting with `2·X¹²`). -/
noncomputable def omega_3_Y_coeff_char_three (W : WeierstrassCurve K) :
    Polynomial K :=
  Polynomial.coeff (W.ω 3) 1

/-! ### ω_3 reduced coefficients (Weierstrass-reduced via y_gen^k helpers)

The raw coefficients `omega_3_X_coeff_char_three := Polynomial.coeff (W.ω 3) 0`
and `omega_3_Y_coeff_char_three := Polynomial.coeff (W.ω 3) 1` extract the
Y⁰ and Y¹ components of the BIVARIATE polynomial `W.ω 3` in `K[X][Y]`.

For the K(E)-level basis decomposition `ω_ff W 3 = aeval x_gen A + aeval x_gen B · y_gen`,
we need the FULL Y⁰ and Y¹ contributions AFTER Weierstrass reduction
(absorbing Y², Y³, Y⁴, Y⁵ contributions via the y_gen^k helpers).

Defined as structured sums using `Polynomial.coeff (W.ω 3) k` for
k = 0..5 plus the appropriate ψ_2^j / cubic_x^l factors from
y_gen_sq/cube/quartic/quintic Weierstrass identities. -/

/-- **Reduced Y⁰ coefficient of ω_3 in char 3** (Weierstrass-reduced).
    Sums Y⁰ contributions from all Y-degrees 0..5 of W.ω 3 after
    substituting y_gen^k → {1, y_gen} basis form via the Weierstrass
    helpers. -/
noncomputable def omega_3_X_coeff_reduced_char_three
    (W : WeierstrassCurve K) : Polynomial K :=
  let ψ : Polynomial K := Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃
  let c : Polynomial K := cubic_x W
  Polynomial.coeff (W.ω 3) 0 +
  c * Polynomial.coeff (W.ω 3) 2 -
  ψ * c * Polynomial.coeff (W.ω 3) 3 +
  c * (ψ ^ 2 + c) * Polynomial.coeff (W.ω 3) 4 -
  ψ * c * (ψ ^ 2 + 2 * c) * Polynomial.coeff (W.ω 3) 5

/-- **Reduced Y¹ coefficient of ω_3 in char 3** (Weierstrass-reduced).
    Sums Y¹ contributions from all Y-degrees 0..5 of W.ω 3. -/
noncomputable def omega_3_Y_coeff_reduced_char_three
    (W : WeierstrassCurve K) : Polynomial K :=
  let ψ : Polynomial K := Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃
  let c : Polynomial K := cubic_x W
  Polynomial.coeff (W.ω 3) 1 -
  ψ * Polynomial.coeff (W.ω 3) 2 +
  (ψ ^ 2 + c) * Polynomial.coeff (W.ω 3) 3 -
  ψ * (ψ ^ 2 + 2 * c) * Polynomial.coeff (W.ω 3) 4 +
  (ψ ^ 4 + 3 * ψ ^ 2 * c + c ^ 2) * Polynomial.coeff (W.ω 3) 5

/-- **Reduced basis decomposition Prop (q=3 char-3)**: K(E)-level
    statement that `ω_ff W 3` equals `aeval x_gen A + aeval x_gen B · y_gen`
    for the Weierstrass-reduced A, B coefficients.

    Truth-bearing version of `OmegaThreeBasisHolds` (which used raw
    Polynomial.coeff and was structurally wrong). -/
def OmegaThreeBasisHoldsReduced (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] : Prop :=
  ω_ff W 3 =
    Polynomial.aeval (x_gen W) (omega_3_X_coeff_reduced_char_three W) +
    Polynomial.aeval (x_gen W) (omega_3_Y_coeff_reduced_char_three W) * y_gen W


/-- **The basis decomposition hypothesis (q=3 char-3)**: in
    `K(E)` (the function field, via the CoordinateRing quotient),
    `ω_ff W 3` decomposes as `aeval x_gen A + aeval x_gen B · y_gen`
    where A = omega_3_X_coeff and B = omega_3_Y_coeff are the Y⁰ and Y¹
    components of `W.ω 3` in the {1, y_gen} basis after Weierstrass
    reduction.

    Sympy-verified (`scripts/verify_omega_3_coefficients.py`): explicit
    forms extracted, but too large for direct Lean transcription. The
    `OmegaThreeBasisHolds W` proof (substantive bivariate identity in
    `K[X][Y]/Weierstrass`) is the q=3 analog of Session 18's
    `omegaTwoBasisHolds_char_two`. -/
def OmegaThreeBasisHolds (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] : Prop :=
  ω_ff W 3 =
    Polynomial.aeval (x_gen W) (omega_3_X_coeff_char_three W) +
    Polynomial.aeval (x_gen W) (omega_3_Y_coeff_char_three W) * y_gen W

/-- **The coupled-residual polynomial (q=3 char-3, raw form)**:
    `A_3 · (ψ_2² + cubic_x) + B_3 · ψ_2 · cubic_x`.

    **WARNING**: This raw form is NOT in `Polynomial.expand K 3`-range
    (sympy-verified `verify_omega3_coupled_residual.py`: nonzero
    coefficients at non-3-divisible exponents). The CORRECTED form
    suitable for the cubing identity is
    `omega3_coupled_residual_full_char_three`, which multiplies through
    by `(ψ_2² + cubic_x)²` to clear the cubic_x denominator.

    Kept here as the structural starting point matching the q=2 pattern;
    used as a building block for the corrected full form. -/
noncomputable def omega3_coupled_residual_char_three
    (W : WeierstrassCurve K) : Polynomial K :=
  omega_3_X_coeff_char_three W *
    ((Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 2 + cubic_x W) +
  omega_3_Y_coeff_char_three W *
    ((Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) * cubic_x W)

/-- **The corrected full coupled-residual polynomial (q=3 char-3)**:
    `(A_3 · (ψ_2² + cubic_x) + B_3 · ψ_2 · cubic_x) · (ψ_2² + cubic_x)²`.

    Sympy-verified (`scripts/verify_omega3_coupled_residual.py`) to lie
    in `Polynomial.expand K 3`-range in char 3, after applying the
    char-3 b-relation `b₈ = b₂·b₆ - b₄²`.

    The extra `(ψ_2² + cubic_x)²` factor reflects the cubing identity
    structure:
    `(α·ψ_3·(ψ_2² + cubic_x))³ = R_3 · (ψ_2² + cubic_x)²` -/
noncomputable def omega3_coupled_residual_full_char_three
    (W : WeierstrassCurve K) : Polynomial K :=
  omega3_coupled_residual_char_three W *
    ((Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 2 + cubic_x W) ^ 2

/-! ### Full witness polynomial — coefficient-by-coefficient defs

The witness polynomial g(X) for the q=3 char=3 coupled-residual
expand-3 membership has 8 X-degree terms with substantial K-coefficient
polynomials (sympy-extracted from
`scripts/verify_omega3_coupled_residual.py`). To avoid Lean elaborator
timeouts on the monolithic expression, each X-degree coefficient is
defined as a separate `noncomputable def` returning a K-element, then
combined into the polynomial via `Polynomial.C`.

This factors the elaboration burden across multiple definitions and
keeps each one small enough to elaborate quickly. -/

/-- **Witness coefficient at X⁷** (q=3 char-3): single monomial. -/
noncomputable def omega3_witness_coeff_X7 (W : WeierstrassCurve K) : K :=
  W.a₁ * W.a₂

/-- **Witness coefficient at X⁶** (q=3 char-3): 14-term polynomial. -/
noncomputable def omega3_witness_coeff_X6 (W : WeierstrassCurve K) : K :=
  W.a₁^7*W.a₂ + W.a₁^5*W.a₄ + W.a₁^4*W.a₂*W.a₃ +
  2*W.a₁^3*W.a₂*W.a₄ + W.a₁^3*W.a₆ +
  2*W.a₁^2*W.a₂^2*W.a₃ + 2*W.a₁^2*W.a₃*W.a₄ +
  W.a₁*W.a₂^4 + W.a₁*W.a₂^2*W.a₄ + W.a₁*W.a₂*W.a₃^2 +
  W.a₁*W.a₂*W.a₆ + 2*W.a₁*W.a₄^2 +
  W.a₂^3*W.a₃ + 2*W.a₃^3

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- **Witness coefficient at X⁰** (constant term, q=3 char-3): ~70-term
    polynomial. -/
noncomputable def omega3_witness_coeff_X0 (W : WeierstrassCurve K) : K :=
  W.a₁^5*W.a₃^6*W.a₄*W.a₆^3 + W.a₁^5*W.a₄*W.a₆^6 +
  2*W.a₁^4*W.a₂*W.a₃^9*W.a₆^2 + W.a₁^4*W.a₂*W.a₃^7*W.a₆^3 +
  2*W.a₁^4*W.a₂*W.a₃^3*W.a₆^5 + W.a₁^4*W.a₂*W.a₃*W.a₆^6 +
  2*W.a₁^3*W.a₂*W.a₃^10*W.a₄*W.a₆ + 2*W.a₁^3*W.a₂*W.a₃^6*W.a₄*W.a₆^3 +
  2*W.a₁^3*W.a₂*W.a₃^4*W.a₄*W.a₆^4 + 2*W.a₁^3*W.a₂*W.a₄*W.a₆^6 +
  W.a₁^3*W.a₃^12*W.a₆ + W.a₁^3*W.a₃^6*W.a₄^3*W.a₆^2 +
  2*W.a₁^3*W.a₃^6*W.a₆^4 + W.a₁^3*W.a₄^3*W.a₆^5 + W.a₁^3*W.a₆^7 +
  W.a₁^2*W.a₂^2*W.a₃^11*W.a₆ + 2*W.a₁^2*W.a₂^2*W.a₃^7*W.a₆^3 +
  W.a₁^2*W.a₂^2*W.a₃^5*W.a₆^4 + 2*W.a₁^2*W.a₂^2*W.a₃*W.a₆^6 +
  2*W.a₁^2*W.a₂*W.a₃^11*W.a₄^2 + 2*W.a₁^2*W.a₂*W.a₃^9*W.a₄^2*W.a₆ +
  2*W.a₁^2*W.a₂*W.a₃^5*W.a₄^2*W.a₆^3 +
  2*W.a₁^2*W.a₂*W.a₃^3*W.a₄^2*W.a₆^4 + 2*W.a₁^2*W.a₃^13*W.a₄ +
  2*W.a₁^2*W.a₃^9*W.a₄^4 + W.a₁^2*W.a₃^7*W.a₄^4*W.a₆ +
  W.a₁^2*W.a₃^7*W.a₄*W.a₆^3 + 2*W.a₁^2*W.a₃^3*W.a₄^4*W.a₆^3 +
  W.a₁^2*W.a₃*W.a₄^4*W.a₆^4 + 2*W.a₁^2*W.a₃*W.a₄*W.a₆^6 +
  2*W.a₁*W.a₂^2*W.a₃^12*W.a₄ + W.a₁*W.a₂^2*W.a₃^10*W.a₄*W.a₆ +
  W.a₁*W.a₂^2*W.a₃^4*W.a₄*W.a₆^4 + W.a₁*W.a₂^2*W.a₄*W.a₆^6 +
  W.a₁*W.a₂*W.a₃^14 + W.a₁*W.a₂*W.a₃^12*W.a₆ +
  2*W.a₁*W.a₂*W.a₃^8*W.a₄^3*W.a₆ + 2*W.a₁*W.a₂*W.a₃^8*W.a₆^3 +
  W.a₁*W.a₂*W.a₃^6*W.a₄^3*W.a₆^2 + 2*W.a₁*W.a₂*W.a₃^6*W.a₆^4 +
  2*W.a₁*W.a₂*W.a₃^2*W.a₄^3*W.a₆^4 + W.a₁*W.a₂*W.a₃^2*W.a₆^6 +
  W.a₁*W.a₂*W.a₄^3*W.a₆^5 + W.a₁*W.a₂*W.a₆^7 +
  2*W.a₁*W.a₃^12*W.a₄^2 + W.a₁*W.a₃^8*W.a₄^5 +
  W.a₁*W.a₃^6*W.a₄^5*W.a₆ + W.a₁*W.a₃^6*W.a₄^2*W.a₆^3 +
  W.a₁*W.a₃^2*W.a₄^5*W.a₆^3 + W.a₁*W.a₄^5*W.a₆^4 +
  2*W.a₁*W.a₄^2*W.a₆^6 + 2*W.a₂^3*W.a₃^13 +
  2*W.a₂^3*W.a₃^11*W.a₆ + W.a₂^3*W.a₃^9*W.a₆^2 +
  2*W.a₂^3*W.a₃^5*W.a₆^4 + W.a₂^3*W.a₃^3*W.a₆^5 +
  W.a₂^3*W.a₃*W.a₆^6 + W.a₂^2*W.a₃^11*W.a₄^2 +
  W.a₂^2*W.a₃^9*W.a₄^2*W.a₆ + W.a₂^2*W.a₃^5*W.a₄^2*W.a₆^3 +
  W.a₂^2*W.a₃^3*W.a₄^2*W.a₆^4 + W.a₂*W.a₃^9*W.a₄^4 +
  W.a₂*W.a₃^3*W.a₄^4*W.a₆^3 + 2*W.a₃^15 + W.a₃^9*W.a₆^3 +
  2*W.a₃^7*W.a₄^6 + 2*W.a₃^3*W.a₆^6 + 2*W.a₃*W.a₄^6*W.a₆^3

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 4096 in
/-- **Witness coefficient at X¹** (q=3 char-3): ~85-term polynomial. -/
noncomputable def omega3_witness_coeff_X1 (W : WeierstrassCurve K) : K :=
  2*W.a₁^8*W.a₃^3*W.a₄*W.a₆^3 + 2*W.a₁^7*W.a₂*W.a₃^4*W.a₆^3 +
  2*W.a₁^7*W.a₂*W.a₆^5 + W.a₁^6*W.a₂*W.a₃^3*W.a₄*W.a₆^3 +
  2*W.a₁^6*W.a₂*W.a₃*W.a₄*W.a₆^4 + W.a₁^6*W.a₃^9*W.a₆ +
  2*W.a₁^6*W.a₃^3*W.a₄^3*W.a₆^2 + W.a₁^6*W.a₃^3*W.a₆^4 +
  W.a₁^5*W.a₂^2*W.a₃^4*W.a₆^3 + W.a₁^5*W.a₂^2*W.a₃^2*W.a₆^4 +
  2*W.a₁^5*W.a₂*W.a₃^2*W.a₄^2*W.a₆^3 +
  2*W.a₁^5*W.a₂*W.a₄^2*W.a₆^4 + 2*W.a₁^5*W.a₃^10*W.a₄ +
  W.a₁^5*W.a₃^6*W.a₄^4 + 2*W.a₁^5*W.a₃^4*W.a₄^4*W.a₆ +
  2*W.a₁^5*W.a₃^4*W.a₄*W.a₆^3 + W.a₁^5*W.a₄^4*W.a₆^3 +
  W.a₁^4*W.a₂^2*W.a₃^3*W.a₄*W.a₆^3 +
  W.a₁^4*W.a₂^2*W.a₃*W.a₄*W.a₆^4 + W.a₁^4*W.a₂*W.a₃^11 +
  2*W.a₁^4*W.a₂*W.a₃^9*W.a₆ + W.a₁^4*W.a₂*W.a₃^7*W.a₄^3 +
  W.a₁^4*W.a₂*W.a₃^5*W.a₄^3*W.a₆ + W.a₁^4*W.a₂*W.a₃^5*W.a₆^3 +
  W.a₁^4*W.a₂*W.a₃^3*W.a₄^3*W.a₆^2 + 2*W.a₁^4*W.a₂*W.a₃^3*W.a₆^4 +
  2*W.a₁^4*W.a₂*W.a₃*W.a₄^3*W.a₆^3 + 2*W.a₁^4*W.a₃^9*W.a₄^2 +
  2*W.a₁^4*W.a₃^5*W.a₄^5 + 2*W.a₁^4*W.a₃^3*W.a₄^5*W.a₆ +
  2*W.a₁^4*W.a₃^3*W.a₄^2*W.a₆^3 + 2*W.a₁^3*W.a₂^3*W.a₃^6*W.a₆^2 +
  W.a₁^3*W.a₂^3*W.a₃^4*W.a₆^3 + 2*W.a₁^3*W.a₂^3*W.a₃^2*W.a₆^4 +
  W.a₁^3*W.a₂^2*W.a₃^2*W.a₄^2*W.a₆^3 +
  W.a₁^3*W.a₂^2*W.a₄^2*W.a₆^4 + 2*W.a₁^3*W.a₂*W.a₃^10*W.a₄ +
  W.a₁^3*W.a₂*W.a₃^6*W.a₄^4 + 2*W.a₁^3*W.a₂*W.a₃^4*W.a₄^4*W.a₆ +
  2*W.a₁^3*W.a₂*W.a₃^4*W.a₄*W.a₆^3 + W.a₁^3*W.a₂*W.a₄^4*W.a₆^3 +
  2*W.a₁^3*W.a₃^12 + W.a₁^3*W.a₃^6*W.a₄^3*W.a₆ +
  2*W.a₁^3*W.a₃^6*W.a₆^3 + W.a₁^3*W.a₃^4*W.a₄^6 +
  W.a₁^3*W.a₄^6*W.a₆^2 + W.a₁^3*W.a₄^3*W.a₆^4 +
  2*W.a₁^2*W.a₂^3*W.a₃^9*W.a₄ + 2*W.a₁^2*W.a₂^3*W.a₃^7*W.a₄*W.a₆ +
  2*W.a₁^2*W.a₂^3*W.a₃^3*W.a₄*W.a₆^3 +
  2*W.a₁^2*W.a₂^3*W.a₃*W.a₄*W.a₆^4 + W.a₁^2*W.a₂^2*W.a₃^11 +
  W.a₁^2*W.a₂^2*W.a₃^7*W.a₄^3 + W.a₁^2*W.a₂^2*W.a₃^5*W.a₄^3*W.a₆ +
  W.a₁^2*W.a₂^2*W.a₃^5*W.a₆^3 + 2*W.a₁^2*W.a₂*W.a₃^9*W.a₄^2 +
  2*W.a₁^2*W.a₂*W.a₃^5*W.a₄^5 + 2*W.a₁^2*W.a₂*W.a₃^3*W.a₄^5*W.a₆ +
  2*W.a₁^2*W.a₂*W.a₃^3*W.a₄^2*W.a₆^3 + 2*W.a₁^2*W.a₃^7*W.a₄^4 +
  2*W.a₁^2*W.a₃^3*W.a₄^7 + W.a₁^2*W.a₃*W.a₄^7*W.a₆ +
  2*W.a₁^2*W.a₃*W.a₄^4*W.a₆^3 + 2*W.a₁*W.a₂^4*W.a₃^10 +
  W.a₁*W.a₂^4*W.a₃^8*W.a₆ + 2*W.a₁*W.a₂^4*W.a₃^6*W.a₆^2 +
  2*W.a₁*W.a₂^4*W.a₃^4*W.a₆^3 + W.a₁*W.a₂^4*W.a₃^2*W.a₆^4 +
  2*W.a₁*W.a₂^4*W.a₆^5 + 2*W.a₁*W.a₂^3*W.a₃^8*W.a₄^2 +
  2*W.a₁*W.a₂^3*W.a₃^6*W.a₄^2*W.a₆ +
  2*W.a₁*W.a₂^3*W.a₃^2*W.a₄^2*W.a₆^3 +
  2*W.a₁*W.a₂^3*W.a₄^2*W.a₆^4 + W.a₁*W.a₂^2*W.a₃^10*W.a₄ +
  W.a₁*W.a₂^2*W.a₃^6*W.a₄^4 + W.a₁*W.a₂^2*W.a₃^4*W.a₄^4*W.a₆ +
  W.a₁*W.a₂^2*W.a₃^4*W.a₄*W.a₆^3 + W.a₁*W.a₂*W.a₃^12 +
  W.a₁*W.a₂*W.a₃^8*W.a₄^3 + W.a₁*W.a₂*W.a₃^6*W.a₄^3*W.a₆ +
  2*W.a₁*W.a₂*W.a₃^6*W.a₆^3 + 2*W.a₁*W.a₂*W.a₃^2*W.a₄^6*W.a₆ +
  W.a₁*W.a₂*W.a₃^2*W.a₄^3*W.a₆^3 + W.a₁*W.a₂*W.a₄^6*W.a₆^2 +
  W.a₁*W.a₂*W.a₄^3*W.a₆^4 + W.a₁*W.a₂*W.a₆^6 +
  2*W.a₁*W.a₃^6*W.a₄^5 + W.a₁*W.a₃^2*W.a₄^8 +
  W.a₁*W.a₄^8*W.a₆ + 2*W.a₁*W.a₄^5*W.a₆^3 +
  2*W.a₂^3*W.a₃^11 + 2*W.a₂^3*W.a₃^9*W.a₆ +
  2*W.a₂^3*W.a₃^7*W.a₄^3 + 2*W.a₂^3*W.a₃^5*W.a₄^3*W.a₆ +
  2*W.a₂^3*W.a₃^5*W.a₆^3 + W.a₂^3*W.a₃^3*W.a₄^3*W.a₆^2 +
  2*W.a₂^3*W.a₃^3*W.a₆^4 + W.a₂^3*W.a₃*W.a₄^3*W.a₆^3 +
  W.a₂^2*W.a₃^9*W.a₄^2 + W.a₂^2*W.a₃^5*W.a₄^5 +
  W.a₂^2*W.a₃^3*W.a₄^5*W.a₆ + W.a₂^2*W.a₃^3*W.a₄^2*W.a₆^3 +
  W.a₂*W.a₃^3*W.a₄^7 + W.a₃^9*W.a₄^3 + W.a₃^3*W.a₄^3*W.a₆^3 +
  2*W.a₃*W.a₄^9

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4096 in
/-- **Witness coefficient at X²** (q=3 char-3): ~70-term polynomial. -/
noncomputable def omega3_witness_coeff_X2 (W : WeierstrassCurve K) : K :=
  W.a₁^11*W.a₄*W.a₆^3 + W.a₁^10*W.a₂*W.a₃*W.a₆^3 +
  2*W.a₁^9*W.a₂*W.a₄*W.a₆^3 + W.a₁^9*W.a₄^3*W.a₆^2 +
  2*W.a₁^9*W.a₆^4 + 2*W.a₁^8*W.a₂^2*W.a₃*W.a₆^3 +
  2*W.a₁^8*W.a₃^3*W.a₄^4 + W.a₁^8*W.a₃*W.a₄^4*W.a₆ +
  W.a₁^8*W.a₃*W.a₄*W.a₆^3 + W.a₁^7*W.a₂^2*W.a₄*W.a₆^3 +
  2*W.a₁^7*W.a₂*W.a₃^4*W.a₄^3 + 2*W.a₁^7*W.a₂*W.a₃^2*W.a₄^3*W.a₆ +
  2*W.a₁^7*W.a₂*W.a₃^2*W.a₆^3 + W.a₁^7*W.a₃^2*W.a₄^5 +
  W.a₁^7*W.a₄^5*W.a₆ + W.a₁^7*W.a₄^2*W.a₆^3 +
  W.a₁^6*W.a₂^3*W.a₃^3*W.a₆^2 + W.a₁^6*W.a₂^3*W.a₃*W.a₆^3 +
  2*W.a₁^6*W.a₂*W.a₃^3*W.a₄^4 + 2*W.a₁^6*W.a₂*W.a₃*W.a₄^4*W.a₆ +
  2*W.a₁^6*W.a₂*W.a₃*W.a₄*W.a₆^3 + 2*W.a₁^6*W.a₃^3*W.a₄^3*W.a₆ +
  W.a₁^6*W.a₃^3*W.a₆^3 + 2*W.a₁^6*W.a₃*W.a₄^6 +
  W.a₁^5*W.a₂^3*W.a₃^6*W.a₄ + W.a₁^5*W.a₂^3*W.a₃^4*W.a₄*W.a₆ +
  W.a₁^5*W.a₂^3*W.a₄*W.a₆^3 + 2*W.a₁^5*W.a₂^2*W.a₃^4*W.a₄^3 +
  W.a₁^5*W.a₂^2*W.a₃^2*W.a₄^3*W.a₆ + W.a₁^5*W.a₂^2*W.a₃^2*W.a₆^3 +
  2*W.a₁^5*W.a₂*W.a₃^2*W.a₄^5 + 2*W.a₁^5*W.a₂*W.a₄^5*W.a₆ +
  2*W.a₁^5*W.a₂*W.a₄^2*W.a₆^3 + W.a₁^5*W.a₃^4*W.a₄^4 +
  W.a₁^4*W.a₂^4*W.a₃^7 + 2*W.a₁^4*W.a₂^4*W.a₃^5*W.a₆ +
  W.a₁^4*W.a₂^4*W.a₃*W.a₆^3 + W.a₁^4*W.a₂^3*W.a₃^5*W.a₄^2 +
  W.a₁^4*W.a₂^3*W.a₃^3*W.a₄^2*W.a₆ +
  W.a₁^4*W.a₂^2*W.a₃*W.a₄^4*W.a₆ + W.a₁^4*W.a₂^2*W.a₃*W.a₄*W.a₆^3 +
  2*W.a₁^4*W.a₂*W.a₃^5*W.a₄^3 + W.a₁^4*W.a₂*W.a₃*W.a₄^6 +
  W.a₁^4*W.a₃^3*W.a₄^5 + 2*W.a₁^3*W.a₂^4*W.a₃^4*W.a₄*W.a₆ +
  2*W.a₁^3*W.a₂^4*W.a₄*W.a₆^3 + 2*W.a₁^3*W.a₂^3*W.a₃^4*W.a₄^3 +
  2*W.a₁^3*W.a₂^3*W.a₃^2*W.a₄^3*W.a₆ +
  2*W.a₁^3*W.a₂^3*W.a₃^2*W.a₆^3 + W.a₁^3*W.a₂^3*W.a₄^3*W.a₆^2 +
  2*W.a₁^3*W.a₂^3*W.a₆^4 + W.a₁^3*W.a₂^2*W.a₃^2*W.a₄^5 +
  W.a₁^3*W.a₂^2*W.a₄^5*W.a₆ + W.a₁^3*W.a₂^2*W.a₄^2*W.a₆^3 +
  2*W.a₁^3*W.a₂*W.a₃^4*W.a₄^4 + 2*W.a₁^3*W.a₂*W.a₄^7 +
  W.a₁^3*W.a₄^3*W.a₆^3 + W.a₁^2*W.a₂^5*W.a₃^5*W.a₆ +
  2*W.a₁^2*W.a₂^5*W.a₃*W.a₆^3 + 2*W.a₁^2*W.a₂^4*W.a₃^5*W.a₄^2 +
  2*W.a₁^2*W.a₂^4*W.a₃^3*W.a₄^2*W.a₆ +
  W.a₁^2*W.a₂^3*W.a₃^3*W.a₄^4 + W.a₁^2*W.a₂^2*W.a₃^5*W.a₄^3 +
  W.a₁^2*W.a₂^2*W.a₃*W.a₄^6 + 2*W.a₁^2*W.a₂*W.a₃^3*W.a₄^5 +
  2*W.a₁*W.a₂^5*W.a₃^6*W.a₄ + W.a₁*W.a₂^5*W.a₃^4*W.a₄*W.a₆ +
  W.a₁*W.a₂^5*W.a₄*W.a₆^3 + 2*W.a₁*W.a₂^4*W.a₃^4*W.a₄^3 +
  W.a₁*W.a₂^2*W.a₃^4*W.a₄^4 + 2*W.a₁*W.a₂^2*W.a₄^7 +
  2*W.a₂^6*W.a₃^7 + 2*W.a₂^6*W.a₃^5*W.a₆ +
  W.a₂^6*W.a₃^3*W.a₆^2 + W.a₂^6*W.a₃*W.a₆^3 +
  W.a₂^5*W.a₃^5*W.a₄^2 + W.a₂^5*W.a₃^3*W.a₄^2*W.a₆ +
  W.a₂^4*W.a₃^3*W.a₄^4 + 2*W.a₂^3*W.a₃^9 +
  2*W.a₂^3*W.a₃^5*W.a₄^3 + 2*W.a₂^3*W.a₃^3*W.a₄^3*W.a₆ +
  2*W.a₂^3*W.a₃^3*W.a₆^3 + 2*W.a₂^3*W.a₃*W.a₄^6 +
  W.a₂^2*W.a₃^3*W.a₄^5 + 2*W.a₃^3*W.a₄^6

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- **Witness coefficient at X³** (q=3 char-3): ~100-term polynomial. -/
noncomputable def omega3_witness_coeff_X3 (W : WeierstrassCurve K) : K :=
  2*W.a₁^13*W.a₂*W.a₆^2 + 2*W.a₁^12*W.a₂*W.a₃*W.a₄*W.a₆ +
  W.a₁^12*W.a₃^3*W.a₆ + W.a₁^11*W.a₂^2*W.a₃^2*W.a₆ +
  2*W.a₁^11*W.a₂*W.a₃^2*W.a₄^2 + 2*W.a₁^11*W.a₂*W.a₄^2*W.a₆ +
  2*W.a₁^11*W.a₃^4*W.a₄ + 2*W.a₁^10*W.a₂^2*W.a₃^3*W.a₄ +
  W.a₁^10*W.a₂^2*W.a₃*W.a₄*W.a₆ + W.a₁^10*W.a₂*W.a₃^5 +
  W.a₁^10*W.a₂*W.a₃^3*W.a₆ + W.a₁^10*W.a₂*W.a₃*W.a₄^3 +
  2*W.a₁^10*W.a₃^3*W.a₄^2 + 2*W.a₁^9*W.a₂^3*W.a₃^4 +
  2*W.a₁^9*W.a₂^3*W.a₃^2*W.a₆ + W.a₁^9*W.a₂^2*W.a₃^2*W.a₄^2 +
  W.a₁^9*W.a₂^2*W.a₄^2*W.a₆ + 2*W.a₁^9*W.a₂*W.a₄^4 +
  2*W.a₁^9*W.a₃^6 + W.a₁^9*W.a₄^3*W.a₆ +
  2*W.a₁^8*W.a₂^3*W.a₃^3*W.a₄ + 2*W.a₁^8*W.a₂^3*W.a₃*W.a₄*W.a₆ +
  W.a₁^8*W.a₂^2*W.a₃*W.a₄^3 + 2*W.a₁^8*W.a₃*W.a₄^4 +
  2*W.a₁^7*W.a₂^4*W.a₃^4 + W.a₁^7*W.a₂^4*W.a₃^2*W.a₆ +
  W.a₁^7*W.a₂^4*W.a₆^2 + 2*W.a₁^7*W.a₂^3*W.a₃^2*W.a₄^2 +
  2*W.a₁^7*W.a₂^3*W.a₄^2*W.a₆ + 2*W.a₁^7*W.a₂^2*W.a₄^4 +
  W.a₁^7*W.a₂*W.a₃^2*W.a₄^3 + 2*W.a₁^7*W.a₂*W.a₄^3*W.a₆ +
  W.a₁^7*W.a₂*W.a₆^3 + 2*W.a₁^7*W.a₄^5 +
  2*W.a₁^6*W.a₂^4*W.a₃*W.a₄*W.a₆ + 2*W.a₁^6*W.a₂*W.a₃*W.a₄^4 +
  W.a₁^5*W.a₂^5*W.a₃^2*W.a₆ + 2*W.a₁^5*W.a₂^4*W.a₃^2*W.a₄^2 +
  2*W.a₁^5*W.a₂^4*W.a₄^2*W.a₆ + W.a₁^5*W.a₂^2*W.a₃^2*W.a₄^3 +
  2*W.a₁^5*W.a₂*W.a₄^5 + W.a₁^5*W.a₃^6*W.a₄ +
  2*W.a₁^5*W.a₄*W.a₆^3 + 2*W.a₁^4*W.a₂^5*W.a₃^3*W.a₄ +
  W.a₁^4*W.a₂^5*W.a₃*W.a₄*W.a₆ + W.a₁^4*W.a₂^4*W.a₃^3*W.a₆ +
  W.a₁^4*W.a₂^4*W.a₃*W.a₄^3 + W.a₁^4*W.a₂^2*W.a₃*W.a₄^4 +
  W.a₁^4*W.a₂*W.a₃^7 + 2*W.a₁^4*W.a₂*W.a₃^3*W.a₄^3 +
  2*W.a₁^4*W.a₂*W.a₃^3*W.a₆^2 + 2*W.a₁^4*W.a₂*W.a₃*W.a₆^3 +
  2*W.a₁^3*W.a₂^6*W.a₃^4 + 2*W.a₁^3*W.a₂^6*W.a₃^2*W.a₆ +
  W.a₁^3*W.a₂^5*W.a₃^2*W.a₄^2 + W.a₁^3*W.a₂^5*W.a₄^2*W.a₆ +
  2*W.a₁^3*W.a₂^4*W.a₃^4*W.a₄ + 2*W.a₁^3*W.a₂^4*W.a₄^4 +
  W.a₁^3*W.a₂^3*W.a₃^6 + 2*W.a₁^3*W.a₂^3*W.a₃^2*W.a₄^3 +
  W.a₁^3*W.a₂^3*W.a₄^3*W.a₆ + W.a₁^3*W.a₂^2*W.a₄^5 +
  2*W.a₁^3*W.a₂*W.a₃^6*W.a₄ + 2*W.a₁^3*W.a₂*W.a₃^4*W.a₄*W.a₆ +
  W.a₁^3*W.a₂*W.a₄*W.a₆^3 + 2*W.a₁^3*W.a₃^6*W.a₆ +
  W.a₁^3*W.a₄^6 + W.a₁^3*W.a₄^3*W.a₆^2 + 2*W.a₁^3*W.a₆^4 +
  2*W.a₁^2*W.a₂^6*W.a₃^3*W.a₄ + 2*W.a₁^2*W.a₂^6*W.a₃*W.a₄*W.a₆ +
  W.a₁^2*W.a₂^5*W.a₃^5 + W.a₁^2*W.a₂^5*W.a₃*W.a₄^3 +
  2*W.a₁^2*W.a₂^4*W.a₃^3*W.a₄^2 + W.a₁^2*W.a₂^3*W.a₃*W.a₄^4 +
  2*W.a₁^2*W.a₂^2*W.a₃^7 + W.a₁^2*W.a₂^2*W.a₃^5*W.a₆ +
  W.a₁^2*W.a₂^2*W.a₃*W.a₆^3 + 2*W.a₁^2*W.a₂*W.a₃^5*W.a₄^2 +
  2*W.a₁^2*W.a₂*W.a₃^3*W.a₄^2*W.a₆ + W.a₁^2*W.a₃^7*W.a₄ +
  2*W.a₁^2*W.a₃^3*W.a₄^4 + W.a₁^2*W.a₃*W.a₄^4*W.a₆ +
  W.a₁^2*W.a₃*W.a₄*W.a₆^3 + 2*W.a₁*W.a₂^7*W.a₃^4 +
  W.a₁*W.a₂^7*W.a₃^2*W.a₆ + 2*W.a₁*W.a₂^7*W.a₆^2 +
  2*W.a₁*W.a₂^6*W.a₃^2*W.a₄^2 + 2*W.a₁*W.a₂^6*W.a₄^2*W.a₆ +
  W.a₁*W.a₂^5*W.a₃^4*W.a₄ + 2*W.a₁*W.a₂^5*W.a₄^4 +
  W.a₁*W.a₂^4*W.a₃^6 + 2*W.a₁*W.a₂^4*W.a₃^2*W.a₄^3 +
  2*W.a₁*W.a₂^4*W.a₄^3*W.a₆ + W.a₁*W.a₂^4*W.a₆^3 +
  W.a₁*W.a₂^3*W.a₄^5 + W.a₁*W.a₂^2*W.a₃^4*W.a₄*W.a₆ +
  2*W.a₁*W.a₂^2*W.a₄*W.a₆^3 + 2*W.a₁*W.a₂*W.a₃^8 +
  2*W.a₁*W.a₂*W.a₃^6*W.a₆ + 2*W.a₁*W.a₂*W.a₃^2*W.a₄^3*W.a₆ +
  2*W.a₁*W.a₂*W.a₃^2*W.a₆^3 + 2*W.a₁*W.a₂*W.a₄^6 +
  W.a₁*W.a₂*W.a₄^3*W.a₆^2 + 2*W.a₁*W.a₂*W.a₆^4 +
  W.a₁*W.a₃^6*W.a₄^2 + W.a₁*W.a₃^2*W.a₄^5 +
  W.a₁*W.a₄^5*W.a₆ + W.a₁*W.a₄^2*W.a₆^3 +
  2*W.a₂^6*W.a₃^5 + 2*W.a₂^6*W.a₃^3*W.a₆ +
  W.a₂^5*W.a₃^3*W.a₄^2 + 2*W.a₂^3*W.a₃^5*W.a₆ +
  2*W.a₂^3*W.a₃^3*W.a₄^3 + W.a₂^3*W.a₃^3*W.a₆^2 +
  2*W.a₂^3*W.a₃*W.a₆^3 + W.a₂^2*W.a₃^5*W.a₄^2 +
  W.a₂^2*W.a₃^3*W.a₄^2*W.a₆ + W.a₂*W.a₃^3*W.a₄^4 +
  W.a₃^9 + W.a₃^3*W.a₆^3 + 2*W.a₃*W.a₄^6

set_option maxHeartbeats 800000 in
/-- **Witness coefficient at X⁴** (q=3 char-3): ~70-term polynomial. -/
noncomputable def omega3_witness_coeff_X4 (W : WeierstrassCurve K) : K :=
  W.a₁^15*W.a₆ + 2*W.a₁^14*W.a₃*W.a₄ + W.a₁^13*W.a₂*W.a₃^2 +
  2*W.a₁^13*W.a₂*W.a₆ + 2*W.a₁^13*W.a₄^2 + 2*W.a₁^12*W.a₂*W.a₃*W.a₄ +
  2*W.a₁^12*W.a₃^3 + W.a₁^11*W.a₂^2*W.a₃^2 + 2*W.a₁^11*W.a₂*W.a₄^2 +
  W.a₁^10*W.a₂^2*W.a₃*W.a₄ + W.a₁^10*W.a₂*W.a₃^3 +
  2*W.a₁^9*W.a₂^3*W.a₃^2 + 2*W.a₁^9*W.a₂^3*W.a₆ +
  W.a₁^9*W.a₂^2*W.a₄^2 + W.a₁^9*W.a₄^3 + 2*W.a₁^8*W.a₃^3*W.a₄ +
  W.a₁^7*W.a₂^4*W.a₆ + 2*W.a₁^7*W.a₂*W.a₃^4 + 2*W.a₁^7*W.a₂*W.a₄^3 +
  2*W.a₁^7*W.a₂*W.a₆^2 + 2*W.a₁^6*W.a₂^4*W.a₃*W.a₄ +
  2*W.a₁^6*W.a₂^3*W.a₃^3 + W.a₁^6*W.a₂*W.a₃^3*W.a₄ +
  2*W.a₁^6*W.a₂*W.a₃*W.a₄*W.a₆ + W.a₁^6*W.a₃^3*W.a₆ +
  W.a₁^5*W.a₂^5*W.a₃^2 + 2*W.a₁^5*W.a₂^4*W.a₄^2 +
  W.a₁^5*W.a₂^2*W.a₃^4 + W.a₁^5*W.a₂^2*W.a₃^2*W.a₆ +
  2*W.a₁^5*W.a₂*W.a₃^2*W.a₄^2 + 2*W.a₁^5*W.a₂*W.a₄^2*W.a₆ +
  2*W.a₁^5*W.a₃^4*W.a₄ + W.a₁^5*W.a₄^4 +
  W.a₁^4*W.a₂^5*W.a₃*W.a₄ + W.a₁^4*W.a₂^4*W.a₃^3 +
  W.a₁^4*W.a₂^2*W.a₃^3*W.a₄ + W.a₁^4*W.a₂^2*W.a₃*W.a₄*W.a₆ +
  W.a₁^4*W.a₂*W.a₃^5 + 2*W.a₁^4*W.a₂*W.a₃^3*W.a₆ +
  2*W.a₁^4*W.a₂*W.a₃*W.a₄^3 + 2*W.a₁^4*W.a₃^3*W.a₄^2 +
  2*W.a₁^3*W.a₂^6*W.a₃^2 + W.a₁^3*W.a₂^6*W.a₆ +
  W.a₁^3*W.a₂^5*W.a₄^2 + W.a₁^3*W.a₂^3*W.a₃^4 +
  2*W.a₁^3*W.a₂^3*W.a₃^2*W.a₆ + W.a₁^3*W.a₂^3*W.a₄^3 +
  W.a₁^3*W.a₂^2*W.a₃^2*W.a₄^2 + W.a₁^3*W.a₂^2*W.a₄^2*W.a₆ +
  2*W.a₁^3*W.a₂*W.a₃^4*W.a₄ + W.a₁^3*W.a₂*W.a₄^4 +
  2*W.a₁^3*W.a₃^6 + W.a₁^3*W.a₄^3*W.a₆ +
  W.a₁^2*W.a₂^6*W.a₃*W.a₄ + 2*W.a₁^2*W.a₂^3*W.a₃^3*W.a₄ +
  2*W.a₁^2*W.a₂^3*W.a₃*W.a₄*W.a₆ + W.a₁^2*W.a₂^2*W.a₃^5 +
  2*W.a₁^2*W.a₂*W.a₃^3*W.a₄^2 + 2*W.a₁^2*W.a₃*W.a₄^4 +
  2*W.a₁*W.a₂^7*W.a₃^2 + 2*W.a₁*W.a₂^7*W.a₆ +
  W.a₁*W.a₂^6*W.a₄^2 + 2*W.a₁*W.a₂^4*W.a₃^4 +
  W.a₁*W.a₂^4*W.a₃^2*W.a₆ + 2*W.a₁*W.a₂^4*W.a₄^3 +
  2*W.a₁*W.a₂^4*W.a₆^2 + 2*W.a₁*W.a₂^3*W.a₃^2*W.a₄^2 +
  2*W.a₁*W.a₂^3*W.a₄^2*W.a₆ + W.a₁*W.a₂^2*W.a₃^4*W.a₄ +
  2*W.a₁*W.a₂*W.a₃^6 + W.a₁*W.a₂*W.a₃^2*W.a₄^3 +
  W.a₁*W.a₂*W.a₄^3*W.a₆ + 2*W.a₁*W.a₂*W.a₆^3 + 2*W.a₁*W.a₄^5 +
  2*W.a₂^3*W.a₃^5 + 2*W.a₂^3*W.a₃^3*W.a₆ +
  W.a₂^3*W.a₃*W.a₄^3 + W.a₂^2*W.a₃^3*W.a₄^2 + W.a₃^3*W.a₄^3

/-- **Witness coefficient at X⁵** (q=3 char-3): 30-term polynomial. -/
noncomputable def omega3_witness_coeff_X5 (W : WeierstrassCurve K) : K :=
  W.a₁^11*W.a₄ + W.a₁^10*W.a₂*W.a₃ +
  2*W.a₁^9*W.a₂*W.a₄ + 2*W.a₁^9*W.a₆ +
  2*W.a₁^8*W.a₂^2*W.a₃ + W.a₁^8*W.a₃*W.a₄ +
  W.a₁^7*W.a₂^2*W.a₄ + 2*W.a₁^7*W.a₂*W.a₃^2 + W.a₁^7*W.a₄^2 +
  W.a₁^6*W.a₂^3*W.a₃ + 2*W.a₁^6*W.a₂*W.a₃*W.a₄ + W.a₁^6*W.a₃^3 +
  W.a₁^5*W.a₂^3*W.a₄ + W.a₁^5*W.a₂^2*W.a₃^2 + 2*W.a₁^5*W.a₂*W.a₄^2 +
  W.a₁^4*W.a₂^4*W.a₃ + W.a₁^4*W.a₂^2*W.a₃*W.a₄ +
  2*W.a₁^3*W.a₂^4*W.a₄ + 2*W.a₁^3*W.a₂^3*W.a₃^2 +
  2*W.a₁^3*W.a₂^3*W.a₆ + W.a₁^3*W.a₂^2*W.a₄^2 + W.a₁^3*W.a₄^3 +
  2*W.a₁^2*W.a₂^5*W.a₃ + W.a₁*W.a₂^5*W.a₄ +
  W.a₂^6*W.a₃ + 2*W.a₂^3*W.a₃^3

/-- **Full witness polynomial (leading X⁵-X⁷ factored)**: composed from
    the coefficient-by-coefficient defs to keep elaboration tractable.
    Lower-degree X⁰-X⁴ coefficients (sympy-extracted, larger) are
    factored similarly in follow-up. -/
noncomputable def omega3_witness_polynomial_char_three
    (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C (omega3_witness_coeff_X0 W) +
  Polynomial.C (omega3_witness_coeff_X1 W) * Polynomial.X +
  Polynomial.C (omega3_witness_coeff_X2 W) * Polynomial.X ^ 2 +
  Polynomial.C (omega3_witness_coeff_X3 W) * Polynomial.X ^ 3 +
  Polynomial.C (omega3_witness_coeff_X4 W) * Polynomial.X ^ 4 +
  Polynomial.C (omega3_witness_coeff_X5 W) * Polynomial.X ^ 5 +
  Polynomial.C (omega3_witness_coeff_X6 W) * Polynomial.X ^ 6 +
  Polynomial.C (omega3_witness_coeff_X7 W) * Polynomial.X ^ 7

/-- **OBSOLETE leading-partial scaffold** — superseded by
    `omega3_witness_polynomial_char_three`. -/
noncomputable def omega3_witness_leading_partial_char_three
    (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C (W.a₁ * W.a₂) * Polynomial.X ^ 7 +
  Polynomial.C (W.a₁ ^ 7 * W.a₂ + W.a₁ ^ 5 * W.a₄ +
    W.a₁ ^ 4 * W.a₂ * W.a₃ + 2 * W.a₁ ^ 3 * W.a₂ * W.a₄ +
    W.a₁ ^ 3 * W.a₆ + 2 * W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ +
    2 * W.a₁ ^ 2 * W.a₃ * W.a₄ + W.a₁ * W.a₂ ^ 4 +
    W.a₁ * W.a₂ ^ 2 * W.a₄ + W.a₁ * W.a₂ * W.a₃ ^ 2 +
    W.a₁ * W.a₂ * W.a₆ + 2 * W.a₁ * W.a₄ ^ 2 +
    W.a₂ ^ 3 * W.a₃ + 2 * W.a₃ ^ 3) * Polynomial.X ^ 6 +
  Polynomial.C (W.a₁ ^ 11 * W.a₄ + W.a₁ ^ 10 * W.a₂ * W.a₃ +
    2 * W.a₁ ^ 9 * W.a₂ * W.a₄ + 2 * W.a₁ ^ 9 * W.a₆ +
    2 * W.a₁ ^ 8 * W.a₂ ^ 2 * W.a₃ + W.a₁ ^ 8 * W.a₃ * W.a₄ +
    W.a₁ ^ 7 * W.a₂ ^ 2 * W.a₄ + 2 * W.a₁ ^ 7 * W.a₂ * W.a₃ ^ 2 +
    W.a₁ ^ 7 * W.a₄ ^ 2 + W.a₁ ^ 6 * W.a₂ ^ 3 * W.a₃ +
    2 * W.a₁ ^ 6 * W.a₂ * W.a₃ * W.a₄ + W.a₁ ^ 6 * W.a₃ ^ 3 +
    W.a₁ ^ 5 * W.a₂ ^ 3 * W.a₄ + W.a₁ ^ 5 * W.a₂ ^ 2 * W.a₃ ^ 2 +
    2 * W.a₁ ^ 5 * W.a₂ * W.a₄ ^ 2 + W.a₁ ^ 4 * W.a₂ ^ 4 * W.a₃ +
    W.a₁ ^ 4 * W.a₂ ^ 2 * W.a₃ * W.a₄ +
    2 * W.a₁ ^ 3 * W.a₂ ^ 4 * W.a₄ +
    2 * W.a₁ ^ 3 * W.a₂ ^ 3 * W.a₃ ^ 2 +
    2 * W.a₁ ^ 3 * W.a₂ ^ 3 * W.a₆ +
    W.a₁ ^ 3 * W.a₂ ^ 2 * W.a₄ ^ 2 + W.a₁ ^ 3 * W.a₄ ^ 3 +
    2 * W.a₁ ^ 2 * W.a₂ ^ 5 * W.a₃ + W.a₁ * W.a₂ ^ 5 * W.a₄ +
    W.a₂ ^ 6 * W.a₃ + 2 * W.a₂ ^ 3 * W.a₃ ^ 3) * Polynomial.X ^ 5

/-- **Witness-parametric existential mem for the q=3 coupled residual**:
    given any polynomial `g` such that `expand K 3 g` equals the
    coupled residual, deduce the membership.

    Trivially axiom-clean (just `⟨g, h_eq⟩`); enables downstream
    work to assume the witness existence parametrically without
    needing the substantive ~500-LOC full polynomial transcription. -/
theorem omega3_coupled_residual_full_mem_expand_three_char_three_via_witness
    (W : WeierstrassCurve K) [CharP K 3]
    {g : Polynomial K}
    (h_eq : Polynomial.expand K 3 g = omega3_coupled_residual_full_char_three W) :
    omega3_coupled_residual_full_char_three W ∈
        Set.range (⇑(Polynomial.expand K 3)) :=
  ⟨g, h_eq⟩

/-- **First helper for the q=3 ω_3 coupled-residual arc**: explicit form
    of `ψ_2² + cubic_x` in char 3.

    `(a₁X + a₃)² + (X³ + a₂X² + a₄X + a₆) = X³ + b₂·X² + 2·b₄·X + b₆`
    in char 3. The coefficient identities `a₁² + a₂ = b₂`,
    `a₃² + a₆ = b₆` hold via `4 = 1` in char 3 and
    `2·a₁·a₃ + a₄ = 2·b₄` via `4·a₄ = a₄`. -/
theorem psi_2_sq_plus_cubic_x_form_char_three
    (W : WeierstrassCurve K) [CharP K 3] :
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 2 + cubic_x W =
    Polynomial.X ^ 3 + Polynomial.C W.b₂ * Polynomial.X ^ 2 +
      Polynomial.C (2 * W.b₄) * Polynomial.X + Polynomial.C W.b₆ := by
  unfold cubic_x
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  have h_3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h_3P : (3 : Polynomial K) = 0 := by
    show ((3 : ℕ) : Polynomial K) = 0
    rw [Nat.cast_ofNat]
    show Polynomial.C ((3 : ℕ) : K) = 0
    rw [show ((3 : ℕ) : K) = 0 by exact_mod_cast h_3, Polynomial.C_0]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_ofNat]
  linear_combination
    -(Polynomial.C W.a₂ * Polynomial.X ^ 2 +
      Polynomial.C W.a₄ * Polynomial.X +
      Polynomial.C W.a₆) * h_3P

/-- **Alternative form (negated b₄)** for `ψ_2² + cubic_x` in char 3:
    `(a₁X + a₃)² + (X³ + a₂X² + a₄X + a₆) = X³ + b₂·X² - b₄·X + b₆`.
    Uses `2·b₄ = -b₄` via `(3 : K) = 0`. -/
theorem psi_2_sq_plus_cubic_x_neg_b4_form_char_three
    (W : WeierstrassCurve K) [CharP K 3] :
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 2 + cubic_x W =
    Polynomial.X ^ 3 + Polynomial.C W.b₂ * Polynomial.X ^ 2 -
      Polynomial.C W.b₄ * Polynomial.X + Polynomial.C W.b₆ := by
  rw [psi_2_sq_plus_cubic_x_form_char_three]
  have h_3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h_2b4_eq_neg_b4 : 2 * W.b₄ = -W.b₄ := by linear_combination W.b₄ * h_3
  rw [h_2b4_eq_neg_b4, Polynomial.C_neg, neg_mul]
  ring

/-- **Weierstrass-quartic of `y_gen` in char 3**: `y_gen^4` in `{1, y_gen}`
    basis after iterated Weierstrass substitution.

    `y_gen^4 = -ψ_2·(ψ_2² + 2·cubic_x)·y_gen + cubic_x·(ψ_2² + cubic_x)`

    Composes `y_gen_sq_weierstrass_char_three` and
    `y_gen_cubed_weierstrass_char_three` via `linear_combination`. -/
theorem y_gen_quartic_weierstrass_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] :
    (y_gen W) ^ 4 =
      -((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
        ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
          2 * (x_gen W ^ 3 +
            algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
            algebraMap K W.toAffine.FunctionField W.a₆))) * y_gen W +
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) := by
  have h_sq := y_gen_sq_weierstrass_char_three W
  have h_cube := y_gen_cubed_weierstrass_char_three W
  linear_combination
    ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆)) * h_sq +
    y_gen W * h_cube

/-- **Weierstrass-quintic of `y_gen` in char 3**: `y_gen^5` in `{1, y_gen}`
    basis after iterated Weierstrass substitution.

    `y_gen^5 = (ψ_2⁴ + 3·ψ_2²·cubic_x + cubic_x²)·y_gen -
               ψ_2·cubic_x·(ψ_2² + 2·cubic_x)`

    (In char 3, the `3·ψ_2²·cubic_x` term vanishes, simplifying to
    `(ψ_2⁴ + cubic_x²)·y_gen - ψ_2·cubic_x·(ψ_2² - cubic_x)`.)

    Composes `y_gen_sq_weierstrass_char_three` and
    `y_gen_quartic_weierstrass_char_three`. -/
theorem y_gen_quintic_weierstrass_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] :
    (y_gen W) ^ 5 =
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 4 +
        3 * (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 *
          (x_gen W ^ 3 +
            algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
            algebraMap K W.toAffine.FunctionField W.a₆) +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆) ^ 2) * y_gen W -
      (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        2 * (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) := by
  have h_sq := y_gen_sq_weierstrass_char_three W
  have h_quartic := y_gen_quartic_weierstrass_char_three W
  linear_combination
    -((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        2 * (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆))) * h_sq +
    y_gen W * h_quartic

/-- **Weierstrass-quartic of `y_gen` in char 5** — same form as char 3
    (any char ≠ 2). -/
theorem y_gen_quartic_weierstrass_char_five (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 5] :
    (y_gen W) ^ 4 =
      -((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
        ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
          2 * (x_gen W ^ 3 +
            algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
            algebraMap K W.toAffine.FunctionField W.a₆))) * y_gen W +
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) := by
  have h_sq := y_gen_sq_weierstrass_char_five W
  have h_cube := y_gen_cubed_weierstrass_char_five W
  linear_combination
    ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆)) * h_sq +
    y_gen W * h_cube

/-- **Weierstrass-quintic of `y_gen` in char 5** — same form as char 3. -/
theorem y_gen_quintic_weierstrass_char_five (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 5] :
    (y_gen W) ^ 5 =
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 4 +
        3 * (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 *
          (x_gen W ^ 3 +
            algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
            algebraMap K W.toAffine.FunctionField W.a₆) +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆) ^ 2) * y_gen W -
      (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        2 * (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) := by
  have h_sq := y_gen_sq_weierstrass_char_five W
  have h_quartic := y_gen_quartic_weierstrass_char_five W
  linear_combination
    -((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        2 * (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆))) * h_sq +
    y_gen W * h_quartic

/-! ### Y-degree contribution helpers — coefficient-multiplied y_gen^k forms

For the basis decomposition `ω_ff W 3 = A_reduced + B_reduced · y_gen`,
each Y-degree contribution from W.ω 3 is `aeval x_gen (coeff_k) · y_gen^k`.
Substituting via the y_gen^k Weierstrass identities gives the
{1, y_gen} basis form for that contribution.

These helpers package the substitution generically for an arbitrary
K(E) coefficient `p` (which will be specialized to
`aeval x_gen (Polynomial.coeff (W.ω 3) k)` in the final composition). -/

/-- **Y² contribution helper**: `p · y_gen² = -p·ψ_2·y_gen + p·cubic_x`. -/
theorem y_gen_sq_mul_basis_form_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] (p : W.toAffine.FunctionField) :
    p * (y_gen W) ^ 2 =
      -p * (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) * y_gen W +
      p * (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) := by
  have h_sq := y_gen_sq_weierstrass_char_three W
  linear_combination p * h_sq

/-- **Y³ contribution helper**: `p · y_gen^3 = p·(ψ_2² + cubic_x)·y_gen
    - p·ψ_2·cubic_x`. -/
theorem y_gen_cubed_mul_basis_form_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] (p : W.toAffine.FunctionField) :
    p * (y_gen W) ^ 3 =
      p * ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) * y_gen W -
      p * (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) := by
  have h_cube := y_gen_cubed_weierstrass_char_three W
  linear_combination p * h_cube

/-- **Y⁴ contribution helper**: `p · y_gen^4 = -p·ψ_2·(ψ_2²+2·cubic_x)·y_gen +
    p·cubic_x·(ψ_2²+cubic_x)`. -/
theorem y_gen_quartic_mul_basis_form_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] (p : W.toAffine.FunctionField) :
    p * (y_gen W) ^ 4 =
      -p * ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
        ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
          2 * (x_gen W ^ 3 +
            algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
            algebraMap K W.toAffine.FunctionField W.a₆))) * y_gen W +
      p * (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) := by
  have h_quartic := y_gen_quartic_weierstrass_char_three W
  linear_combination p * h_quartic

/-- **Y⁵ contribution helper**: `p · y_gen^5 = p·(ψ_2⁴+3ψ_2²·cubic_x+cubic_x²)·y_gen
    - p·ψ_2·cubic_x·(ψ_2²+2·cubic_x)`. -/
theorem y_gen_quintic_mul_basis_form_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] (p : W.toAffine.FunctionField) :
    p * (y_gen W) ^ 5 =
      p * ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 4 +
        3 * (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 *
          (x_gen W ^ 3 +
            algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
            algebraMap K W.toAffine.FunctionField W.a₆) +
        (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆) ^ 2) * y_gen W -
      p * (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) *
      (x_gen W ^ 3 +
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
        algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₆) *
      ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
        2 * (x_gen W ^ 3 +
          algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) := by
  have h_quintic := y_gen_quintic_weierstrass_char_three W
  linear_combination p * h_quintic

/-- **α-cubed basis form** (q=3 char-3): combined char-3 cubing
    + Weierstrass substitution chain.

    `(α₀ + α₁·y_gen)^3 = (α₀³ - α₁³·ψ_2·cubic_x) +
                         α₁³·(ψ_2² + cubic_x)·y_gen`

    in char 3, where ψ_2 = a₁·x + a₃ and cubic_x = x³ + a₂·x² + a₄·x + a₆.

    q=3 analog of `alpha_squared_basis_form`. -/
theorem alpha_cubed_basis_form_char_three (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [CharP K 3] (a b : W.toAffine.FunctionField) :
    (a + b * y_gen W) ^ 3 =
      (a ^ 3 - b ^ 3 *
        (algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) *
        (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
          algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₆)) +
      b ^ 3 *
        ((algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
          algebraMap K W.toAffine.FunctionField W.a₃) ^ 2 +
          (x_gen W ^ 3 + algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W ^ 2 +
            algebraMap K W.toAffine.FunctionField W.a₄ * x_gen W +
            algebraMap K W.toAffine.FunctionField W.a₆)) * y_gen W := by
  rw [char_three_cube_basis_form, y_gen_cubed_weierstrass_char_three]
  ring

set_option maxHeartbeats 800000 in
/-- **K(E)-level sum decomposition of `ω_ff W 3` via natDegree bound**:
    given `(W.ω 3).natDegree ≤ 5`, expresses `ω_ff W 3` as the explicit
    sum over Y-degrees 0..5 of `aeval x_gen (coeff_k) · y_gen^k`.

    Witness-parametric on the natDegree bound (which is itself a
    bounded mathlib-API derivation from the W.ω 3 formula structure). -/
theorem omega_ff_three_decomp_via_nat_degree_bound
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_deg : (W.ω 3).natDegree ≤ 5) :
    ω_ff W 3 =
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 0) +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 1) * y_gen W +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 2) * (y_gen W) ^ 2 +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 3) * (y_gen W) ^ 3 +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 4) * (y_gen W) ^ 4 +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 5) * (y_gen W) ^ 5 := by
  -- Use Polynomial.as_sum_range_C_mul_X_pow' to expand W.ω 3 as a sum
  have h_lt : (W.ω 3).natDegree < 6 := by omega
  have h_decomp_poly := (W.ω 3).as_sum_range_C_mul_X_pow' h_lt
  -- Bridge: algebraMap CR KE ∘ mk W ∘ Polynomial.C = aeval x_gen
  have h_alg_eq_aeval : ∀ p : Polynomial K,
      algebraMap (Polynomial K) W.toAffine.FunctionField p =
      Polynomial.aeval (x_gen W) p := fun p ↦ by
    show algebraMap (Polynomial K) W.toAffine.FunctionField p =
      Polynomial.aeval (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) p
    rw [Polynomial.aeval_algebraMap_apply (A := W.toAffine.CoordinateRing)
          (B := W.toAffine.FunctionField),
        Polynomial.aeval_algebraMap_apply (A := Polynomial K)
          (B := W.toAffine.CoordinateRing),
        Polynomial.aeval_X_left_apply, ← IsScalarTower.algebraMap_apply]
  -- Bridge: algebraMap (mk W X) = y_gen W
  have h_X_y : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (Affine.CoordinateRing.mk W.toAffine Polynomial.X) = y_gen W := by
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.root W.toAffine.polynomial) = _
    rfl
  -- Bridge: algebraMap (mk W (C p)) = aeval x_gen p (for p : Polynomial K)
  have h_C_aeval : ∀ p : Polynomial K,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (Affine.CoordinateRing.mk W.toAffine (Polynomial.C p)) =
      Polynomial.aeval (x_gen W) p := fun p ↦ by
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing p) = _
    rw [← IsScalarTower.algebraMap_apply]
    exact h_alg_eq_aeval p
  unfold ω_ff
  conv_lhs => rw [h_decomp_poly]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    map_add, map_mul, map_pow, h_C_aeval, h_X_y]
  ring

set_option maxHeartbeats 1000000 in
/-- **Witness-parametric `OmegaThreeBasisHoldsReduced` discharge**:
    given the polynomial-algebra decomposition of `ω_ff W 3` as a sum
    over Y-degrees 0..5, the Weierstrass-reduced basis decomposition
    follows from composing the four Y-degree contribution helpers
    (`y_gen_sq/cubed/quartic/quintic_weierstrass_char_three`).

    The hypothesis `h_decomp` captures the polynomial-algebra step
    (W.ω 3 expansion as a Y-polynomial sum at the K(E) level).
    Witness-parametric to keep the Lean transcription tractable while
    the unconditional discharge of `h_decomp` is set up. -/
theorem omega_ff_three_basis_decomp_via_witness_char_three
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 3]
    (h_decomp : ω_ff W 3 =
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 0) +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 1) * y_gen W +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 2) * (y_gen W) ^ 2 +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 3) * (y_gen W) ^ 3 +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 4) * (y_gen W) ^ 4 +
      Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 5) * (y_gen W) ^ 5) :
    OmegaThreeBasisHoldsReduced W := by
  unfold OmegaThreeBasisHoldsReduced
    omega_3_X_coeff_reduced_char_three omega_3_Y_coeff_reduced_char_three
  rw [h_decomp]
  -- Use the Y-degree contribution helpers (multiplied form) for k=2,3,4,5.
  have h_sq_mul := y_gen_sq_mul_basis_form_char_three W
    (Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 2))
  have h_cube_mul := y_gen_cubed_mul_basis_form_char_three W
    (Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 3))
  have h_quartic_mul := y_gen_quartic_mul_basis_form_char_three W
    (Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 4))
  have h_quintic_mul := y_gen_quintic_mul_basis_form_char_three W
    (Polynomial.aeval (x_gen W) (Polynomial.coeff (W.ω 3) 5))
  rw [h_sq_mul, h_cube_mul, h_quartic_mul, h_quintic_mul]
  -- Now goal: sums of {1, y_gen} basis terms = X_reduced + Y_reduced · y_gen
  -- after aeval distributes.
  simp only [map_add, map_mul, map_pow, map_sub, map_ofNat,
    Polynomial.aeval_C, Polynomial.aeval_X]
  unfold cubic_x
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  ring

/-! ### natDegree foundational helpers (q=3 unconditional chain)

Sub-helpers toward `(W.ω 3).natDegree ≤ 5`. Each gives a Y-natDegree
bound on a building-block polynomial in `R[X][Y]`. -/

/-- **Y-natDegree of polynomialY ≤ 1**: `polynomialY = C(C 2)·Y + C(C a₁·X + C a₃)`. -/
theorem natDegree_polynomialY_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    W.toAffine.polynomialY.natDegree ≤ 1 := by
  unfold WeierstrassCurve.Affine.polynomialY
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
  · rw [Polynomial.natDegree_C]; omega

/-- **Y-natDegree of polynomialX ≤ 1**: `polynomialX = C(C a₁)·Y - C(...)`. -/
theorem natDegree_polynomialX_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    W.toAffine.polynomialX.natDegree ≤ 1 := by
  unfold WeierstrassCurve.Affine.polynomialX
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  refine max_le ?_ ?_
  · refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
  · rw [Polynomial.natDegree_C]; omega

/-- **Y-natDegree of negPolynomial ≤ 1**: `negPolynomial = -Y - C(C a₁·X + C a₃)`. -/
theorem natDegree_negPolynomial_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    W.toAffine.negPolynomial.natDegree ≤ 1 := by
  unfold WeierstrassCurve.Affine.negPolynomial
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  refine max_le ?_ ?_
  · rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
  · rw [Polynomial.natDegree_C]; omega

/-- **Y-natDegree of ψ_2 ≤ 1**: ψ_2 = polynomialY by definition. -/
theorem natDegree_ψ_2_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    W.ψ₂.natDegree ≤ 1 := by
  show W.toAffine.polynomialY.natDegree ≤ 1
  exact natDegree_polynomialY_le W

/-- **Y-natDegree of ψ_3 = 0** (ψ_3 = C Ψ_3 is constant in Y). -/
theorem natDegree_ψ_three_eq_zero {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) :
    (W.ψ 3).natDegree = 0 := by
  rw [WeierstrassCurve.ψ_three]
  exact Polynomial.natDegree_C _

/-- **Y-natDegree of ψ_4 ≤ 1** (ψ_4 = C preΨ_4 · ψ_2). -/
theorem natDegree_ψ_four_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    (W.ψ 4).natDegree ≤ 1 := by
  rw [WeierstrassCurve.ψ_four]
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_C]
  exact (zero_add _).le.trans (natDegree_ψ_2_le W)

/-- **Y-natDegree of (W.polynomial)² ≤ 4** (Weierstrass affine polynomial squared). -/
theorem natDegree_polynomial_sq_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    (W.toAffine.polynomial ^ 2).natDegree ≤ 4 := by
  refine (Polynomial.natDegree_pow_le).trans ?_
  rw [W.toAffine.natDegree_polynomial]

/-- **Y-natDegree of Ψ_2Sq embedded as C Ψ_2Sq = 0** (constant in Y). -/
theorem natDegree_C_Ψ₂Sq_eq_zero {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) :
    (Polynomial.C W.Ψ₂Sq).natDegree = 0 := Polynomial.natDegree_C _

/-- **Y-natDegree of C·Ψ_3 = 0** (Ψ_3 is in R[X], C·Ψ_3 is constant in Y). -/
theorem natDegree_C_Ψ_3_eq_zero {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) :
    (Polynomial.C W.Ψ₃).natDegree = 0 := Polynomial.natDegree_C _

/-- **Y-natDegree of `C(C a₁) · polyY`** ≤ 1: `C(C a₁) · polyY` has natDegree
    ≤ natDegree polyY ≤ 1. -/
theorem natDegree_CC_a1_mul_polynomialY_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    (Polynomial.C (Polynomial.C W.a₁) * W.toAffine.polynomialY).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_C]
  exact (zero_add _).le.trans (natDegree_polynomialY_le W)

/-- **Y-natDegree of `negPolynomial · (W.ψ 3)^3` ≤ 1** —
    `negPolynomial` has natDegree ≤ 1, `(W.ψ 3)^3 = (C Ψ_3)^3 = C(Ψ_3^3)` has natDegree 0. -/
theorem natDegree_negPolynomial_mul_psi_three_cubed_le
    {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) :
    (W.toAffine.negPolynomial * (W.ψ 3) ^ 3).natDegree ≤ 1 := by
  have h_ψ3 : ((W.ψ 3) ^ 3).natDegree ≤ 0 :=
    Polynomial.natDegree_pow_le.trans (by rw [natDegree_ψ_three_eq_zero])
  have h_neg := natDegree_negPolynomial_le W
  refine (Polynomial.natDegree_mul_le).trans ?_
  omega

/-- **Y-natDegree of `(C(C a₁) · polyY - polyX) · C Ψ_3` ≤ 1** —
    first half of the INNER bracket in W.ω 3's formula. -/
theorem natDegree_INNER_first_term_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    ((Polynomial.C (Polynomial.C W.a₁) * W.toAffine.polynomialY -
        W.toAffine.polynomialX) * Polynomial.C W.Ψ₃).natDegree ≤ 1 := by
  have h_sub : ((Polynomial.C (Polynomial.C W.a₁) * W.toAffine.polynomialY -
      W.toAffine.polynomialX)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    exact max_le (natDegree_CC_a1_mul_polynomialY_le W) (natDegree_polynomialX_le W)
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_C]
  omega

/-- **Y-natDegree of `polynomial · (2 · polynomial + C Ψ₂Sq)` ≤ 4** —
    second half of the INNER bracket. -/
theorem natDegree_polynomial_mul_two_polynomial_plus_C_Ψ₂Sq_le
    {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) :
    (W.toAffine.polynomial *
      (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq)).natDegree ≤ 4 := by
  have h_poly : W.toAffine.polynomial.natDegree = 2 := W.toAffine.natDegree_polynomial
  have h_two_poly : (2 * W.toAffine.polynomial).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h2 : ((2 : (Polynomial R)[X])).natDegree = 0 := by
      norm_num [Polynomial.natDegree_natCast]
    omega
  have h_sum : (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [Polynomial.natDegree_C]; omega
  refine (Polynomial.natDegree_mul_le).trans ?_
  omega

/-- **Y-natDegree of `4 · polynomial · (2·polynomial + C Ψ₂Sq)` ≤ 4** —
    the second summand of INNER (with the leading 4·). -/
theorem natDegree_INNER_second_term_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    (4 * W.toAffine.polynomial *
      (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq)).natDegree ≤ 4 := by
  rw [show (4 : (Polynomial R)[X]) * W.toAffine.polynomial =
    W.toAffine.polynomial * 4 by ring]
  rw [show W.toAffine.polynomial * (4 : (Polynomial R)[X]) *
    (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq) =
    W.toAffine.polynomial *
      (4 * (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq)) by ring]
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [W.toAffine.natDegree_polynomial]
  have h_4mul : (4 * (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq)).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h4 : ((4 : (Polynomial R)[X])).natDegree = 0 := by
      norm_num [Polynomial.natDegree_natCast]
    rw [h4, Nat.zero_add]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have h2 : ((2 : (Polynomial R)[X])).natDegree = 0 := by
        norm_num [Polynomial.natDegree_natCast]
      rw [h2, Nat.zero_add, W.toAffine.natDegree_polynomial]
    · rw [Polynomial.natDegree_C]; omega
  omega

/-- **Y-natDegree of INNER ≤ 4**: the bracket in W.ω 3's formula. -/
theorem natDegree_INNER_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    ((Polynomial.C (Polynomial.C W.a₁) * W.toAffine.polynomialY -
        W.toAffine.polynomialX) * Polynomial.C W.Ψ₃ +
      4 * W.toAffine.polynomial *
        (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq)).natDegree ≤ 4 := by
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · exact (natDegree_INNER_first_term_le W).trans (by omega)
  · exact natDegree_INNER_second_term_le W

/-- **redInvarDenom_3 has Y-natDegree ≤ 1** (unconditional).

    The m=3 branch of redInvarDenom evaluates to
    `complEDS · complEDS · normEDS_4 = ψ_4`. -/
theorem natDegree_redInvarDenom_three_le {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) :
    (redInvarDenom W.ψ₂ (Polynomial.C W.Ψ₃)
      (Polynomial.C W.preΨ₄) 3).natDegree ≤ 1 := by
  have h : redInvarDenom W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) 3 =
      W.ψ 4 := by
    simp [redInvarDenom, complEDS_one]
  rw [h]
  exact natDegree_ψ_four_le W


/-- **`(W.ω 3).natDegree ≤ 5` via component natDegree witnesses** —
    composes the natDegree bound from individual summand bounds taken
    as hypotheses. The two remaining mathlib-API witnesses
    (redInvarDenom_3 explicit + complEDSAux₂_3 explicit) are taken
    parametric here; their unconditional discharge is the final
    bounded mathlib gap. -/
theorem natDegree_ω_three_le_via_component_witnesses
    {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R)
    (h_redInvar : (redInvarDenom W.ψ₂ (Polynomial.C W.Ψ₃)
      (Polynomial.C W.preΨ₄) 3).natDegree ≤ 1)
    (h_complEDSAux₂ : (complEDSAux₂ W.ψ₂ (Polynomial.C W.Ψ₃)
      (Polynomial.C W.preΨ₄) 3).natDegree ≤ 1) :
    (W.ω 3).natDegree ≤ 5 := by
  have h_INNER := natDegree_INNER_le W
  have h_negPoly := natDegree_negPolynomial_mul_psi_three_cubed_le W
  -- Goal after unfold: (redInvarDenom · INNER - complEDSAux₂ + negPolynomial · ψ_3^3).natDegree ≤ 5
  rw [show W.ω 3 = redInvarDenom W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) 3 *
      ((Polynomial.C (Polynomial.C W.a₁) * W.toAffine.polynomialY -
          W.toAffine.polynomialX) * Polynomial.C W.Ψ₃ +
        4 * W.toAffine.polynomial *
          (2 * W.toAffine.polynomial + Polynomial.C W.Ψ₂Sq)) -
      complEDSAux₂ W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) 3 +
      W.toAffine.negPolynomial * (W.ψ 3) ^ 3 from rfl]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · refine (Polynomial.natDegree_sub_le _ _).trans ?_
    refine max_le ?_ ?_
    · refine (Polynomial.natDegree_mul_le).trans ?_; omega
    · omega
  · omega

/-- **`OmegaThreeBasisHoldsReduced` discharge via natDegree bound**:
    given `(W.ω 3).natDegree ≤ 5`, the basis decomposition holds
    UNCONDITIONALLY (modulo the single mathlib-API natDegree bound).

    Composes `omega_ff_three_decomp_via_nat_degree_bound` (the K(E)-level
    sum decomposition) with `omega_ff_three_basis_decomp_via_witness_char_three`
    (the substantive composition shipped commit `2ff083b`). The natDegree
    bound becomes the single mathlib-API gap remaining for q=3 char=3
    unconditional. -/
theorem omegaThreeBasisHoldsReduced_via_nat_degree_bound
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 3]
    (h_deg : (W.ω 3).natDegree ≤ 5) :
    OmegaThreeBasisHoldsReduced W :=
  omega_ff_three_basis_decomp_via_witness_char_three W
    (omega_ff_three_decomp_via_nat_degree_bound W h_deg)

/-! ### preΨ_4 ≠ 0 cascade — q=3 unconditional close -/

/-- **(2 : K) ≠ 0 in char 3**. -/
theorem two_ne_zero_of_char_three {K' : Type*} [CommRing K'] [Nontrivial K'] [CharP K' 3] :
    (2 : K') ≠ 0 := by
  intro h
  have h3 : (3 : K') = 0 := CharP.cast_eq_zero K' 3
  have h1 : (1 : K') = 0 := by linear_combination h3 - h
  exact one_ne_zero h1

/-- **preΨ_4 ≠ 0 in char 3** — direct from mathlib's `preΨ₄_ne_zero` + `2 ≠ 0`. -/
theorem preΨ_4_ne_zero_of_char_three {K' : Type*} [CommRing K'] [Nontrivial K'] [CharP K' 3]
    (W : WeierstrassCurve K') : W.preΨ₄ ≠ 0 :=
  W.preΨ₄_ne_zero two_ne_zero_of_char_three

/-- **ψ_2 ≠ 0 in char 3**. -/
theorem ψ_2_ne_zero_of_char_three {K' : Type*} [CommRing K'] [Nontrivial K'] [CharP K' 3]
    (W : WeierstrassCurve K') : W.ψ₂ ≠ 0 := by
  show W.toAffine.polynomialY ≠ 0
  unfold WeierstrassCurve.Affine.polynomialY
  intro h
  -- Take coeff at degree 1: C(C 2) = 0, so C 2 = 0, so 2 = 0 — contradicting char 3.
  have h_coeff_1 := congrArg (Polynomial.coeff · 1) h
  simp only [Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_one, Polynomial.coeff_C, mul_one] at h_coeff_1
  -- After simp: C(2 : K') = 0 (or close to it)
  rw [if_neg (by decide : (1 : ℕ) ≠ 0), add_zero] at h_coeff_1
  rw [Polynomial.C_eq_zero] at h_coeff_1
  exact two_ne_zero_of_char_three h_coeff_1

/-- **(W.ψ 4) ≠ 0 in char 3** — `ψ_4 = C preΨ_4 · ψ_2`, both nonzero. -/
theorem ψ_four_ne_zero_of_char_three {K' : Type*} [CommRing K'] [Nontrivial K']
    [IsDomain K'] [CharP K' 3] (W : WeierstrassCurve K') :
    (W.ψ 4 : (Polynomial K')[X]) ≠ 0 := by
  rw [WeierstrassCurve.ψ_four]
  intro h
  rcases mul_eq_zero.mp h with h1 | h2
  · rw [Polynomial.C_eq_zero] at h1
    exact preΨ_4_ne_zero_of_char_three W h1
  · exact ψ_2_ne_zero_of_char_three W h2

/-- **(W.ψ 4)² ≠ 0 in char 3**. -/
theorem ψ_four_sq_ne_zero_of_char_three {K' : Type*} [CommRing K'] [Nontrivial K']
    [IsDomain K'] [CharP K' 3] (W : WeierstrassCurve K') :
    (W.ψ 4 : (Polynomial K')[X]) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (ψ_four_ne_zero_of_char_three W)

/-- **complEDSAux₂_3 = C preΨ_4² · ψ_2** in char 3 — explicit form via
    `complEDSAux₂_mul_b · ψ_2 = (ψ_4)²` + ψ_2 cancellation in domain. -/
theorem complEDSAux₂_three_eq_of_char_three {K' : Type*} [CommRing K'] [Nontrivial K']
    [IsDomain K'] [CharP K' 3] (W : WeierstrassCurve K') :
    complEDSAux₂ W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) 3 =
      (Polynomial.C W.preΨ₄) ^ 2 * W.ψ₂ := by
  have h_mul := complEDSAux₂_mul_b W.ψ₂ (Polynomial.C W.Ψ₃)
    (Polynomial.C W.preΨ₄) 3
  rw [show (3 - 2 : ℤ) = 1 from by decide,
      show (3 + 1 : ℤ) = 4 from by decide,
      normEDS_one, one_mul] at h_mul
  -- h_mul : complEDSAux₂_3 · ψ_2 = (normEDS ... 4)²
  -- normEDS ... 4 = W.ψ 4 = C preΨ_4 · ψ_2 (by definition + ψ_four)
  have h_norm_eq : normEDS W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) 4 =
      Polynomial.C W.preΨ₄ * W.ψ₂ := WeierstrassCurve.ψ_four W
  rw [h_norm_eq] at h_mul
  -- h_mul : complEDSAux₂_3 · ψ_2 = (C preΨ_4 · ψ_2)²
  have h_eq : complEDSAux₂ W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) 3 * W.ψ₂ =
      ((Polynomial.C W.preΨ₄) ^ 2 * W.ψ₂) * W.ψ₂ := by
    rw [h_mul]; ring
  exact mul_right_cancel₀ (ψ_2_ne_zero_of_char_three W) h_eq

/-- **complEDSAux₂_3 has Y-natDegree ≤ 1** in char 3 — UNCONDITIONAL.

    Via the explicit form `C preΨ_4² · ψ_2`: C preΨ_4² has Y-natDegree 0,
    ψ_2 has Y-natDegree ≤ 1, so the product has natDegree ≤ 1. -/
theorem natDegree_complEDSAux₂_three_le_of_char_three {K' : Type*} [CommRing K']
    [Nontrivial K'] [IsDomain K'] [CharP K' 3] (W : WeierstrassCurve K') :
    (complEDSAux₂ W.ψ₂ (Polynomial.C W.Ψ₃)
      (Polynomial.C W.preΨ₄) 3).natDegree ≤ 1 := by
  rw [complEDSAux₂_three_eq_of_char_three]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h_pre : ((Polynomial.C W.preΨ₄ : (Polynomial K')[X]) ^ 2).natDegree = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    refine Polynomial.natDegree_pow_le.trans ?_
    rw [Polynomial.natDegree_C]
  have h_psi2 := natDegree_ψ_2_le W
  omega

/-- **(W.ω 3).natDegree ≤ 5 UNCONDITIONAL in char 3**. -/
theorem natDegree_ω_three_le_of_char_three {K' : Type*} [CommRing K'] [Nontrivial K']
    [IsDomain K'] [CharP K' 3] (W : WeierstrassCurve K') :
    (W.ω 3).natDegree ≤ 5 :=
  natDegree_ω_three_le_via_component_witnesses W
    (natDegree_redInvarDenom_three_le W)
    (natDegree_complEDSAux₂_three_le_of_char_three W)

/-- **OmegaThreeBasisHoldsReduced UNCONDITIONAL in char 3** — composes the
    natDegree bound with `omegaThreeBasisHoldsReduced_via_nat_degree_bound`.

    This is the **q=3 char=3 BASIS DECOMPOSITION CLOSE** axiom-clean
    UNCONDITIONAL — the substantive q=3-specific witness for the bound chain. -/
theorem omegaThreeBasisHoldsReduced_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 3] :
    OmegaThreeBasisHoldsReduced W :=
  omegaThreeBasisHoldsReduced_via_nat_degree_bound W
    (natDegree_ω_three_le_of_char_three W)

/-- **x_gen cube-root existence for q=3 char=3** — UNCONDITIONAL on
    Worker C-side. Composes `Φ_three_mem_expand_three_char_three` and
    `ΨSq_three_mem_expand_three_char_three` (both axiom-clean) via
    `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`.

    This is the x-side half of the cube-root function for q=3 char=3,
    now unconditional axiom-clean. -/
theorem mulByInt_three_pullback_x_gen_cube_root_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 3]
    (h_card : Fintype.card K = 3) :
    ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) := by
  refine mulByInt_q_pullback_x_gen_qth_root_of_expand_witness W ?_ ?_ ?_
  · -- W.Φ (card K) ∈ expand K (card K)
    show W.Φ ((Fintype.card K : ℕ) : ℤ) ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K)))
    rw [h_card]
    exact_mod_cast Φ_three_mem_expand_three_char_three W
  · -- W.ΨSq (card K) ∈ expand K (card K)
    show W.ΨSq ((Fintype.card K : ℕ) : ℤ) ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K)))
    rw [h_card]
    exact_mod_cast ΨSq_three_mem_expand_three_char_three W
  · rw [h_card]; decide

/-- **x_gen square-root existence for q=2 char=2** — UNCONDITIONAL on the
    Worker C-side. Composes `Φ_two_mem_expand_two_char_two` and
    `ΨSq_two_mem_expand_two_char_two` (both axiom-clean) via
    `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`.

    This is the x-side half of the square-root function for q=2 char=2,
    mirroring the q=3 char=3 case (`mulByInt_three_pullback_x_gen_cube_root_unconditional`).
    Together with the q=2 char=2 y-side root (`y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
    + the basis-decomposition cascade), this gives both generators a
    q-th root in `K(E)`, so `Im([q]*) ⊆ Im(π*)` reduces to the generator
    case via `mulByInt_q_pullback_range_subset_frobenius_of_xy_subfield_witness`. -/
theorem mulByInt_two_pullback_x_gen_sq_root_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2) :
    ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) := by
  refine mulByInt_q_pullback_x_gen_qth_root_of_expand_witness W ?_ ?_ ?_
  · show W.Φ ((Fintype.card K : ℕ) : ℤ) ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K)))
    rw [h_card]
    exact_mod_cast Φ_two_mem_expand_two_char_two W
  · show W.ΨSq ((Fintype.card K : ℕ) : ℤ) ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K)))
    rw [h_card]
    exact_mod_cast ΨSq_two_mem_expand_two_char_two W
  · rw [h_card]; decide

/-! ### y_gen q=2 char=2 — discharge `h_psi_ne` (a₁·x_gen + a₃ ≠ 0)

The y-side squaring identity needs `aeval x_gen (C a₁ X + C a₃) ≠ 0` in
`KE`. Direct from `Δ_of_char_two`: if `a₁ X + a₃ = 0` as a polynomial,
then `a₁ = a₃ = 0`, forcing `Δ = 0` and contradicting `[IsElliptic]`. -/

/-- In char 2 with `[IsElliptic]`, the polynomial `a₁ X + a₃ ∈ K[X]` is
nonzero. Local copy of the same fact in `AdditionPullback/Frobenius.lean`,
inlined here to avoid pulling that import chain into `Verschiebung`. -/
private theorem a₁X_plus_a₃_polynomial_ne_zero_char_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2] :
    (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃ :
      Polynomial K) ≠ 0 := by
  intro h
  have h_a1 : W.toAffine.a₁ = 0 := by
    have := congr_arg (Polynomial.coeff · 1) h
    simpa using this
  have h_a3 : W.toAffine.a₃ = 0 := by
    have := congr_arg (Polynomial.coeff · 0) h
    simpa using this
  have h_delta : W.toAffine.Δ = 0 := by
    rw [WeierstrassCurve.Δ_of_char_two, h_a1, h_a3]; ring
  exact W.toAffine.isUnit_Δ.ne_zero h_delta

/-- `aeval x_gen (C a₁ X + C a₃) ≠ 0` in `KE` for char-2 elliptic `W`.
The `h_psi_ne` discharge for the squaring identity. Combines the
polynomial-level nonzero with injectivity of `K[X] → CoordinateRing → KE`. -/
private theorem aeval_x_gen_a₁X_plus_a₃_ne_zero_char_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2] :
    Polynomial.aeval (x_gen W)
        (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) ≠
      (0 : W.toAffine.FunctionField) := by
  -- Convert aeval x_gen p = algebraMap (K[X]) KE p, then use injectivity of the chain.
  have h_inj : Function.Injective
      (algebraMap (Polynomial K) W.toAffine.FunctionField) :=
    (IsFractionRing.injective W.toAffine.CoordinateRing
      W.toAffine.FunctionField).comp
      Affine.CoordinateRing.algebraMap_poly_injective
  have h_eq : Polynomial.aeval (x_gen W)
      (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) =
      algebraMap (Polynomial K) W.toAffine.FunctionField
        (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) := by
    show Polynomial.aeval
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))
      (Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃) = _
    rw [Polynomial.aeval_algebraMap_apply
          (A := W.toAffine.CoordinateRing) (B := W.toAffine.FunctionField),
        Polynomial.aeval_algebraMap_apply
          (A := Polynomial K) (B := W.toAffine.CoordinateRing),
        Polynomial.aeval_X_left_apply]
    rfl
  rw [h_eq]
  intro h0
  exact a₁X_plus_a₃_polynomial_ne_zero_char_two W
    (h_inj (h0.trans (map_zero _).symm))

/-- **y_gen square-root existence for q=2 char=2** — UNCONDITIONAL.
Composes the basis-decomposition chain
(`y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`) with the now-axiom-clean
discharges of its three witness hypotheses (`aeval_x_gen_a₁X_plus_a₃_ne_zero_char_two`
and two applications of `polyExpandRoot_aeval_pow_eq` /
`polyPowCardEq_of_finite`). Then transports the q-th root through
`mulByInt_q_pullback_y_gen_qth_root_of_witness`. -/
theorem mulByInt_two_pullback_y_gen_sq_root_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2) :
    ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) := by
  refine mulByInt_q_pullback_y_gen_qth_root_of_witness W ?_ ?_
  · -- Squaring identity discharges to give: ∃ g, g^q = mulByInt_y W q.
    refine ⟨y_qth_root_q_eq_2_char_2 W h_card, ?_⟩
    have h_pow := polyPowCardEq_of_finite (K := K)
    have h_psi_ne := aeval_x_gen_a₁X_plus_a₃_ne_zero_char_two W
    -- The polyExpandRoot pow-equalities, with h_card-substituted membership.
    -- Bridge `^Fintype.card K` to `^ 2` via a Fintype.card K = 2 substitution
    -- packaged as an explicit equality (avoids `rw` motive issues with the
    -- dependent `polyExpandRoot` proof argument).
    -- Use `Eq.mpr`/`▸` cast directly to bridge `^ Fintype.card K` to `^ 2`.
    -- The `polyExpandRoot ... (h_card ▸ ...)` proof argument prevents `rw [h_card]`
    -- from forming a valid motive; transport via the equality on the whole
    -- statement instead.
    have h_alpha_0 :
        (Polynomial.aeval (x_gen W)
          (polyExpandRoot (omega2_coupled_residual_char_two W)
            (h_card ▸ omega2_coupled_residual_mem_expand_two_char_two W : _))) ^ 2 =
        Polynomial.aeval (x_gen W) (omega2_coupled_residual_char_two W) := by
      simpa [h_card] using polyExpandRoot_aeval_pow_eq W (omega2_coupled_residual_char_two W)
        (h_card ▸ omega2_coupled_residual_mem_expand_two_char_two W : _) h_pow (x_gen W)
    have h_alpha_1 :
        (Polynomial.aeval (x_gen W)
          (polyExpandRoot (omega2_Y_coeff_char_two W)
            (h_card ▸ omega2_Y_coeff_mem_expand_two_char_two W : _))) ^ 2 =
        Polynomial.aeval (x_gen W) (omega2_Y_coeff_char_two W) := by
      simpa [h_card] using polyExpandRoot_aeval_pow_eq W (omega2_Y_coeff_char_two W)
        (h_card ▸ omega2_Y_coeff_mem_expand_two_char_two W : _) h_pow (x_gen W)
    rw [h_card]
    exact y_qth_root_squared_eq_mulByInt_y_two_of_witnesses W h_card h_psi_ne
      h_alpha_0 h_alpha_1
  · rw [h_card]; decide

/-! ### q=2 char=2 final inclusion: `Im([q]*) ⊆ Im(π*)`

Composes the just-shipped axiom-clean q-th-root constructions for x_gen
and y_gen with `mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness`
and `functionField_eq_intermediateField_adjoin_xy` to discharge the
inclusion **unconditionally** for q=2 char=2. -/

/-- **`Im([q]*) ⊆ Im(π*)` for q=2 char=2 (UNCONDITIONAL)**: the final
Silverman III.6.2 inclusion in fieldRange form, discharged axiom-clean
via the explicit q-th-root construction (Session 3 polynomial-side route).
Composes:
* `functionField_eq_intermediateField_adjoin_xy` (K(E) generated by x_gen, y_gen).
* `mulByInt_two_pullback_x_gen_sq_root_unconditional` (x-side q-th root).
* `mulByInt_two_pullback_y_gen_sq_root_unconditional` (y-side q-th root).
* `mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness` (the
  IntermediateField-level generator reduction).

This closes the qf_nonneg-side prerequisite for the q=2 char=2 case of
the Verschiebung construction. The q=3 char=3 analog is on the same
path; the y-side q-th root remains as the open piece for q=3. -/
theorem mulByInt_two_pullback_fieldRange_subset_frobenius_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 2]
    (h_card : Fintype.card K = 2) :
    ∀ z : W.toAffine.FunctionField,
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈
        (frobeniusIsog W).pullback.fieldRange :=
  mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness W
    (functionField_eq_intermediateField_adjoin_xy W)
    ((frobeniusIsog_pullback_mem_iff W _).mpr
      (mulByInt_two_pullback_x_gen_sq_root_unconditional W h_card))
    ((frobeniusIsog_pullback_mem_iff W _).mpr
      (mulByInt_two_pullback_y_gen_sq_root_unconditional W h_card))

end HasseWeil
