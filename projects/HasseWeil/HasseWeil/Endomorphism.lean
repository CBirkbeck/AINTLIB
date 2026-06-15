import HasseWeil.Basic

/-!
# Endomorphism Degree and Trace (Isogeny-based, following Silverman)

Following Silverman III.4–6, we define the trace of an endomorphism isogeny.
The degree is computed from the pullback via `Module.finrank`, as defined in
`Basic.lean`.

## Architecture

Silverman's End(E) consists of algebraic endomorphisms. We model these as
`Isogeny E E` (from Basic.lean), which carries:
- `pullback : K(E₂) →ₐ[F] K(E₁)` (the pullback on function fields)
- `toAddMonoidHom : E₁.Point →+ E₂.Point` (the map on rational points)

Injectivity of the pullback is derived automatically (`Isogeny.pullback_injective`).

The degree is *computed* as `[K(E₁) : φ*K(E₂)]` via `Module.finrank`.
The degree of `mulByInt E n` is `(n²).toNat` (Sutherland Theorem 6.9).

## Key Definitions

- `isogTrace`: The trace of an endomorphism, `tr(α) = 1 + deg(α) - deg(1-α)`.
- `isogOneSub`: The isogeny `1 - α`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4–6, V.1
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Isogeny arithmetic -/

section IsogArith

variable {E : Affine F} [E.IsElliptic]

/-! **[2026-05-28 placeholder grind]** The general-`α` placeholders `isogOneSub α`
and `isogSmulSub α r s` (both `pullback := AlgHom.id`, giving a false degree 1)
were deleted, along with their lemmas `isogOneSub_toAddMonoidHom`,
`isogOneSub_mulByInt_hom`, `isogSmulSub_toAddMonoidHom`. There is no genuine
function-field pullback for a general `1 − α` / `r·α − s` in the project, so
these are kept witness-parametric at use sites instead. The concrete scalar
cases `isogOneSub_mulByInt` (= `[1−n]`) and `isogSmulSub_mulByInt` (= `[rm−s]`)
below ARE genuine (real division-polynomial pullback via `mulByInt`). -/

end IsogArith

/-! ### Concrete pullbacks for scalar isogenies

When `α = [m]` (multiplication by m), the isogenies `1 - [m]` and `r·[m] - s`
reduce to multiplication by a single integer:
- `1 - [m] = [1 - m]`
- `r·[m] - s·[1] = [r·m - s]`

In these cases we can provide concrete pullbacks using `mulByInt_pullbackAlgHom`,
which is constructed from division polynomials in `MulByIntPullback.lean`. -/

section ScalarPullbacks

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]

/-- `1 - [n]` as `[1-n]` with a concrete pullback from division polynomials.

    Since `[1] - [n] = [1-n]` in the endomorphism ring, this isogeny has the same
    pullback as `mulByInt W (1-n)`. For `1 - n ≠ 0`, the pullback is
    `mulByInt_pullbackAlgHom W (1-n)` (constructed via division polynomials).
    For `1 - n = 0` (i.e., n = 1), it is the identity on K(E), corresponding
    to the zero map `[0]`. -/
noncomputable def isogOneSub_mulByInt (n : ℤ) : Isogeny W.toAffine W.toAffine :=
  mulByInt W (1 - n)

@[simp] theorem isogOneSub_mulByInt_pullback (n : ℤ) :
    (isogOneSub_mulByInt (W := W) n).pullback = (mulByInt W (1 - n)).pullback := rfl

/-- The degree of `isogOneSub_mulByInt n` equals that of `mulByInt W (1-n)`. -/
theorem isogOneSub_mulByInt_degree (n : ℤ) :
    (isogOneSub_mulByInt (W := W) n).degree = (mulByInt W (1 - n)).degree := rfl

/-- `r·[m] - s` as `[r·m - s]` with a concrete pullback from division polynomials.

    Since `r·[m] - s·[1] = [r·m - s]` in the endomorphism ring, this isogeny has the
    same pullback as `mulByInt W (r * m - s)`. -/
noncomputable def isogSmulSub_mulByInt (m r s : ℤ) : Isogeny W.toAffine W.toAffine :=
  mulByInt W (r * m - s)

@[simp] theorem isogSmulSub_mulByInt_pullback (m r s : ℤ) :
    (isogSmulSub_mulByInt (W := W) m r s).pullback =
      (mulByInt W (r * m - s)).pullback := rfl

/-- The degree of `isogSmulSub_mulByInt m r s` equals that of `mulByInt W (r*m - s)`. -/
theorem isogSmulSub_mulByInt_degree (m r s : ℤ) :
    (isogSmulSub_mulByInt (W := W) m r s).degree = (mulByInt W (r * m - s)).degree := rfl

end ScalarPullbacks

/-! ### The trace of an endomorphism isogeny -/

section Trace

variable {E : Affine F} [E.IsElliptic]

/-- The trace of an endomorphism isogeny α, defined by
    `tr(α) = 1 + deg(α) - deg(1 - α)`.

    The isogeny `1 - α` must be supplied with its degree.
    For `α = [n]`, we have `1 - α = [1-n]` with degree `(1-n)²`,
    giving `tr([n]) = 1 + n² - (1-n)² = 2n`.

    Reference: Silverman III.8, Sutherland Lecture 7. -/
noncomputable def isogTrace (α : Isogeny E E) (one_sub_α : Isogeny E E) : ℤ :=
  1 + (α.degree : ℤ) - (one_sub_α.degree : ℤ)

/-- The trace of `[n]` is `2n` (for `n ≠ 0` and `1-n ≠ 0`). -/
theorem isogTrace_mulByInt (n : ℤ) (hn : n ≠ 0) (hn1 : 1 - n ≠ 0) :
    isogTrace (mulByInt E n) (mulByInt E (1 - n)) = 2 * n := by
  unfold isogTrace
  rw [mulByInt_degree _ _ hn, mulByInt_degree _ _ hn1]
  have h1 : 0 ≤ n ^ 2 := sq_nonneg n
  have h2 : 0 ≤ (1 - n) ^ 2 := sq_nonneg (1 - n)
  rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
  ring

end Trace

/-! ### Degree quadratic form for mulByInt (specific case of Silverman III.6.3)

For `α = [m]` and `isogSmulSub_mulByInt m r s = [r·m - s]`, we get:

  `deg([r·m - s]) = m²·r² - 2m·r·s + s² = (deg [m])·r² - tr([m])·r·s + s²`

which gives the III.6.3 identity unconditionally for the mulByInt case. -/

section DegreeQuadraticMulByInt

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]

/-- **T-III-6-3 (unconditional mulByInt case)**: the degree quadratic
    formula holds for `α = [m]`: `deg([r·m - s]) = m²r² - 2m·r·s + s²`. -/
theorem degree_quadratic_mulByInt (m r s : ℤ) (hm : m ≠ 0) (hm1 : 1 - m ≠ 0)
    (h_ne : r * m - s ≠ 0) :
    ((isogSmulSub_mulByInt (W := W) m r s).degree : ℤ) =
      ((mulByInt W.toAffine m).degree : ℤ) * r ^ 2
      - isogTrace (mulByInt W.toAffine m) (mulByInt W.toAffine (1 - m)) * r * s
      + s ^ 2 := by
  rw [isogSmulSub_mulByInt_degree, mulByInt_degree _ _ h_ne,
    mulByInt_degree _ _ hm, isogTrace_mulByInt m hm hm1]
  have h1 : 0 ≤ m ^ 2 := sq_nonneg m
  have h2 : 0 ≤ (r * m - s) ^ 2 := sq_nonneg (r * m - s)
  rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
  ring

/-- **Degree quadratic form non-negativity for mulByInt**: for any r, s ∈ ℤ
    (with appropriate non-degeneracy), the degree of `[r·m - s]` is
    non-negative. This is a direct consequence of degree being a ℕ. -/
theorem degree_quadratic_mulByInt_nonneg (m r s : ℤ) (hm : m ≠ 0) (hm1 : 1 - m ≠ 0)
    (h_ne : r * m - s ≠ 0) :
    0 ≤ ((mulByInt W.toAffine m).degree : ℤ) * r ^ 2
      - isogTrace (mulByInt W.toAffine m) (mulByInt W.toAffine (1 - m)) * r * s
      + s ^ 2 := by
  rw [← degree_quadratic_mulByInt m r s hm hm1 h_ne]
  exact Int.natCast_nonneg _

end DegreeQuadraticMulByInt

end HasseWeil
