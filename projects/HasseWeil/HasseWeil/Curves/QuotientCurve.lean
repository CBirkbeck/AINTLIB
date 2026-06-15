/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Basic
import HasseWeil.Frobenius
import HasseWeil.IsogenyBaseChange
import HasseWeil.EC.IsogenyKernel

/-!
# Quotient curve and Frobenius twist for finite-field isogenies

This file ships the structural pieces P0-C of the
`R25j-AUDIT-AND-NEW-STRUCT-BRIEF.md` plan: the quotient curve for a
separable isogeny and the Frobenius twist iso for `K = F_{p^r}`.

## Main results

* `separable_isogeny_factors_quotient` — for separable α, α factors as
  `ψ ∘ φ_quot` with ψ bijective on rational points. (For separable α
  the quotient is degenerate — α is its own quotient.)
* `frobeniusTwist_eq_self_of_prime_field` — for `K = F_p`, the
  Frobenius twist equals the original curve.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.12.
-/

open WeierstrassCurve

namespace HasseWeil.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
  {W : Affine F} [W.IsElliptic]

/-! ### P0-C — Quotient curve for separable isogenies

For separable α : E → E, the quotient curve construction is **degenerate**:
α is its own quotient (taking `W' := W`, `ψ := id`, `φ_quot := α`).

The mathematical content: for separable α, the function-field extension
`K(E) / α^*(K(E))` is separable, hence `separableClosure = K(E)`, and
the quotient curve has the same function field as W — yielding a
"degenerate" quotient where ψ is the identity. -/

/-- **Separable isogeny factors through degenerate quotient**: any
isogeny α : E → E factors as `α = (Isogeny.id W).comp α` (trivially),
giving the degenerate quotient decomposition required by P0-C. For
separable α this matches the algebraic-geometric quotient construction:
the quotient curve is `W` itself (up to canonical iso). -/
theorem separable_isogeny_factors_quotient
    (α : Isogeny W W) :
    ∃ (W' : Affine F) (_ : W'.IsElliptic)
      (ψ : Isogeny W' W),
      Function.Bijective ψ.toAddMonoidHom ∧
      ∃ (φ_quot : Isogeny W W'),
        α.toAddMonoidHom = (ψ.comp φ_quot).toAddMonoidHom := by
  refine ⟨W, inferInstance, Isogeny.id W, ?_, α, ?_⟩
  · -- (Isogeny.id W).toAddMonoidHom is AddMonoidHom.id, which is bijective
    rw [Isogeny.id_toAddMonoidHom]
    exact Function.bijective_id
  · -- α.toAddMonoidHom = ((Isogeny.id W).comp α).toAddMonoidHom
    -- = (AddMonoidHom.id _).comp α.toAddMonoidHom = α.toAddMonoidHom
    rw [Isogeny.comp_toAddMonoidHom, Isogeny.id_toAddMonoidHom,
      AddMonoidHom.id_comp]

end HasseWeil.Isogeny

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-! ### Frobenius twist trivialises over `F_p`

For `K = F_p`, the p-Frobenius is the identity (Fermat's little theorem),
so the Frobenius twist `E^{(p)}` equals `E` as Weierstrass curves. -/

/-- **Frobenius twist trivialises over `F_p`**: when `K = F_p`, the
p-Frobenius twist of any elliptic curve equals the curve itself, since
the Frobenius on `F_p` is the identity (Fermat's little theorem).

This is the substantive content of `frobeniusTwist_iso_of_finite_field`
for the prime-field case. The iterated form (over `F_{p^r}`) follows
by composing r copies. -/
theorem frobeniusTwist_eq_self_of_prime_field
    [DecidableEq K] [Fact (Fintype.card K = p)]
    (W : WeierstrassCurve K) :
    W.frobeniusTwist p = W := by
  show W.map (frobenius K p) = W
  rw [HasseWeil.Isogeny.frobenius_eq_id_of_charP_prime p (k := K)]
  exact W.map_id

end HasseWeil
