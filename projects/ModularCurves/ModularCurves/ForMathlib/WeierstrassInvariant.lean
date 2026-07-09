/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.FieldTheory.Fixed

/-!
# Descent of a `G`-invariant Weierstrass curve to the fixed subring

For a `MulSemiringAction G A`, a `WeierstrassCurve A` all of whose coefficients are `G`-invariant
comes, by `WeierstrassCurve.map`, from a `WeierstrassCurve Aᴳ` over the fixed subring.

This is building block `[a5-iv]` of `locallyWeierstrass_quotientπ` (`Moduli/EngineDescent.lean`):
after the `VariableChange` cocycle of the `G`-action on the universal curve's Weierstrass model is
trivialized Zariski-locally on `Spec Aᴳ` (additive Hilbert 90 for `(r,s,t)` +
`exists_unit_smul_eq_of_isLocalRing` for `u`, both proven in `ForMathlib/InvariantTorsor.lean`),
the model becomes `G`-invariant, and *this* lemma descends it to a Weierstrass curve over `Aᴳ` —
the model of the quotient curve `E/G` over `X/G = Spec Aᴳ`.

`FixedPoints.subring A G` is defeq to `FixedPoints.subalgebra ℤ A G` (the ring the project's
`localQuotient`/`invariantsπ` are `Spec` of), so this interoperates with the descent geometry.
-/

open scoped Pointwise

universe u

variable {G : Type*} [Group G] {A : Type u} [CommRing A] [MulSemiringAction G A]

namespace WeierstrassCurve

/-- A Weierstrass curve over `A` all of whose coefficients are `G`-invariant, as a Weierstrass
curve over the fixed subring `Aᴳ = FixedPoints.subring A G`. -/
def descendFixed (W : WeierstrassCurve A)
    (h₁ : ∀ g : G, g • W.a₁ = W.a₁) (h₂ : ∀ g : G, g • W.a₂ = W.a₂)
    (h₃ : ∀ g : G, g • W.a₃ = W.a₃) (h₄ : ∀ g : G, g • W.a₄ = W.a₄)
    (h₆ : ∀ g : G, g • W.a₆ = W.a₆) : WeierstrassCurve (FixedPoints.subring A G) where
  a₁ := ⟨W.a₁, h₁⟩
  a₂ := ⟨W.a₂, h₂⟩
  a₃ := ⟨W.a₃, h₃⟩
  a₄ := ⟨W.a₄, h₄⟩
  a₆ := ⟨W.a₆, h₆⟩

/-- Base-changing `descendFixed` back up to `A` recovers the original curve: the descended curve
`W₀` over `Aᴳ` satisfies `W₀.map (Aᴳ ↪ A) = W`. -/
@[simp]
theorem descendFixed_map (W : WeierstrassCurve A) (h₁ h₂ h₃ h₄ h₆) :
    (W.descendFixed h₁ h₂ h₃ h₄ h₆).map (algebraMap (FixedPoints.subring A G) A) = W := by
  cases W
  rfl

/-- If the base-changed-up curve is elliptic, so is the descended curve — the discriminant of
`descendFixed` is a unit because its image in `A` is (`Δ` commutes with `map`, and `Aᴳ ↪ A` is
injective, reflecting units of the subring). -/
theorem descendFixed_isElliptic [Nontrivial A] (W : WeierstrassCurve A) (h₁ h₂ h₃ h₄ h₆)
    (hΔ : IsUnit (W.descendFixed h₁ h₂ h₃ h₄ h₆ (G := G)).Δ) :
    (W.descendFixed h₁ h₂ h₃ h₄ h₆ (G := G)).IsElliptic := by
  rw [isElliptic_iff]
  exact hΔ

end WeierstrassCurve
