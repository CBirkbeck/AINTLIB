import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-!
# Route 2A — fibres of point-map endomorphisms as kernel cosets (keystone foundation)

The multiplicity-free geometric divisor pullback `β*((Q)) = Σ_{βP=Q} (P)` (separable case, used by
both the Weil-pairing construction and the separable adjoint, Silverman III.8) is summed over the
**fibre** `{P : βP = Q}`. This file ships the group-theoretic foundation: a fibre of a point-map
endomorphism is a coset of the kernel, hence finite when the kernel is finite.

This is the point-map (`AddMonoidHom`) form of the project's `EC.Isogeny` fibre machinery — the
level at which the Weil pairing and the pullback divisor operate.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.4 (fibres of an isogeny are cosets of
the kernel).
-/

namespace HasseWeil.WeilPairing

set_option linter.unusedSectionVars false

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- **Fibre as a kernel coset.** Given `f P₀ = Q`, the fibre `{P : f P = Q}` is in canonical
bijection with `ker f` via `P ↦ P − P₀`. -/
def fiberEquivKer (f : W.Point →+ W.Point) {P₀ Q : W.Point} (hP₀ : f P₀ = Q) :
    {P : W.Point // f P = Q} ≃ f.ker where
  toFun := fun ⟨P, hP⟩ => ⟨P - P₀, by rw [AddMonoidHom.mem_ker, map_sub, hP, hP₀, sub_self]⟩
  invFun := fun ⟨T, hT⟩ => ⟨P₀ + T, by rw [map_add, hP₀, (AddMonoidHom.mem_ker).mp hT, add_zero]⟩
  left_inv := fun ⟨P, hP⟩ => by simp
  right_inv := fun ⟨T, hT⟩ => by simp

/-- **Fibres are finite when the kernel is.** -/
theorem fiber_finite (f : W.Point →+ W.Point) (h : Finite f.ker) (Q : W.Point) :
    Finite {P : W.Point // f P = Q} := by
  rcases Classical.em (∃ P₀, f P₀ = Q) with ⟨P₀, hP₀⟩ | hempty
  · exact Finite.of_equiv _ (fiberEquivKer f hP₀).symm
  · haveI : IsEmpty {P : W.Point // f P = Q} := ⟨fun ⟨P, hP⟩ => hempty ⟨P, hP⟩⟩
    infer_instance

/-- **Fibre cardinality = kernel cardinality** (for a nonempty fibre). The constant fibre size that
makes `deg = #ker` for a separable isogeny (Silverman III.4.10c). -/
theorem fiber_card_eq_ker_card (f : W.Point →+ W.Point) {P₀ Q : W.Point} (hP₀ : f P₀ = Q) :
    Nat.card {P : W.Point // f P = Q} = Nat.card f.ker :=
  Nat.card_eq_of_bijective _ (fiberEquivKer f hP₀).bijective

end HasseWeil.WeilPairing
