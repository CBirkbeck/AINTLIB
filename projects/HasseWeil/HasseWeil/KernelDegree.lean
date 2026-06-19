import HasseWeil.Ramification
import Mathlib.FieldTheory.Finite.Basic

/-!
# Kernel-Degree Theorem and Frobenius Fixed Points

For elliptic curves over finite fields:
- Rational points = Frobenius fixed points = ker(1-π)
- For separable isogenies: #ker(φ) = deg(φ)

The first fact is pure group theory. The second requires ramification theory.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], Proposition III.4.10, V.1.1
-/

open WeierstrassCurve FiniteField

namespace HasseWeil

/-! ### Frobenius fixed points

Over `K = F_q`: the Frobenius `π : x ↦ x^q` acts as the identity on K-rational
coordinates (since `a^q = a` for `a ∈ F_q`). So every K-rational point is fixed
by π, and (1-π) kills exactly the K-rational points.

Formally: `Point.map (frobeniusAlgHom K K) = id` on `E(K)` because
`frobeniusAlgHom K K = AlgHom.id K K` (the Frobenius is the identity on `F_q`).
-/

section FrobeniusId

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- The Frobenius algebra homomorphism is the identity on `F_q` itself.
    This is because `a^q = a` for all `a ∈ F_q` (the defining property of `F_q`). -/
theorem frobeniusAlgHom_eq_id :
    frobeniusAlgHom K K = AlgHom.id K K := by
  apply AlgHom.ext; intro a
  simp [pow_card]

end FrobeniusId

/-! ### Group-theoretic fiber size

For any group homomorphism φ : G → H between abelian groups, all fibers over
points in the image have the same cardinality as ker(φ). This follows from
the bijection `φ⁻¹(Q) ≅ ker(φ)` via translation by a preimage of Q.
-/

section FiberSize

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
variable [Fintype G] [DecidableEq G] [DecidableEq H]
variable (φ : G →+ H)

/-- The fiber of a group homomorphism over any point in the image is in bijection
    with the kernel. -/
noncomputable def fiberEquivKer (Q : H) (P₀ : G) (hP₀ : φ P₀ = Q) :
    {P : G // φ P = Q} ≃ φ.ker := {
  toFun := fun ⟨P, hP⟩ ↦ ⟨P - P₀, by
    simp [AddMonoidHom.mem_ker, map_sub, hP, hP₀]⟩
  invFun := fun ⟨K, hK⟩ ↦ ⟨K + P₀, by
    simp [AddMonoidHom.mem_ker.mp hK, hP₀]⟩
  left_inv := fun ⟨P, _⟩ ↦ by simp
  right_inv := fun ⟨K, _⟩ ↦ by simp }

omit [DecidableEq G] in
/-- All fibers of a group homomorphism over points in the image have the same
    cardinality as the kernel. -/
theorem card_fiber_eq_card_ker (Q : H) (hQ : Q ∈ Set.range φ) :
    Fintype.card {P : G // φ P = Q} = Fintype.card φ.ker := by
  obtain ⟨P₀, hP₀⟩ := hQ
  exact Fintype.card_congr (fiberEquivKer φ Q P₀ hP₀)

end FiberSize

end HasseWeil
