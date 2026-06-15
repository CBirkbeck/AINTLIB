import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Isogenies via Function Field Extensions

We define isogenies between elliptic curves as injective `K`-algebra homomorphisms
on function fields, following Silverman III.4. The degree of an isogeny is the degree
of the corresponding field extension.

## Main Definitions

* `HasseWeil.Isogeny`: An isogeny from `E₁` to `E₂`, represented as an injective
  `K`-algebra homomorphism `K(E₂) →ₐ[K] K(E₁)` on function fields.
* `HasseWeil.Isogeny.degree`: The degree `[K(E₁) : φ*K(E₂)]`.

## Design Note

The degree is defined as `Module.finrank K(E₂) K(E₁)` where `K(E₁)` is given a
`K(E₂)`-algebra structure via the pullback `φ* : K(E₂) →ₐ[F] K(E₁)`. This avoids
working with subalgebra ranges and makes the tower law (degree multiplicativity)
a direct application of `Module.finrank_mul_finrank`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

variable (F : Type*) [Field F]

/-- An isogeny `φ : E₁ → E₂` between elliptic curves over a field `F`,
    represented by the pullback `φ* : K(E₂) →ₐ[F] K(E₁)` on function fields. -/
structure PullbackIsogeny (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic] where
  /-- The pullback `φ* : K(E₂) →ₐ[F] K(E₁)` on function fields. -/
  pullback : W₂.FunctionField →ₐ[F] W₁.FunctionField

namespace PullbackIsogeny

variable {F : Type*} [Field F]
variable {W₁ W₂ W₃ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- The pullback of an isogeny is injective: any algebra homomorphism from a field
    is injective because the kernel of a ring homomorphism from a field is trivial. -/
theorem pullback_injective (φ : PullbackIsogeny F W₁ W₂) :
    Function.Injective φ.pullback :=
  φ.pullback.toRingHom.injective

/-- An isogeny `φ : E₁ → E₂` makes `K(E₁)` into a `K(E₂)`-algebra via pullback. -/
@[reducible]
noncomputable def toAlgebra (φ : PullbackIsogeny F W₁ W₂) :
    Algebra W₂.FunctionField W₁.FunctionField :=
  φ.pullback.toRingHom.toAlgebra

/-- The degree of an isogeny, defined as `[K(E₁) : K(E₂)]` where `K(E₁)` is
    a `K(E₂)`-module via the pullback. -/
noncomputable def degree (φ : PullbackIsogeny F W₁ W₂) : ℕ :=
  @Module.finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra.toModule

set_option maxHeartbeats 400000 in
-- AlgHom.comp on FunctionField needs extra heartbeats for typeclass synthesis.
/-- Composition of isogenies corresponds to composition of pullbacks. -/
noncomputable def comp (ψ : PullbackIsogeny F W₂ W₃) (φ : PullbackIsogeny F W₁ W₂) :
    PullbackIsogeny F W₁ W₃ where
  pullback := φ.pullback.comp ψ.pullback

/-- The algebra map from (ψ∘φ)* factors through φ* and ψ*. -/
theorem comp_algebraMap_eq (ψ : PullbackIsogeny F W₂ W₃) (φ : PullbackIsogeny F W₁ W₂)
    (x : W₃.FunctionField) :
    (ψ.comp φ).pullback x = φ.pullback (ψ.pullback x) := rfl

set_option maxHeartbeats 800000 in
-- Degree multiplicativity needs extra heartbeats for the tower law with FunctionField.
/-- **Degree multiplicativity**: `deg(ψ ∘ φ) = deg(φ) · deg(ψ)`.
    Follows from the tower law for field extensions. -/
theorem comp_degree (ψ : PullbackIsogeny F W₂ W₃) (φ : PullbackIsogeny F W₁ W₂) :
    (ψ.comp φ).degree = φ.degree * ψ.degree := by
  unfold degree
  letI inst₁ : Algebra W₂.FunctionField W₁.FunctionField := φ.toAlgebra
  letI inst₂ : Algebra W₃.FunctionField W₂.FunctionField := ψ.toAlgebra
  letI inst₃ : Algebra W₃.FunctionField W₁.FunctionField := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Free W₂.FunctionField W₁.FunctionField :=
    Module.Free.of_divisionRing _ _
  rw [mul_comm]
  exact (Module.finrank_mul_finrank
    W₃.FunctionField W₂.FunctionField W₁.FunctionField).symm

end PullbackIsogeny

end HasseWeil
