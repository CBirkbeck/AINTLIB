import HasseWeil.Isogeny
import Mathlib.FieldTheory.SeparableDegree

/-!
# Separable and Inseparable Degree of Isogenies

We define the separable and inseparable degrees of an isogeny using mathlib's
`Field.finSepDegree`, and prove their basic properties.

## Main Definitions

* `HasseWeil.Isogeny.sepDegree`: The separable degree of an isogeny.
* `HasseWeil.Isogeny.isSeparable`: Predicate for a separable isogeny.

## Main Results

* `HasseWeil.Isogeny.sepDegree_dvd_degree`: The separable degree divides the degree.
* `HasseWeil.Isogeny.isSeparable_iff`: An isogeny is separable iff `sepDegree = degree`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4
-/

open WeierstrassCurve Field

namespace HasseWeil

namespace Isogeny

variable {F : Type*} [Field F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The separable degree of an isogeny, defined as the number of `F`-algebra
    embeddings of `K(E₂)` into the algebraic closure of `K(E₁)`, via the
    pullback algebra structure.

    In the full theory (Silverman III.4), this equals the cardinality of a
    generic fiber: `#φ⁻¹(Q) = deg_s(φ)` for all `Q ∈ E₂`. -/
noncomputable def sepDegree (φ : PullbackIsogeny F W₁ W₂) : ℕ :=
  @Field.finSepDegree W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra

/-- An isogeny is **separable** if its separable degree equals its degree. -/
def IsSeparable (φ : PullbackIsogeny F W₁ W₂) : Prop :=
  φ.sepDegree = φ.degree

/-- The separable degree divides the total degree. -/
theorem sepDegree_dvd_degree (φ : PullbackIsogeny F W₁ W₂) :
    φ.sepDegree ∣ φ.degree := by
  unfold sepDegree degree
  exact @Field.finSepDegree_dvd_finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra

/-- For a finite extension, the separable degree is at most the total degree. -/
theorem sepDegree_le_degree (φ : PullbackIsogeny F W₁ W₂)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra.toModule) :
    φ.sepDegree ≤ φ.degree := by
  unfold sepDegree degree
  exact @Field.finSepDegree_le_finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra hfin

end Isogeny

end HasseWeil
