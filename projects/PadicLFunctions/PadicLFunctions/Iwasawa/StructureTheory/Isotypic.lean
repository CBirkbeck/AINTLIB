import PadicLFunctions.Iwasawa.StructureTheory.CharIdeal
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.DirectSum.Module

/-!
# Equivariant isotypic decomposition and `Ch_{Λ(𝒢)}`  (S13-S5)

For the Galois group `𝒢 = H × Γ'` with `H = μ_{p-1}` of order prime to `p` and
`Γ' ≅ ℤ_p`, the group Iwasawa algebra splits as `Λ(𝒢) ≅ 𝒪_L[H] ⊗_{𝒪_L} Λ`
(realised here as `Λ[H] = MonoidAlgebra Λ H`).  Because `|H|` is invertible in
`𝒪_L` (prime to `p`), the orthogonal idempotents `e_ω = |H|⁻¹ Σ_a ω⁻¹(a)[a]`,
indexed by the characters `ω : H → 𝒪_L^×`, split every `Λ(𝒢)`-module into its
isotypic components `M = ⨁_ω M^{(ω)}`, each finitely generated and torsion over
`Λ`.  The equivariant characteristic ideal is `Ch_{Λ(𝒢)}(M) = ⨁_ω Ch_Λ(M^{(ω)})`.
(RJW TeX 3659–3676; CS06, Appendix A.1, lemma.)

**Field-extension caveat** (RJW TeX 3664): the character values `ω(a)` may force a
finite extension of `L`; the idempotents live over `𝒪_L` only after extending so
that `μ_{|H|} ⊆ 𝒪_L`.  We index characters by `H →* 𝒪ˣ` and assume the needed
roots of unity are present in `𝒪`.

## Main declarations

* `Iwasawa.IwasawaAlgebraGroup 𝒪 H` (notation `Λ⟦H⟧`): the group Iwasawa algebra
  `Λ(𝒢) = Λ[H]`.
* `Iwasawa.isotypicIdempotent`: the orthogonal idempotent `e_ω ∈ Λ(𝒢)` of a
  character (RJW TeX 3661).
* `Iwasawa.isotypicComponent` / `Iwasawa.isInternal_isotypicComponent`: the
  `ω`-components and the internal direct-sum decomposition `M = ⨁_ω M^{(ω)}`.
* `Iwasawa.charIdealGroup`: the equivariant characteristic ideal
  `Ch_{Λ(𝒢)}(M) = ⨁_ω Ch_Λ(M^{(ω)})`.
-/

noncomputable section

open DirectSum

namespace Iwasawa

variable (𝒪 : Type*) [CommRing 𝒪] (H : Type*) [CommGroup H] [Fintype H]

local notation "Λ" => IwasawaAlgebra 𝒪

/-- The **group Iwasawa algebra** `Λ(𝒢) = Λ[H] = MonoidAlgebra Λ H` for
`𝒢 = H × Γ'`.  Canonically `Λ(𝒢) ≅ 𝒪[H] ⊗_𝒪 Λ` (RJW TeX 3659). -/
abbrev IwasawaAlgebraGroup : Type _ := MonoidAlgebra (IwasawaAlgebra 𝒪) H

@[inherit_doc] scoped notation "Λ⟦" H "⟧" => IwasawaAlgebraGroup _ H

local notation "Λ𝒢" => IwasawaAlgebraGroup 𝒪 H

/-- The **isotypic idempotent** `e_ω = |H|⁻¹ Σ_{a ∈ H} ω⁻¹(a)·[a] ∈ Λ(𝒢)` attached
to a character `ω : H → 𝒪^×`.  Well-defined since `|H|` is invertible in `𝒪`
(prime-to-`p`).  (RJW TeX 3661.) -/
def isotypicIdempotent [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ) : Λ𝒢 :=
  sorry

/-- The idempotents `e_ω` are genuine idempotents: `e_ω² = e_ω`. -/
theorem isIdempotentElem_isotypicIdempotent [Invertible (Fintype.card H : 𝒪)]
    (ω : H →* 𝒪ˣ) : IsIdempotentElem (isotypicIdempotent 𝒪 H ω) := by
  sorry

/-- Orthogonality of the isotypic idempotents: `e_ω · e_ψ = 0` for `ω ≠ ψ`. -/
theorem isotypicIdempotent_orthogonal [Invertible (Fintype.card H : 𝒪)]
    {ω ψ : H →* 𝒪ˣ} (h : ω ≠ ψ) :
    isotypicIdempotent 𝒪 H ω * isotypicIdempotent 𝒪 H ψ = 0 := by
  sorry

/-- The **`ω`-isotypic component** `M^{(ω)} = e_ω · M` of a `Λ(𝒢)`-module. -/
def isotypicComponent (ω : H →* 𝒪ˣ) (M : Type*) [AddCommGroup M]
    [Module (IwasawaAlgebraGroup 𝒪 H) M] : Submodule (IwasawaAlgebraGroup 𝒪 H) M :=
  sorry

/-- **The equivariant isotypic decomposition** `M = ⨁_ω M^{(ω)}` (RJW TeX 3662–3666):
the isotypic components give an internal direct-sum decomposition of any
`Λ(𝒢)`-module, the idempotents `e_ω` being orthogonal and summing to `1`. -/
theorem isInternal_isotypicComponent [Invertible (Fintype.card H : 𝒪)]
    [DecidableEq (H →* 𝒪ˣ)]
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M] :
    DirectSum.IsInternal (fun ω : H →* 𝒪ˣ => isotypicComponent 𝒪 H ω M) := by
  sorry

/-- The **equivariant characteristic ideal** `Ch_{Λ(𝒢)}(M) = ⨁_ω Ch_Λ(M^{(ω)})`
(RJW TeX 3672–3676): assembled from the characteristic ideals (S13-S4) of the
isotypic components, each of which is finitely generated and torsion over `Λ`. -/
def charIdealGroup [Invertible (Fintype.card H : 𝒪)]
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M]
    (_hM : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M) :
    Ideal (IwasawaAlgebraGroup 𝒪 H) :=
  sorry

end Iwasawa
