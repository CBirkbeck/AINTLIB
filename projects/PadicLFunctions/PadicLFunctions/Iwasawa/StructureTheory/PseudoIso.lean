import PadicLFunctions.Iwasawa.StructureTheory.IwasawaAlgebra

/-!
# Pseudo-isomorphism of Λ-modules  (S13-S2)

Two finitely generated `Λ`-modules are *pseudo-isomorphic*, written `M ~ M'`, when
they differ only by finite pieces.  Following RJW TeX 3631–3635 (verbatim: a
homomorphism `M → M'` "with finite kernel and cokernel"), we take the single-map
characterisation: there is a `Λ`-linear `f : M → M'` with finite kernel and finite
cokernel.  On the class of finitely generated *torsion* `Λ`-modules this is an
equivalence relation; **it is not symmetric in general** (Washington §13.2,
Warning) — symmetry needs the finite-generation+torsion hypotheses.

## Main declarations

* `Iwasawa.IsPseudoIso M M'`: `∃ f : M →ₗ[Λ] M', Finite (ker f) ∧ Finite (coker f)`
  (RJW TeX 3631).
* `Iwasawa.IsPseudoIso.refl` / `.trans`: reflexivity and transitivity.
* `Iwasawa.IsPseudoIso.symm`: symmetry **on finitely generated torsion modules**
  (the restriction is essential — Washington §13.2 Warning).
-/

noncomputable section

namespace Iwasawa

variable (𝒪 : Type*) [CommRing 𝒪]

local notation "Λ" => IwasawaAlgebra 𝒪

/-- A `Λ`-linear map with finite kernel and finite cokernel — a **pseudo-isomorphism**.
Two `Λ`-modules `M`, `M'` are pseudo-isomorphic, `M ~ M'`, if such a map `M → M'`
exists (RJW TeX 3631, "finite kernel and cokernel"). -/
def IsPseudoIso (M M' : Type*) [AddCommGroup M] [Module Λ M]
    [AddCommGroup M'] [Module Λ M'] : Prop :=
  ∃ f : M →ₗ[Λ] M', Finite (LinearMap.ker f) ∧ Finite (M' ⧸ LinearMap.range f)

variable {𝒪}
variable {M M' M'' : Type*} [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
  [AddCommGroup M'] [Module (IwasawaAlgebra 𝒪) M']
  [AddCommGroup M''] [Module (IwasawaAlgebra 𝒪) M'']

/-- Pseudo-isomorphism is reflexive: the identity map has zero kernel and trivial
cokernel. -/
theorem IsPseudoIso.refl (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M] :
    IsPseudoIso 𝒪 M M := by
  sorry

/-- Pseudo-isomorphism is transitive (compose the two maps; kernels and cokernels
stay finite). -/
theorem IsPseudoIso.trans (h : IsPseudoIso 𝒪 M M') (h' : IsPseudoIso 𝒪 M' M'') :
    IsPseudoIso 𝒪 M M'' := by
  sorry

/-- **Symmetry on finitely generated torsion modules** (Washington §13.2): for
finitely generated torsion `Λ`-modules, `M ~ M'` implies `M' ~ M`.  This fails for
general `Λ`-modules — pseudo-isomorphism is *not* a symmetric relation without
these hypotheses (Washington §13.2, Warning). -/
theorem IsPseudoIso.symm [Module.Finite (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M']
    (hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M)
    (hM' : Module.IsTorsion (IwasawaAlgebra 𝒪) M')
    (h : IsPseudoIso 𝒪 M M') :
    IsPseudoIso 𝒪 M' M := by
  sorry

end Iwasawa
