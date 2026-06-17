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

/-- If a submodule `S` and the quotient `N ⧸ S` are both finite, then `N` is finite.
Used to propagate finiteness of kernels and cokernels through composites of
pseudo-isomorphisms. -/
private theorem finite_of_finite_quotient {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) [Finite S] [Finite (N ⧸ S)] : Finite N := by
  have h : Nat.card N = Nat.card S * Nat.card (N ⧸ S) :=
    Submodule.card_eq_card_quotient_mul_card S
  have hN : Nat.card N ≠ 0 := by
    rw [h]; exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  exact Nat.finite_of_card_ne_zero hN

variable {𝒪}
variable {M M' M'' : Type*} [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
  [AddCommGroup M'] [Module (IwasawaAlgebra 𝒪) M']
  [AddCommGroup M''] [Module (IwasawaAlgebra 𝒪) M'']

/-- Pseudo-isomorphism is reflexive: the identity map has zero kernel and trivial
cokernel. -/
theorem IsPseudoIso.refl (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M] :
    IsPseudoIso 𝒪 M M :=
  ⟨LinearMap.id, by rw [LinearMap.ker_id]; infer_instance,
    by rw [LinearMap.range_id]; infer_instance⟩

/-- Pseudo-isomorphism is transitive (compose the two maps; kernels and cokernels
stay finite). -/
theorem IsPseudoIso.trans (h : IsPseudoIso 𝒪 M M') (h' : IsPseudoIso 𝒪 M' M'') :
    IsPseudoIso 𝒪 M M'' := by
  obtain ⟨f₁, hk₁, hc₁⟩ := h
  obtain ⟨f₂, hk₂, hc₂⟩ := h'
  refine ⟨f₂ ∘ₗ f₁, ?_, ?_⟩
  · -- Finite kernel: `g : ker (f₂ ∘ₗ f₁) → ker f₂` via `f₁` has finite kernel
    -- (it injects into `ker f₁`) and finite range (inside `ker f₂`).
    have hmem : ∀ x : LinearMap.ker (f₂ ∘ₗ f₁), f₁ (x : M) ∈ LinearMap.ker f₂ := by
      rintro ⟨x, hx⟩
      rw [LinearMap.mem_ker] at hx ⊢
      simpa using hx
    set g : LinearMap.ker (f₂ ∘ₗ f₁) →ₗ[IwasawaAlgebra 𝒪] LinearMap.ker f₂ :=
      (f₁.domRestrict (LinearMap.ker (f₂ ∘ₗ f₁))).codRestrict (LinearMap.ker f₂) hmem with hg
    have hgapp : ∀ y : LinearMap.ker (f₂ ∘ₗ f₁), (g y : M') = f₁ (y : M) := fun _ => rfl
    haveI hkg : Finite (LinearMap.ker g) := by
      apply Finite.of_injective (β := LinearMap.ker f₁)
        fun x : LinearMap.ker g => ⟨(x.1 : M), by
          have hx : (g x.1 : M') = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
          rw [LinearMap.mem_ker, ← hgapp x.1]; exact hx⟩
      rintro a b hab
      have hM := congrArg (Subtype.val : LinearMap.ker f₁ → M) hab
      apply Subtype.ext
      apply Subtype.ext
      exact hM
    haveI : Finite (LinearMap.range g) := inferInstance
    haveI hqg : Finite (LinearMap.ker (f₂ ∘ₗ f₁) ⧸ LinearMap.ker g) :=
      Finite.of_equiv _ g.quotKerEquivRange.symm.toEquiv
    exact finite_of_finite_quotient (LinearMap.ker g)
  · -- Finite cokernel: `M'' ⧸ range (f₂ ∘ₗ f₁)` is an extension of `M'' ⧸ range f₂`
    -- (finite) by `(range f₂)/range (f₂ ∘ₗ f₁)`, itself a quotient of the finite
    -- `M' ⧸ range f₁` (the image of `f₂`).
    have hle : LinearMap.range (f₂ ∘ₗ f₁) ≤ LinearMap.range f₂ := by
      rw [LinearMap.range_comp]; exact LinearMap.map_le_range
    have hcond : LinearMap.range f₁ ≤ Submodule.comap f₂ (LinearMap.range (f₂ ∘ₗ f₁)) := by
      rw [LinearMap.range_comp]
      intro y hy
      rw [Submodule.mem_comap]
      exact Submodule.mem_map_of_mem hy
    haveI : Finite ((M'' ⧸ LinearMap.range (f₂ ∘ₗ f₁)) ⧸
        (LinearMap.range f₂).map (LinearMap.range (f₂ ∘ₗ f₁)).mkQ) :=
      Finite.of_equiv _ (Submodule.quotientQuotientEquivQuotient _ _ hle).symm.toEquiv
    haveI : Finite ((LinearMap.range f₂).map (LinearMap.range (f₂ ∘ₗ f₁)).mkQ) := by
      have hSeq : (Submodule.mapQ (LinearMap.range f₁) (LinearMap.range (f₂ ∘ₗ f₁)) f₂ hcond).range
          = (LinearMap.range f₂).map (LinearMap.range (f₂ ∘ₗ f₁)).mkQ :=
        Submodule.range_mapQ (LinearMap.range f₁) (LinearMap.range (f₂ ∘ₗ f₁)) f₂ hcond
      rw [← hSeq]
      exact Finite.of_surjective _ (LinearMap.surjective_rangeRestrict _)
    exact finite_of_finite_quotient
      ((LinearMap.range f₂).map (LinearMap.range (f₂ ∘ₗ f₁)).mkQ)

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
