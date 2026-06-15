module

public import BernoulliRegular.Reflection.SingularKummer.SingularLinearAction

/-!
# Singular Kummer: choosing the singular class in a character component

This file proves the final elementary choice step after component surjectivity:
if the projected target component of `A[p]` is nontrivial, then the matching
projected component of the singular group contains a class with nontrivial
image in `A[p]`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace LinearComponentChoice

variable {R M N : Type*} [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- Linear analogue of the component-lifting lemma.  If a linear map sends a
source submodule onto a nontrivial target submodule, then some element of the
source submodule has nonzero image. -/
theorem exists_lift_of_map_eq_of_ne_bot
    (f : M →ₗ[R] N) (S : Submodule R M) (T : Submodule R N)
    (hmap : S.map f = T) (hT : T ≠ ⊥) :
    ∃ x : S, f x.1 ≠ 0 := by
  haveI : Nontrivial T := (Submodule.nontrivial_iff_ne_bot).2 hT
  obtain ⟨y, hy_ne⟩ := exists_ne (0 : T)
  have hy_map : y.1 ∈ S.map f := by
    simp [hmap, y.2]
  obtain ⟨x, hxS, hx⟩ := hy_map
  refine ⟨⟨x, hxS⟩, ?_⟩
  intro hx_zero
  exact hy_ne (Subtype.ext <| hx.symm.trans hx_zero)

/-- Elementwise form of the linear component-lifting lemma. -/
theorem exists_mem_lift_with_nonzero_image_of_ne_bot
    (f : M →ₗ[R] N) (S : Submodule R M) (T : Submodule R N)
    (hmap : S.map f = T) (hT : T ≠ ⊥) :
    ∃ x : M, x ∈ S ∧ f x ∈ T ∧ f x ≠ 0 := by
  obtain ⟨x, hx_ne⟩ := exists_lift_of_map_eq_of_ne_bot f S T hmap hT
  refine ⟨x.1, x.2, ?_, hx_ne⟩
  rw [← hmap]
  exact ⟨x.1, x.2, rfl⟩

end LinearComponentChoice

namespace SingularLinearAction
namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- From a nontrivial projected component of `A[p]`, choose a singular class in
the matching projected component with nontrivial class-group image. -/
theorem exists_singular_class_in_characterProjection_of_target_ne_bot
    (p : ℕ) [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p ≃*
          SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.classGroupPTorsion (R := R) p ≃*
          SingularKummer.SingularPair.classGroupPTorsion (R := R) p)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p),
      SingularKummer.SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (ρS d x) =
        ρA d (SingularKummer.SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x))
    (hA :
      LinearMap.range
        (CharacterProjection.characterProjection (p := p) i
          (mulActionToAdditiveLinearAction (p := p) ρA)) ≠ ⊥) :
    ∃ s : SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p,
      Additive.ofMul s ∈
        LinearMap.range
          (CharacterProjection.characterProjection (p := p) i
            (mulActionToAdditiveLinearAction (p := p) ρS)) ∧
      SingularKummer.SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p s ≠ 1 := by
  let sourceComponent : Submodule (ZMod p)
      (Additive (SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)) :=
    LinearMap.range
      (CharacterProjection.characterProjection (p := p) i
        (mulActionToAdditiveLinearAction (p := p) ρS))
  let targetComponent : Submodule (ZMod p)
      (Additive (SingularKummer.SingularPair.classGroupPTorsion (R := R) p)) :=
    LinearMap.range
      (CharacterProjection.characterProjection (p := p) i
        (mulActionToAdditiveLinearAction (p := p) ρA))
  have hmap :
      sourceComponent.map
          (SingularKummer.SingularPair.singularGroupClassMapToPTorsionLinear
            (R := R) (K := K) p) =
        targetComponent :=
    singular_characterProjection_range_eq_range_of_multiplicative_equivariant
      (R := R) (K := K) p i ρS ρA hρ
  obtain ⟨x, hx_source, _hx_target, hx_ne⟩ :=
    LinearComponentChoice.exists_mem_lift_with_nonzero_image_of_ne_bot
      (SingularKummer.SingularPair.singularGroupClassMapToPTorsionLinear (R := R) (K := K) p)
      sourceComponent targetComponent hmap hA
  refine ⟨x.toMul, ?_, ?_⟩
  · exact hx_source
  · intro htrivial
    exact hx_ne (Additive.ext <| htrivial)

end SingularPair
end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
