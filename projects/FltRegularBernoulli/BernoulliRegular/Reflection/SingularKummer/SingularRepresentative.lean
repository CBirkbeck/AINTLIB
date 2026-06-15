module

public import BernoulliRegular.Reflection.SingularKummer.SingularClassChoice

/-!
# Singular Kummer: representatives of singular quotient classes

This file unwraps a class in the singular quotient into an explicit singular
pair `(I, alpha)`.  The representative automatically satisfies
`(alpha) = I^p`, and nontriviality of the quotient class image in `A[p]`
transfers to the represented singular pair.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every singular quotient class has a singular-pair representative. -/
theorem exists_representative (p : ℕ)
    (x : SingularGroup (R := R) (K := K) p) :
    ∃ s : SingularPair R K p,
      (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) = x := by
  refine QuotientGroup.induction_on x ?_
  intro s
  exact ⟨s, rfl⟩

/-- A singular quotient class with nontrivial image in `A[p]` has a
singular-pair representative with nontrivial image in `A[p]`. -/
theorem exists_representative_of_nontrivial_class_image (p : ℕ)
    {x : SingularGroup (R := R) (K := K) p}
    (hx : singularGroupClassMapToPTorsion (R := R) (K := K) p x ≠ 1) :
    ∃ s : SingularPair R K p,
      (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) = x ∧
        classMapToPTorsion (R := R) (K := K) p s ≠ 1 ∧
          toPrincipalIdeal R K (generator s) = ideal s ^ p := by
  obtain ⟨s, hs⟩ := exists_representative (R := R) (K := K) p x
  refine ⟨s, hs, ?_, principal_eq_ideal_pow (R := R) (K := K) s⟩
  intro hs_trivial
  apply hx
  rw [← hs]
  exact hs_trivial

end SingularPair

namespace SingularLinearAction
namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Representative form of the singular-class choice theorem: from a
nontrivial projected component of `A[p]`, choose a singular pair `(I, alpha)`
whose quotient class lies in the projected singular component and whose class
image in `A[p]` is nontrivial. -/
theorem exists_representative_in_characterProjection_of_target_ne_bot
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
          (SingularKummer.SingularLinearAction.mulActionToAdditiveLinearAction (p := p) ρA)) ≠ ⊥) :
    ∃ s : SingularKummer.SingularPair R K p,
      Additive.ofMul
          (QuotientGroup.mk s : SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p) ∈
        LinearMap.range
          (CharacterProjection.characterProjection (p := p) i
            (SingularKummer.SingularLinearAction.mulActionToAdditiveLinearAction (p := p) ρS)) ∧
      SingularKummer.SingularPair.classMapToPTorsion (R := R) (K := K) p s ≠ 1 ∧
      toPrincipalIdeal R K (SingularKummer.SingularPair.generator s) =
        SingularKummer.SingularPair.ideal s ^ p := by
  obtain ⟨x, hx_component, hx_nontrivial⟩ :=
    exists_singular_class_in_characterProjection_of_target_ne_bot
      (R := R) (K := K) p i ρS ρA hρ hA
  obtain ⟨s, hs, hs_nontrivial, hs_singular⟩ :=
    SingularKummer.SingularPair.exists_representative_of_nontrivial_class_image
      (R := R) (K := K) p hx_nontrivial
  refine ⟨s, ?_, hs_nontrivial, hs_singular⟩
  rw [hs]
  exact hx_component

end SingularPair
end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
