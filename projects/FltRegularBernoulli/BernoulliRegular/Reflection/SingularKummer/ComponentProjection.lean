module

public import BernoulliRegular.Reflection.SingularKummer.ComponentChoice

/-!
# Singular Kummer: component ranges under a surjective map

If a surjective homomorphism commutes with two endomorphisms, then it maps the
range of the source endomorphism onto the range of the target endomorphism.

For the singular-Kummer argument this is the elementary algebra behind component surjectivity once
the character component is realized as the range of the corresponding
projection operator.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ComponentProjection

variable {G H : Type*} [Group G] [Group H]

/-- A surjective homomorphism commuting with two endomorphisms maps the source
projection range onto the target projection range. -/
theorem map_range_eq_range_of_surjective_of_commute
    (φ : G →* H) (eG : G →* G) (eH : H →* H)
    (hφ : Function.Surjective φ)
    (hcomm : ∀ x : G, φ (eG x) = eH (φ x)) :
    eG.range.map φ = eH.range := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := hx
    exact ⟨φ a, (hcomm a).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hφ z
    exact ⟨eG x, ⟨x, rfl⟩, hcomm x⟩

open scoped nonZeroDivisors

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Singular-sequence specialization: commuting projection operators on `S`
and `A[p]` give a surjection from the projected singular component to the
projected class-group component. -/
theorem singular_map_range_eq_range_of_commute
    (p : ℕ)
    (eS :
      SingularPair.SingularGroup (R := R) (K := K) p →*
        SingularPair.SingularGroup (R := R) (K := K) p)
    (eA :
      SingularPair.classGroupPTorsion (R := R) p →*
        SingularPair.classGroupPTorsion (R := R) p)
    (hcomm : ∀ x : SingularPair.SingularGroup (R := R) (K := K) p,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (eS x) =
        eA (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x)) :
    eS.range.map (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p) =
      eA.range :=
  map_range_eq_range_of_surjective_of_commute
    (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p)
    eS eA
    (SingularPair.singularGroupClassMapToPTorsion_surjective (R := R) (K := K) p)
    hcomm

/-- If the projected `A[p]` component is nontrivial, then there is a singular
class in the projected singular component with nontrivial image. -/
theorem exists_singular_projection_lift_of_target_ne_bot
    (p : ℕ)
    (eS :
      SingularPair.SingularGroup (R := R) (K := K) p →*
        SingularPair.SingularGroup (R := R) (K := K) p)
    (eA :
      SingularPair.classGroupPTorsion (R := R) p →*
        SingularPair.classGroupPTorsion (R := R) p)
    (hcomm : ∀ x : SingularPair.SingularGroup (R := R) (K := K) p,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (eS x) =
        eA (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x))
    (hA : eA.range ≠ ⊥) :
    ∃ x : eS.range,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x.1 ≠ 1 :=
  ComponentChoice.exists_singular_lift_of_component_map_eq_of_ne_bot
    (R := R) (K := K) p eS.range eA.range
    (singular_map_range_eq_range_of_commute (R := R) (K := K) p eS eA hcomm)
    hA

end ComponentProjection

end SingularKummer
end Reflection
end BernoulliRegular

end
