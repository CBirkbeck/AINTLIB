module

public import BernoulliRegular.Reflection.SingularKummer.SingularPair

/-!
# Singular Kummer: equivariance of the singular exact sequence

This file proves that the pair-form singular exact sequence is equivariant
under every automorphism that preserves principal fractional ideals.

This is the algebraic input needed for the later `Delta`-component argument.
The actual cyclotomic `Delta`-action should instantiate
`PrincipalIdealPreservingEquiv` using the semilinear action of field
automorphisms on `𝓞_K` and its fractional ideals.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

namespace SingularPair

/-- An automorphism of fractional ideals and generators preserving principal
fractional ideals.

For the cyclotomic application, this is the datum supplied by an element of
`Delta`: it acts on fractional ideals and on `Kˣ`, and sends `(gamma)` to
`(sigma gamma)`. -/
structure PrincipalIdealPreservingEquiv where
  idealEquiv : (FractionalIdeal R⁰ K)ˣ ≃* (FractionalIdeal R⁰ K)ˣ
  unitEquiv : Kˣ ≃* Kˣ
  map_principal :
    ∀ gamma : Kˣ,
      idealEquiv (toPrincipalIdeal R K gamma) =
        toPrincipalIdeal R K (unitEquiv gamma)

namespace PrincipalIdealPreservingEquiv

variable {R K}
variable (A : PrincipalIdealPreservingEquiv R K)

/-- Principal fractional ideals are preserved as a subgroup. -/
theorem map_principalSubgroup :
    (toPrincipalIdeal R K).range.map A.idealEquiv =
      (toPrincipalIdeal R K).range := by
  ext I
  constructor
  · rintro ⟨J, ⟨gamma, rfl⟩, rfl⟩
    exact ⟨A.unitEquiv gamma, (A.map_principal gamma).symm⟩
  · rintro ⟨gamma, rfl⟩
    refine ⟨toPrincipalIdeal R K (A.unitEquiv.symm gamma), ?_, ?_⟩
    · exact ⟨A.unitEquiv.symm gamma, rfl⟩
    · change
        A.idealEquiv (toPrincipalIdeal R K (A.unitEquiv.symm gamma)) =
          toPrincipalIdeal R K gamma
      rw [A.map_principal, A.unitEquiv.apply_symm_apply]

/-- The induced automorphism of the ideal class group. -/
def classGroupEquiv : ClassGroup R ≃* ClassGroup R :=
  (ClassGroup.equiv (R := R) K).trans <|
    (QuotientGroup.congr
      (toPrincipalIdeal R K).range
      (toPrincipalIdeal R K).range
      A.idealEquiv
      A.map_principalSubgroup).trans
      (ClassGroup.equiv (R := R) K).symm

@[simp]
theorem classGroupEquiv_mk (I : (FractionalIdeal R⁰ K)ˣ) :
    A.classGroupEquiv (ClassGroup.mk (R := R) (K := K) I) =
      ClassGroup.mk (R := R) (K := K) (A.idealEquiv I) := by
  apply (ClassGroup.equiv (R := R) K).injective
  simp [classGroupEquiv, ClassGroup.equiv_mk]
  rfl

/-- The induced automorphism of `A[p]`. -/
def classGroupPTorsionEquiv (p : ℕ) :
    classGroupPTorsion (R := R) p ≃* classGroupPTorsion (R := R) p where
  toFun c := ⟨A.classGroupEquiv c.1, by
    calc
      A.classGroupEquiv c.1 ^ p = A.classGroupEquiv (c.1 ^ p) := by
        rw [map_pow]
      _ = 1 := by
        rw [show c.1 ^ p = 1 from c.2, map_one]⟩
  invFun c := ⟨A.classGroupEquiv.symm c.1, by
    calc
      A.classGroupEquiv.symm c.1 ^ p = A.classGroupEquiv.symm (c.1 ^ p) := by
        rw [map_pow]
      _ = 1 := by
        rw [show c.1 ^ p = 1 from c.2, map_one]⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp
  map_mul' c d := by
    apply Subtype.ext
    simp

@[simp]
theorem classGroupPTorsionEquiv_apply_coe (p : ℕ)
    (c : classGroupPTorsion (R := R) p) :
    (A.classGroupPTorsionEquiv p c : ClassGroup R) =
      A.classGroupEquiv c.1 :=
  rfl

/-- The induced automorphism of singular pairs. -/
def singularPairEquiv (p : ℕ) : SingularPair R K p ≃* SingularPair R K p where
  toFun s := ⟨⟨A.idealEquiv (ideal s), A.unitEquiv (generator s)⟩, by
    change toPrincipalIdeal R K (A.unitEquiv (generator s)) =
      A.idealEquiv (ideal s) ^ p
    rw [← A.map_principal, principal_eq_ideal_pow (R := R) (K := K) s, map_pow]⟩
  invFun s := ⟨⟨A.idealEquiv.symm (ideal s), A.unitEquiv.symm (generator s)⟩, by
    change toPrincipalIdeal R K (A.unitEquiv.symm (generator s)) =
      A.idealEquiv.symm (ideal s) ^ p
    have hprincipal :=
      A.map_principal (A.unitEquiv.symm (generator s))
    have hprincipal' :
        toPrincipalIdeal R K (A.unitEquiv.symm (generator s)) =
          A.idealEquiv.symm (toPrincipalIdeal R K (generator s)) := by
      apply A.idealEquiv.injective
      calc
        A.idealEquiv (toPrincipalIdeal R K (A.unitEquiv.symm (generator s))) =
            toPrincipalIdeal R K (A.unitEquiv (A.unitEquiv.symm (generator s))) := by
          rw [hprincipal]
        _ = toPrincipalIdeal R K (generator s) := by
          rw [A.unitEquiv.apply_symm_apply]
        _ = A.idealEquiv (A.idealEquiv.symm (toPrincipalIdeal R K (generator s))) := by
          rw [A.idealEquiv.apply_symm_apply]
    rw [hprincipal', principal_eq_ideal_pow (R := R) (K := K) s, map_pow]⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext <;> simp [ideal, generator]
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext <;> simp [ideal, generator]
  map_mul' s t := by
    apply Subtype.ext
    apply Prod.ext <;> simp [ideal, generator]

@[simp]
theorem singularPairEquiv_ideal (p : ℕ) (s : SingularPair R K p) :
    ideal (A.singularPairEquiv p s) = A.idealEquiv (ideal s) :=
  rfl

@[simp]
theorem singularPairEquiv_generator (p : ℕ) (s : SingularPair R K p) :
    generator (A.singularPairEquiv p s) = A.unitEquiv (generator s) :=
  rfl

@[simp]
theorem singularPairEquiv_principalPair (p : ℕ) (gamma : Kˣ) :
    A.singularPairEquiv p (principalPair (R := R) (K := K) p gamma) =
      principalPair (R := R) (K := K) p (A.unitEquiv gamma) := by
  apply Subtype.ext
  apply Prod.ext
  · change A.idealEquiv (toPrincipalIdeal R K gamma) =
      toPrincipalIdeal R K (A.unitEquiv gamma)
    exact A.map_principal gamma
  · change A.unitEquiv (gamma ^ p) = A.unitEquiv gamma ^ p
    simp

/-- Principal pairs are preserved as a subgroup. -/
theorem map_principalPairSubgroup (p : ℕ) :
    (principalPairSubgroup (R := R) (K := K) p).map (A.singularPairEquiv p) =
      principalPairSubgroup (R := R) (K := K) p := by
  ext s
  constructor
  · rintro ⟨t, ⟨gamma, rfl⟩, rfl⟩
    exact ⟨A.unitEquiv gamma, by simp⟩
  · rintro ⟨gamma, rfl⟩
    refine ⟨principalPair (R := R) (K := K) p (A.unitEquiv.symm gamma), ?_, ?_⟩
    · exact ⟨A.unitEquiv.symm gamma, rfl⟩
    · simp

/-- The induced automorphism of the singular quotient. -/
def singularGroupEquiv (p : ℕ) :
    SingularGroup (R := R) (K := K) p ≃*
      SingularGroup (R := R) (K := K) p :=
  QuotientGroup.congr
    (principalPairSubgroup (R := R) (K := K) p)
    (principalPairSubgroup (R := R) (K := K) p)
    (A.singularPairEquiv p)
    (A.map_principalPairSubgroup p)

@[simp]
theorem singularGroupEquiv_mk (p : ℕ) (s : SingularPair R K p) :
    A.singularGroupEquiv p
      (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) =
      (QuotientGroup.mk (A.singularPairEquiv p s) :
        SingularGroup (R := R) (K := K) p) :=
  rfl

/-- Fractional units are preserved by the automorphism. -/
def fractionalUnitEquiv :
    fractionalUnitSubgroup (R := R) (K := K) ≃*
      fractionalUnitSubgroup (R := R) (K := K) where
  toFun u := ⟨A.unitEquiv u.1, by
    change toPrincipalIdeal R K (A.unitEquiv u.1) = 1
    rw [← A.map_principal, u.2, map_one]⟩
  invFun u := ⟨A.unitEquiv.symm u.1, by
    change toPrincipalIdeal R K (A.unitEquiv.symm u.1) = 1
    apply A.idealEquiv.injective
    rw [A.map_principal, A.unitEquiv.apply_symm_apply, u.2, map_one]⟩
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp

@[simp]
theorem fractionalUnitEquiv_apply_coe
    (u : fractionalUnitSubgroup (R := R) (K := K)) :
    (A.fractionalUnitEquiv u : Kˣ) = A.unitEquiv u.1 :=
  rfl

@[simp]
theorem singularPairEquiv_unitPair (p : ℕ)
    (u : fractionalUnitSubgroup (R := R) (K := K)) :
    A.singularPairEquiv p (unitPair (R := R) (K := K) p u) =
      unitPair (R := R) (K := K) p (A.fractionalUnitEquiv u) := by
  apply Subtype.ext
  apply Prod.ext
  · change A.idealEquiv (1 : (FractionalIdeal R⁰ K)ˣ) = 1
    simp
  · rfl

/-- The unit map into the singular quotient is equivariant. -/
theorem unitToSingularGroup_equivariant (p : ℕ)
    (u : fractionalUnitSubgroup (R := R) (K := K)) :
    A.singularGroupEquiv p (unitToSingularGroup (R := R) (K := K) p u) =
      unitToSingularGroup (R := R) (K := K) p (A.fractionalUnitEquiv u) := by
  simp [unitToSingularGroup]

/-- The singular-pair map to `A[p]` is equivariant. -/
theorem classMapToPTorsion_equivariant (p : ℕ) (s : SingularPair R K p) :
    A.classGroupPTorsionEquiv p
        (classMapToPTorsion (R := R) (K := K) p s) =
      classMapToPTorsion (R := R) (K := K) p (A.singularPairEquiv p s) := by
  apply Subtype.ext
  change A.classGroupEquiv (ClassGroup.mk (R := R) (K := K) (ideal s)) =
    ClassGroup.mk (R := R) (K := K) (A.idealEquiv (ideal s))
  simp

/-- The singular quotient map `S → A[p]` is equivariant. -/
theorem singularGroupClassMapToPTorsion_equivariant (p : ℕ)
    (x : SingularGroup (R := R) (K := K) p) :
    A.classGroupPTorsionEquiv p
        (singularGroupClassMapToPTorsion (R := R) (K := K) p x) =
      singularGroupClassMapToPTorsion (R := R) (K := K) p
        (A.singularGroupEquiv p x) := by
  refine QuotientGroup.induction_on x ?_
  intro s
  simp [classMapToPTorsion_equivariant]

end PrincipalIdealPreservingEquiv

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
