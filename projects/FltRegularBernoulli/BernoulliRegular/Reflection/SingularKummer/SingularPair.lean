module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Singular Kummer: singular pairs

This file begins the formal singular-group construction in a choice-free form.

Instead of immediately quotienting singular numbers modulo global `p`-th
powers, we first use *singular pairs*

```text
(I, alpha),    (alpha) = I^p,
```

where `I` is an invertible fractional ideal and `alpha` is a nonzero element of
the fraction field.  Such a pair maps canonically to the class of `I`, and that
class is killed by `p`.

This is the formal core of the map from singular data to `A[p]`.
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

/-- A singular pair is a fractional ideal `I` together with a generator
`alpha` of `I^p`. -/
def singularPairSubgroup (p : ℕ) : Subgroup ((FractionalIdeal R⁰ K)ˣ × Kˣ) where
  carrier := {x | toPrincipalIdeal R K x.2 = x.1 ^ p}
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    change toPrincipalIdeal R K (x.2 * y.2) = (x.1 * y.1) ^ p
    rw [map_mul, hx, hy, mul_pow]
  inv_mem' := by
    intro x hx
    change toPrincipalIdeal R K x.2⁻¹ = x.1⁻¹ ^ p
    rw [map_inv, hx, inv_pow]

/-- The group of singular pairs `(I, alpha)` with `(alpha) = I^p`. -/
abbrev SingularPair (p : ℕ) : Type _ :=
  singularPairSubgroup R K p

namespace SingularPair

variable {R K}
variable {p : ℕ}

/-- The fractional ideal in a singular pair. -/
def ideal (s : SingularPair R K p) : (FractionalIdeal R⁰ K)ˣ :=
  s.1.1

/-- The nonzero generator in a singular pair. -/
def generator (s : SingularPair R K p) : Kˣ :=
  s.1.2

/-- The defining relation `(generator s) = (ideal s)^p`. -/
theorem principal_eq_ideal_pow (s : SingularPair R K p) :
    toPrincipalIdeal R K (generator s) = ideal s ^ p :=
  s.2

@[simp]
theorem ideal_one :
    ideal (R := R) (K := K) (p := p) 1 = 1 :=
  rfl

@[simp]
theorem generator_one :
    generator (R := R) (K := K) (p := p) 1 = 1 :=
  rfl

@[simp]
theorem ideal_mul (s t : SingularPair R K p) :
    ideal (s * t) = ideal s * ideal t :=
  rfl

@[simp]
theorem generator_mul (s t : SingularPair R K p) :
    generator (s * t) = generator s * generator t :=
  rfl

/-- Principal fractional ideals map to the trivial class. -/
@[simp]
theorem classGroup_mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk (R := R) (K := K) (toPrincipalIdeal R K x) = 1 := by
  apply (ClassGroup.equiv (R := R) K).injective
  rw [ClassGroup.equiv_mk]
  simp

/-- A singular pair maps to the class of its fractional ideal. -/
def classMap (p : ℕ) : SingularPair R K p →* ClassGroup R where
  toFun s := ClassGroup.mk (R := R) (K := K) (ideal s)
  map_one' := by
    simp [ideal]
  map_mul' := by
    intro s t
    simp [ideal]

@[simp]
theorem classMap_apply (s : SingularPair R K p) :
    classMap (R := R) (K := K) p s =
      ClassGroup.mk (R := R) (K := K) (ideal s) :=
  rfl

/-- The class attached to a singular pair is killed by `p`. -/
theorem classMap_pow_eq_one (s : SingularPair R K p) :
    classMap (R := R) (K := K) p s ^ p = 1 := by
  change (ClassGroup.mk (R := R) (K := K) (ideal s)) ^ p = 1
  rw [← map_pow (ClassGroup.mk (R := R) (K := K)) (ideal s) p]
  rw [← principal_eq_ideal_pow (R := R) (K := K) s]
  simp

/-- If a class is killed by `p`, then it is represented by a singular pair. -/
theorem exists_of_class_pow_eq_one {c : ClassGroup R} (hc : c ^ p = 1) :
    ∃ s : SingularPair R K p, classMap (R := R) (K := K) p s = c := by
  refine ClassGroup.induction (R := R) K
    (P := fun c => c ^ p = 1 →
      ∃ s : SingularPair R K p, classMap (R := R) (K := K) p s = c)
    ?_ c hc
  intro I hI
  have hI_principal :
      QuotientGroup.mk' (toPrincipalIdeal R K).range (I ^ p) = 1 := by
    have hmk :
        ClassGroup.mk (R := R) (K := K) (I ^ p) = 1 := by
      simpa [map_pow] using hI
    have hmapeq : ∀ J : (FractionalIdeal R⁰ K)ˣ,
        Units.mapEquiv (↑(FractionalIdeal.canonicalEquiv R⁰ K K)) J = J := fun J => by
      apply Units.ext
      rw [Units.coe_mapEquiv, FractionalIdeal.canonicalEquiv_self,
        RingEquiv.coe_mulEquiv_refl, MulEquiv.refl_apply]
    have hquot := congrArg (ClassGroup.equiv (R := R) K) hmk
    rw [ClassGroup.equiv_mk, map_one, hmapeq] at hquot
    exact hquot
  obtain ⟨alpha, halpha⟩ :=
    (QuotientGroup.eq_one_iff
      (N := (toPrincipalIdeal R K).range) (I ^ p)).1 hI_principal
  refine ⟨⟨⟨I, alpha⟩, ?_⟩, rfl⟩
  change toPrincipalIdeal R K alpha = I ^ p
  exact halpha

/-- The `p`-torsion subgroup of the class group. -/
abbrev classGroupPTorsion (p : ℕ) : Subgroup (ClassGroup R) :=
  (powMonoidHom p : ClassGroup R →* ClassGroup R).ker

/-- The singular-pair class map, with codomain restricted to `A[p]`. -/
def classMapToPTorsion (p : ℕ) :
    SingularPair R K p →* classGroupPTorsion (R := R) p where
  toFun s := ⟨classMap (R := R) (K := K) p s, by
    simpa [classGroupPTorsion] using classMap_pow_eq_one (R := R) (K := K) s⟩
  map_one' := by
    apply Subtype.ext
    simp [classMap]
  map_mul' := by
    intro s t
    apply Subtype.ext
    simp [classMap]

@[simp]
theorem classMapToPTorsion_apply_coe (s : SingularPair R K p) :
    (classMapToPTorsion (R := R) (K := K) p s : ClassGroup R) =
      ClassGroup.mk (R := R) (K := K) (ideal s) :=
  rfl

/-- Every `p`-torsion class is represented by a singular pair. -/
theorem classMapToPTorsion_surjective (p : ℕ) :
    Function.Surjective (classMapToPTorsion (R := R) (K := K) p) := by
  intro c
  obtain ⟨s, hs⟩ :=
    exists_of_class_pow_eq_one (R := R) (K := K) (p := p) (c := c.1)
      (show c.1 ^ p = 1 from c.2)
  exact ⟨s, Subtype.ext hs⟩

/-- Principal pairs `(gamma, gamma^p)`.  Quotienting by these pairs identifies
singular-pair representatives that differ by a global `p`-th power. -/
def principalPair (p : ℕ) : Kˣ →* SingularPair R K p where
  toFun gamma := ⟨⟨toPrincipalIdeal R K gamma, gamma ^ p⟩, by
    change toPrincipalIdeal R K (gamma ^ p) = (toPrincipalIdeal R K gamma) ^ p
    rw [map_pow]⟩
  map_one' := by
    apply Subtype.ext
    ext <;> simp
  map_mul' := by
    intro gamma delta
    apply Subtype.ext
    ext <;> simp [map_mul, mul_pow]

/-- The subgroup of principal pairs. -/
abbrev principalPairSubgroup (p : ℕ) : Subgroup (SingularPair R K p) :=
  (principalPair (R := R) (K := K) p).range

/-- The singular group in pair form: singular pairs modulo principal pairs. -/
abbrev SingularGroup (p : ℕ) : Type _ :=
  SingularPair R K p ⧸ principalPairSubgroup (R := R) (K := K) p

@[simp]
theorem classMapToPTorsion_principalPair (p : ℕ) (gamma : Kˣ) :
    classMapToPTorsion (R := R) (K := K) p
      (principalPair (R := R) (K := K) p gamma) = 1 := by
  apply Subtype.ext
  change ClassGroup.mk (R := R) (K := K) (toPrincipalIdeal R K gamma) = 1
  simp

/-- The class map from the singular group to `A[p]`. -/
def singularGroupClassMapToPTorsion (p : ℕ) :
    SingularGroup (R := R) (K := K) p →* classGroupPTorsion (R := R) p :=
  QuotientGroup.lift
    (principalPairSubgroup (R := R) (K := K) p)
    (classMapToPTorsion (R := R) (K := K) p)
    (by
      intro s hs
      obtain ⟨gamma, rfl⟩ := hs
      exact classMapToPTorsion_principalPair (R := R) (K := K) p gamma)

@[simp]
theorem singularGroupClassMapToPTorsion_mk (p : ℕ) (s : SingularPair R K p) :
    singularGroupClassMapToPTorsion (R := R) (K := K) p
      (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) =
        classMapToPTorsion (R := R) (K := K) p s :=
  rfl

/-- The singular-group class map is still surjective onto `A[p]`. -/
theorem singularGroupClassMapToPTorsion_surjective (p : ℕ) :
    Function.Surjective
      (singularGroupClassMapToPTorsion (R := R) (K := K) p) := by
  intro c
  obtain ⟨s, hs⟩ := classMapToPTorsion_surjective (R := R) (K := K) p c
  exact ⟨(QuotientGroup.mk s : SingularGroup (R := R) (K := K) p), by simpa using hs⟩

/-- Fractional units: elements of `Kˣ` whose principal fractional ideal is
the unit fractional ideal.  For rings of integers this is the image of the
global unit group in `Kˣ`. -/
abbrev fractionalUnitSubgroup : Subgroup Kˣ :=
  (toPrincipalIdeal R K).ker

/-- A fractional unit gives the singular pair `(1, u)`. -/
def unitPair (p : ℕ) : fractionalUnitSubgroup (R := R) (K := K) →*
    SingularPair R K p where
  toFun u := ⟨⟨1, u.1⟩, by
    change toPrincipalIdeal R K u.1 = (1 : (FractionalIdeal R⁰ K)ˣ) ^ p
    rw [u.2]
    simp⟩
  map_one' := by
    apply Subtype.ext
    ext <;> simp
  map_mul' := by
    intro u v
    apply Subtype.ext
    ext <;> simp

@[simp]
theorem unitPair_ideal (p : ℕ) (u : fractionalUnitSubgroup (R := R) (K := K)) :
    ideal (unitPair (R := R) (K := K) p u) = 1 :=
  rfl

@[simp]
theorem unitPair_generator (p : ℕ) (u : fractionalUnitSubgroup (R := R) (K := K)) :
    generator (unitPair (R := R) (K := K) p u) = u.1 :=
  rfl

/-- The map from fractional units to the singular quotient. -/
def unitToSingularGroup (p : ℕ) :
    fractionalUnitSubgroup (R := R) (K := K) →*
      SingularGroup (R := R) (K := K) p :=
  (QuotientGroup.mk' (principalPairSubgroup (R := R) (K := K) p)).comp
    (unitPair (R := R) (K := K) p)

@[simp]
theorem unitToSingularGroup_apply (p : ℕ)
    (u : fractionalUnitSubgroup (R := R) (K := K)) :
    unitToSingularGroup (R := R) (K := K) p u =
      (QuotientGroup.mk (unitPair (R := R) (K := K) p u) :
        SingularGroup (R := R) (K := K) p) :=
  rfl

@[simp]
theorem singularGroupClassMapToPTorsion_unitToSingularGroup
    (p : ℕ) (u : fractionalUnitSubgroup (R := R) (K := K)) :
    singularGroupClassMapToPTorsion (R := R) (K := K) p
      (unitToSingularGroup (R := R) (K := K) p u) = 1 := by
  apply Subtype.ext
  simp [unitToSingularGroup]

/-- A singular pair whose ideal part is principal is equal to a unit pair times
the corresponding principal pair. -/
theorem eq_unitPair_mul_principalPair_of_ideal_eq_principal
    (s : SingularPair R K p) {gamma : Kˣ}
    (hgamma : toPrincipalIdeal R K gamma = ideal s) :
    s =
      unitPair (R := R) (K := K) p
        ⟨generator s / gamma ^ p, by
          change toPrincipalIdeal R K (generator s / gamma ^ p) = 1
          rw [map_div, map_pow, hgamma, principal_eq_ideal_pow (R := R) (K := K) s]
          simp⟩ *
        principalPair (R := R) (K := K) p gamma := by
  apply Subtype.ext
  apply Prod.ext
  · change ideal s = 1 * toPrincipalIdeal R K gamma
    simp [hgamma]
  · change generator s = (generator s / gamma ^ p) * gamma ^ p
    simp

/-- The kernel of the singular-group class map is exactly the image of the
fractional-unit classes. -/
theorem singularGroupClassMapToPTorsion_ker_eq_unitToSingularGroup_range (p : ℕ) :
    (singularGroupClassMapToPTorsion (R := R) (K := K) p).ker =
      (unitToSingularGroup (R := R) (K := K) p).range := by
  apply le_antisymm
  · intro x hx
    revert hx
    refine QuotientGroup.induction_on x ?_
    intro s hs
    have hs_class :
        ClassGroup.mk (R := R) (K := K) (ideal s) = 1 :=
      congrArg Subtype.val hs
    have hprincipal_quot :
        QuotientGroup.mk' (toPrincipalIdeal R K).range (ideal s) = 1 := by
      have hquot := congrArg (ClassGroup.equiv (R := R) K) hs_class
      simpa [ClassGroup.equiv_mk] using hquot
    obtain ⟨gamma, hgamma⟩ :=
      (QuotientGroup.eq_one_iff
        (N := (toPrincipalIdeal R K).range) (ideal s)).1 hprincipal_quot
    let u : fractionalUnitSubgroup (R := R) (K := K) :=
      ⟨generator s / gamma ^ p, by
        change toPrincipalIdeal R K (generator s / gamma ^ p) = 1
        rw [map_div, map_pow, hgamma, principal_eq_ideal_pow (R := R) (K := K) s]
        simp⟩
    refine ⟨u, ?_⟩
    have hs_eq :
        s = unitPair (R := R) (K := K) p u *
          principalPair (R := R) (K := K) p gamma :=
      eq_unitPair_mul_principalPair_of_ideal_eq_principal
        (R := R) (K := K) (p := p) s hgamma
    rw [unitToSingularGroup_apply]
    rw [hs_eq, QuotientGroup.mk_mul]
    simp [principalPairSubgroup]
  · intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact MonoidHom.mem_ker.mpr
      (singularGroupClassMapToPTorsion_unitToSingularGroup (R := R) (K := K) p u)

/-- Exactness of the singular sequence at `S`: the kernel of `S → A[p]` is
the image of the unit classes. -/
theorem unitToSingularGroup_exact_singularGroupClassMapToPTorsion (p : ℕ) :
    Function.MulExact
      (unitToSingularGroup (R := R) (K := K) p)
      (singularGroupClassMapToPTorsion (R := R) (K := K) p) := by
  rw [MonoidHom.mulExact_iff]
  exact singularGroupClassMapToPTorsion_ker_eq_unitToSingularGroup_range
    (R := R) (K := K) p

/-- The pair-form singular exact sequence: unit classes map into the singular
group, the singular group maps onto `A[p]`, and the middle term is exact. -/
theorem singularGroup_pair_exact_and_surjective (p : ℕ) :
    Function.MulExact
        (unitToSingularGroup (R := R) (K := K) p)
        (singularGroupClassMapToPTorsion (R := R) (K := K) p) ∧
      Function.Surjective
        (singularGroupClassMapToPTorsion (R := R) (K := K) p) :=
  ⟨unitToSingularGroup_exact_singularGroupClassMapToPTorsion
      (R := R) (K := K) p,
    singularGroupClassMapToPTorsion_surjective (R := R) (K := K) p⟩

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
