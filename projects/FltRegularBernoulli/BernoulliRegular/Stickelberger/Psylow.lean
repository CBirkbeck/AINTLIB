module

public import BernoulliRegular.Characters
public import BernoulliRegular.Stickelberger.Annihilation
public import BernoulliRegular.Stickelberger.Eigenspaces
public import Mathlib.GroupTheory.Sylow

/-!
# The `p`-Sylow part of the cyclotomic class group

This file fixes a Sylow `p`-subgroup of a cyclotomic class group and packages its
character-tagged and boundary components. It also restricts the Stickelberger annihilation
statement to the chosen Sylow subgroup.

## Main definitions

* `CyclotomicClassGroupPSylow`: the chosen Sylow subgroup as a type.
* `CyclotomicClassGroupPSylowComponent`: a character-tagged subgroup.
* `OddComponentBernoulliAnnihilation`: the odd-component annihilation certificate.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField Pointwise nonZeroDivisors

namespace BernoulliRegular

-- The accessor API intentionally retains the section's ambient instances.
set_option linter.unusedSectionVars false

section PSylow

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

/-- A fixed Sylow `p`-subgroup of the class group of the cyclotomic field. -/
def cyclotomicClassGroupPSylow : Sylow p (ClassGroup (𝓞 L)) :=
  default

/-- The chosen Sylow subgroup as a subgroup of the full class group. -/
abbrev cyclotomicClassGroupPSylowSubgroup : Subgroup (ClassGroup (𝓞 L)) :=
  (cyclotomicClassGroupPSylow (p := p) (L := L) : Subgroup (ClassGroup (𝓞 L)))

/-- The chosen Sylow subgroup, used as a type. -/
abbrev CyclotomicClassGroupPSylow : Type _ :=
  cyclotomicClassGroupPSylowSubgroup (p := p) (L := L)

/-- Coercing the Sylow identity gives the class-group identity. -/
@[simp]
lemma cyclotomicClassGroupPSylow_one_coe :
    ((1 : CyclotomicClassGroupPSylow (p := p) (L := L)) : ClassGroup (𝓞 L)) = 1 :=
  rfl

/-- Sylow elements are equal when their class-group coercions are equal. -/
lemma cyclotomicClassGroupPSylow_ext
    {x y : CyclotomicClassGroupPSylow (p := p) (L := L)}
    (h : (x : ClassGroup (𝓞 L)) = y) :
    x = y :=
  Subtype.ext h

/-- Equality to one in the Sylow subgroup is detected in the class group. -/
lemma cyclotomicClassGroupPSylow_eq_one_iff
    (x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
    x = 1 ↔ (x : ClassGroup (𝓞 L)) = 1 :=
  Subtype.ext_iff

/-- A character-tagged subgroup of the chosen Sylow subgroup. -/
structure CyclotomicClassGroupPSylowComponent where
  character : MulChar (ZMod p)ˣ ℚ
  subgroup : Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L))

namespace CyclotomicClassGroupPSylowComponent

variable {p L}

instance : CoeOut (CyclotomicClassGroupPSylowComponent (p := p) (L := L))
    (Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L))) :=
  ⟨subgroup⟩

/-- The underlying type of a declared component. -/
abbrev Carrier (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) : Type _ :=
  C.subgroup

/-- Coercing the component identity gives the Sylow identity. -/
@[simp]
lemma one_coe (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) :
    ((1 : C.Carrier) : CyclotomicClassGroupPSylow (p := p) (L := L)) = 1 :=
  rfl

/-- Component elements are equal when their class-group coercions are equal. -/
lemma ext {C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)}
    {x y : C.Carrier}
    (h : ((x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
        ClassGroup (𝓞 L)) = y) :
    x = y :=
  Subtype.ext (cyclotomicClassGroupPSylow_ext (p := p) (L := L) h)

/-- Equality to one in a component is detected in the class group. -/
lemma eq_one_iff (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L))
    (x : C.Carrier) :
    x = 1 ↔
      (((x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
          ClassGroup (𝓞 L)) = 1) := by
  simp only [Subtype.ext_iff, one_coe, cyclotomicClassGroupPSylow_one_coe]

end CyclotomicClassGroupPSylowComponent

/-- The Stickelberger class-group action restricted to the chosen Sylow subgroup. -/
def stickelbergerPSylowClassAction
    (hp_odd : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    CyclotomicClassGroupPSylow (p := p) (L := L) :=
  ⟨characterSideStickelbergerClassAction (p := p) (L := L)
      (stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ),
    by
      rw [stickelbergerCharacterCoefficientGroupRingTarget_annihilates_primeClass
        (p := p) (L := L) hp_odd hχ]
      exact Subgroup.one_mem _⟩

/-- The restricted Stickelberger class-group action is trivial. -/
theorem stickelbergerPSylowClassAction_eq_one
    (hp_odd : p ≠ 2) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    stickelbergerPSylowClassAction (p := p) (L := L) hp_odd χ hχ = 1 := by
  rw [cyclotomicClassGroupPSylow_eq_one_iff]
  exact stickelbergerCharacterCoefficientGroupRingTarget_annihilates_primeClass
    (p := p) (L := L) hp_odd hχ

/-- A component element trivial in the full class group is trivial in its component. -/
theorem pSylowComponent_eq_one_of_class_eq_one
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) {x : C.Carrier}
    (h : ((x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
        ClassGroup (𝓞 L)) = 1) :
    x = 1 :=
  (CyclotomicClassGroupPSylowComponent.eq_one_iff C x).2 h

/-- Trivial boundary components `A₀` and `A₁` of the chosen Sylow subgroup. -/
structure CyclotomicClassGroupBoundaryComponents where
  componentZero : Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L))
  componentOne : Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L))
  componentZero_eq_bot : componentZero = ⊥
  componentOne_eq_bot : componentOne = ⊥

namespace CyclotomicClassGroupBoundaryComponents

variable {p L}

/-- The `A₀` boundary component. -/
abbrev A0 (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L)) :
    Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L)) :=
  B.componentZero

/-- The `A₁` boundary component. -/
abbrev A1 (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L)) :
    Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L)) :=
  B.componentOne

/-- The `A₀` component is trivial. -/
theorem A0_eq_bot (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L)) :
    B.A0 = ⊥ :=
  B.componentZero_eq_bot

/-- The `A₁` component is trivial. -/
theorem A1_eq_bot (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L)) :
    B.A1 = ⊥ :=
  B.componentOne_eq_bot

/-- Every element of a subgroup equal to `⊥` is the identity. -/
lemma eq_one_of_mem_bot
    {H : Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L))}
    (hH : H = ⊥) (x : H) :
    x = 1 :=
  Subtype.ext <| Subgroup.mem_bot.mp (by simpa only [hH] using x.2)

/-- Elementwise form of `A₀ = 1`: every element of the boundary component is
the identity. -/
theorem A0_eq_one (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L))
    (x : B.A0) :
    x = 1 :=
  eq_one_of_mem_bot (p := p) (L := L) B.A0_eq_bot x

/-- Elementwise form of `A₁ = 1`: every element of the boundary component is
the identity. -/
theorem A1_eq_one (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L))
    (x : B.A1) :
    x = 1 :=
  eq_one_of_mem_bot (p := p) (L := L) B.A1_eq_bot x

end CyclotomicClassGroupBoundaryComponents

/-- The complex Dirichlet character induced by a rational unit-group character. -/
def complexUnitMulCharDirichlet (χ : MulChar (ZMod p)ˣ ℚ) : DirichletCharacter ℂ p :=
  (unitMulCharDirichlet p χ).ringHomComp (Rat.castHom ℂ)

/-- The induced complex Dirichlet character is nontrivial when the original character is. -/
lemma complexUnitMulCharDirichlet_ne_one {χ : MulChar (ZMod p)ˣ ℚ} (hχ : χ ≠ 1) :
    complexUnitMulCharDirichlet p χ ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (f := Rat.castHom ℂ) Rat.cast_injective).mpr
    (unitMulCharDirichlet_ne_one (p := p) hχ)

/-- The rational Bernoulli scalar attached to the `χ`-eigenspace. -/
def pSylowBernoulliScalar (χ : MulChar (ZMod p)ˣ ℚ) : ℚ :=
  BernoulliGen (unitMulCharDirichlet p χ⁻¹) 1

/-- The Bernoulli projection formula and class-group annihilation for an odd component. -/
structure OddComponentBernoulliAnnihilation
    (hp_odd : p ≠ 2) (χ : MulChar (ZMod p)ˣ ℚ)
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) where
  component_character : C.character = χ
  odd : IsOddUnitCharacter (p := p) χ
  projection_formula :
    charIdempotent χ * stickelbergerElement p =
      pSylowBernoulliScalar (p := p) χ • charIdempotent χ
  sylow_class_action_eq_one :
    stickelbergerPSylowClassAction (p := p) (L := L) hp_odd
        (complexUnitMulCharDirichlet p χ)
        (complexUnitMulCharDirichlet_ne_one (p := p)
          (IsOddUnitCharacter.ne_one (p := p) odd)) =
      1

/-- Constructs the Bernoulli annihilation certificate for an odd component. -/
theorem oddComponentBernoulliAnnihilation
    (hp_odd : p ≠ 2) {χ : MulChar (ZMod p)ˣ ℚ}
    (hχ_odd : IsOddUnitCharacter (p := p) χ)
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L))
    (hC : C.character = χ) :
    OddComponentBernoulliAnnihilation (p := p) (L := L) hp_odd χ C where
  component_character := hC
  odd := hχ_odd
  projection_formula := by
    simpa only [pSylowBernoulliScalar] using
      charIdempotent_mul_stickelbergerElement_eq_BernoulliGen
        (p := p) (χ := χ) (IsOddUnitCharacter.ne_one (p := p) hχ_odd)
  sylow_class_action_eq_one :=
    stickelbergerPSylowClassAction_eq_one
      (p := p) (L := L) hp_odd
      (complexUnitMulCharDirichlet_ne_one (p := p)
        (IsOddUnitCharacter.ne_one (p := p) hχ_odd))

end PSylow

end BernoulliRegular

end
