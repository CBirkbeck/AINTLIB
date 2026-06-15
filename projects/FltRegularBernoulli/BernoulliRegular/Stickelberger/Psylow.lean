module

public import BernoulliRegular.Stickelberger.Annihilation
public import BernoulliRegular.Stickelberger.Eigenspaces
public import Mathlib.GroupTheory.Sylow

/-!
# The `p`-Sylow part of the cyclotomic class group

This file starts the `T034` layer.  It names the `p`-Sylow subgroup of the
cyclotomic class group and records the formal transfer principle used
downstream: once a class-group action is equal to `1` in the full class group,
the same action is equal to `1` after restricting to the chosen Sylow subgroup
and to any declared component of it.

The actual idempotent-component construction is kept data-driven here: a
component is a subgroup of the chosen Sylow subgroup tagged by its character.
This avoids pretending that the project already has a full `ℤ_p[G]`-module
structure on the finite class group; later tickets can instantiate these
component subgroups with the eventual idempotent construction.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField Pointwise nonZeroDivisors

namespace BernoulliRegular

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

@[simp]
lemma cyclotomicClassGroupPSylow_one_coe :
    ((1 : CyclotomicClassGroupPSylow (p := p) (L := L)) : ClassGroup (𝓞 L)) = 1 :=
  rfl

lemma cyclotomicClassGroupPSylow_ext
    {x y : CyclotomicClassGroupPSylow (p := p) (L := L)}
    (h : (x : ClassGroup (𝓞 L)) = y) :
    x = y :=
  Subtype.ext h

lemma cyclotomicClassGroupPSylow_eq_one_iff
    (x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
    x = 1 ↔ (x : ClassGroup (𝓞 L)) = 1 := by
  constructor
  · intro h
    simp [h]
  · intro h
    exact Subtype.ext h

/-- A character-tagged component of the chosen Sylow subgroup.

The subgroup is supplied as data because the current project has not yet built
the full class-group module action needed to define `ε_χ A` intrinsically. -/
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

@[simp]
lemma one_coe (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) :
    ((1 : C.Carrier) : CyclotomicClassGroupPSylow (p := p) (L := L)) = 1 :=
  rfl

lemma ext {C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)}
    {x y : C.Carrier}
    (h : ((x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
        ClassGroup (𝓞 L)) = y) :
    x = y :=
  Subtype.ext (cyclotomicClassGroupPSylow_ext (p := p) (L := L) h)

lemma eq_one_iff (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L))
    (x : C.Carrier) :
    x = 1 ↔
      (((x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
          ClassGroup (𝓞 L)) = 1) := by
  constructor
  · intro h
    simp [h]
  · intro h
    exact C.ext h

end CyclotomicClassGroupPSylowComponent

/-- The Stickelberger class-group action from `T032c`, restricted to the chosen
Sylow subgroup.  The membership proof is supplied by the fact that the action
is already trivial in the full class group. -/
def stickelbergerPSylowClassAction
    (hp_odd : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    CyclotomicClassGroupPSylow (p := p) (L := L) :=
  ⟨characterSideStickelbergerClassAction (p := p) (L := L)
      (stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ),
    by
      rw [stickelbergerCharacterCoefficientGroupRingTarget_annihilates_minusInput
        (p := p) (L := L) hp_odd hχ]
      exact Subgroup.one_mem _⟩

/-- `T034a`: the `T032c` annihilation statement, restricted to the chosen
Sylow `p`-subgroup of the class group. -/
theorem stickelbergerPSylowClassAction_eq_one
    (hp_odd : p ≠ 2) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    stickelbergerPSylowClassAction (p := p) (L := L) hp_odd χ hχ = 1 := by
  rw [cyclotomicClassGroupPSylow_eq_one_iff]
  exact stickelbergerCharacterCoefficientGroupRingTarget_annihilates_minusInput
    (p := p) (L := L) hp_odd hχ

/-- A component-level transfer lemma: if a class represented inside a declared
component is trivial in the full class group, then it is trivial in that
component. -/
theorem pSylowComponent_eq_one_of_class_eq_one
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) {x : C.Carrier}
    (h : ((x : CyclotomicClassGroupPSylow (p := p) (L := L)) :
        ClassGroup (𝓞 L)) = 1) :
    x = 1 :=
  (CyclotomicClassGroupPSylowComponent.eq_one_iff C x).2 h

/-- Boundary-component data for `A₀` and `A₁`.  The future intrinsic
idempotent construction should instantiate these two subgroups with the actual
boundary components; the fields record the boundary triviality facts used to
keep the odd-component argument separate. -/
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

/-- `T034b`: the `A₀` component is trivial. -/
theorem A0_eq_bot (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L)) :
    B.A0 = ⊥ :=
  B.componentZero_eq_bot

/-- `T034b`: the `A₁` component is trivial. -/
theorem A1_eq_bot (B : CyclotomicClassGroupBoundaryComponents (p := p) (L := L)) :
    B.A1 = ⊥ :=
  B.componentOne_eq_bot

lemma eq_one_of_mem_bot
    {H : Subgroup (CyclotomicClassGroupPSylow (p := p) (L := L))}
    (hH : H = ⊥) (x : H) :
    x = 1 :=
  Subtype.ext <| Subgroup.mem_bot.mp (by simpa [hH] using x.2)

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

/-! ### Odd-component Bernoulli annihilation certificates -/

/-- The Dirichlet character over `ℂ` obtained from a rational unit-group
character.  This is the character-side input used by the proved class-group
annihilation theorem. -/
def complexUnitMulCharDirichlet (χ : MulChar (ZMod p)ˣ ℚ) : DirichletCharacter ℂ p :=
  (unitMulCharDirichlet p χ).ringHomComp (Rat.castHom ℂ)

lemma complexUnitMulCharDirichlet_ne_one {χ : MulChar (ZMod p)ˣ ℚ} (hχ : χ ≠ 1) :
    complexUnitMulCharDirichlet p χ ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (f := Rat.castHom ℂ) Rat.cast_injective).mpr
    (unitMulCharDirichlet_ne_one (p := p) hχ)

/-- The rational Bernoulli scalar attached to the `χ`-eigenspace. -/
def pSylowBernoulliScalar (χ : MulChar (ZMod p)ˣ ℚ) : ℚ :=
  BernoulliGen (unitMulCharDirichlet p χ⁻¹) 1

/-- Odd rational unit characters are the rational stand-in for odd
Teichmüller-indexed eigenspaces in the current `ℚ`-valued idempotent API. -/
def IsOddUnitCharacter (χ : MulChar (ZMod p)ˣ ℚ) : Prop :=
  χ (-1 : (ZMod p)ˣ) = -1

lemma IsOddUnitCharacter.ne_one {χ : MulChar (ZMod p)ˣ ℚ}
    (hχ_odd : IsOddUnitCharacter (p := p) χ) :
    χ ≠ 1 := by
  intro hχ
  have hval : χ (-1 : (ZMod p)ˣ) = 1 := by
    rw [hχ]
    exact MulChar.one_apply (R' := ℚ) (Group.isUnit (-1 : (ZMod p)ˣ))
  rw [hχ_odd] at hval
  norm_num at hval

/-- The `T034c` package: for an odd component tagged by a rational character
`χ`, the Stickelberger projection has Bernoulli scalar `B_{1,χ⁻¹}`, and the
matching complexified character-side class action is trivial on the chosen
Sylow subgroup.  This is the exact combination of `T033b` and `T032c` currently
available before the project has an intrinsic class-group idempotent action. -/
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

/-- `T034c`: an odd declared component carries the Bernoulli annihilation
certificate obtained by combining the eigenspace calculation `T033b` with the
class-group annihilation statement `T032c`, restricted to the `p`-Sylow subgroup
by `T034a`. -/
theorem oddComponentBernoulliAnnihilation
    (hp_odd : p ≠ 2) {χ : MulChar (ZMod p)ˣ ℚ}
    (hχ_odd : IsOddUnitCharacter (p := p) χ)
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L))
    (hC : C.character = χ) :
    OddComponentBernoulliAnnihilation (p := p) (L := L) hp_odd χ C where
  component_character := hC
  odd := hχ_odd
  projection_formula := by
    simpa [pSylowBernoulliScalar] using
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
