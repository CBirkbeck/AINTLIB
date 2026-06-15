module

public import BernoulliRegular.Stickelberger.Action

/-!
# Stickelberger class-group annihilation package

This file packages the `T032b` principality result in class-group language.
The current Gauss-sum factorisation API is character-side and applies to the
orbit of the distinguished prime above `p`; the statements here expose that
precise class-group action without introducing a broader class-group module
formalisation yet.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField Pointwise nonZeroDivisors

namespace BernoulliRegular

section CharacterSideAnnihilation

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

local instance : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩

/-- A character-side translate of the distinguished prime, bundled as a
nonzero ideal for use in `ClassGroup.mk0`. -/
noncomputable def characterSidePrimeClassIdeal (b : (ZMod (p - 1))ˣ) :
    (Ideal (𝓞 L))⁰ :=
  ⟨sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (primeAboveP_ne_bot (p := p) (L := L)
        (P := sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L))⟩

/-- The class-group action of a nonnegative character-side group-ring exponent
on the distinguished prime class. Coefficients are read in the same inverse
basis convention as `characterSideStickelbergerIdealAction`. -/
noncomputable def characterSideStickelbergerClassAction
    (E : MonoidAlgebra ℤ (ZMod (p - 1))ˣ) : ClassGroup (𝓞 L) :=
  ∏ b : (ZMod (p - 1))ˣ,
    ClassGroup.mk0 (characterSidePrimeClassIdeal (p := p) (L := L) b) ^ (E b⁻¹).toNat

/-- The class-group product induced by `E` is the class of the corresponding
ideal product. -/
lemma classGroup_mk0_characterSideStickelbergerIdealAction_eq_classAction
    (E : MonoidAlgebra ℤ (ZMod (p - 1))ˣ)
    (hE : characterSideStickelbergerIdealAction (p := p) (L := L) E ≠ ⊥) :
    ClassGroup.mk0
        (⟨characterSideStickelbergerIdealAction (p := p) (L := L) E,
          mem_nonZeroDivisors_iff_ne_zero.mpr hE⟩ : (Ideal (𝓞 L))⁰) =
      characterSideStickelbergerClassAction (p := p) (L := L) E := by
  let F : (ZMod (p - 1))ˣ → (Ideal (𝓞 L))⁰ := fun b =>
    (characterSidePrimeClassIdeal (p := p) (L := L) b) ^ (E b⁻¹).toNat
  have hprod :
      (∏ b : (ZMod (p - 1))ˣ, F b : (Ideal (𝓞 L))⁰).1 =
        characterSideStickelbergerIdealAction (p := p) (L := L) E := by
    simp [F, characterSideStickelbergerIdealAction, characterSidePrimeClassIdeal]
  have hsub :
      (⟨characterSideStickelbergerIdealAction (p := p) (L := L) E,
        mem_nonZeroDivisors_iff_ne_zero.mpr hE⟩ : (Ideal (𝓞 L))⁰) =
        ∏ b : (ZMod (p - 1))ˣ, F b :=
    Subtype.ext <| hprod.symm
  rw [hsub, map_prod]
  simp [F, characterSideStickelbergerClassAction]

/-- `T032c`: the character-side Stickelberger exponent supplied by the
Gauss-sum factorisation annihilates the distinguished-prime class. -/
theorem stickelbergerCharacterCoefficientGroupRingTarget_annihilates_primeClass
    (hp_odd : p ≠ 2) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    characterSideStickelbergerClassAction (p := p) (L := L)
        (stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ) =
      (1 : ClassGroup (𝓞 L)) := by
  rw [← classGroup_mk0_characterSideStickelbergerIdealAction_eq_classAction
    (p := p) (L := L)
    (E := stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ)
    (hE := characterSideStickelbergerIdealAction_ne_bot (p := p) (L := L) hp_odd hχ)]
  simpa [characterSideStickelbergerIdealActionClassIdeal] using
    classGroup_mk0_characterSideStickelbergerIdealAction_eq_one
      (p := p) (L := L) hp_odd hχ

/-- Minus-part facing alias of the class-group annihilation statement.

`T034` will add the `p`-Sylow and idempotent-component infrastructure; this
name provides the exact annihilation input available from `T032`. -/
theorem stickelbergerCharacterCoefficientGroupRingTarget_annihilates_minusInput
    (hp_odd : p ≠ 2) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    characterSideStickelbergerClassAction (p := p) (L := L)
        (stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ) =
      (1 : ClassGroup (𝓞 L)) :=
  stickelbergerCharacterCoefficientGroupRingTarget_annihilates_primeClass
    (p := p) (L := L) hp_odd hχ

end CharacterSideAnnihilation

end BernoulliRegular

end
