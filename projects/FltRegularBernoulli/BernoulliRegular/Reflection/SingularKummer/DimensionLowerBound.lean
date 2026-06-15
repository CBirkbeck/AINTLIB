module

public import BernoulliRegular.Reflection.SingularKummer.GlobalUnitKernel
public import BernoulliRegular.Reflection.SingularKummer.SingularLinearAction
public import BernoulliRegular.Reflection.SingularKummer.SingularZMod
public import BernoulliRegular.UnitQuotient.GlobalUnitDimension
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Singular Kummer: dimension lower bounds

This file records the REF-08 dimension step.  The first lemma is the reusable
linear algebra argument: if a component of the kernel side has dimension one
and the matching target component is nonzero, then the middle component has
dimension at least two.

The singular-Kummer wrapper applies that lemma to the exact sequence

```text
E/E^p -> S -> A[p].
```

The actual cyclotomic component compatibility for `S_i` is kept as explicit
hypotheses, so this file can be used before the final concrete `Delta` action
on the singular group is fully assembled.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace LinearDimensionLowerBound

variable {F U S A : Type*} [Field F]
variable [AddCommGroup U] [Module F U]
variable [AddCommGroup S] [Module F S]
variable [AddCommGroup A] [Module F A]

/-- A two-dimensional lower bound from a kernel line and a nonzero quotient
component. -/
theorem finrank_ge_two_of_kernel_line_of_target_ne_bot
    (ι : U →ₗ[F] S) (π : S →ₗ[F] A)
    (Ui : Submodule F U) (Si : Submodule F S) (Ai : Submodule F A)
    [Module.Finite F Si]
    (hιUi : Submodule.map ι Ui ≤ Si)
    (hπSi : Submodule.map π Si = Ai)
    (hπι : ∀ u : U, π (ι u) = 0)
    (hι_inj : Function.Injective ι)
    (hUi_finrank : Module.finrank F Ui = 1)
    (hAi_ne_bot : Ai ≠ ⊥) :
    2 ≤ Module.finrank F Si := by
  have hUi_ne_bot : Ui ≠ ⊥ := by
    intro hUi_bot
    have hfinrank_zero : Module.finrank F Ui = 0 := by
      subst hUi_bot
      simp
    rw [hUi_finrank] at hfinrank_zero
    exact Nat.succ_ne_zero 0 hfinrank_zero
  obtain ⟨u0, hu0_mem, hu0_ne_zero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hUi_ne_bot
  let u : Ui := ⟨u0, hu0_mem⟩
  have hu_ne_zero : u ≠ 0 := fun hu_zero =>
    hu0_ne_zero (congrArg Subtype.val hu_zero)
  obtain ⟨a, ha_mem, ha_ne_zero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hAi_ne_bot
  have ha_mem_map : a ∈ Submodule.map π Si := by
    simpa [hπSi] using ha_mem
  obtain ⟨s, hs_mem, hs_image⟩ := ha_mem_map
  let uS : Si := ⟨ι u.1, hιUi ⟨u.1, u.2, rfl⟩⟩
  let sS : Si := ⟨s, hs_mem⟩
  have hπ_uS : π (uS : S) = 0 := by
    change π (ι u.1) = 0
    exact hπι u.1
  have hπ_sS : π (sS : S) = a := by
    change π s = a
    exact hs_image
  have huS_ne_zero : uS ≠ 0 := by
    intro huS_zero
    apply hu_ne_zero
    apply Subtype.ext
    apply hι_inj
    have hval : ι u.1 = 0 := by
      simpa [uS] using congrArg Subtype.val huS_zero
    simpa using hval
  have hli : LinearIndependent F ![uS, sS] := by
    refine (LinearIndependent.pair_iff' (K := F) huS_ne_zero).2 ?_
    intro c hc
    have hmap : π ((c • uS : Si) : S) = π (sS : S) :=
      congrArg (fun x : Si => π (x : S)) hc
    have hleft : π ((c • uS : Si) : S) = 0 := by
      calc
        π ((c • uS : Si) : S) = π (c • (uS : S)) := rfl
        _ = c • π (uS : S) := map_smul π c (uS : S)
        _ = c • 0 := by rw [hπ_uS]
        _ = 0 := smul_zero c
    have hright : π (sS : S) = 0 := hmap.symm.trans hleft
    have ha_zero : a = 0 := by
      simpa [hπ_sS] using hright
    exact ha_ne_zero ha_zero
  have hcard : Fintype.card (Fin 2) ≤ Module.finrank F Si :=
    hli.fintype_card_le_finrank
  simpa using hcard

end LinearDimensionLowerBound

namespace SingularPair

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

/-- The global-unit inclusion `E/E^p -> S` as a `ZMod p`-linear map. -/
def globalUnitPowerQuotientToSingularGroupLinear :
    Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) →ₗ[ZMod p]
      Additive (SingularGroup (R := 𝓞 K) (K := K) p) :=
  (globalUnitPowerQuotientToSingularGroup K p).toAdditive.toZModLinearMap p

@[simp]
theorem globalUnitPowerQuotientToSingularGroupLinear_apply_toMul
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    (globalUnitPowerQuotientToSingularGroupLinear K p x).toMul =
      globalUnitPowerQuotientToSingularGroup K p x.toMul :=
  rfl

/-- The linearized global-unit map is injective. -/
theorem globalUnitPowerQuotientToSingularGroupLinear_injective :
    Function.Injective (globalUnitPowerQuotientToSingularGroupLinear K p) := fun x y hxy =>
  Additive.ext <| globalUnitPowerQuotientToSingularGroup_injective K p <| by
    simpa using congrArg Additive.toMul hxy

/-- The composition `E/E^p -> S -> A[p]` is zero. -/
@[simp]
theorem singularGroupClassMapToPTorsionLinear_globalUnitPowerQuotientToSingularGroupLinear
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p
        (globalUnitPowerQuotientToSingularGroupLinear K p x) = 0 := by
  apply Additive.ext
  change
    singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p
        (globalUnitPowerQuotientToSingularGroup K p x.toMul) = 1
  have hmem :
      globalUnitPowerQuotientToSingularGroup K p x.toMul ∈
        (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p).ker := by
    rw [singularGroupClassMapToPTorsion_ker_eq_globalUnitPowerQuotientToSingularGroup_range]
    exact ⟨x.toMul, rfl⟩
  exact hmem

/-- Component-level REF-08 for the singular exact sequence. -/
theorem singularGroup_component_finrank_ge_two
    (Ucomp :
      Submodule (ZMod p)
        (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)))
    (Scomp :
      Submodule (ZMod p)
        (Additive (SingularGroup (R := 𝓞 K) (K := K) p)))
    (Acomp :
      Submodule (ZMod p)
        (Additive (classGroupPTorsion (R := 𝓞 K) p)))
    [Module.Finite (ZMod p) Scomp]
    (hU_to_S :
      Submodule.map (globalUnitPowerQuotientToSingularGroupLinear K p) Ucomp ≤
        Scomp)
    (hS_to_A :
      Submodule.map
          (singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p)
          Scomp =
        Acomp)
    (hU_finrank : Module.finrank (ZMod p) Ucomp = 1)
    (hA_ne_bot : Acomp ≠ ⊥) :
    2 ≤ Module.finrank (ZMod p) Scomp :=
  LinearDimensionLowerBound.finrank_ge_two_of_kernel_line_of_target_ne_bot
      (F := ZMod p)
      (globalUnitPowerQuotientToSingularGroupLinear K p)
      (singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p)
      Ucomp Scomp Acomp hU_to_S hS_to_A
      (singularGroupClassMapToPTorsionLinear_globalUnitPowerQuotientToSingularGroupLinear K p)
      (globalUnitPowerQuotientToSingularGroupLinear_injective K p)
      hU_finrank hA_ne_bot

/-- The `i`-th singular character-projection component for a chosen
`Delta`-action. -/
def singularGroupCharacterProjectionComponent [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularGroup (R := 𝓞 K) (K := K) p ≃*
          SingularGroup (R := 𝓞 K) (K := K) p) :
    Submodule (ZMod p)
      (Additive (SingularGroup (R := 𝓞 K) (K := K) p)) :=
  LinearMap.range
    (CharacterProjection.characterProjection (p := p) i
      (SingularLinearAction.mulActionToAdditiveLinearAction (p := p) ρS))

/-- The `i`-th `A[p]` character-projection component for a chosen
`Delta`-action. -/
def classGroupPTorsionCharacterProjectionComponent [NeZero p] (i : ℕ)
    (ρA :
      CharacterProjection.Delta p →*
        classGroupPTorsion (R := 𝓞 K) p ≃*
          classGroupPTorsion (R := 𝓞 K) p) :
    Submodule (ZMod p)
      (Additive (classGroupPTorsion (R := 𝓞 K) p)) :=
  LinearMap.range
    (CharacterProjection.characterProjection (p := p) i
      (SingularLinearAction.mulActionToAdditiveLinearAction (p := p) ρA))

/-- For compatible `Delta`-actions, the singular exact-sequence map carries the
singular character-projection component onto the matching `A[p]` component. -/
theorem singularGroupCharacterProjectionComponent_map_eq [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularGroup (R := 𝓞 K) (K := K) p ≃*
          SingularGroup (R := 𝓞 K) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        classGroupPTorsion (R := 𝓞 K) p ≃*
          classGroupPTorsion (R := 𝓞 K) p)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p (ρS d x) =
        ρA d (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p x)) :
    Submodule.map
        (singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p)
        (singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS) =
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i ρA :=
  CharacterProjection.map_characterProjection_range_eq_range_of_surjective
      (p := p) i
      (SingularLinearAction.mulActionToAdditiveLinearAction (p := p) ρS)
      (SingularLinearAction.mulActionToAdditiveLinearAction (p := p) ρA)
      (singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p)
      (singularGroupClassMapToPTorsionLinear_surjective (R := 𝓞 K) (K := K) p)
      (fun d x =>
        SingularLinearAction.linear_equivariant_of_multiplicative_equivariant
          (p := p)
          (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p)
          ρS ρA hρ d x)

/-- The class map restricted to matching singular and class-group character
projection components. -/
def singularGroupClassComponentMap [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularGroup (R := 𝓞 K) (K := K) p ≃*
          SingularGroup (R := 𝓞 K) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        classGroupPTorsion (R := 𝓞 K) p ≃*
          classGroupPTorsion (R := 𝓞 K) p)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p (ρS d x) =
        ρA d (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p x)) :
    singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS →ₗ[ZMod p]
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i ρA where
  toFun x := by
    refine ⟨singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p x.1, ?_⟩
    have hx :
        singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p x.1 ∈
          Submodule.map
            (singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p)
            (singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS) :=
      ⟨x.1, x.2, rfl⟩
    rw [singularGroupCharacterProjectionComponent_map_eq K p i ρS ρA hρ] at hx
    exact hx
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- The component class map is onto because the global singular class map is
onto and compatible with character projections. -/
theorem singularGroupClassComponentMap_surjective [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularGroup (R := 𝓞 K) (K := K) p ≃*
          SingularGroup (R := 𝓞 K) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        classGroupPTorsion (R := 𝓞 K) p ≃*
          classGroupPTorsion (R := 𝓞 K) p)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p (ρS d x) =
        ρA d (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p x)) :
    Function.Surjective (singularGroupClassComponentMap K p i ρS ρA hρ) := by
  intro y
  have hy :
      (y : Additive (classGroupPTorsion (R := 𝓞 K) p)) ∈
        Submodule.map
          (singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p)
          (singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS) := by
    rw [singularGroupCharacterProjectionComponent_map_eq K p i ρS ρA hρ]
    exact y.2
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext <| hxy

/-- REF-08 with the singular and torsion components taken to be actual
character-projection ranges for a compatible `Delta`-action. -/
theorem singularGroupCharacterProjectionComponent_finrank_ge_two [NeZero p]
    (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularGroup (R := 𝓞 K) (K := K) p ≃*
          SingularGroup (R := 𝓞 K) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        classGroupPTorsion (R := 𝓞 K) p ≃*
          classGroupPTorsion (R := 𝓞 K) p)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS)]
    (Ucomp :
      Submodule (ZMod p)
        (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)))
    (hU_to_S :
      Submodule.map (globalUnitPowerQuotientToSingularGroupLinear K p) Ucomp ≤
        singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p (ρS d x) =
        ρA d (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p x))
    (hU_finrank : Module.finrank (ZMod p) Ucomp = 1)
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i ρA ≠
        ⊥) :
    2 ≤ Module.finrank (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS) :=
  singularGroup_component_finrank_ge_two K p Ucomp
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i ρS)
      (classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i ρA)
      hU_to_S
      (singularGroupCharacterProjectionComponent_map_eq K p i ρS ρA hρ)
      hU_finrank hA_ne_bot

/-- REF-08 specialized to the even power-character unit component and actual
singular/torsion character-projection ranges for a compatible `Delta`-action.
-/
theorem singularGroupCharacterProjectionComponent_finrank_ge_two_of_even_power_character
    (hp_gt_two : 2 < p) {j : ℕ}
    (hj_even : Even j) (hj_low : 2 ≤ j) (hj_high : j ≤ p - 3)
    (ρS :
      CharacterProjection.Delta p →*
        SingularGroup (R := 𝓞 K) (K := K) p ≃*
          SingularGroup (R := 𝓞 K) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        classGroupPTorsion (R := 𝓞 K) p ≃*
          classGroupPTorsion (R := 𝓞 K) p)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) j ρS)]
    (hU_to_S :
      Submodule.map (globalUnitPowerQuotientToSingularGroupLinear K p)
          (cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
            (cyclotomicUnitDeltaPowerCharacter (p := p) j)) ≤
        singularGroupCharacterProjectionComponent (K := K) (p := p) j ρS)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p (ρS d x) =
        ρA d (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p x))
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) j ρA ≠
        ⊥) :
    2 ≤ Module.finrank (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) j ρS) :=
  singularGroupCharacterProjectionComponent_finrank_ge_two K p j ρS ρA
      (cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
        (cyclotomicUnitDeltaPowerCharacter (p := p) j))
      hU_to_S hρ
      (cyclotomicUnitPowerQuotientDeltaPowerCharacterEigenspace_finrank
        (p := p) K hp_gt_two hj_even hj_low hj_high)
      hA_ne_bot

/-- REF-08 specialized to the even power-character unit component formalized in
REF-07. -/
theorem singularGroup_component_finrank_ge_two_of_even_power_character
    (hp_gt_two : 2 < p) {j : ℕ}
    (hj_even : Even j) (hj_low : 2 ≤ j) (hj_high : j ≤ p - 3)
    (Scomp :
      Submodule (ZMod p)
        (Additive (SingularGroup (R := 𝓞 K) (K := K) p)))
    (Acomp :
      Submodule (ZMod p)
        (Additive (classGroupPTorsion (R := 𝓞 K) p)))
    [Module.Finite (ZMod p) Scomp]
    (hU_to_S :
      Submodule.map (globalUnitPowerQuotientToSingularGroupLinear K p)
          (cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
            (cyclotomicUnitDeltaPowerCharacter (p := p) j)) ≤
        Scomp)
    (hS_to_A :
      Submodule.map
          (singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p)
          Scomp =
        Acomp)
    (hA_ne_bot : Acomp ≠ ⊥) :
    2 ≤ Module.finrank (ZMod p) Scomp :=
  singularGroup_component_finrank_ge_two K p
      (cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
        (cyclotomicUnitDeltaPowerCharacter (p := p) j))
      Scomp Acomp hU_to_S hS_to_A
      (cyclotomicUnitPowerQuotientDeltaPowerCharacterEigenspace_finrank
        (p := p) K hp_gt_two hj_even hj_low hj_high)
      hA_ne_bot

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end
