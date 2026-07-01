module

public import BernoulliRegular.Reflection.Local.ComponentDimension
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionEigen
public import BernoulliRegular.Reflection.SingularKummer.CyclotomicAction
public import BernoulliRegular.Reflection.SingularKummer.Localization
public import BernoulliRegular.Reflection.SingularKummer.LocalizationKernel.LocalToCompletedBridge

/-!
# Singular Kummer: choosing a class in the localization kernel

This file records the REF-13 dimension argument.  Once the localization map is
expressed on the `i`-th singular component with codomain the completed local
principal-unit `i`-component, the inequality

```text
  dim S_i >= 2,       dim (U / U^p)_i = 1
```

gives a nonzero singular class killed by localization.  The final theorem also
unwraps that class to a singular pair `(I, eta)`, recording the singular
principal-ideal relation and the `Delta` eigenrelation.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularPair

open SingularLinearAction.SingularPair

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

set_option maxHeartbeats 800000 in
-- `QuotientGroup.lift` unfolds the cyclotomic local-unit quotient and the
-- completed principal-unit quotient; keep the larger budget local to this
-- descent.
set_option synthInstance.maxHeartbeats 80000 in
-- The completed quotient's `ZMod p` module is synthesized through additive
-- and quotient-group wrappers.
set_option synthInstance.maxHeartbeats 80000 in
-- The component codomain repeats the same completed quotient module synthesis
-- while building the projected linear map.
/-- The concrete completed localization map, projected to the target `i`-th
character component. -/
noncomputable def singularGroupCompletedLocalizationComponentMap {i : ℕ} :
    singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p) →ₗ[ZMod p]
      Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i where
  toFun x :=
    ⟨Local.completedPrincipalUnitModPCharacterProjection (p := p) K i
        (singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K x.1),
      ⟨singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K x.1, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- REF-13, component-level kernel choice.

Given the component-level localization map from the singular `i`-component to
the local completed principal-unit `i`-component, there is a nonzero singular
component class killed by it. -/
theorem exists_nonzero_in_component_localization_kernel
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥)
    (loc_i :
      singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) →ₗ[ZMod p]
        Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) :
    ∃ x :
      singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p),
      x ≠ 0 ∧ loc_i x = 0 := by
  have hS_ge_two :
      2 ≤ Module.finrank (ZMod p)
        (singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p)) :=
    cyclotomicSingularGroupCharacterProjectionComponent_finrank_ge_two_of_even_power_character
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
  have hLocal_finrank :
      Module.finrank (ZMod p)
        (Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) = 1 :=
    Local.completedPrincipalUnitModPCharacterProjectionRange_finrank_one
      (p := p) (K := K) hp_gt_two hi_low (by omega)
  haveI : FiniteDimensional (ZMod p)
      (Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) :=
    FiniteDimensional.of_finrank_eq_succ hLocal_finrank
  have hlt :
      Module.finrank (ZMod p)
          (Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) <
        Module.finrank (ZMod p)
          (singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p)) := by
    omega
  exact LinearDimensionKernel.exists_ne_zero_map_eq_zero_of_finrank_lt loc_i hlt

set_option synthInstance.maxHeartbeats 80000 in
-- The completed unit quotient's `ZMod p` instance is deeply wrapped through
-- additive and quotient-group structures.
/-- Restrict an equivariant localization map to the matching source and target
character-projection components. -/
def completedLocalComponentMap {i : ℕ}
    (loc :
      Additive (SingularGroup (R := 𝓞 K) (K := K) p) →ₗ[ZMod p]
        Additive (Local.completedPrincipalUnitModPQuotient p K))
    (hloc : ∀ (a : CharacterProjection.Delta p)
        (x : Additive (SingularGroup (R := 𝓞 K) (K := K) p)),
      loc
          (SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
            (cyclotomicSingularGroupAction K p) a x) =
        Local.completedPrincipalUnitModPDeltaActionZMod (p := p) K a (loc x)) :
    singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p) →ₗ[ZMod p]
      Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i where
  toFun x := by
    refine ⟨loc x.1, ?_⟩
    obtain ⟨y, hy⟩ := x.2
    refine ⟨loc y, ?_⟩
    let ρS :=
      SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
        (cyclotomicSingularGroupAction K p)
    let ρU := Local.completedPrincipalUnitModPDeltaActionZMod (p := p) K
    have hmap :
        loc (CharacterProjection.characterProjection (p := p) i ρS y) =
          CharacterProjection.characterProjection (p := p) i ρU (loc y) :=
      CharacterProjection.map_projection_apply
        (p := p) ρS ρU loc hloc
        (CharacterProjection.characterProjectionCoefficient (p := p) i) y
    symm
    calc
      loc x.1 = loc (CharacterProjection.characterProjection (p := p) i ρS y) := by
        rw [hy]
      _ = Local.completedPrincipalUnitModPCharacterProjection (p := p) K i (loc y) := by
        simpa [Local.completedPrincipalUnitModPCharacterProjection, ρS, ρU] using hmap
  map_add' x y :=
    Subtype.ext <| map_add loc x.1 y.1
  map_smul' c x :=
    Subtype.ext <| map_smul loc c x.1

/-- REF-21.6d2a, abstract component form.

If the global-unit component injects into the singular component, the component
class map is the actual singular-to-class map, and the local target has the
same dimension as that unit component, then the primary pseudo-unit subspace
`ker loc_i` has dimension at least the matching class-group component. -/
theorem componentLocalizationKernel_finrank_ge_classComponent [NeZero p] {i : ℕ}
    [FiniteDimensional (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    [FiniteDimensional (ZMod p)
      (classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p))]
    [FiniteDimensional (ZMod p)
      (Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i)]
    (Ucomp :
      Submodule (ZMod p)
        (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)))
    [FiniteDimensional (ZMod p) Ucomp]
    (hU_to_S :
      Submodule.map (globalUnitPowerQuotientToSingularGroupLinear K p) Ucomp ≤
        singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p))
    (hU_finrank_eq_local :
      Module.finrank (ZMod p) Ucomp =
        Module.finrank (ZMod p)
          (Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i))
    (loc_i :
      singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) →ₗ[ZMod p]
        Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) :
    Module.finrank (ZMod p)
        (classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicClassGroupPTorsionAction K p)) ≤
      Module.finrank (ZMod p) (LinearMap.ker loc_i) := by
  let unitToSingularComponent :
      Ucomp →ₗ[ZMod p]
        singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) := {
    toFun := fun u =>
      ⟨globalUnitPowerQuotientToSingularGroupLinear K p u.1,
        hU_to_S ⟨u.1, u.2, rfl⟩⟩
    map_add' := by
      intro u v
      apply Subtype.ext
      simp
    map_smul' := by
      intro c u
      apply Subtype.ext
      simp }
  let classComponentMap :=
    singularGroupClassComponentMap K p i
      (cyclotomicSingularGroupAction K p)
      (cyclotomicClassGroupPTorsionAction K p)
      (by
        intro d x
        exact (cyclotomicSingularGroupClassMapToPTorsion_equivariant K p d x).symm)
  refine
    LinearDimensionKernel.finrank_class_le_ker_localization_of_leftKernel
      unitToSingularComponent classComponentMap loc_i
      (singularGroupClassComponentMap_surjective K p i
        (cyclotomicSingularGroupAction K p)
        (cyclotomicClassGroupPTorsionAction K p)
        (by
          intro d x
          exact (cyclotomicSingularGroupClassMapToPTorsion_equivariant K p d x).symm))
      ?_ ?_ hU_finrank_eq_local
  · intro u
    apply Subtype.ext
    change
      singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p
          (globalUnitPowerQuotientToSingularGroupLinear K p u.1) = 0
    exact singularGroupClassMapToPTorsionLinear_globalUnitPowerQuotientToSingularGroupLinear
      K p u.1
  · intro u v huv
    exact Subtype.ext <|
      globalUnitPowerQuotientToSingularGroupLinear_injective K p <| congrArg Subtype.val huv

set_option maxHeartbeats 1000000 in
-- The component finite-dimensionality proof unfolds the projected singular
-- exact sequence and the cyclotomic component maps.
set_option synthInstance.maxHeartbeats 120000 in
/-- REF-21.6d2a1: the concrete even-character singular component is
finite-dimensional without an external finiteness hypothesis.

The proof uses the component form of `E/E^p -> S -> A[p]`: the matching unit
component is one-dimensional, the matching class component is finite, and the
kernel of the component class map is supplied by global units. -/
theorem singularGroupCharacterProjectionComponent_finiteDimensional_of_even_power_character
    [NeZero p] (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3) :
    FiniteDimensional (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p)) := by
  let Ucomp :=
    cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
      (cyclotomicUnitDeltaPowerCharacter (p := p) i)
  have hU_finrank :
      Module.finrank (ZMod p) Ucomp = 1 :=
    cyclotomicUnitPowerQuotientDeltaPowerCharacterEigenspace_finrank
      (p := p) K hp_gt_two hi_even hi_low hi_high
  haveI : FiniteDimensional (ZMod p) Ucomp :=
    FiniteDimensional.of_finrank_eq_succ hU_finrank
  let unitToSingularComponent :
      Ucomp →ₗ[ZMod p]
        singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) := {
    toFun := fun u =>
      ⟨globalUnitPowerQuotientToSingularGroupLinear K p u.1,
        globalUnitPowerQuotientToSingularGroupLinear_mem_characterProjectionComponent
          (K := K) (p := p) (i := i) u.2⟩
    map_add' := by
      intro u v
      apply Subtype.ext
      simp
    map_smul' := by
      intro c u
      apply Subtype.ext
      simp }
  let classComponentMap :=
    singularGroupClassComponentMap K p i
      (cyclotomicSingularGroupAction K p)
      (cyclotomicClassGroupPTorsionAction K p)
      (by
        intro d x
        exact (cyclotomicSingularGroupClassMapToPTorsion_equivariant K p d x).symm)
  have hker :
      ∀ v :
        singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p),
        classComponentMap v = 0 → ∃ u : Ucomp, unitToSingularComponent u = v := by
    intro v hv
    have hglobal_zero :
        singularGroupClassMapToPTorsionLinear (R := 𝓞 K) (K := K) p v.1 = 0 := by
      have hval := congrArg Subtype.val hv
      simpa [classComponentMap, singularGroupClassComponentMap] using hval
    have hmul_mem :
        v.1.toMul ∈
          (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p).ker := by
      change singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p v.1.toMul = 1
      have htoMul := congrArg Additive.toMul hglobal_zero
      simpa [singularGroupClassMapToPTorsionLinear_apply_toMul] using htoMul
    rw [singularGroupClassMapToPTorsion_ker_eq_globalUnitPowerQuotientToSingularGroup_range
      (K := K) (p := p)] at hmul_mem
    obtain ⟨q, hq⟩ := hmul_mem
    let qadd : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) :=
      Additive.ofMul q
    have hqadd :
        globalUnitPowerQuotientToSingularGroupLinear K p qadd = v.1 := by
      apply Additive.ext
      change globalUnitPowerQuotientToSingularGroup K p q = v.1.toMul
      exact hq
    have hq_eigen : qadd ∈ Ucomp := by
      intro a
      apply globalUnitPowerQuotientToSingularGroupLinear_injective (K := K) (p := p)
      calc
        globalUnitPowerQuotientToSingularGroupLinear K p
            (cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K a qadd)
            = SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
                (cyclotomicSingularGroupAction K p) a
              (globalUnitPowerQuotientToSingularGroupLinear K p qadd) :=
                globalUnitPowerQuotientToSingularGroupLinear_equivariant
                  (K := K) (p := p) a qadd
        _ = SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
                (cyclotomicSingularGroupAction K p) a v.1 := by
                rw [hqadd]
        _ = ((a : ZMod p) ^ i) • v.1 :=
                singularGroup_additive_apply_eq_smul_of_mem_characterProjection_range
                    (R := 𝓞 K) (K := K) p i
                    (cyclotomicSingularGroupAction K p) a v.2
        _ = globalUnitPowerQuotientToSingularGroupLinear K p
              ((cyclotomicUnitDeltaPowerCharacter (p := p) i a) • qadd) := by
                rw [cyclotomicUnitDeltaPowerCharacter_apply, ← hqadd, map_smul]
    refine ⟨⟨qadd, hq_eigen⟩, ?_⟩
    exact Subtype.ext <| hqadd
  exact LinearDimensionKernel.finiteDimensional_of_surjective_of_leftKernel
    unitToSingularComponent classComponentMap
    (singularGroupClassComponentMap_surjective K p i
      (cyclotomicSingularGroupAction K p)
      (cyclotomicClassGroupPTorsionAction K p)
      (by
        intro d x
        exact (cyclotomicSingularGroupClassMapToPTorsion_equivariant K p d x).symm))
    hker

/-- REF-21.6d2a, concrete even-character form for the completed lambda-local
localization component.  This is the formal dimension estimate

```text
dim ker(loc_lambda | V_i) >= dim A_i
```

for the weak-reflection primary pseudo-unit subspace. -/
theorem completedLocalizationKernel_finrank_ge_classComponent_of_even_power_character
    [NeZero p] (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3) :
    Module.finrank (ZMod p)
        (classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicClassGroupPTorsionAction K p)) ≤
      Module.finrank (ZMod p)
        (LinearMap.ker
          (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i))) := by
  let Ucomp :=
    cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
      (cyclotomicUnitDeltaPowerCharacter (p := p) i)
  have hU_finrank :
      Module.finrank (ZMod p) Ucomp = 1 :=
    cyclotomicUnitPowerQuotientDeltaPowerCharacterEigenspace_finrank
      (p := p) K hp_gt_two hi_even hi_low hi_high
  have hLocal_finrank :
      Module.finrank (ZMod p)
        (Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) = 1 :=
    Local.completedPrincipalUnitModPCharacterProjectionRange_finrank_one
      (p := p) (K := K) hp_gt_two hi_low (by omega)
  haveI : FiniteDimensional (ZMod p) Ucomp :=
    FiniteDimensional.of_finrank_eq_succ hU_finrank
  haveI : FiniteDimensional (ZMod p)
      (Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) :=
    FiniteDimensional.of_finrank_eq_succ hLocal_finrank
  haveI : FiniteDimensional (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p)) :=
    singularGroupCharacterProjectionComponent_finiteDimensional_of_even_power_character
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high
  haveI : FiniteDimensional (ZMod p)
      (classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p)) :=
    inferInstance
  refine
    componentLocalizationKernel_finrank_ge_classComponent
      (K := K) (p := p) (i := i)
      Ucomp ?_ ?_
      (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i))
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact globalUnitPowerQuotientToSingularGroupLinear_mem_characterProjectionComponent
      (K := K) (p := p) (i := i) hx
  · rw [hU_finrank, hLocal_finrank]

/-- REF-13 representative form of the localization-kernel choice.

The map `loc_i` is the component-level localization map into the completed
local principal-unit component.  The theorem produces a singular pair
representative `(I, eta)` whose singular class is nonzero, lies in the
`i`-component, is killed by `loc_i`, satisfies `(eta) = I^p`, and obeys the
corresponding `Delta` eigenrelation. -/
theorem exists_singularPair_in_component_localization_kernel
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥)
    (loc_i :
      singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) →ₗ[ZMod p]
        Local.completedPrincipalUnitModPCharacterProjectionRange (p := p) K i) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ hs_component :
        Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p) ∈
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p),
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        loc_i ⟨Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p), hs_component⟩ = 0 ∧
        toPrincipalIdeal (𝓞 K) K (generator s) = ideal s ^ p ∧
        ∀ b : CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p) := by
  obtain ⟨x, hx_ne_zero, hx_loc⟩ :=
    exists_nonzero_in_component_localization_kernel
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot loc_i
  obtain ⟨s, hs⟩ :=
    exists_representative (R := 𝓞 K) (K := K) p x.1.toMul
  have hs_component :
      Additive.ofMul
          (QuotientGroup.mk s :
            SingularGroup (R := 𝓞 K) (K := K) p) ∈
        singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) := by
    simp [hs, x.2]
  refine ⟨s, hs_component, ?_, ?_, principal_eq_ideal_pow (R := 𝓞 K) (K := K) s, ?_⟩
  · intro hs_trivial
    apply hx_ne_zero
    apply Subtype.ext
    apply Additive.ext
    change x.1.toMul = 1
    rw [← hs]
    exact hs_trivial
  · have harg :
        (⟨Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p), hs_component⟩ :
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p)) = x := by
      apply Subtype.ext
      apply Additive.ext
      change (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) =
        x.1.toMul
      exact hs
    simpa [harg] using hx_loc
  · intro b
    have hx_eigen :=
      singularGroup_additive_apply_eq_smul_of_mem_characterProjection_range
        (R := 𝓞 K) (K := K) p i (cyclotomicSingularGroupAction K p) b x.2
    rw [hs]
    exact hx_eigen

/-- Concrete REF-13 component-kernel form using the REF-12 localization
composed with the completed local principal-unit bridge, then projected to the
target `i`-component.

The remaining stronger endpoint for REF-13 is to prove equivariance of this
concrete completed localization map; that upgrades this projected kernel
statement to the full completed-localization kernel statement below. -/
theorem exists_singularPair_in_concrete_completed_localization_component_kernel
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ hs_component :
        Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p) ∈
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p),
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i)
          ⟨Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p), hs_component⟩ = 0 ∧
        toPrincipalIdeal (𝓞 K) K (generator s) = ideal s ^ p ∧
        ∀ b : CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p) :=
  exists_singularPair_in_component_localization_kernel
    (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
    (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i))

/-- REF-13 representative form for an equivariant full localization map into
the completed local principal-unit quotient. -/
theorem exists_singularPair_in_completed_localization_kernel
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥)
    (loc :
      Additive (SingularGroup (R := 𝓞 K) (K := K) p) →ₗ[ZMod p]
        Additive (Local.completedPrincipalUnitModPQuotient p K))
    (hloc : ∀ (a : CharacterProjection.Delta p)
        (x : Additive (SingularGroup (R := 𝓞 K) (K := K) p)),
      loc
          (SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
            (cyclotomicSingularGroupAction K p) a x) =
        Local.completedPrincipalUnitModPDeltaActionZMod (p := p) K a (loc x)) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ _hs_component :
        Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p) ∈
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p),
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        loc (Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        toPrincipalIdeal (𝓞 K) K (generator s) = ideal s ^ p ∧
        ∀ b : CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p) := by
  obtain ⟨s, hs_component, hs_ne, hs_loc, hs_principal, hs_eigen⟩ :=
    exists_singularPair_in_component_localization_kernel
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
      (completedLocalComponentMap (K := K) (p := p) (i := i) loc hloc)
  refine ⟨s, hs_component, hs_ne, ?_, hs_principal, hs_eigen⟩
  have hval := congrArg Subtype.val hs_loc
  simpa [completedLocalComponentMap] using hval

/-- Concrete REF-13 full-kernel form, with an explicit supplied equivariance
statement for localization into `U_lambda / U_lambda^p`. -/
theorem exists_singularPair_in_concrete_completed_localization_kernel_of_cyclotomicLocalUnits
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥)
    (hloc : ∀ (a : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupLocalizationToCyclotomicLocalUnits (p := p) K
          (cyclotomicSingularGroupAction K p a x) =
        cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
          (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K x)) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ _hs_component :
        Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p) ∈
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p),
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
          (Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        toPrincipalIdeal (𝓞 K) K (generator s) = ideal s ^ p ∧
        ∀ b : CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p) :=
  exists_singularPair_in_completed_localization_kernel
    (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
    (singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K)
    (singularGroupLocalizationToCompletedPrincipalUnitsLinear_equivariant_of_cyclotomicLocalUnits
      (p := p) (K := K) hloc)

/-- Concrete REF-13 full-kernel form for the completed lambda-local
localization. -/
theorem exists_singularPair_in_concrete_completed_localization_kernel
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ _hs_component :
        Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p) ∈
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p),
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
          (Additive.ofMul
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        toPrincipalIdeal (𝓞 K) K (generator s) = ideal s ^ p ∧
        ∀ b : CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk s :
                  SingularGroup (R := 𝓞 K) (K := K) p) :=
  exists_singularPair_in_completed_localization_kernel
    (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
    (singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K)
    (singularGroupLocalizationToCompletedPrincipalUnitsLinear_equivariant (p := p) (K := K))

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
