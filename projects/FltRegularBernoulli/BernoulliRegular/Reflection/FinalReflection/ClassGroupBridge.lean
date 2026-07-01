module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import BernoulliRegular.Reflection.ClassGroupModP.PlusMinusInstance
public import BernoulliRegular.Reflection.Kummer.CoprimeCharacterSplitting
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicConjugateNorm
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LambdaLocalPthPower
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.OneSidedKummerReciprocity
public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelCharacterLift
public import BernoulliRegular.Reflection.SingularKummer.IntegralNormalization
public import BernoulliRegular.Reflection.SingularKummer.LocalizationKernel.DimensionKernelChoice

/-!
# Final weak reflection statements

This file records the weak reflection statement used by Kummer's criterion.
The component-level theorem is the single remaining proof hole in this route;
the class-number consequence below is proved from it and the plus/minus
eigenspace identifications.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace BernoulliRegular

open Reflection.SingularKummer
open Reflection.SingularKummer.FiniteLevelCharacterLift.FinitePrimaryBridge
open Reflection.SingularKummer.SingularPair
open Reflection.Kummer

universe u

/-- `#(ZMod p)ˣ = p - 1` is a unit in `ZMod p`. -/
theorem finalReflection_card_zMod_units_isUnit
    (p : ℕ) [Fact p.Prime] :
    IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p)) := by
  rw [ZMod.card_units]
  rw [show ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) from ?_]
  · exact isUnit_one.neg
  · push_cast [Nat.cast_pred (Fact.out : Nat.Prime p).pos]
    rw [ZMod.natCast_self]
    ring

/-- A nontrivial eigenspace component of `Cl(O_K)/p` gives a nontrivial
character-projection range for the same `ClassGroupModP` action.

This is the first step in the finite-group comparison needed by the primary
pseudo-unit lower bound. -/
theorem classGroupModP_characterProjectionComponent_ne_bot_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (i : ℕ)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    LinearMap.range
        (Reflection.SingularKummer.CharacterProjection.characterProjection
          (p := p) i (cyclotomicGalActionLinearEquivModP (p := p) (K := K))) ≠
      (⊥ : Submodule (ZMod p) (Additive (ClassGroupModP K p))) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨v, hv_mem, hv_ne⟩ := hcomp
  have hcard :
      IsUnit
        ((Fintype.card (Reflection.SingularKummer.CharacterProjection.Delta p) :
          ZMod p)) := by
    simpa [Reflection.SingularKummer.CharacterProjection.Delta] using
      finalReflection_card_zMod_units_isUnit p
  have hv_range :
      v ∈
        LinearMap.range
          (Reflection.SingularKummer.CharacterProjection.characterProjection
            (p := p) i (cyclotomicGalActionLinearEquivModP (p := p) (K := K))) := by
    have hv_eigen :
        ∀ a : Reflection.SingularKummer.CharacterProjection.Delta p,
          cyclotomicGalActionLinearEquivModP (p := p) (K := K) a v =
            ((a : ZMod p) ^ i) • v := by
      intro a
      rw [cyclotomicGalActionLinearEquivModP_apply]
      exact hv_mem a
    exact
      CharacterProjection.mem_characterProjection_range_of_forall_apply_eq_smul
        (p := p) hcard i
        (cyclotomicGalActionLinearEquivModP (p := p) (K := K)) hv_eigen
  exact (Submodule.ne_bot_iff _).2 ⟨v, hv_range, hv_ne⟩

/-- The natural quotient map
`Cl(O_K) / p Cl(O_K) -> ClassGroupModP K p`, written additively and in the
`ElementaryQuotient` model. -/
noncomputable def classGroupElementaryQuotientToModPLinear
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] :
    ElementaryQuotientComponent.ElementaryQuotient
        (Additive (ClassGroup (𝓞 K))) p →ₗ[ZMod p]
      Additive (ClassGroupModP K p) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let q :
      Additive (ClassGroup (𝓞 K)) →+
        Additive (ClassGroupModP K p) :=
    (QuotientGroup.mk' ((powMonoidHom p :
      ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range)).toAdditive
  exact
    (QuotientAddGroup.lift
      (Reflection.SingularKummer.multiplesSubgroup
        (Additive (ClassGroup (𝓞 K))) p)
      q
      (by
        rintro x ⟨y, rfl⟩
        apply Additive.ext
        change QuotientGroup.mk (y.toMul ^ p) = (1 : ClassGroupModP K p)
        exact
          (QuotientGroup.eq_one_iff
            (N := (powMonoidHom p :
              ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range)
            (y.toMul ^ p)).2 ⟨y.toMul, rfl⟩)).toZModLinearMap p

@[simp]
theorem classGroupElementaryQuotientToModPLinear_mk
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) :
    classGroupElementaryQuotientToModPLinear p K
        (QuotientAddGroup.mk (Additive.ofMul c) :
          ElementaryQuotientComponent.ElementaryQuotient
            (Additive (ClassGroup (𝓞 K))) p) =
      Additive.ofMul (QuotientGroup.mk c : ClassGroupModP K p) :=
  rfl

theorem classGroupElementaryQuotientToModPLinear_surjective
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] :
    Function.Surjective (classGroupElementaryQuotientToModPLinear p K) := by
  intro v
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective v.toMul
  exact ⟨QuotientAddGroup.mk (Additive.ofMul c), rfl⟩

theorem classGroupElementaryQuotientToModPLinear_equivariant
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a : CharacterProjection.Delta p)
    (x :
      ElementaryQuotientComponent.ElementaryQuotient
        (Additive (ClassGroup (𝓞 K))) p) :
    classGroupElementaryQuotientToModPLinear p K
        (ElementaryQuotientComponent.elementaryQuotientAction
          (p := p) (cyclotomicGalActionAddEquivHom (p := p) (K := K)) a x) =
      cyclotomicGalActionLinearEquivModP (p := p) (K := K) a
        (classGroupElementaryQuotientToModPLinear p K x) := by
  induction x using QuotientAddGroup.induction_on
  rfl

/-- A nontrivial `ClassGroupModP` character component gives a nontrivial
component in the elementary quotient of the full class group. -/
theorem classGroup_elementaryComponentNontrivial_of_modP_component_ne_bot
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (i : ℕ)
    (hmod :
      LinearMap.range
          (CharacterProjection.characterProjection
            (p := p) i (cyclotomicGalActionLinearEquivModP (p := p) (K := K))) ≠
        (⊥ : Submodule (ZMod p) (Additive (ClassGroupModP K p)))) :
    ElementaryQuotientComponent.ElementaryComponentNontrivial
      (p := p) i (cyclotomicGalActionAddEquivHom (p := p) (K := K)) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let f := classGroupElementaryQuotientToModPLinear p K
  have hmap :
      Submodule.map f
          (ElementaryQuotientComponent.elementaryComponent (p := p) i
            (cyclotomicGalActionAddEquivHom (p := p) (K := K))) =
        LinearMap.range
          (CharacterProjection.characterProjection
            (p := p) i (cyclotomicGalActionLinearEquivModP (p := p) (K := K))) :=
    CharacterProjection.map_characterProjection_range_eq_range_of_surjective
      (p := p) i
      (ElementaryQuotientComponent.elementaryQuotientAction
        (p := p) (cyclotomicGalActionAddEquivHom (p := p) (K := K)))
      (cyclotomicGalActionLinearEquivModP (p := p) (K := K))
      f
      (classGroupElementaryQuotientToModPLinear_surjective p K)
      (classGroupElementaryQuotientToModPLinear_equivariant p K)
  intro hbot
  apply hmod
  rw [← hmap, hbot]
  exact Submodule.map_bot f

/-- Finite group comparison for the cyclotomic class group: a nontrivial
`ClassGroupModP` component gives a nontrivial matching component of the
`p`-torsion of the full class group, for the same explicit class-group action.
-/
theorem classGroup_additivePTorsion_component_nontrivial_of_modP_component_ne_bot
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (i : ℕ)
    (hmod :
      LinearMap.range
          (CharacterProjection.characterProjection
            (p := p) i (cyclotomicGalActionLinearEquivModP (p := p) (K := K))) ≠
        (⊥ : Submodule (ZMod p) (Additive (ClassGroupModP K p)))) :
    TorsionComponent.TorsionComponentNontrivial (p := p) i
      (cyclotomicGalActionAddEquivHom (p := p) (K := K)) :=
  torsionComponentNontrivial_of_elementaryComponentNontrivial_finite
        (p := p) (A := Additive (ClassGroup (𝓞 K))) i
        (cyclotomicGalActionAddEquivHom (p := p) (K := K))
        (classGroup_elementaryComponentNontrivial_of_modP_component_ne_bot
          p K i hmod)

/-- The two `A[p]` models used in the reflection files are linearly
equivalent: additive `p`-torsion of the class group is the additive form of
the multiplicative subgroup `classGroupPTorsion`. -/
noncomputable def classGroupPTorsionAdditiveEquiv
    (p : ℕ)
    (K : Type u) [Field K] [NumberField K] :
    TorsionComponent.PTorsion (Additive (ClassGroup (𝓞 K))) p ≃+
      Additive (classGroupPTorsion (R := 𝓞 K) p) where
  toFun x :=
    Additive.ofMul ⟨x.1.toMul, by
      have hx : Additive.ofMul (x.1.toMul ^ p) = 0 := by
        rw [ofMul_pow]
        exact x.2
      exact ofMul_eq_zero.mp hx⟩
  invFun y :=
    ⟨Additive.ofMul ((y.toMul : classGroupPTorsion (R := 𝓞 K) p) : ClassGroup (𝓞 K)), by
      change
        p • Additive.ofMul
            ((y.toMul : classGroupPTorsion (R := 𝓞 K) p) : ClassGroup (𝓞 K)) = 0
      rw [← ofMul_pow]
      have hy :
          ((y.toMul : classGroupPTorsion (R := 𝓞 K) p) : ClassGroup (𝓞 K)) ^ p = 1 :=
        (y.toMul : classGroupPTorsion (R := 𝓞 K) p).2
      exact ofMul_eq_zero.mpr hy⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Additive.ext
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.ext
    apply Subtype.ext
    simp

/-- Compatibility of the fractional-ideal cyclotomic action with integral
ideal representatives. -/
theorem cyclotomicFractionalIdealEquiv_mk0
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a : CharacterProjection.Delta p) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicFractionalIdealEquiv K p a (FractionalIdeal.mk0 K I) =
      FractionalIdeal.mk0 K
        (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I) := by
  apply Units.ext
  change
    cyclotomicFractionalIdealHom K p a
        (I : FractionalIdeal (𝓞 K)⁰ K) =
      (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a I.1 :
        FractionalIdeal (𝓞 K)⁰ K)
  simp [cyclotomicFractionalIdealHom, Furtwaengler.cyclotomicGaloisConjugate,
    cyclotomicRingOfIntegersAuto]
  rfl

/-- The class-group action used by `ClassGroupModP` agrees with the
principal-ideal-preserving action used by the singular Kummer exact sequence. -/
theorem cyclotomicGalActionMonoidHom_eq_principalIdealPreserving_classGroupEquiv
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a : CharacterProjection.Delta p) (c : ClassGroup (𝓞 K)) :
    cyclotomicGalActionMonoidHom (p := p) (K := K) a c =
      (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).classGroupEquiv c := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective (R := 𝓞 K) c
  rw [← hI]
  calc
    cyclotomicGalActionMonoidHom (p := p) (K := K) a (ClassGroup.mk0 I)
        = ClassGroup.mk0
            (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I) :=
          cyclotomicGalActionOnClassGroup_mk0 (p := p) (K := K) a I
    _ = ClassGroup.mk (R := 𝓞 K) (K := K)
          (FractionalIdeal.mk0 K
            (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I)) := by
          rw [ClassGroup.mk_mk0]
    _ = ClassGroup.mk (R := 𝓞 K) (K := K)
          (cyclotomicFractionalIdealEquiv K p a (FractionalIdeal.mk0 K I)) := by
          rw [cyclotomicFractionalIdealEquiv_mk0]
    _ =
        (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).classGroupEquiv
          (ClassGroup.mk (R := 𝓞 K) (K := K) (FractionalIdeal.mk0 K I)) := by
          rw [SingularPair.PrincipalIdealPreservingEquiv.classGroupEquiv_mk]
          rfl
    _ =
        (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).classGroupEquiv
          (ClassGroup.mk0 I) := by
          rw [ClassGroup.mk_mk0]

/-- Linear form of `classGroupPTorsionAdditiveEquiv`. -/
noncomputable def classGroupPTorsionAdditiveLinearEquiv
    (p : ℕ) [NeZero p]
    (K : Type u) [Field K] [NumberField K] :
    TorsionComponent.PTorsion (Additive (ClassGroup (𝓞 K))) p ≃ₗ[ZMod p]
      Additive (classGroupPTorsion (R := 𝓞 K) p) :=
  { (classGroupPTorsionAdditiveEquiv p K).toAddMonoidHom.toZModLinearMap p with
    invFun := (classGroupPTorsionAdditiveEquiv p K).symm
    left_inv := (classGroupPTorsionAdditiveEquiv p K).left_inv
    right_inv := (classGroupPTorsionAdditiveEquiv p K).right_inv }

theorem classGroupPTorsionAdditiveLinearEquiv_equivariant
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a : CharacterProjection.Delta p)
    (x : TorsionComponent.PTorsion (Additive (ClassGroup (𝓞 K))) p) :
    classGroupPTorsionAdditiveLinearEquiv p K
        (TorsionComponent.torsionAction (p := p)
          (cyclotomicGalActionAddEquivHom (p := p) (K := K)) a x) =
      SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
          (cyclotomicClassGroupPTorsionAction K p) a
        (classGroupPTorsionAdditiveLinearEquiv p K x) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  apply Additive.ext
  apply Subtype.ext
  change
    (cyclotomicGalActionMulEquiv (p := p) (K := K) a) x.1.toMul =
      ((cyclotomicClassGroupPTorsionAction K p a)
        ⟨x.1.toMul, _⟩ : ClassGroup (𝓞 K))
  simp [cyclotomicClassGroupPTorsionAction, cyclotomicGalActionMulEquiv,
    cyclotomicGalActionMonoidHom_eq_principalIdealPreserving_classGroupEquiv]

theorem classGroupPTorsionCharacterProjectionComponent_ne_bot_of_additivePTorsion
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (i : ℕ)
    (h :
      TorsionComponent.TorsionComponentNontrivial (p := p) i
        (cyclotomicGalActionAddEquivHom (p := p) (K := K))) :
    classGroupPTorsionCharacterProjectionComponent
        (K := K) (p := p) i (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥ := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let e := classGroupPTorsionAdditiveLinearEquiv p K
  have hmap :
      Submodule.map e.toLinearMap
          (TorsionComponent.torsionComponent (p := p) i
            (cyclotomicGalActionAddEquivHom (p := p) (K := K))) =
        classGroupPTorsionCharacterProjectionComponent
          (K := K) (p := p) i (cyclotomicClassGroupPTorsionAction K p) :=
    CharacterProjection.map_characterProjection_range_eq_range_of_surjective
      (p := p) i
      (TorsionComponent.torsionAction (p := p)
        (cyclotomicGalActionAddEquivHom (p := p) (K := K)))
      (SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
        (cyclotomicClassGroupPTorsionAction K p))
      e.toLinearMap e.surjective
      (classGroupPTorsionAdditiveLinearEquiv_equivariant p K)
  intro hbot
  apply h
  apply le_antisymm
  · intro x hx
    have hxmap :
        e.toLinearMap x ∈
          (⊥ : Submodule (ZMod p)
            (Additive (classGroupPTorsion (R := 𝓞 K) p))) := by
      rw [← hbot, ← hmap]
      exact ⟨x, hx, rfl⟩
    have hxzero : e.toLinearMap x = 0 := by
      simpa using hxmap
    have hxzero' : e x = e 0 := by
      simpa using hxzero
    have hx0 : x = 0 := e.injective hxzero'
    rw [hx0]
    exact Submodule.zero_mem _
  · exact bot_le

/-- Combined finite class-group bridge needed by the primary kernel lower
bound: a nonzero `ClassGroupModP` character component gives the corresponding
nonzero multiplicative class `p`-torsion component. -/
theorem classGroupPTorsionCharacterProjectionComponent_ne_bot_of_modP_component_ne_bot
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (i : ℕ)
    (hmod :
      LinearMap.range
          (CharacterProjection.characterProjection
            (p := p) i (cyclotomicGalActionLinearEquivModP (p := p) (K := K))) ≠
        (⊥ : Submodule (ZMod p) (Additive (ClassGroupModP K p)))) :
    classGroupPTorsionCharacterProjectionComponent
        (K := K) (p := p) i (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥ :=
  classGroupPTorsionCharacterProjectionComponent_ne_bot_of_additivePTorsion
    p K i
    (classGroup_additivePTorsion_component_nontrivial_of_modP_component_ne_bot
      p K i hmod)

/-- Complete finite class-group bridge from the public
`eigenspaceComponentNontrivial` predicate to the multiplicative `A[p]`
component used by the singular-Kummer exact sequence. -/
theorem classGroupPTorsionCharacterProjectionComponent_ne_bot_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (i : ℕ)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    classGroupPTorsionCharacterProjectionComponent
        (K := K) (p := p) i (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥ :=
  classGroupPTorsionCharacterProjectionComponent_ne_bot_of_modP_component_ne_bot
    p K i
    (classGroupModP_characterProjectionComponent_ne_bot_of_eigenspaceComponentNontrivial
      p K i hcomp)

/-- A nonzero linear character of Galois weight `k` detects a nonzero
`k`-eigenspace component of `Cl(O_K)/p`.

This is the final projection step in weak reflection: once the residue-symbol
pairing produces a nontrivial character with the reflected Galois weight, the
standard character idempotent produces a nonzero vector in the reflected
component. -/
theorem eigenspaceComponentNontrivial_of_nontrivial_linear_character
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (k : ℕ)
    (φ : Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p)
    (hφ_galois : ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      φ (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ k) * φ v)
    (hφ_nontrivial : ∃ v : Additive (ClassGroupModP K p), φ v ≠ 0) :
    eigenspaceComponentNontrivial p K k :=
  eigenspace_nontrivial_of_phi_nontrivial
    (standardEigenspaceProjectionData
      (cyclotomicGalActionInstance (p := p) (K := K)) φ k
      hφ_galois (finalReflection_card_zMod_units_isUnit p))
    hφ_nontrivial

/-- Injective residue-symbol character families give nontrivial reflected
components.

This is the abstract no-sorry endpoint for the primary pseudo-unit strategy.
The intended later instantiation is:

* `Primary` is the locally-primary pseudo-unit component `V_i^0`;
* `characterFamily x` is the residue-symbol character attached to `x`;
* `h_injective` is the nondegeneracy theorem for the Kummer pairing;
* `h_galois` is the Galois covariance computation, with `k` the reflected
  component index.

The theorem itself is only linear algebra plus the explicit eigenspace
projection above. -/
theorem eigenspaceComponentNontrivial_of_injective_character_family
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (k : ℕ)
    (Primary : Type*) [AddCommGroup Primary] [Module (ZMod p) Primary]
    [Nontrivial Primary]
    (characterFamily :
      Primary →ₗ[ZMod p] (Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p))
    (h_injective : Function.Injective characterFamily)
    (h_galois : ∀ (x : Primary) (a : (ZMod p)ˣ)
        (v : Additive (ClassGroupModP K p)),
      characterFamily x
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ k) * characterFamily x v) :
    eigenspaceComponentNontrivial p K k := by
  obtain ⟨x, hx_ne⟩ : ∃ x : Primary, x ≠ 0 := exists_ne (0 : Primary)
  let φ : Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p := characterFamily x
  have hφ_nontrivial : ∃ v : Additive (ClassGroupModP K p), φ v ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hφ_eq_zero : characterFamily x = 0 := by
      ext v
      exact hzero v
    apply hx_ne
    apply h_injective
    simpa using hφ_eq_zero
  exact eigenspaceComponentNontrivial_of_nontrivial_linear_character
    p K k φ (h_galois x) hφ_nontrivial

/-- Weak-reflection endpoint from an injective primary-pseudo-unit character
family with the reflected Galois weight.

This is the form the explicit residue-symbol pairing should instantiate after
the primary localization-kernel construction and nondegeneracy theorem are in
place. -/
theorem weakReflection_componentNontrivial_of_injective_reflected_character_family
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {i : ℕ}
    (Primary : Type*) [AddCommGroup Primary] [Module (ZMod p) Primary]
    [Nontrivial Primary]
    (characterFamily :
      Primary →ₗ[ZMod p] (Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p))
    (h_injective : Function.Injective characterFamily)
    (h_galois : ∀ (x : Primary) (a : (ZMod p)ˣ)
        (v : Additive (ClassGroupModP K p)),
      characterFamily x
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ reflectedComponentIndex p i) * characterFamily x v) :
    eigenspaceComponentNontrivial p K (reflectedComponentIndex p i) :=
  eigenspaceComponentNontrivial_of_injective_character_family
    p K (reflectedComponentIndex p i) Primary characterFamily h_injective h_galois

/-- The completed localization-kernel lower bound gives a nontrivial primary
pseudo-unit space once the matching class `p`-torsion component is nonzero.

This repackages the proved dimension estimate
`completedLocalizationKernel_finrank_ge_classComponent_of_even_power_character`
into the `Nontrivial` typeclass shape needed by
`weakReflection_componentNontrivial_of_injective_reflected_character_family`.
It does not assert the remaining bridge from `ClassGroupModP` nontriviality to
the class `p`-torsion component; that is a separate finite-group/component
comparison step. -/
theorem completedLocalizationKernel_nontrivial_of_classPTorsion_component
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hA_ne_bot :
      Reflection.SingularKummer.SingularPair.classGroupPTorsionCharacterProjectionComponent
          (K := K) (p := p) i
          (Reflection.SingularKummer.SingularPair.cyclotomicClassGroupPTorsionAction K p) ≠
        ⊥) :
    Nontrivial
      (LinearMap.ker
        (Reflection.SingularKummer.SingularPair.singularGroupCompletedLocalizationComponentMap
          (K := K) (p := p) (i := i))) := by
  let Acomp :=
    Reflection.SingularKummer.SingularPair.classGroupPTorsionCharacterProjectionComponent
      (K := K) (p := p) i
      (Reflection.SingularKummer.SingularPair.cyclotomicClassGroupPTorsionAction K p)
  let Primary :=
    LinearMap.ker
      (Reflection.SingularKummer.SingularPair.singularGroupCompletedLocalizationComponentMap
        (K := K) (p := p) (i := i))
  have hle :
      Module.finrank (ZMod p) Acomp ≤ Module.finrank (ZMod p) Primary := by
    simpa [Acomp, Primary] using
      completedLocalizationKernel_finrank_ge_classComponent_of_even_power_character
        (K := K) (p := p) hp_gt_two hi_even hi_low hi_high
  haveI : Nontrivial Acomp := Submodule.nontrivial_iff_ne_bot.mpr (by
    simpa [Acomp] using hA_ne_bot)
  have hA_pos : 0 < Module.finrank (ZMod p) Acomp := Module.finrank_pos
  have hPrimary_pos : 0 < Module.finrank (ZMod p) Primary :=
    lt_of_lt_of_le hA_pos hle
  exact Module.nontrivial_of_finrank_pos hPrimary_pos

/-- From a nontrivial public class-group mod-`p` component, the completed
localization kernel in the same even interior component is nontrivial.

This is the fully assembled lower-bound step:

`A_i != 0` in `Cl(O_K)/p` gives `A[p]_i != 0`, and the proved local-primary
dimension estimate gives `V_i^0 != 0`. -/
theorem completedLocalizationKernel_nontrivial_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    Nontrivial
      (LinearMap.ker
        (Reflection.SingularKummer.SingularPair.singularGroupCompletedLocalizationComponentMap
          (K := K) (p := p) (i := i))) :=
  completedLocalizationKernel_nontrivial_of_classPTorsion_component
    p K hp_gt_two hi_even hi_low hi_high
    (classGroupPTorsionCharacterProjectionComponent_ne_bot_of_eigenspaceComponentNontrivial
      p K i hcomp)

/-- Representative form of the primary pseudo-unit lower-bound step.

From a nonzero `A[p]_i` character component, the completed-localization
argument produces a singular pair `(I, eta)` in the `i`-component whose
singular class is nontrivial, whose completed lambda-localization vanishes,
and whose generator satisfies the singular relation `(eta) = I^p`.

This is the concrete data needed before constructing the residue-symbol
character attached to `eta`. -/
theorem exists_primarySingularPair_of_classPTorsion_component
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent
          (K := K) (p := p) i (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    ∃ s : Reflection.SingularKummer.SingularPair (𝓞 K) K p,
      ∃ _hs_component :
        Additive.ofMul
            (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ∈
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p),
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
          (Additive.ofMul
            (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        toPrincipalIdeal (𝓞 K) K (generator s) = ideal s ^ p ∧
        ∀ b : Reflection.SingularKummer.CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  haveI : FiniteDimensional (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p)) :=
    singularGroupCharacterProjectionComponent_finiteDimensional_of_even_power_character
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high
  exact exists_singularPair_in_concrete_completed_localization_kernel
    (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot

/-- Public-input version of `exists_primarySingularPair_of_classPTorsion_component`.

It starts from `eigenspaceComponentNontrivial p K i` and performs the finite
bridge to the matching `A[p]_i` component before invoking the existing
completed-localization-kernel representative theorem. -/
theorem exists_primarySingularPair_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    ∃ s : Reflection.SingularKummer.SingularPair (𝓞 K) K p,
      ∃ _hs_component :
        Additive.ofMul
            (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ∈
          singularGroupCharacterProjectionComponent (K := K) (p := p) i
            (cyclotomicSingularGroupAction K p),
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
          (Additive.ofMul
            (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        toPrincipalIdeal (𝓞 K) K (generator s) = ideal s ^ p ∧
        ∀ b : Reflection.SingularKummer.CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p) :=
  exists_primarySingularPair_of_classPTorsion_component
    p K hp_gt_two hi_even hi_low hi_high
    (classGroupPTorsionCharacterProjectionComponent_ne_bot_of_eigenspaceComponentNontrivial
      p K i hcomp)

/-- In the prime cyclotomic field, the rational prime ideal `(p)` is the
`(p - 1)`-st power of the distinguished lambda prime. -/
theorem span_natCast_prime_eq_zetaPrime_pow
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) = zetaPrime p K ^ (p - 1) := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζpow :
      IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simpa only [zero_add, pow_one] using (IsCyclotomicExtension.zeta_spec p ℚ K)
  have hmap :=
    IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow
      (p := p) (k := 0) (K := K) hζpow
  have hfin : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank K
      (Polynomial.cyclotomic.irreducible_rat (Fact.out : Nat.Prime p).pos),
      Nat.totient_prime (Fact.out : Nat.Prime p)]
  rw [hfin] at hmap
  simpa [zetaPrime, Ideal.map_span, Set.image_singleton] using hmap

/-- Integral-normalized public-input version of the primary singular-pair
extraction.  This is the representative shape needed before passing from
the singular group to an integral residue-symbol numerator. -/
theorem exists_integral_normalized_primarySingularPair_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ t : SingularPair (𝓞 K) K p,
      ∃ gamma : Kˣ,
      ∃ J : (Ideal (𝓞 K))⁰,
        generator t = generator s * gamma ^ p ∧
        ideal t = FractionalIdeal.mk0 K J ∧
        IsCoprime (J : Ideal (𝓞 K)) (zetaPrime p K) ∧
        toPrincipalIdeal (𝓞 K) K (generator t) =
          (FractionalIdeal.mk0 K J) ^ p ∧
        (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) =
          QuotientGroup.mk s ∧
        ∃ _ht_component :
          Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p) ∈
            singularGroupCharacterProjectionComponent (K := K) (p := p) i
              (cyclotomicSingularGroupAction K p),
          (QuotientGroup.mk t :
              SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
          singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
            (Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
          ∀ b : Reflection.SingularKummer.CharacterProjection.Delta p,
            Additive.ofMul
                (cyclotomicSingularGroupAction K p b
                  (QuotientGroup.mk t :
                    SingularGroup (R := 𝓞 K) (K := K) p)) =
              ((b : ZMod p) ^ i) •
                Additive.ofMul
                  (QuotientGroup.mk t :
                    SingularGroup (R := 𝓞 K) (K := K) p) := by
  haveI : FiniteDimensional (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p)) :=
    singularGroupCharacterProjectionComponent_finiteDimensional_of_even_power_character
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high
  haveI : (zetaPrime p K).IsMaximal :=
    Ideal.IsPrime.isMaximal (zetaPrime_isPrime p K) (zetaPrime_ne_bot p K)
  exact
    exists_integral_coprime_normalized_singularPair_in_concrete_completed_localization_kernel
      (K := K) (p := p) (P := zetaPrime p K) hp_gt_two hi_even hi_low hi_high
      (classGroupPTorsionCharacterProjectionComponent_ne_bot_of_eigenspaceComponentNontrivial
        p K i hcomp)

/-- Integral numerator extracted from the normalized primary singular pair.

This packages the output of integral normalization in the shape needed by the
residue-symbol API: an actual `η : O_K`, nonzero and locally primary at
lambda, prime to `p`, with `(η) = J^p`, whose image in `K` is the normalized
singular-pair generator.  Nontriviality of the singular quotient also proves
that this numerator is not a global `p`-th power. -/
theorem exists_integral_numerator_primarySingularPair_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    ∃ η : 𝓞 K,
      ∃ t : SingularPair (𝓞 K) K p,
      ∃ J : (Ideal (𝓞 K))⁰,
        η ≠ 0 ∧
        Furtwaengler.IsLambdaLocalPthPower (p := p) (K := K) η ∧
        IsCoprime
          (Ideal.span ({η} : Set (𝓞 K)))
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) ∧
        (¬ ∃ β : K, β ^ p = (η : K)) ∧
        algebraMap (𝓞 K) K η = (generator t : K) ∧
        Ideal.span ({η} : Set (𝓞 K)) = (J : Ideal (𝓞 K)) ^ p ∧
        ideal t = FractionalIdeal.mk0 K J ∧
        (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
          (Additive.ofMul
            (QuotientGroup.mk t :
              SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        ∀ b : Reflection.SingularKummer.CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk t :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk t :
                  SingularGroup (R := 𝓞 K) (K := K) p) := by
  obtain ⟨_s, t, _gamma, J, _ht_generator, ht_ideal, hJ_coprime, ht_principal, _hclass,
    _ht_component, ht_ne, ht_loc, ht_eigen⟩ :=
    exists_integral_normalized_primarySingularPair_of_eigenspaceComponentNontrivial
      (p := p) (K := K) hp_gt_two hi_even hi_low hi_high hcomp
  obtain ⟨η, hη_cast, hη_span⟩ :=
    exists_integral_generator_of_principal_eq_mk0_pow
      (R := 𝓞 K) (K := K) (p := p) (g := generator t) (J := J) ht_principal
  have hη_ne : η ≠ 0 := by
    intro hη_zero
    have hgen_zero : ((generator t : Kˣ) : K) = 0 := by
      simpa [hη_zero] using hη_cast.symm
    exact (generator t).ne_zero hgen_zero
  have hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K) := by
    intro hpow
    apply not_isPow_generator_of_singularGroup_mk_ne_one
      (R := 𝓞 K) (K := K) (p := p) (Fact.out : Nat.Prime p).ne_zero t ht_ne
    rcases hpow with ⟨β, hβ⟩
    exact ⟨β, hβ.trans hη_cast⟩
  have hη_local : Furtwaengler.IsLambdaLocalPthPower (p := p) (K := K) η :=
    Furtwaengler.IsLambdaLocalPthPower.of_singularPair_completedLocalization_eq_zero
      (p := p) (K := K) (s := t) hη_ne hη_cast ht_loc
  have hη_lambda :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K))) (zetaPrime p K) := by
    rw [hη_span]
    exact hJ_coprime.pow_left
  have hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) := by
    rw [span_natCast_prime_eq_zetaPrime_pow (p := p) (K := K)]
    exact hη_lambda.pow_right
  exact ⟨η, t, J, hη_ne, hη_local, hη_prime_to_p, hη_not_pow, hη_cast, hη_span,
    ht_ideal, ht_ne, ht_loc, ht_eigen⟩

/-- WR-03 bridge from the extracted primary pseudo-unit to admissible
principal-symbol vanishing.

The finite bad set `S` must contain the normalized prime factors of `(η)` and
of `(p)`.  For any nonzero principal denominator `(γ)` coprime to `S`, the
canonical residue symbol `(η / (γ))_p` vanishes. -/
theorem exists_integral_numerator_principalSymbol_eq_zero_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    ∃ η : 𝓞 K,
      ∃ t : SingularPair (𝓞 K) K p,
      ∃ J : (Ideal (𝓞 K))⁰,
        η ≠ 0 ∧
        Furtwaengler.IsLambdaLocalPthPower (p := p) (K := K) η ∧
        IsCoprime
          (Ideal.span ({η} : Set (𝓞 K)))
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) ∧
        (¬ ∃ β : K, β ^ p = (η : K)) ∧
        algebraMap (𝓞 K) K η = (generator t : K) ∧
        Ideal.span ({η} : Set (𝓞 K)) = (J : Ideal (𝓞 K)) ^ p ∧
        ideal t = FractionalIdeal.mk0 K J ∧
        (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
          (Additive.ofMul
            (QuotientGroup.mk t :
              SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        (∀ b : Reflection.SingularKummer.CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk t :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk t :
                  SingularGroup (R := 𝓞 K) (K := K) p)) ∧
        ∀ (S : Finset (Ideal (𝓞 K))) (γ : 𝓞 K),
          γ ≠ 0 →
          (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({η} : Set (𝓞 K))), P ∈ S) →
          (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S) →
          (∀ P ∈ S, IsCoprime (Ideal.span ({γ} : Set (𝓞 K))) P) →
          Furtwaengler.pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (Ideal.span ({γ} : Set (𝓞 K))) = 0 := by
  obtain ⟨η, t, J, hη_ne, hη_local, hη_prime_to_p, hη_not_pow, hη_cast,
    hη_span, ht_ideal, ht_ne, ht_loc, ht_eigen⟩ :=
    exists_integral_numerator_primarySingularPair_of_eigenspaceComponentNontrivial
      (p := p) (K := K) hp_gt_two hi_even hi_low hi_high hcomp
  have hp_ne_two : p ≠ 2 := by omega
  have hp_odd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp_ne_two
  refine ⟨η, t, J, hη_ne, hη_local, hη_prime_to_p, hη_not_pow, hη_cast,
    hη_span, ht_ideal, ht_ne, ht_loc, ht_eigen, ?_⟩
  intro S γ hγ_ne hS_eta hS_p hγ_coprime
  exact
    Furtwaengler.locallyPrimaryPseudoUnit_principalSymbol_eq_zero_canonical_of_coprime_badSet
      p hp_odd K (J : Ideal (𝓞 K)) S hη_ne hγ_ne hη_prime_to_p hη_local
      hη_span hS_eta hS_p hγ_coprime

/-- WR-05 bridge from the extracted primary pseudo-unit to a nontrivial
canonical residue-symbol character.

The character is the explicit Kummer-bad-set coprime representative character
from `Reflection.Kummer.CoprimeCharacterSplitting`.  Its nontriviality is
proved by the Kummer splitting engine and uses reciprocity only through
`oneSidedKummerPrincipalReciprocity_canonical`, via the principal-vanishing
corollary already used in WR-03/WR-04. -/
theorem exists_integral_numerator_nontrivial_residueCharacter_of_eigenspaceComponentNontrivial
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    ∃ η : 𝓞 K,
      ∃ t : SingularPair (𝓞 K) K p,
      ∃ J : (Ideal (𝓞 K))⁰,
      ∃ hη_ne : η ≠ 0,
      ∃ hη_local : Furtwaengler.IsLambdaLocalPthPower (p := p) (K := K) η,
      ∃ hη_prime_to_p :
        IsCoprime
          (Ideal.span ({η} : Set (𝓞 K)))
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))),
      ∃ hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K),
      ∃ _hη_cast : algebraMap (𝓞 K) K η = (generator t : K),
      ∃ hη_span : Ideal.span ({η} : Set (𝓞 K)) = (J : Ideal (𝓞 K)) ^ p,
        ideal t = FractionalIdeal.mk0 K J ∧
        (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
        singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
          (Additive.ofMul
            (QuotientGroup.mk t :
              SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
        (∀ b : Reflection.SingularKummer.CharacterProjection.Delta p,
          Additive.ofMul
              (cyclotomicSingularGroupAction K p b
                (QuotientGroup.mk t :
                  SingularGroup (R := 𝓞 K) (K := K) p)) =
            ((b : ZMod p) ^ i) •
              Additive.ofMul
                (QuotientGroup.mk t :
                  SingularGroup (R := 𝓞 K) (K := K) p)) ∧
        ∃ v : Additive (ClassGroupModP K p),
          Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear
            (p := p) (K := K)
            (by omega)
            ((Fact.out : Nat.Prime p).odd_of_ne_two (by omega))
            η hη_ne hη_not_pow (J : Ideal (𝓞 K))
            hη_prime_to_p hη_local hη_span v ≠ 0 := by
  obtain ⟨η, t, J, hη_ne, hη_local, hη_prime_to_p, hη_not_pow, hη_cast,
    hη_span, ht_ideal, ht_ne, ht_loc, ht_eigen⟩ :=
    exists_integral_numerator_primarySingularPair_of_eigenspaceComponentNontrivial
      (p := p) (K := K) hp_gt_two hi_even hi_low hi_high hcomp
  have hp_ne_two : p ≠ 2 := by omega
  have hp_odd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp_ne_two
  have hnontriv :
      ∃ v : Additive (ClassGroupModP K p),
        Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear
          (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow
          (J : Ideal (𝓞 K)) hη_prime_to_p hη_local hη_span v ≠ 0 :=
    Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear_nontrivial_of_not_isPow
      (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow
      (J : Ideal (𝓞 K)) hη_prime_to_p hη_local hη_span
  exact ⟨η, t, J, hη_ne, hη_local, hη_prime_to_p, hη_not_pow, hη_cast,
    hη_span, ht_ideal, ht_ne, ht_loc, ht_eigen, hnontriv⟩

end BernoulliRegular

end
