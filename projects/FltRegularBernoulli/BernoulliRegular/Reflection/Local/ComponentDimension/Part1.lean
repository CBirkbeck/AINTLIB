module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import BernoulliRegular.Reflection.Local.GradedAction
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionIdempotent

/-!
# Local unit component dimensions

This file starts the REF-11d assembly layer.  It packages the completed local
principal-unit quotient `completed U_1 / completed U_1^p` with its additive
`ZMod p` character projectors, using the `Delta` action constructed in
`Local.DeltaAction`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- For `p > 2`, the order of `Delta = (ZMod p)^*` is invertible in
`ZMod p`. -/
theorem deltaCard_isUnit_zmod (hp_gt_two : 2 < p) :
    IsUnit (Fintype.card (SingularKummer.CharacterProjection.Delta p) : ZMod p) := by
  rw [show Fintype.card (SingularKummer.CharacterProjection.Delta p) = p - 1 by
    rw [ZMod.card_units]]
  refine (ZMod.isUnit_iff_coprime (p - 1) p).2 ?_
  have hp_not_dvd : ¬ p ∣ p - 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega : 0 < p - 1) (by omega : p - 1 < p)
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd).symm

/-- The completed local mod-`p` principal-unit quotient action as a
`ZMod p`-linear equivalence. -/
noncomputable def completedPrincipalUnitModPLinearEquivZMod
    (a : CyclotomicUnitDelta p) :
    Additive (completedPrincipalUnitModPQuotient p K) ≃ₗ[ZMod p]
      Additive (completedPrincipalUnitModPQuotient p K) where
  __ := MulEquiv.toAdditive ((completedPrincipalUnitModPDeltaAction (p := p) K) a)
  map_smul' c x :=
    ZMod.map_smul
      ((MulEquiv.toAdditive
        ((completedPrincipalUnitModPDeltaAction (p := p) K) a)).toAddMonoidHom) c x

@[simp]
theorem completedPrincipalUnitModPLinearEquivZMod_apply
    (a : CyclotomicUnitDelta p)
    (x : Additive (completedPrincipalUnitModPQuotient p K)) :
    completedPrincipalUnitModPLinearEquivZMod (p := p) K a x =
      Additive.ofMul ((completedPrincipalUnitModPDeltaAction (p := p) K) a x.toMul) :=
  rfl

/-- The actual `Delta` action on `completed U_1 / completed U_1^p` as a
`ZMod p`-linear action. -/
noncomputable def completedPrincipalUnitModPDeltaActionZMod :
    CyclotomicUnitDelta p →*
      (Additive (completedPrincipalUnitModPQuotient p K) ≃ₗ[ZMod p]
        Additive (completedPrincipalUnitModPQuotient p K)) where
  toFun := completedPrincipalUnitModPLinearEquivZMod (p := p) K
  map_one' := by
    ext x
    apply Additive.ext
    change completedPrincipalUnitModPDeltaAction (p := p) K 1 x.toMul = x.toMul
    simp
  map_mul' a b := by
    ext x
    apply Additive.ext
    change completedPrincipalUnitModPDeltaAction (p := p) K (a * b) x.toMul =
      completedPrincipalUnitModPDeltaAction (p := p) K a
        (completedPrincipalUnitModPDeltaAction (p := p) K b x.toMul)
    rw [map_mul]
    rfl

@[simp]
theorem completedPrincipalUnitModPDeltaActionZMod_apply
    (a : CyclotomicUnitDelta p)
    (x : Additive (completedPrincipalUnitModPQuotient p K)) :
    completedPrincipalUnitModPDeltaActionZMod (p := p) K a x =
      Additive.ofMul ((completedPrincipalUnitModPDeltaAction (p := p) K) a x.toMul) :=
  rfl

/-- The `i`-th character projection on the completed local principal-unit
mod-`p` quotient `completed U_1 / completed U_1^p`. -/
noncomputable def completedPrincipalUnitModPCharacterProjection (i : ℕ) :
    Additive (completedPrincipalUnitModPQuotient p K) →ₗ[ZMod p]
      Additive (completedPrincipalUnitModPQuotient p K) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact SingularKummer.CharacterProjection.characterProjection (p := p) i
    (completedPrincipalUnitModPDeltaActionZMod (p := p) K)

/-- The range of the `i`-th character projection on
`completed U_1 / completed U_1^p`. -/
noncomputable def completedPrincipalUnitModPCharacterProjectionRange (i : ℕ) :
    Submodule (ZMod p) (Additive (completedPrincipalUnitModPQuotient p K)) :=
  LinearMap.range (completedPrincipalUnitModPCharacterProjection (p := p) K i)

set_option synthInstance.maxHeartbeats 80000 in
-- The submodule structure repeatedly synthesizes the quotient's `ZMod p`
-- module instance through additive/multiplicative wrappers.
set_option maxHeartbeats 800000 in
-- The submodule structure repeatedly synthesizes the quotient's `ZMod p`
-- module instance through additive/multiplicative wrappers.
/-- The eigenspace in `completed U_1 / completed U_1^p` for the `j`-th
power character of `Delta`. -/
def completedPrincipalUnitModPDeltaPowerEigenspace (j : ℕ) :
    Submodule (ZMod p) (Additive (completedPrincipalUnitModPQuotient p K)) where
  carrier := {x | ∀ a : CyclotomicUnitDelta p,
    completedPrincipalUnitModPDeltaActionZMod (p := p) K a x =
      ((a : ZMod p) ^ j) • x}
  zero_mem' := by
    intro a
    simp
  add_mem' hx hy := by
    intro a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    rw [map_smul, hx a, smul_smul, smul_smul, mul_comm]

theorem completedPrincipalUnitModPCharacterProjectionRange_eq_eigenspace
    (hp_gt_two : 2 < p) (j : ℕ) :
    completedPrincipalUnitModPCharacterProjectionRange (p := p) K j =
      completedPrincipalUnitModPDeltaPowerEigenspace (p := p) K j := by
  ext x
  constructor
  · intro hx a
    exact SingularKummer.CharacterProjection.mem_characterProjection_range_apply
      (p := p) j (completedPrincipalUnitModPDeltaActionZMod (p := p) K) a hx
  · intro hx
    exact
      SingularKummer.CharacterProjection.mem_characterProjection_range_of_forall_apply_eq_smul
        (p := p) (deltaCard_isUnit_zmod (p := p) hp_gt_two) j
        (completedPrincipalUnitModPDeltaActionZMod (p := p) K) (by
          intro a
          exact hx a)

/-- The additive completed maximal-ideal graded quotient `m^n / m^(n+1)`,
written in the principal-ideal form supplied by
`Ideal.quotEquivPowQuotPowSucc`. -/
abbrev completedMaximalIdealGradedQuotient (n : ℕ) : Type _ :=
  ((completedLocalCyclotomicMaximalIdeal p K) ^ n :
      Ideal (completedLocalCyclotomicRing p K)) ⧸
    (completedLocalCyclotomicMaximalIdeal p K •
      (⊤ : Submodule (completedLocalCyclotomicRing p K)
        ((completedLocalCyclotomicMaximalIdeal p K) ^ n :
          Ideal (completedLocalCyclotomicRing p K))))

/-- The additive local maximal-ideal graded quotient `m^n / m^(n+1)`,
before completion. -/
abbrev localMaximalIdealGradedQuotient (n : ℕ) : Type _ :=
  ((localCyclotomicMaximalIdeal p K) ^ n :
      Ideal (localCyclotomicRing p K)) ⧸
    (localCyclotomicMaximalIdeal p K •
      (⊤ : Submodule (localCyclotomicRing p K)
        ((localCyclotomicMaximalIdeal p K) ^ n :
          Ideal (localCyclotomicRing p K))))

/-- Since the local maximal ideal is principal, every local graded quotient is
the residue field as a plain type. -/
noncomputable def localMaximalIdealGradedQuotientEquivResidue
    (n : ℕ) :
    (localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K) ≃
      localMaximalIdealGradedQuotient p K n :=
  Ideal.quotEquivPowQuotPowSuccEquiv
    (localCyclotomicMaximalIdeal_isPrincipal (p := p) (K := K))
    (localCyclotomicMaximalIdeal_ne_bot (p := p) (K := K)) n

theorem localMaximalIdealGradedQuotient_card (n : ℕ) :
    Nat.card (localMaximalIdealGradedQuotient p K n) = p :=
  (Nat.card_congr
    (localMaximalIdealGradedQuotientEquivResidue (p := p) (K := K) n)).symm.trans
      (localCyclotomicResidueCard (p := p) (K := K))

private theorem factor_evalₐ_pow_le
    {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  simp only [AdicCompletion.evalₐ, AlgHom.coe_comp, Function.comp_apply,
    AlgHom.ofLinearMap_apply]
  have htrans :
      AdicCompletion.transitionMap I R hmn ((AdicCompletion.eval I R n) x) =
        ((AdicCompletion.eval I R m) x) :=
    AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := R) hmn x
  rw [← htrans]
  induction ((AdicCompletion.eval I R n) x) using Quotient.inductionOn' with
  | h r =>
    rfl

/-- The completed quotient by `mhat^N` is the original local quotient by
`m^N`, for every power. -/
noncomputable def completedQuotientPowEquivLocalQuotientPow (N : ℕ) :
    completedLocalCyclotomicRing p K ⧸ completedLocalCyclotomicMaximalIdeal p K ^ N ≃
      localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K ^ N := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  let f : S → R ⧸ M ^ N := AdicCompletion.evalₐ M N
  let e : S ⧸ Mhat ^ N → R ⧸ M ^ N :=
    fun q => Quotient.liftOn' q f (by
      intro a b h
      rw [← sub_eq_zero, ← map_sub]
      have hker : a - b ∈ RingHom.ker (AdicCompletion.evalₐ M N).toRingHom := by
        rw [← completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) N]
        simpa [Mhat] using ((Submodule.quotientRel_def (p := Mhat ^ N)).mp h)
      exact RingHom.mem_ker.mp hker)
  refine Equiv.ofBijective e ?_
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn' with
    | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      change f a = f b at hxy
      apply Ideal.Quotient.eq.mpr
      rw [completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) N]
      rw [RingHom.mem_ker, map_sub]
      exact sub_eq_zero.mpr hxy
  · intro y
    rcases AdicCompletion.surjective_evalₐ M N y with ⟨x, hx⟩
    refine ⟨Ideal.Quotient.mk (Mhat ^ N) x, ?_⟩
    rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk]
    exact hx

@[simp]
theorem completedQuotientPowEquivLocalQuotientPow_mk
    (N : ℕ) (x : completedLocalCyclotomicRing p K) :
    completedQuotientPowEquivLocalQuotientPow (p := p) (K := K) N
      (Ideal.Quotient.mk ((completedLocalCyclotomicMaximalIdeal p K) ^ N) x) =
        AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) N x := by
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk]
  rfl

/-- The local quotient by `m^N` maps back to the completed quotient by
`mhat^N`. -/
noncomputable def localQuotientPowToCompletedQuotientPow (N : ℕ) :
    localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K ^ N ≃
      completedLocalCyclotomicRing p K ⧸ completedLocalCyclotomicMaximalIdeal p K ^ N := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  let g : R ⧸ M ^ N → S ⧸ Mhat ^ N :=
    fun q => Quotient.liftOn' q
      (fun r => Ideal.Quotient.mk (Mhat ^ N) (algebraMap R S r))
      (by
        intro a b h
        rw [Ideal.Quotient.eq]
        rw [← map_sub]
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem (algebraMap R S)
          ((Submodule.quotientRel_def (p := M ^ N)).mp h))
  let e := completedQuotientPowEquivLocalQuotientPow (p := p) (K := K) N
  have hleft : Function.LeftInverse e g := by
    intro q
    induction q using Quotient.inductionOn' with
    | h r =>
      calc
        e ((algebraMap R (S ⧸ Mhat ^ N)) r) =
            e (Ideal.Quotient.mk (Mhat ^ N) (algebraMap R S r)) := rfl
        _ = AdicCompletion.evalₐ M N (algebraMap R S r) := by
          rw [completedQuotientPowEquivLocalQuotientPow_mk]
        _ = Ideal.Quotient.mk (M ^ N) r := by
          change AdicCompletion.evalₐ M N (AdicCompletion.of M R r) =
            Ideal.Quotient.mk (M ^ N) r
          exact AdicCompletion.evalₐ_of (I := M) N r
  refine ⟨g, e, hleft, ?_⟩
  intro q
  exact e.injective (hleft (e q))

@[simp]
theorem localQuotientPowToCompletedQuotientPow_mk
    (N : ℕ) (x : localCyclotomicRing p K) :
    localQuotientPowToCompletedQuotientPow (p := p) (K := K) N
      (Ideal.Quotient.mk ((localCyclotomicMaximalIdeal p K) ^ N) x) =
        Ideal.Quotient.mk ((completedLocalCyclotomicMaximalIdeal p K) ^ N)
          (algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K) x) :=
  rfl

theorem completedQuotientPowEquivLocalQuotientPow_mem_map_pow
    (n : ℕ)
    {q : completedLocalCyclotomicRing p K ⧸
        completedLocalCyclotomicMaximalIdeal p K ^ (n + 1)}
    (hq : q ∈ Ideal.map
        (Ideal.Quotient.mk ((completedLocalCyclotomicMaximalIdeal p K) ^ (n + 1)))
        ((completedLocalCyclotomicMaximalIdeal p K) ^ n)) :
    completedQuotientPowEquivLocalQuotientPow (p := p) (K := K) (n + 1) q ∈
      Ideal.map
        (Ideal.Quotient.mk ((localCyclotomicMaximalIdeal p K) ^ (n + 1)))
        ((localCyclotomicMaximalIdeal p K) ^ n) := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  rcases Ideal.mem_image_of_mem_map_of_surjective
      (Ideal.Quotient.mk (Mhat ^ (n + 1))) Ideal.Quotient.mk_surjective hq with
    ⟨x, hx, rfl⟩
  rw [completedQuotientPowEquivLocalQuotientPow_mk]
  show AdicCompletion.evalₐ M (n + 1) x ∈
    Ideal.map (Ideal.Quotient.mk (M ^ (n + 1))) (M ^ n)
  have hxker : x ∈ RingHom.ker (AdicCompletion.evalₐ M n).toRingHom := by
    rw [← completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) n]
    simpa [Mhat] using hx
  rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right n.le_succ)]
  rw [RingHom.mem_ker]
  rw [factor_evalₐ_pow_le M n.le_succ]
  exact RingHom.mem_ker.mp hxker

theorem localQuotientPowToCompletedQuotientPow_mem_map_pow
    (n : ℕ)
    {q : localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K ^ (n + 1)}
    (hq : q ∈ Ideal.map
        (Ideal.Quotient.mk ((localCyclotomicMaximalIdeal p K) ^ (n + 1)))
        ((localCyclotomicMaximalIdeal p K) ^ n)) :
    localQuotientPowToCompletedQuotientPow (p := p) (K := K) (n + 1) q ∈
      Ideal.map
        (Ideal.Quotient.mk ((completedLocalCyclotomicMaximalIdeal p K) ^ (n + 1)))
        ((completedLocalCyclotomicMaximalIdeal p K) ^ n) := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  rcases Ideal.mem_image_of_mem_map_of_surjective
      (Ideal.Quotient.mk (M ^ (n + 1))) Ideal.Quotient.mk_surjective hq with
    ⟨x, hx, rfl⟩
  change Ideal.Quotient.mk (Mhat ^ (n + 1)) (algebraMap R S x) ∈
    Ideal.map (Ideal.Quotient.mk (Mhat ^ (n + 1))) (Mhat ^ n)
  refine Ideal.mem_map_of_mem _ ?_
  change algebraMap R S x ∈ (completedLocalCyclotomicMaximalIdeal p K) ^ n
  rw [completedLocalCyclotomicMaximalIdeal, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem (algebraMap R S) hx

/-- The completed and local maximal-ideal graded image ideals agree through
the quotient equivalence. -/
noncomputable def completedMaximalIdealGradedImageEquivLocal (n : ℕ) :
    Ideal.map
        (Ideal.Quotient.mk ((completedLocalCyclotomicMaximalIdeal p K) ^ (n + 1)))
        ((completedLocalCyclotomicMaximalIdeal p K) ^ n) ≃
      Ideal.map
        (Ideal.Quotient.mk ((localCyclotomicMaximalIdeal p K) ^ (n + 1)))
        ((localCyclotomicMaximalIdeal p K) ^ n) where
  toFun q :=
    ⟨completedQuotientPowEquivLocalQuotientPow (p := p) (K := K) (n + 1) q.1,
      completedQuotientPowEquivLocalQuotientPow_mem_map_pow
        (p := p) (K := K) n q.2⟩
  invFun q :=
    ⟨localQuotientPowToCompletedQuotientPow (p := p) (K := K) (n + 1) q.1,
      localQuotientPowToCompletedQuotientPow_mem_map_pow
        (p := p) (K := K) n q.2⟩
  left_inv q := by
    ext
    exact (localQuotientPowToCompletedQuotientPow (p := p) (K := K) (n + 1)).right_inv q.1
  right_inv q := by
    ext
    exact (localQuotientPowToCompletedQuotientPow (p := p) (K := K) (n + 1)).left_inv q.1

/-- The completed maximal-ideal graded quotient is the original local graded
quotient as a plain type. -/
noncomputable def completedMaximalIdealGradedQuotientEquivLocal
    (n : ℕ) :
    completedMaximalIdealGradedQuotient p K n ≃
      localMaximalIdealGradedQuotient p K n :=
  (Ideal.powQuotPowSuccEquivMapMkPowSuccPow
    (completedLocalCyclotomicMaximalIdeal p K) n).trans
    ((completedMaximalIdealGradedImageEquivLocal (p := p) (K := K) n).trans
      (Ideal.powQuotPowSuccEquivMapMkPowSuccPow
        (localCyclotomicMaximalIdeal p K) n).symm)

theorem completedMaximalIdealGradedQuotient_card (n : ℕ) :
    Nat.card (completedMaximalIdealGradedQuotient p K n) = p :=
  (Nat.card_congr
    (completedMaximalIdealGradedQuotientEquivLocal (p := p) (K := K) n)).trans
      (localMaximalIdealGradedQuotient_card (p := p) (K := K) n)

private theorem mem_completedMaximalIdeal_smul_top_iff
    (n : ℕ)
    {x : ((completedLocalCyclotomicMaximalIdeal p K) ^ n :
      Ideal (completedLocalCyclotomicRing p K))} :
    x ∈ completedLocalCyclotomicMaximalIdeal p K •
        (⊤ : Submodule (completedLocalCyclotomicRing p K)
          ((completedLocalCyclotomicMaximalIdeal p K) ^ n :
            Ideal (completedLocalCyclotomicRing p K))) ↔
      (x : completedLocalCyclotomicRing p K) ∈
        completedLocalCyclotomicMaximalIdeal p K ^ (n + 1) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  change x ∈ M • (⊤ : Submodule S (M ^ n : Ideal S)) ↔ (x : S) ∈ M ^ (n + 1)
  rw [Submodule.mem_smul_top_iff]
  change (x : S) ∈ M • (M ^ n : Ideal S) ↔ (x : S) ∈ M ^ (n + 1)
  rw [Ideal.smul_eq_mul, pow_succ']

/-- The completed unit graded map `completed U_n -> m^n / m^(n+1)`,
`u ↦ u - 1`. -/
noncomputable def completedPrincipalUnitGradedToIdealQuotient
    (n : ℕ) [Fact (1 ≤ n)] :
    completedPrincipalUnitSubgroup p K n →*
      Multiplicative (completedMaximalIdealGradedQuotient p K n) :=
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let N : Submodule S (M ^ n : Ideal S) :=
    M • (⊤ : Submodule S (M ^ n : Ideal S))
  let toIdeal : completedPrincipalUnitSubgroup p K n → (M ^ n : Ideal S) := fun u =>
    ⟨((u : completedLocalCyclotomicUnitGroup p K) : S) - 1, by
      have hu := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := n)
        (u := (u : completedLocalCyclotomicUnitGroup p K))).mp u.2
      simpa [S, M] using hu⟩
  {
    toFun := fun u => Multiplicative.ofAdd (Submodule.mkQ N (toIdeal u))
    map_one' := by
      apply Multiplicative.ofAdd.injective
      change Submodule.mkQ N (toIdeal 1) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have htoIdeal_one :
          toIdeal (1 : completedPrincipalUnitSubgroup p K n) = 0 := by
        ext
        simp [toIdeal]
      rw [htoIdeal_one]
      exact N.zero_mem
    map_mul' := by
      intro u v
      rw [← ofAdd_add]
      apply congrArg Multiplicative.ofAdd
      rw [← map_add]
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
      change (Submodule.Quotient.mk (toIdeal (u * v)) :
          (M ^ n : Ideal S) ⧸ N) = Submodule.Quotient.mk (toIdeal u + toIdeal v)
      rw [Submodule.Quotient.eq]
      rw [mem_completedMaximalIdeal_smul_top_iff (p := p) (K := K) n]
      have huM : (((u : completedPrincipalUnitSubgroup p K n) :
            completedLocalCyclotomicUnitGroup p K) : S) - 1 ∈ M ^ n := by
        have hu := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := n)
          (u := (u : completedLocalCyclotomicUnitGroup p K))).mp u.2
        simpa [S, M] using hu
      have hvM : (((v : completedPrincipalUnitSubgroup p K n) :
            completedLocalCyclotomicUnitGroup p K) : S) - 1 ∈ M ^ n := by
        have hv := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := n)
          (u := (v : completedLocalCyclotomicUnitGroup p K))).mp v.2
        simpa [S, M] using hv
      have hprod :
          ((((u : completedPrincipalUnitSubgroup p K n) :
                completedLocalCyclotomicUnitGroup p K) : S) - 1) *
            ((((v : completedPrincipalUnitSubgroup p K n) :
                completedLocalCyclotomicUnitGroup p K) : S) - 1) ∈ M ^ (n + 1) := by
        have hmul :
            ((((u : completedPrincipalUnitSubgroup p K n) :
                  completedLocalCyclotomicUnitGroup p K) : S) - 1) *
              ((((v : completedPrincipalUnitSubgroup p K n) :
                  completedLocalCyclotomicUnitGroup p K) : S) - 1) ∈
                M ^ n * M ^ n :=
          Ideal.mul_mem_mul huM hvM
        have hmul' :
            ((((u : completedPrincipalUnitSubgroup p K n) :
                  completedLocalCyclotomicUnitGroup p K) : S) - 1) *
              ((((v : completedPrincipalUnitSubgroup p K n) :
                  completedLocalCyclotomicUnitGroup p K) : S) - 1) ∈
                M ^ (n + n) := by
          simpa [pow_add] using hmul
        have hn : 1 ≤ n := Fact.out
        exact Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) hmul'
      convert hprod using 1
      simp [toIdeal, Units.val_mul]
      ring
  }

@[simp]
theorem completedPrincipalUnitGradedToIdealQuotient_apply
    (n : ℕ) [Fact (1 ≤ n)] (u : completedPrincipalUnitSubgroup p K n) :
    completedPrincipalUnitGradedToIdealQuotient (p := p) K n u =
      Multiplicative.ofAdd
        (Submodule.mkQ
          (completedLocalCyclotomicMaximalIdeal p K •
            (⊤ : Submodule (completedLocalCyclotomicRing p K)
              ((completedLocalCyclotomicMaximalIdeal p K) ^ n :
                Ideal (completedLocalCyclotomicRing p K))))
          ⟨((u : completedLocalCyclotomicUnitGroup p K) :
              completedLocalCyclotomicRing p K) - 1, by
            have hu := (mem_completedPrincipalUnitSubgroup_iff
              (p := p) (K := K) (n := n)
              (u := (u : completedLocalCyclotomicUnitGroup p K))).mp u.2
            simpa using hu⟩) :=
  rfl

theorem completedPrincipalUnitGradedToIdealQuotient_surjective
    (n : ℕ) [Fact (1 ≤ n)] :
    Function.Surjective
      (completedPrincipalUnitGradedToIdealQuotient (p := p) K n) := by
  intro y
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let N : Submodule S (M ^ n : Ideal S) :=
    M • (⊤ : Submodule S (M ^ n : Ideal S))
  rcases Quotient.exists_rep y.toAdd with ⟨x, hx⟩
  have hxM : (x : S) ∈ M := by
    simpa [pow_one] using Ideal.pow_le_pow_right (Fact.out : 1 ≤ n) x.2
  have hunit : IsUnit (1 + (x : S)) :=
    isUnit_one_add_of_mem_completedLocalCyclotomicMaximalIdeal (p := p) (K := K) hxM
  let u0 : completedLocalCyclotomicUnitGroup p K := hunit.unit
  have hu0_val : (u0 : S) = 1 + (x : S) := hunit.unit_spec
  have hu0_mem : u0 ∈ completedPrincipalUnitSubgroup p K n := by
    rw [mem_completedPrincipalUnitSubgroup_iff]
    change (u0 : S) - 1 ∈ M ^ n
    rw [hu0_val, add_sub_cancel_left]
    exact x.2
  refine ⟨⟨u0, hu0_mem⟩, ?_⟩
  apply Multiplicative.ofAdd.injective
  change Submodule.mkQ N
      ⟨(u0 : S) - 1, by
        have hu := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := n)
          (u := u0)).mp hu0_mem
        simpa [S, M] using hu⟩ = y.toAdd
  rw [← hx]
  apply congrArg (Submodule.mkQ N)
  ext
  simp [hu0_val]

theorem completedPrincipalUnitGradedToIdealQuotient_ker
    (n : ℕ) [Fact (1 ≤ n)] :
    (completedPrincipalUnitGradedToIdealQuotient (p := p) K n).ker =
      completedPrincipalUnitGradedSubgroup p K n := by
  ext u
  constructor
  · intro hu
    rw [MonoidHom.mem_ker] at hu
    change completedPrincipalUnitGradedToIdealQuotient (p := p) K n u =
      Multiplicative.ofAdd (0 : completedMaximalIdealGradedQuotient p K n) at hu
    have hzero :
        Submodule.mkQ
          (completedLocalCyclotomicMaximalIdeal p K •
            (⊤ : Submodule (completedLocalCyclotomicRing p K)
              ((completedLocalCyclotomicMaximalIdeal p K) ^ n :
                Ideal (completedLocalCyclotomicRing p K))))
          ⟨((u : completedLocalCyclotomicUnitGroup p K) :
              completedLocalCyclotomicRing p K) - 1, by
            have hu' := (mem_completedPrincipalUnitSubgroup_iff
              (p := p) (K := K) (n := n)
              (u := (u : completedLocalCyclotomicUnitGroup p K))).mp u.2
            simpa using hu'⟩ = 0 := by
      simpa [completedPrincipalUnitGradedToIdealQuotient_apply] using
        (Multiplicative.ofAdd.injective hu)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
    rw [completedPrincipalUnitGradedSubgroup,
      Subgroup.mem_subgroupOf, mem_completedPrincipalUnitSubgroup_iff]
    exact (mem_completedMaximalIdeal_smul_top_iff (p := p) (K := K) n).mp hzero
  · intro hu
    rw [completedPrincipalUnitGradedSubgroup, Subgroup.mem_subgroupOf,
      mem_completedPrincipalUnitSubgroup_iff] at hu
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [completedPrincipalUnitGradedToIdealQuotient_apply]
    change Submodule.mkQ
      (completedLocalCyclotomicMaximalIdeal p K •
        (⊤ : Submodule (completedLocalCyclotomicRing p K)
          ((completedLocalCyclotomicMaximalIdeal p K) ^ n :
            Ideal (completedLocalCyclotomicRing p K))))
      ⟨((u : completedLocalCyclotomicUnitGroup p K) :
          completedLocalCyclotomicRing p K) - 1, _⟩ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (mem_completedMaximalIdeal_smul_top_iff (p := p) (K := K) n).mpr hu

/-- The completed unit graded quotient is the corresponding additive
maximal-ideal graded quotient, in multiplicative notation. -/
noncomputable def completedPrincipalUnitGradedQuotientEquivIdealQuotient
    (n : ℕ) [Fact (1 ≤ n)] :
    completedPrincipalUnitGradedQuotient p K n ≃*
      Multiplicative (completedMaximalIdealGradedQuotient p K n) :=
  (QuotientGroup.quotientMulEquivOfEq
    (completedPrincipalUnitGradedToIdealQuotient_ker (p := p) (K := K) n).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (completedPrincipalUnitGradedToIdealQuotient (p := p) K n)
        (completedPrincipalUnitGradedToIdealQuotient_surjective (p := p) (K := K) n))

theorem completedPrincipalUnitGradedQuotient_card_eq_idealQuotient
    (n : ℕ) [Fact (1 ≤ n)] :
    Nat.card (completedPrincipalUnitGradedQuotient p K n) =
      Nat.card (completedMaximalIdealGradedQuotient p K n) := by
  calc
    Nat.card (completedPrincipalUnitGradedQuotient p K n) =
        Nat.card (Multiplicative (completedMaximalIdealGradedQuotient p K n)) :=
      Nat.card_congr
        (completedPrincipalUnitGradedQuotientEquivIdealQuotient
          (p := p) (K := K) n).toEquiv
    _ = Nat.card (completedMaximalIdealGradedQuotient p K n) :=
      Nat.card_congr Multiplicative.toAdd

theorem completedPrincipalUnitGradedQuotient_card
    (n : ℕ) [Fact (1 ≤ n)] :
    Nat.card (completedPrincipalUnitGradedQuotient p K n) = p :=
  (completedPrincipalUnitGradedQuotient_card_eq_idealQuotient
    (p := p) (K := K) n).trans
      (completedMaximalIdealGradedQuotient_card (p := p) (K := K) n)

theorem completedPrincipalUnitGradedQuotient_additive_card
    (n : ℕ) [Fact (1 ≤ n)] :
    Nat.card (Additive (completedPrincipalUnitGradedQuotient p K n)) = p :=
  (Nat.card_congr Additive.toMul).trans
    (completedPrincipalUnitGradedQuotient_card (p := p) (K := K) n)

theorem completedPrincipalUnitGradedQuotient_finrank_one
    (n : ℕ) [Fact (1 ≤ n)] :
    Module.finrank (ZMod p)
      (Additive (completedPrincipalUnitGradedQuotient p K n)) = 1 := by
  let V := Additive (completedPrincipalUnitGradedQuotient p K n)
  have hcard : Nat.card V = p :=
    completedPrincipalUnitGradedQuotient_additive_card (p := p) (K := K) n
  haveI : Finite V := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (Fact.out : p.Prime).ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hpow : p ^ Module.finrank (ZMod p) V = p := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcard, Nat.card_zmod] at h
    exact h.symm
  exact ((Fact.out : p.Prime).pow_eq_iff.mp hpow).2

/-- On the `n`-th completed graded quotient, the `n`-th character projector
has full range. -/
theorem completedPrincipalUnitGradedCharacterProjectionRange_eq_top_self
    (hp_gt_two : 2 < p) (n : ℕ) [Fact (1 ≤ n)] :
    completedPrincipalUnitGradedCharacterProjectionRange (p := p) K n n = ⊤ := by
  ext x
  constructor
  · intro _hx
    exact Submodule.mem_top
  · intro _hx
    exact
      SingularKummer.CharacterProjection.mem_characterProjection_range_of_forall_apply_eq_smul
        (p := p) (deltaCard_isUnit_zmod (p := p) hp_gt_two) n
        (completedPrincipalUnitGradedDeltaActionZMod (p := p) K n)
        (by
          intro a
          exact completedPrincipalUnitGradedDeltaActionZMod_apply_eq_smul
            (p := p) (K := K) n a x)

theorem completedPrincipalUnitGradedCharacterProjectionRange_finrank_self
    (hp_gt_two : 2 < p) (n : ℕ) [Fact (1 ≤ n)] :
    Module.finrank (ZMod p)
        (completedPrincipalUnitGradedCharacterProjectionRange (p := p) K n n) =
      Module.finrank (ZMod p)
        (Additive (completedPrincipalUnitGradedQuotient p K n)) := by
  rw [completedPrincipalUnitGradedCharacterProjectionRange_eq_top_self
    (p := p) (K := K) hp_gt_two n]
  simp

theorem completedPrincipalUnitGradedCharacterProjectionRange_finrank_self_one
    (hp_gt_two : 2 < p) (n : ℕ) [Fact (1 ≤ n)] :
    Module.finrank (ZMod p)
        (completedPrincipalUnitGradedCharacterProjectionRange (p := p) K n n) = 1 := by
  rw [completedPrincipalUnitGradedCharacterProjectionRange_finrank_self
    (p := p) (K := K) hp_gt_two n]
  exact completedPrincipalUnitGradedQuotient_finrank_one (p := p) (K := K) n

/-- Inclusion of a deeper completed principal-unit subgroup into `completed U_1`. -/
def completedPrincipalUnitSubgroupToOne (n : ℕ) (hn : 1 ≤ n) :
    completedPrincipalUnitSubgroup p K n →*
      completedPrincipalUnitSubgroup p K 1 where
  toFun u :=
    ⟨(u : completedLocalCyclotomicUnitGroup p K),
      completedPrincipalUnitSubgroup_mono (p := p) (K := K) hn u.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem completedPrincipalUnitSubgroupToOne_coe
    (n : ℕ) (hn : 1 ≤ n) (u : completedPrincipalUnitSubgroup p K n) :
    ((completedPrincipalUnitSubgroupToOne (p := p) (K := K) n hn u :
        completedPrincipalUnitSubgroup p K 1) :
        completedLocalCyclotomicUnitGroup p K) =
      (u : completedLocalCyclotomicUnitGroup p K) :=
  rfl

/-- The quotient class map `completed U_n -> completed U_1 / completed U_1^p`. -/
def completedPrincipalUnitModPClassOfLevel (n : ℕ) (hn : 1 ≤ n) :
    completedPrincipalUnitSubgroup p K n →*
      completedPrincipalUnitModPQuotient p K :=
  (completedPrincipalUnitModPClass p K).comp
    (completedPrincipalUnitSubgroupToOne (p := p) (K := K) n hn)

@[simp]
theorem completedPrincipalUnitModPClassOfLevel_apply
    (n : ℕ) (hn : 1 ≤ n) (u : completedPrincipalUnitSubgroup p K n) :
    completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn u =
      completedPrincipalUnitModPClass p K
        (completedPrincipalUnitSubgroupToOne (p := p) (K := K) n hn u) :=
  rfl

/-- The image of `completed U_n` inside the additive quotient
`completed U_1 / completed U_1^p`. -/
def completedPrincipalUnitModPFiltrationAddSubgroup (n : ℕ) (hn : 1 ≤ n) :
    AddSubgroup (Additive (completedPrincipalUnitModPQuotient p K)) :=
  (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn).toAdditive.range

/-- The image of `completed U_n` inside the additive quotient, as a
`ZMod p`-submodule. -/
def completedPrincipalUnitModPFiltration (n : ℕ) (hn : 1 ≤ n) :
    Submodule (ZMod p) (Additive (completedPrincipalUnitModPQuotient p K)) :=
  AddSubgroup.toZModSubmodule p
    (completedPrincipalUnitModPFiltrationAddSubgroup (p := p) (K := K) n hn)

theorem mem_completedPrincipalUnitModPFiltration_iff
    (n : ℕ) (hn : 1 ≤ n)
    {x : Additive (completedPrincipalUnitModPQuotient p K)} :
    x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) n hn ↔
      ∃ u : completedPrincipalUnitSubgroup p K n,
        x = Additive.ofMul
          (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn u) := by
  constructor
  · intro hx
    change x ∈
      (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn).toAdditive.range at hx
    rcases hx with ⟨u, hu⟩
    exact ⟨u, hu.symm⟩
  · rintro ⟨u, rfl⟩
    change Additive.ofMul
        ((completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn) u) ∈
      (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn).toAdditive.range
    exact ⟨u, rfl⟩

theorem completedPrincipalUnitModPFiltration_mono
    {m n : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (h : n ≤ m) :
    completedPrincipalUnitModPFiltration (p := p) (K := K) m hm ≤
      completedPrincipalUnitModPFiltration (p := p) (K := K) n hn := by
  intro x hx
  rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) m hm] at hx
  rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) n hn]
  rcases hx with ⟨u, rfl⟩
  let v : completedPrincipalUnitSubgroup p K n :=
    ⟨(u : completedLocalCyclotomicUnitGroup p K),
      completedPrincipalUnitSubgroup_mono (p := p) (K := K) h u.2⟩
  refine ⟨v, ?_⟩
  apply Additive.ext
  rfl

theorem completedPrincipalUnitModPFiltration_succ_le
    (n : ℕ) (hn : 1 ≤ n) :
    completedPrincipalUnitModPFiltration (p := p) (K := K) (n + 1) (Nat.le_succ_of_le hn) ≤
      completedPrincipalUnitModPFiltration (p := p) (K := K) n hn :=
  completedPrincipalUnitModPFiltration_mono (p := p) (K := K)
    hn (Nat.le_succ_of_le hn) (Nat.le_succ n)

theorem completedPrincipalUnitModPFiltration_one_eq_top :
    completedPrincipalUnitModPFiltration (p := p) (K := K) 1 (by decide) = ⊤ := by
  ext x
  constructor
  · intro _hx
    exact Submodule.mem_top
  · intro _hx
    cases x with
    | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro u
      rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) 1 (by decide)]
      exact ⟨u, rfl⟩

theorem completedPrincipalUnitModPClassOfLevel_p_add_one_eq_one
    (hp1 : 1 ≤ p + 1)
    (u : completedPrincipalUnitSubgroup p K (p + 1)) :
    completedPrincipalUnitModPClassOfLevel (p := p) (K := K) (p + 1)
        hp1 u = 1 := by
  rw [completedPrincipalUnitModPClassOfLevel_apply]
  exact (QuotientGroup.eq_one_iff
    (N := completedPrincipalUnitModPSubgroup p K)
    (completedPrincipalUnitSubgroupToOne (p := p) (K := K) (p + 1) hp1 u)).2 (by
      rw [completedPrincipalUnitModPSubgroup_eq_p_add_one (p := p) (K := K)]
      rw [mem_completedPrincipalUnitPAddOneSubgroup_iff]
      exact u.2)

theorem completedPrincipalUnitModPFiltration_p_add_one_eq_bot :
    completedPrincipalUnitModPFiltration (p := p) (K := K) (p + 1)
        (by omega : 1 ≤ p + 1) = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) (p + 1)
      (by omega : 1 ≤ p + 1)] at hx
    rcases hx with ⟨u, rfl⟩
    rw [completedPrincipalUnitModPClassOfLevel_p_add_one_eq_one
      (p := p) (K := K) (by omega : 1 ≤ p + 1) u]
    rfl
  · intro hx
    rw [Submodule.mem_bot] at hx
    rw [hx]
    exact Submodule.zero_mem _

theorem completedPrincipalUnitGradedClass_eq_of_modPClassOfLevel_eq
    (n : ℕ) [Fact (1 ≤ n)] (hnp : n ≤ p)
    {u v : completedPrincipalUnitSubgroup p K n}
    (h : completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n (Fact.out : 1 ≤ n) u =
      completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n (Fact.out : 1 ≤ n) v) :
    completedPrincipalUnitGradedClass p K n u =
      completedPrincipalUnitGradedClass p K n v := by
  apply (QuotientGroup.eq).2
  rw [mem_completedPrincipalUnitGradedSubgroup_iff]
  rw [completedPrincipalUnitModPClassOfLevel_apply,
    completedPrincipalUnitModPClassOfLevel_apply] at h
  have hmod :
      (completedPrincipalUnitSubgroupToOne (p := p) (K := K) n (Fact.out : 1 ≤ n) u)⁻¹ *
          completedPrincipalUnitSubgroupToOne (p := p) (K := K) n (Fact.out : 1 ≤ n) v ∈
        completedPrincipalUnitModPSubgroup p K :=
    (QuotientGroup.eq).1 h
  rw [completedPrincipalUnitModPSubgroup_eq_p_add_one (p := p) (K := K)] at hmod
  rw [mem_completedPrincipalUnitPAddOneSubgroup_iff] at hmod
  change ((u⁻¹ * v : completedPrincipalUnitSubgroup p K n) :
      completedLocalCyclotomicUnitGroup p K) ∈
    completedPrincipalUnitSubgroup p K (n + 1)
  exact completedPrincipalUnitSubgroup_mono (p := p) (K := K)
    (by omega : n + 1 ≤ p + 1) hmod

theorem zmod_smul_toMul_completedPrincipalUnitModP
    (c : ZMod p) (x : Additive (completedPrincipalUnitModPQuotient p K)) :
    (c • x).toMul = x.toMul ^ c.val := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul, toMul_nsmul]

theorem zmod_smul_toMul_completedPrincipalUnitGraded
    (n : ℕ) [Fact (1 ≤ n)] (c : ZMod p)
    (x : Additive (completedPrincipalUnitGradedQuotient p K n)) :
    (c • x).toMul = x.toMul ^ c.val := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul, toMul_nsmul]

end CyclotomicSetup
end Local
end Reflection
end BernoulliRegular

end
