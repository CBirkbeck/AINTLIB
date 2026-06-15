module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelCoefficientReduction
public import BernoulliRegular.Characters

/-!
# Singular Kummer: finite-level Teichmuller character lift

This file constructs the finite-level character lift used by the exact
idempotent argument.  The lift is obtained by taking the `p`-adic
Teichmuller unit and reducing it modulo `p^N`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelCharacterLift

open BernoulliRegular.Reflection.SingularKummer.FiniteLevelCoefficientReduction

variable {p : ℕ} [Fact p.Prime]

/-- Reducing the first finite quotient of `ℤ_[p]` gives the residue map. -/
theorem cast_toZModPow_one_eq_toZMod (x : ℤ_[p]) :
    ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p)
        (PadicInt.toZModPow (p := p) 1 x) =
      PadicInt.toZMod (p := p) x := by
  have hhom :
      (ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p)).comp
          (PadicInt.toZModPow (p := p) 1) =
        PadicInt.toZMod (p := p) := by
    apply ZMod.ringHom_eq_of_ker_eq
    calc
      RingHom.ker ((ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p)).comp
          (PadicInt.toZModPow (p := p) 1))
          = RingHom.ker (PadicInt.toZModPow (p := p) 1) := by
            ext y
            rw [RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply]
            simpa [ZMod.castHom_apply] using
              (ZMod.cast_zmod_eq_zero_iff_of_le
              (m := p ^ 1) (n := p) (by simp [pow_one])
                ((PadicInt.toZModPow (p := p) 1) y))
      _ = RingHom.ker (PadicInt.toZMod (p := p)) := by
            rw [PadicInt.ker_toZModPow, PadicInt.ker_toZMod, pow_one,
              PadicInt.maximalIdeal_eq_span_p]
  exact congrFun (congrArg DFunLike.coe hhom) x

/-- Reduction of the `N`-th finite quotient of `ℤ_[p]` to `ZMod p` is the
residue map. -/
theorem cast_toZModPow_eq_toZMod {N : ℕ} (hN : 1 ≤ N) (x : ℤ_[p]) :
    ZMod.castHom (show p ∣ p ^ N by simpa [pow_one] using pow_dvd_pow p hN)
        (ZMod p) (PadicInt.toZModPow (p := p) N x) =
      PadicInt.toZMod (p := p) x := by
  have hpN : p ∣ p ^ N := by simpa [pow_one] using pow_dvd_pow p hN
  have hp1 : p ∣ p ^ 1 := by simp
  have h1N : p ^ 1 ∣ p ^ N := pow_dvd_pow p hN
  have hcompat := congrFun
    (congrArg DFunLike.coe
      (PadicInt.zmod_cast_comp_toZModPow (p := p) 1 N hN)) x
  have hcastp :
      ZMod.castHom hpN (ZMod p)
          (PadicInt.toZModPow (p := p) N x) =
        ZMod.castHom hp1 (ZMod p)
          (PadicInt.toZModPow (p := p) 1 x) := by
    calc
      ZMod.castHom hpN (ZMod p) (PadicInt.toZModPow (p := p) N x)
          = ZMod.castHom hp1 (ZMod p)
              (ZMod.castHom h1N (ZMod (p ^ 1))
                (PadicInt.toZModPow (p := p) N x)) := by
            have hcomp := congrFun
              (congrArg DFunLike.coe (ZMod.castHom_comp hp1 h1N))
              (PadicInt.toZModPow (p := p) N x)
            simpa [ZMod.castHom_apply] using hcomp.symm
      _ = ZMod.castHom hp1 (ZMod p)
          (PadicInt.toZModPow (p := p) 1 x) :=
            congrArg (ZMod.castHom hp1 (ZMod p)) hcompat
  exact hcastp.trans (cast_toZModPow_one_eq_toZMod (p := p) x)

/-- The `p`-adic Teichmuller value of a unit modulo `p`, as a unit of
`ℤ_[p]`. -/
def teichmullerPadicUnit (a : CharacterProjection.Delta p) : ℤ_[p]ˣ :=
  (isUnit_teichmuller (p := p) (Units.ne_zero a)).unit

@[simp]
theorem teichmullerPadicUnit_val (a : CharacterProjection.Delta p) :
    (teichmullerPadicUnit (p := p) a : ℤ_[p]) =
      teichmuller p (a : ZMod p) :=
  (isUnit_teichmuller (p := p) (Units.ne_zero a)).unit_spec

/-- The Teichmuller lift of `(ZMod p)^*` to units modulo `p^N`. -/
def teichmullerUnitModPow (N : ℕ) :
    CharacterProjection.Delta p →* (ZMod (p ^ N))ˣ where
  toFun a := Units.map (PadicInt.toZModPow (p := p) N) (teichmullerPadicUnit (p := p) a)
  map_one' := by
    ext
    simp [teichmullerPadicUnit]
  map_mul' a b := by
    ext
    simp [teichmullerPadicUnit, teichmuller_mul]

/-- The `i`-th power of the finite-level Teichmuller lift. -/
def teichmullerCharacterModPow (N i : ℕ) :
    CharacterProjection.Delta p →* (ZMod (p ^ N))ˣ :=
  (teichmullerUnitModPow (p := p) N) ^ i

/-- The finite-level Teichmuller unit reduces to the original unit modulo `p`. -/
theorem teichmullerUnitModPow_cast {N : ℕ} (hN : 1 ≤ N)
    (a : CharacterProjection.Delta p) :
    ZMod.castHom (show p ∣ p ^ N by simpa [pow_one] using pow_dvd_pow p hN)
        (ZMod p) (teichmullerUnitModPow (p := p) N a : ZMod (p ^ N)) =
      (a : ZMod p) := by
  rw [teichmullerUnitModPow]
  simp [cast_toZModPow_eq_toZMod (p := p) hN,
    teichmullerPadicUnit_val, toZMod_teichmuller]

/-- The `i`-th power of the finite-level Teichmuller character reduces to
`a ↦ a^i` modulo `p`. -/
theorem teichmullerCharacterModPow_cast {N : ℕ} (hN : 1 ≤ N) (i : ℕ)
    (a : CharacterProjection.Delta p) :
    ZMod.castHom (show p ∣ p ^ N by simpa [pow_one] using pow_dvd_pow p hN)
        (ZMod p) (teichmullerCharacterModPow (p := p) N i a : ZMod (p ^ N)) =
      ((a : ZMod p) ^ i) := by
  rw [teichmullerCharacterModPow]
  change ZMod.castHom (show p ∣ p ^ N by simpa [pow_one] using pow_dvd_pow p hN)
      (ZMod p) ((teichmullerUnitModPow (p := p) N a : ZMod (p ^ N)) ^ i) =
    ((a : ZMod p) ^ i)
  rw [map_pow, teichmullerUnitModPow_cast (p := p) hN]

/-- The order of `Delta = (ZMod p)^*` is invertible modulo `p`. -/
theorem isUnit_card_delta_zmod :
    IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod p) := by
  rw [ZMod.isUnit_iff_coprime, ZMod.card_units]
  exact (Nat.coprime_self_sub_left (Fact.out : p.Prime).one_le).2
    (Nat.coprime_one_left p)

/-- The order of `Delta = (ZMod p)^*` is invertible modulo every `p^N`. -/
theorem isUnit_card_delta_zmod_pow (N : ℕ) :
    IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod (p ^ N)) := by
  rw [ZMod.isUnit_iff_coprime, ZMod.card_units]
  exact ((Nat.coprime_self_sub_left (Fact.out : p.Prime).one_le).2
    (Nat.coprime_one_left p)).pow_right N

variable {A : Type*} [AddCommGroup A] [Finite A]

/-- Final finite-level bridge for a group carrying a `ZMod (p^N)`-module
structure.  The lifted character is supplied by the Teichmuller lift, so the
theorem no longer assumes an abstract character-lift hypothesis. -/
theorem torsionComponentNontrivial_of_elementaryComponentNontrivial_modPow
    {N : ℕ} (hN : 1 ≤ N) (i : ℕ)
    [Module (ZMod (p ^ N)) A]
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (hV : ElementaryQuotientComponent.ElementaryComponentNontrivial
      (p := p) i rho) :
    TorsionComponent.TorsionComponentNontrivial (p := p) i rho := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  exact torsionComponentNontrivial_of_finiteLevelCharacter_cast
      (p := p) (m := p ^ N)
      (hcardp := isUnit_card_delta_zmod (p := p))
      (hcardm := isUnit_card_delta_zmod_pow (p := p) N)
      (hm := by simpa [pow_one] using pow_dvd_pow p hN)
      i rho (teichmullerCharacterModPow (p := p) N i)
      (teichmullerCharacterModPow_cast (p := p) hN i) hV

/-- Final bridge for an additive group killed by a fixed power of `p`. -/
theorem torsionComponentNontrivial_of_elementaryComponentNontrivial_pow_killed
    {N : ℕ} (hN : 1 ≤ N) (hkill : ∀ x : A, p ^ N • x = 0) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (hV : ElementaryQuotientComponent.ElementaryComponentNontrivial
      (p := p) i rho) :
    TorsionComponent.TorsionComponentNontrivial (p := p) i rho := by
  letI : Module (ZMod (p ^ N)) A :=
    AddCommGroup.zmodModule (n := p ^ N) hkill
  exact torsionComponentNontrivial_of_elementaryComponentNontrivial_modPow
    (p := p) (A := A) hN i rho hV

/-- Final bridge when the group is killed by some positive power of `p`. -/
theorem torsionComponentNontrivial_of_elementaryComponentNontrivial_exists_pow_killed
    (hkill : ∃ N : ℕ, 1 ≤ N ∧ ∀ x : A, p ^ N • x = 0) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (hV : ElementaryQuotientComponent.ElementaryComponentNontrivial
      (p := p) i rho) :
    TorsionComponent.TorsionComponentNontrivial (p := p) i rho := by
  obtain ⟨N, hN, hkillN⟩ := hkill
  exact torsionComponentNontrivial_of_elementaryComponentNontrivial_pow_killed
    (p := p) (A := A) hN hkillN i rho hV

namespace FinitePrimaryBridge

open ElementaryQuotientComponent
open FiniteLevelProjectionBridge
open ProjectedSubgroupComparison
open TorsionComponent

variable {A : Type*} [AddCommGroup A] [Finite A]

def primaryComponentAddEquiv (e : A ≃+ A) :
    AddCommGroup.primaryComponent A p ≃+ AddCommGroup.primaryComponent A p where
  toFun x := ⟨e x, by
    rw [AddCommGroup.mem_primaryComponent]
    obtain ⟨k, hk⟩ := (AddCommGroup.mem_primaryComponent).1 x.2
    exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
  invFun x := ⟨e.symm x, by
    rw [AddCommGroup.mem_primaryComponent]
    obtain ⟨k, hk⟩ := (AddCommGroup.mem_primaryComponent).1 x.2
    exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
  map_add' x y := by
    apply Subtype.ext
    change e ((x : A) + (y : A)) = e (x : A) + e (y : A)
    exact map_add e (x : A) (y : A)

omit [Finite A] [Fact p.Prime] in
@[simp]
theorem primaryComponentAddEquiv_apply_coe
    (e : A ≃+ A) (x : AddCommGroup.primaryComponent A p) :
    ((primaryComponentAddEquiv (p := p) e x :
      AddCommGroup.primaryComponent A p) : A) = e x :=
  rfl

def primaryComponentAction
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    CharacterProjection.Delta p →*
      Multiplicative
        (AddCommGroup.primaryComponent A p ≃+ AddCommGroup.primaryComponent A p) where
  toFun d := Multiplicative.ofAdd
    (primaryComponentAddEquiv (p := p) (Multiplicative.toAdd (rho d)))
  map_one' := by
    ext x
    change ((primaryComponentAddEquiv (p := p) (Multiplicative.toAdd (rho 1))) x : A) =
      ((Multiplicative.toAdd (1 : Multiplicative
        (AddCommGroup.primaryComponent A p ≃+ AddCommGroup.primaryComponent A p))) x : A)
    rw [primaryComponentAddEquiv_apply_coe, map_one]
    rfl
  map_mul' a b := by
    ext x
    change ((primaryComponentAddEquiv (p := p) (Multiplicative.toAdd (rho (a * b)))) x : A) =
      ((Multiplicative.toAdd (Multiplicative.ofAdd
          (primaryComponentAddEquiv (p := p) (Multiplicative.toAdd (rho a))) *
          Multiplicative.ofAdd
          (primaryComponentAddEquiv (p := p) (Multiplicative.toAdd (rho b)))) ) x : A)
    rw [primaryComponentAddEquiv_apply_coe, map_mul]
    rfl

omit [Finite A] in
theorem primaryComponent_elementaryQuotientLinearMap_equivariant
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p)
    (x : ElementaryQuotient (AddCommGroup.primaryComponent A p) p) :
    subgroupElementaryQuotientLinearMap (p := p)
        (AddCommGroup.primaryComponent A p)
        (elementaryQuotientAction (p := p) (primaryComponentAction (p := p) rho) d x) =
      elementaryQuotientAction (p := p) rho d
        (subgroupElementaryQuotientLinearMap (p := p)
          (AddCommGroup.primaryComponent A p) x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    change quotientMap A p
        ((primaryComponentAddEquiv (p := p) (Multiplicative.toAdd (rho d))) z : A) =
      quotientMap A p ((Multiplicative.toAdd (rho d)) (z : A))
    rw [primaryComponentAddEquiv_apply_coe]

theorem elementaryComponentNontrivial_primary_of_elementaryComponentNontrivial
    (i : ℕ) (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (hV : ElementaryComponentNontrivial (p := p) i rho) :
    ElementaryComponentNontrivial (p := p) i
      (primaryComponentAction (p := p) rho) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let B := AddCommGroup.primaryComponent A p
  let f : ElementaryQuotient B p →ₗ[ZMod p] ElementaryQuotient A p :=
    subgroupElementaryQuotientLinearMap (p := p) B
  have hmap :
      Submodule.map f
          (elementaryComponent (p := p) i
            (primaryComponentAction (p := p) rho)) =
        elementaryComponent (p := p) i rho :=
    CharacterProjection.map_characterProjection_range_eq_range_of_surjective
      (p := p) i
      (elementaryQuotientAction (p := p) (primaryComponentAction (p := p) rho))
      (elementaryQuotientAction (p := p) rho)
      f
      (primaryComponent_elementaryQuotientLinearMap_surjective
        (p := p) (A := A))
      (primaryComponent_elementaryQuotientLinearMap_equivariant
        (p := p) rho)
  intro hbot
  apply hV
  rw [← hmap, hbot]
  exact Submodule.map_bot f

theorem primaryComponent_exists_pow_killed :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ x : AddCommGroup.primaryComponent A p, p ^ N • x = 0 := by
  let B := AddCommGroup.primaryComponent A p
  have hP : IsPGroup p (Multiplicative B) := by
    intro x
    let z : B := Multiplicative.toAdd x
    obtain ⟨k, hk⟩ : ∃ k : ℕ, addOrderOf (z : A) = p ^ k :=
      (AddCommGroup.mem_primaryComponent_iff_addOrderOf).1 z.2
    refine ⟨k, ?_⟩
    apply Multiplicative.ext
    change (p ^ k • z : B) = 0
    apply Subtype.ext
    change p ^ k • (z : A) = 0
    rw [← hk]
    exact addOrderOf_nsmul_eq_zero (z : A)
  obtain ⟨N, hcardN⟩ := (IsPGroup.iff_card.mp hP)
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  intro x
  have hdvd : addOrderOf x ∣ p ^ N := by
    have hx_dvd : addOrderOf x ∣ Nat.card B := addOrderOf_dvd_natCard x
    have hcardB : Nat.card B = p ^ N :=
      (Nat.card_congr (Multiplicative.ofAdd : B ≃ Multiplicative B)).trans hcardN
    simpa [hcardB] using hx_dvd
  have hkillN : p ^ N • x = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd
  calc
    p ^ (N + 1) • x = p • (p ^ N • x) := by
      rw [pow_succ, mul_nsmul]
    _ = 0 := by rw [hkillN, nsmul_zero]

def subgroupTorsionToTorsionLinearMap [NeZero p]
    (B : AddSubgroup A) :
    torsionBySubgroup B p →ₗ[ZMod p] torsionBySubgroup A p :=
  (subgroupTorsionToTorsion B p).toZModLinearMap p

omit [Finite A] in
@[simp]
theorem subgroupTorsionToTorsionLinearMap_apply_coe [NeZero p]
    (B : AddSubgroup A) (x : torsionBySubgroup B p) :
    ((subgroupTorsionToTorsionLinearMap (p := p) B x :
      torsionBySubgroup A p) : A) = (x.1 : A) :=
  rfl

omit [Finite A] in
theorem subgroupTorsionToTorsionLinearMap_equivariant [NeZero p]
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p)
    (x : torsionBySubgroup (AddCommGroup.primaryComponent A p) p) :
    subgroupTorsionToTorsionLinearMap (p := p)
        (AddCommGroup.primaryComponent A p)
        (torsionAction (p := p) (primaryComponentAction (p := p) rho) d x) =
      torsionAction (p := p) rho d
        (subgroupTorsionToTorsionLinearMap (p := p)
          (AddCommGroup.primaryComponent A p) x) := by
  apply Subtype.ext
  rw [subgroupTorsionToTorsionLinearMap_apply_coe,
    TorsionComponent.torsionAction_apply_coe,
    TorsionComponent.torsionAction_apply_coe,
    subgroupTorsionToTorsionLinearMap_apply_coe]
  change ((primaryComponentAddEquiv (p := p) (Multiplicative.toAdd (rho d)))
      (x : AddCommGroup.primaryComponent A p) : A) = _
  rw [primaryComponentAddEquiv_apply_coe]

omit [Finite A] in
theorem subgroupTorsionToTorsion_mem_torsionComponent_of_mem [NeZero p]
    (i : ℕ) (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    {x : torsionBySubgroup (AddCommGroup.primaryComponent A p) p}
    (hx : x ∈ TorsionComponent.torsionComponent (p := p) i
      (primaryComponentAction (p := p) rho)) :
    subgroupTorsionToTorsionLinearMap (p := p)
        (AddCommGroup.primaryComponent A p) x ∈
      TorsionComponent.torsionComponent (p := p) i rho := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨subgroupTorsionToTorsionLinearMap (p := p)
      (AddCommGroup.primaryComponent A p) y, ?_⟩
  exact
    CharacterProjection.map_projection_apply
      (p := p)
      (TorsionComponent.torsionAction (p := p)
        (primaryComponentAction (p := p) rho))
      (TorsionComponent.torsionAction (p := p) rho)
      (subgroupTorsionToTorsionLinearMap (p := p)
        (AddCommGroup.primaryComponent A p))
      (subgroupTorsionToTorsionLinearMap_equivariant
        (p := p) rho)
      (CharacterProjection.characterProjectionCoefficient (p := p) i) y |>.symm

theorem torsionComponentNontrivial_of_elementaryComponentNontrivial_finite
    (i : ℕ) (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (hV : ElementaryComponentNontrivial (p := p) i rho) :
    TorsionComponentNontrivial (p := p) i rho := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let B := AddCommGroup.primaryComponent A p
  have hV_B : ElementaryComponentNontrivial (p := p) i
      (primaryComponentAction (p := p) rho) :=
    elementaryComponentNontrivial_primary_of_elementaryComponentNontrivial
      (p := p) (A := A) i rho hV
  have hT_B : TorsionComponentNontrivial (p := p) i
      (primaryComponentAction (p := p) rho) :=
    torsionComponentNontrivial_of_elementaryComponentNontrivial_exists_pow_killed
      (p := p) (A := B)
      (primaryComponent_exists_pow_killed (p := p) (A := A)) i
      (primaryComponentAction (p := p) rho) hV_B
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    TorsionComponent.exists_ne_zero_mem_torsionComponent
      (p := p) hT_B
  refine TorsionComponent.torsionComponentNontrivial_of_exists_ne_zero_mem ?_
  refine ⟨subgroupTorsionToTorsionLinearMap (p := p) B x, ?_, ?_⟩
  · intro hx_zero
    apply hx_ne
    apply Subtype.ext
    apply Subtype.ext
    simpa [B, subgroupTorsionToTorsionLinearMap] using
      congrArg (fun y : torsionBySubgroup A p => (y.1 : A)) hx_zero
  · exact subgroupTorsionToTorsion_mem_torsionComponent_of_mem
      (p := p) (A := A) i rho hx_mem

end FinitePrimaryBridge

end FiniteLevelCharacterLift

end SingularKummer
end Reflection
end BernoulliRegular

end

end
