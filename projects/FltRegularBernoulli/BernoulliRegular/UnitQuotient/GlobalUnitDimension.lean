module

public import BernoulliRegular.UnitQuotient.FreeProjectorRanges
public import Mathlib.Algebra.Module.ZMod

/-!
# Unit quotients: global unit component dimensions

This file assembles `REF-07d`.  The map

```text
E / E^p -> (E / E_tors) / p
```

has the cyclotomic torsion line as kernel.  The kernel is the Teichmuller
line, so it has no even eigenspace.  Therefore the already proved free-part
dimension statement lifts to the actual quotient `E/E^p` for every nontrivial
even character.  The final theorem specializes this to the standard
`j`-power character with `2 <= j <= p - 3`.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset MonoidAlgebra

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

private theorem characterProjector_mem_eigenspace
    {G R M : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [Field R] [AddCommGroup M] [Module R M]
    [Invertible (Fintype.card G : R)] [Invertible (2 : R)]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)]
    (ρ : Representation R G M) (χ : MulChar G R) (x : M) :
    ∀ a : G,
      ρ a (ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x) =
        χ a • ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x := by
  intro a
  rw [← Representation.asAlgebraHom_single_one ρ a]
  rw [← Module.End.mul_apply, ← map_mul,
    single_mul_charIdempotent (G := G) (R := R) a χ, map_smul]
  rfl

/-- For a character `χ : G →* R`, the character idempotent acts as the
identity on its eigenspace: any `x` with `ρ a x = χ(a) · x` for every
`a ∈ G` is fixed by `e_χ`. -/
theorem characterProjector_apply_of_mem_eigenspace
    {G R M : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [CommRing R] [AddCommGroup M] [Module R M]
    [Invertible (Fintype.card G : R)]
    (ρ : Representation R G M) (χ : MulChar G R) {x : M}
    (hx : ∀ a : G, ρ a x = χ a • x) :
    ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x = x := by
  classical
  calc
    ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x
        = ⅟(Fintype.card G : R) •
            ∑ a : G, χ a • ρ a⁻¹ x := by
          simp [charIdempotent_def, map_sum]
    _ = ⅟(Fintype.card G : R) • ∑ _a : G, x := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          rw [hx a⁻¹, smul_smul, ← map_mul, mul_inv_cancel, MulChar.map_one, one_smul]
    _ = x := by
          rw [Finset.sum_const, Finset.card_univ]
          rw [← Nat.cast_smul_eq_nsmul R (Fintype.card G) x]
          rw [smul_smul, invOf_mul_self, one_smul]

private theorem characterProjector_intertwines
    {G R V W : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [Field R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Invertible (Fintype.card G : R)]
    (ρV : Representation R G V) (ρW : Representation R G W)
    (f : V →ₗ[R] W) (hf : ∀ (a : G) (x : V), f (ρV a x) = ρW a (f x))
    (χ : MulChar G R) (x : V) :
    f (ρV.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x) =
      ρW.asAlgebraHom (charIdempotent (G := G) (R := R) χ) (f x) := by
  classical
  simp [charIdempotent_def, map_sum, hf]

/-- For `p > 2`, the order of `Delta = (ZMod p)^*` is invertible in
`ZMod p`. -/
@[implicit_reducible]
noncomputable def cyclotomicUnitDeltaCardInvertibleZMod (hp_gt_two : 2 < p) :
    Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) := by
  rw [show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units]]
  have hp_not_dvd : ¬ p ∣ p - 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  exact invertibleOfCoprime (R := ZMod p)
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd).symm)

/-- `ZMod p` contains enough roots of unity for `Delta`. -/
theorem cyclotomicUnitDelta_hasEnoughRootsOfUnity_zmod :
    HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicUnitDelta p)) := by
  haveI : NeZero (p - 1) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  exact HasEnoughRootsOfUnity.of_dvd (ZMod p)
    ((Group.exponent_dvd_card (G := CyclotomicUnitDelta p)).trans
      (by rw [ZMod.card_units]))

/-- Additive `ZMod p`-module structure on `E/E^p`. -/
instance cyclotomicUnitPowerQuotientModuleZMod :
    Module (ZMod p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    simpa using cyclotomicUnitPowerQuotient_pow_eq_one (p := p) (N := 1) K x.toMul

/-- The actual `Delta` action on `E/E^p`, as a `ZMod p`-linear action after
passing to additive notation. -/
noncomputable def cyclotomicUnitPowerQuotientLinearEquivZMod
    (a : CyclotomicUnitDelta p) :
    Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) ≃ₗ[ZMod p]
      Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) where
  toFun :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).toFun
  invFun :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).invFun
  left_inv :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).left_inv
  right_inv :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).right_inv
  map_add' :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).map_add
  map_smul' c x :=
    ZMod.map_smul
      ((MulEquiv.toAdditive
        ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).toAddMonoidHom) c x

@[simp]
theorem cyclotomicUnitPowerQuotientLinearEquivZMod_apply
    (a : CyclotomicUnitDelta p)
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientLinearEquivZMod (p := p) K a x =
      Additive.ofMul
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a x.toMul) :=
  rfl

/-- The actual `Delta` action on `E/E^p` as a linear representation. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaActionZMod :
    CyclotomicUnitDelta p →*
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) ≃ₗ[ZMod p]
        Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) where
  toFun := cyclotomicUnitPowerQuotientLinearEquivZMod (p := p) K
  map_one' := by
    ext x
    apply Additive.ext
    simp [CyclotomicUnitQuotientDeltaAction.act]
  map_mul' := by
    intro a b
    ext x
    apply Additive.ext
    simp [CyclotomicUnitQuotientDeltaAction.act_comp]

/-- The actual `Delta` representation on `E/E^p`. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaRepresentation :
    Representation (ZMod p) (CyclotomicUnitDelta p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K)

@[simp]
theorem cyclotomicUnitPowerQuotientDeltaRepresentation_apply
    (a : CyclotomicUnitDelta p)
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientDeltaRepresentation (p := p) K a x =
      cyclotomicUnitPowerQuotientLinearEquivZMod (p := p) K a x :=
  rfl

/-- The `χ`-eigenspace in the actual quotient `E/E^p`. -/
def cyclotomicUnitPowerQuotientDeltaCharacterEigenspace
    (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Submodule (ZMod p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) where
  carrier := {x | ∀ a,
    cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K a x = χ a • x}
  zero_mem' := by
    intro a
    simp
  add_mem' hx hy := by
    intro a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    rw [map_smul, hx a, smul_smul, smul_smul, mul_comm]

/-- The full `Delta` character projector on `E/E^p`. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaCharacterProjector
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Module.End (ZMod p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  exact (cyclotomicUnitPowerQuotientDeltaRepresentation (p := p) K).asAlgebraHom
    (charIdempotent (G := CyclotomicUnitDelta p) (R := ZMod p) χ)

theorem cyclotomicUnitPowerQuotientDeltaCharacterProjector_mem_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p))
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientDeltaCharacterProjector (p := p) K hp_gt_two χ x ∈
      cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  letI : Invertible (2 : ZMod p) := twoInvertibleZModOfPrimeGtTwo (p := p) hp_gt_two
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicUnitDelta p)) :=
    cyclotomicUnitDelta_hasEnoughRootsOfUnity_zmod (p := p)
  exact characterProjector_mem_eigenspace
    (ρ := cyclotomicUnitPowerQuotientDeltaRepresentation (p := p) K) χ x

/-- The full `Delta` representation on the reduced free quotient. -/
noncomputable def cyclotomicUnitFreePartModPDeltaRepresentation :
    Representation (ZMod p) (CyclotomicUnitDelta p)
      (CyclotomicUnitFreePartModP (p := p) K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K)

/-- The full `Delta` character projector on the reduced free quotient. -/
noncomputable def cyclotomicUnitFreePartModPDeltaCharacterProjector
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Module.End (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  exact (cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K).asAlgebraHom
    (charIdempotent (G := CyclotomicUnitDelta p) (R := ZMod p) χ)

/-- The map `E/E^p -> (E/E_tors)/p`, in additive `ZMod p`-linear form. -/
noncomputable def cyclotomicUnitPowerQuotientToFreePartModPLinear :
    Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) →ₗ[ZMod p]
      CyclotomicUnitFreePartModP (p := p) K :=
  (MonoidHom.toAdditiveLeft
      (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K)).toZModLinearMap p

@[simp]
theorem cyclotomicUnitPowerQuotientToFreePartModPLinear_apply
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x =
      (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K x.toMul).toAdd :=
  rfl

theorem cyclotomicUnitPowerQuotientToFreePartModPLinear_surjective :
    Function.Surjective
      (cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K) := by
  intro y
  obtain ⟨x, hx⟩ :=
    cyclotomicUnitPowerQuotientToFreePartModP_surjective
      (p := p) (K := K) (Multiplicative.ofAdd y)
  refine ⟨Additive.ofMul x, ?_⟩
  change (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K x).toAdd = y
  simpa using congrArg Multiplicative.toAdd hx

theorem cyclotomicUnitPowerQuotientToFreePartModPLinear_equivariant
    (a : CyclotomicUnitDelta p)
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K
        (cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K a x) =
      cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K a
        (cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x) := by
  have h :=
    cyclotomicUnitPowerQuotientToFreePartModP_equivariant
      (p := p) (K := K) a x.toMul
  change
    (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a x.toMul)).toAdd =
      cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
        ((cyclotomicUnitPowerQuotientToFreePartModP (p := p) K x.toMul).toAdd)
  simpa [cyclotomicUnitFreePartModPMulEquiv] using congrArg Multiplicative.toAdd h

theorem cyclotomicUnitPowerQuotientToFreePartModPLinear_mem_eigenspace
    {χ : MulChar (CyclotomicUnitDelta p) (ZMod p)}
    {x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)}
    (hx : x ∈ cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ) :
    cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K χ := by
  intro a
  rw [← cyclotomicUnitPowerQuotientToFreePartModPLinear_equivariant
    (p := p) (K := K) a x, hx a, map_smul]

theorem cyclotomicUnitPowerQuotientToFreePartModPLinear_projector
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p))
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K
        (cyclotomicUnitPowerQuotientDeltaCharacterProjector (p := p) K hp_gt_two χ x) =
      cyclotomicUnitFreePartModPDeltaCharacterProjector (p := p) K hp_gt_two χ
        (cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  exact characterProjector_intertwines
    (ρV := cyclotomicUnitPowerQuotientDeltaRepresentation (p := p) K)
    (ρW := cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K)
    (f := cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K)
    (fun a x => cyclotomicUnitPowerQuotientToFreePartModPLinear_equivariant
      (p := p) (K := K) a x)
    χ x

theorem cyclotomicUnitModPDeltaAction_neg_one_zetaPowerClass :
    (cyclotomicUnitModPDeltaAction (p := p) K).act
        (-1 : CyclotomicUnitDelta p) (cyclotomicZetaPowerClass (p := p) K) =
      (cyclotomicZetaPowerClass (p := p) K)⁻¹ := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hval :
      ((-1 : CyclotomicUnitDelta p) : ZMod p).val = p - 1 := by
    change (-1 : ZMod p).val = p - 1
    cases p with
    | zero => cases hp_pos
    | succ q =>
        change (-1 : ZMod q.succ).val = q
        exact ZMod.val_neg_one q
  have hpow :
      (cyclotomicZetaPowerClass (p := p) K) ^ (p - 1) =
        (cyclotomicZetaPowerClass (p := p) K)⁻¹ := by
    have hzeta_p :
        (cyclotomicZetaPowerClass (p := p) K) ^ p = 1 := by
      simpa using cyclotomicUnitPowerQuotient_pow_eq_one
        (p := p) (N := 1) K (cyclotomicZetaPowerClass (p := p) K)
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, show p - 1 + 1 = p by omega, hzeta_p]
  rw [cyclotomicUnitModPDeltaAction_act_zetaPowerClass, hval, hpow]

theorem cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed
    (hp_gt_two : 2 < p)
    {x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)}
    (hx_torsion : x.toMul ∈ cyclotomicTorsionPowerClassSubgroup (p := p) K)
    (hfixed :
      cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K
        (-1 : CyclotomicUnitDelta p) x = x) :
    x = 0 := by
  have hp_odd : p ≠ 2 := by omega
  have hx_line : x.toMul ∈
      Subgroup.zpowers (cyclotomicZetaPowerClass (p := p) K) := by
    simpa [cyclotomicTorsionPowerClassSubgroup_eq_zpowers_zeta
      (p := p) (K := K) hp_odd] using hx_torsion
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx_line
  have hact_inv :
      (cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K
        (-1 : CyclotomicUnitDelta p) x).toMul = x.toMul⁻¹ := by
    change (cyclotomicUnitModPDeltaAction (p := p) K).act
        (-1 : CyclotomicUnitDelta p) x.toMul = x.toMul⁻¹
    rw [← hn]
    change ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut
        (-1 : CyclotomicUnitDelta p))
          ((cyclotomicZetaPowerClass (p := p) K) ^ n) =
      ((cyclotomicZetaPowerClass (p := p) K) ^ n)⁻¹
    rw [map_zpow]
    have hneg :=
      cyclotomicUnitModPDeltaAction_neg_one_zetaPowerClass (p := p) (K := K)
    change ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut
        (-1 : CyclotomicUnitDelta p)) (cyclotomicZetaPowerClass (p := p) K) =
      (cyclotomicZetaPowerClass (p := p) K)⁻¹ at hneg
    rw [hneg, inv_zpow]
  have hinv : x.toMul⁻¹ = x.toMul := by
    rw [← hact_inv, hfixed]
  have hneg : -x = x := by
    apply Additive.toMul.injective
    rw [toMul_neg, hinv]
  have htwo_smul : (2 : ZMod p) • x = 0 := by
    have hsum : x + x = 0 := by
      calc
        x + x = -x + x := by rw [hneg]
        _ = 0 := neg_add_cancel x
    simpa [two_smul] using hsum
  letI : Invertible (2 : ZMod p) := twoInvertibleZModOfPrimeGtTwo (p := p) hp_gt_two
  calc
    x = (1 : ZMod p) • x := by rw [one_smul]
    _ = (⅟(2 : ZMod p) * 2) • x := by rw [invOf_mul_self]
    _ = ⅟(2 : ZMod p) • ((2 : ZMod p) • x) := by rw [mul_smul]
    _ = 0 := by rw [htwo_smul, smul_zero]

theorem cyclotomicUnitPowerQuotientDeltaCharacterEigenspace_eq_zero_of_map_eq_zero
    (hp_gt_two : 2 < p) {χ : MulChar (CyclotomicUnitDelta p) (ZMod p)}
    (hχ_even : IsEvenDeltaCharacter (p := p) χ)
    {x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)}
    (hx : x ∈ cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ)
    (hmap : cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x = 0) :
    x = 0 := by
  have hker :
      x.toMul ∈ (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K).ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.ext
    change (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K x.toMul).toAdd = 0
    simpa using hmap
  have hx_torsion : x.toMul ∈ cyclotomicTorsionPowerClassSubgroup (p := p) K := by
    simpa [cyclotomicUnitPowerQuotientToFreePartModP_ker (p := p) (K := K)] using hker
  have hfixed :
      cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K
          (-1 : CyclotomicUnitDelta p) x = x := by
    have h := hx (-1 : CyclotomicUnitDelta p)
    rw [hχ_even, one_smul] at h
    exact h
  exact cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed
    (p := p) (K := K) hp_gt_two hx_torsion hfixed

/-- The actual `χ`-component of `E/E^p` maps isomorphically to the reduced
free quotient for even characters. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaCharacterEigenspaceEquivFreePart
    (hp_gt_two : 2 < p) {χ : MulChar (CyclotomicUnitDelta p) (ZMod p)}
    (hχ_even : IsEvenDeltaCharacter (p := p) χ) :
    cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ ≃ₗ[ZMod p]
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K χ := by
  let F :
      cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ →ₗ[ZMod p]
        cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K χ :=
    {
    toFun x :=
      ⟨cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x.1,
        cyclotomicUnitPowerQuotientToFreePartModPLinear_mem_eigenspace
          (p := p) (K := K) x.2⟩
    map_add' x y := by
      ext
      exact map_add (cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K) x.1 y.1
    map_smul' c x := by
      ext
      exact map_smul (cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K) c x.1
    }
  exact LinearEquiv.ofBijective F ⟨by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    have hmap :
        cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K (x.1 - y.1) = 0 := by
      change cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x.1 =
          cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K y.1 at hval
      rw [map_sub, hval, sub_self]
    have hxsub :
        x.1 - y.1 ∈
          cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ :=
      Submodule.sub_mem _ x.2 y.2
    have hzero :=
      cyclotomicUnitPowerQuotientDeltaCharacterEigenspace_eq_zero_of_map_eq_zero
        (p := p) (K := K) hp_gt_two hχ_even hxsub hmap
    exact sub_eq_zero.mp hzero, by
    intro y
    obtain ⟨x, hx⟩ :=
      cyclotomicUnitPowerQuotientToFreePartModPLinear_surjective (p := p) (K := K) y.1
    let x' :=
      cyclotomicUnitPowerQuotientDeltaCharacterProjector (p := p) K hp_gt_two χ x
    have hx'_mem :
        x' ∈ cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ :=
      cyclotomicUnitPowerQuotientDeltaCharacterProjector_mem_eigenspace
        (p := p) (K := K) hp_gt_two χ x
    refine ⟨⟨x', hx'_mem⟩, ?_⟩
    apply Subtype.ext
    change cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x' = y.1
    rw [cyclotomicUnitPowerQuotientToFreePartModPLinear_projector
      (p := p) (K := K) hp_gt_two χ x, hx]
    letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
      cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
    exact characterProjector_apply_of_mem_eigenspace
      (ρ := cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K) χ y.2⟩

theorem cyclotomicUnitPowerQuotientDeltaCharacterEigenspace_finrank_of_even_ne_one
    (hp_gt_two : 2 < p)
    {χ : MulChar (CyclotomicUnitDelta p) (ZMod p)}
    (hχ_even : IsEvenDeltaCharacter (p := p) χ)
    (hχ_ne : χ ≠ (1 : MulChar (CyclotomicUnitDelta p) (ZMod p))) :
    Module.finrank (ZMod p)
        (cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ) = 1 := by
  classical
  rw [LinearEquiv.finrank_eq
    (cyclotomicUnitPowerQuotientDeltaCharacterEigenspaceEquivFreePart
      (p := p) (K := K) hp_gt_two hχ_even)]
  letI : Fintype {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    Fintype.ofFinite _
  letI : DiscreteTopology (NumberField.Units.unitLattice K) :=
    NumberField.Units.instDiscrete_unitLattice K
  letI : IsZLattice ℝ (NumberField.Units.unitLattice K) := by
    refine ⟨?_⟩
    convert NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K
  exact cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one
    (p := p) (K := K) hp_gt_two hχ_even hχ_ne

/-- The `j`-power mod-`p` character of `Delta`. -/
def cyclotomicUnitDeltaPowerCharacter (j : ℕ) :
    MulChar (CyclotomicUnitDelta p) (ZMod p) where
  toFun a := (a : ZMod p) ^ j
  map_one' := by simp
  map_mul' a b := by
    change (((a * b : CyclotomicUnitDelta p) : ZMod p) ^ j) =
      (a : ZMod p) ^ j * (b : ZMod p) ^ j
    rw [Units.val_mul, mul_pow]
  map_nonunit' a ha := (ha (Group.isUnit a)).elim

@[simp]
theorem cyclotomicUnitDeltaPowerCharacter_apply
    (j : ℕ) (a : CyclotomicUnitDelta p) :
    cyclotomicUnitDeltaPowerCharacter (p := p) j a = (a : ZMod p) ^ j :=
  rfl

theorem cyclotomicUnitDeltaPowerCharacter_even_of_even
    {j : ℕ} (hj_even : Even j) :
    IsEvenDeltaCharacter (p := p)
      (cyclotomicUnitDeltaPowerCharacter (p := p) j) := by
  obtain ⟨k, rfl⟩ := hj_even
  change ((-1 : CyclotomicUnitDelta p) : ZMod p) ^ (k + k) = 1
  rw [show k + k = 2 * k by omega, pow_mul]
  simp

theorem cyclotomicUnitDeltaPowerCharacter_ne_one_of_pos_lt
    {j : ℕ} (hj_pos : 0 < j) (hj_lt : j < p - 1) :
    cyclotomicUnitDeltaPowerCharacter (p := p) j ≠
      (1 : MulChar (CyclotomicUnitDelta p) (ZMod p)) := by
  classical
  letI : IsCyclic (CyclotomicUnitDelta p) := by
    dsimp [CyclotomicUnitDelta]
    exact ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := CyclotomicUnitDelta p)
  intro hχ
  have happly :
      cyclotomicUnitDeltaPowerCharacter (p := p) j g =
        (1 : MulChar (CyclotomicUnitDelta p) (ZMod p)) g := by
    rw [hχ]
  rw [MulChar.one_apply (R := CyclotomicUnitDelta p) (R' := ZMod p)
    (x := g) (Group.isUnit g)] at happly
  have hgpow : g ^ j = 1 := by
    apply Units.ext
    change (g : ZMod p) ^ j = 1
    simpa [cyclotomicUnitDeltaPowerCharacter] using happly
  have hdiv : p - 1 ∣ j := by
    have hdiv' := orderOf_dvd_of_pow_eq_one hgpow
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units] at hdiv'
  exact Nat.not_dvd_of_pos_of_lt hj_pos hj_lt hdiv

theorem cyclotomicUnitPowerQuotientDeltaPowerCharacterEigenspace_finrank
    (hp_gt_two : 2 < p) {j : ℕ}
    (hj_even : Even j) (hj_low : 2 ≤ j) (hj_high : j ≤ p - 3) :
    Module.finrank (ZMod p)
        (cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
          (cyclotomicUnitDeltaPowerCharacter (p := p) j)) = 1 :=
  cyclotomicUnitPowerQuotientDeltaCharacterEigenspace_finrank_of_even_ne_one
    (p := p) (K := K) hp_gt_two
    (cyclotomicUnitDeltaPowerCharacter_even_of_even (p := p) hj_even)
    (cyclotomicUnitDeltaPowerCharacter_ne_one_of_pos_lt (p := p)
      (by omega) (by omega))

end BernoulliRegular

end
