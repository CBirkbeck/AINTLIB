module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.AugmentationTrace

/-!
# Unit quotients: complex conjugation and augmentation traces

This file identifies the action of -1 with complex conjugation on infinite
places and computes the trace of the augmentation action through the even
quotient.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite
attribute [local instance] NumberField.Units.instZLattice_unitLattice

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Complex conjugation on the ring of integers in the `p`-th cyclotomic
field, with the CM structure supplied by `p > 2`. -/
noncomputable def cyclotomicRingOfIntegersComplexConj
    (hp_gt_two : 2 < p) :
    𝓞 K ≃+* 𝓞 K := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  exact (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv

/-- Complex conjugation on units in the `p`-th cyclotomic field, with the CM
structure supplied by `p > 2`. -/
noncomputable def cyclotomicUnitsComplexConj
    (hp_gt_two : 2 < p) :
    CyclotomicUnitGroup K ≃* CyclotomicUnitGroup K := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  exact NumberField.IsCMField.unitsComplexConj K

@[simp]
theorem cyclotomicUnitsComplexConj_apply_coe
    (hp_gt_two : 2 < p) (u : CyclotomicUnitGroup K) :
    ((cyclotomicUnitsComplexConj (p := p) K hp_gt_two u : CyclotomicUnitGroup K) :
        𝓞 K) =
      cyclotomicRingOfIntegersComplexConj (p := p) K hp_gt_two (u : 𝓞 K) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  rfl

/-- Complex conjugation as a rational Galois automorphism of the cyclotomic
field. -/
noncomputable def cyclotomicComplexConjGal
    (hp_gt_two : 2 < p) : Gal(K / ℚ) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  exact
    { (NumberField.IsCMField.complexConj K).toRingEquiv with
      commutes' := fun q => by
        exact map_ratCast
          ((NumberField.IsCMField.complexConj K).toRingEquiv.toRingHom) q }

/-- Under the standard cyclotomic Galois identification, complex conjugation
is the element `-1` of `(ZMod p)^*`. -/
theorem cyclotomicGalEquivZMod_complexConjGal_eq_neg_one
    (hp_gt_two : 2 < p) :
    cyclotomicGalEquivZMod (p := p) K
        (cyclotomicComplexConjGal (p := p) K hp_gt_two) = -1 := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  let c : Gal(K / ℚ) := cyclotomicComplexConjGal (p := p) K hp_gt_two
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  let hunit : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
  have hzeta_torsion : hunit ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2
        ⟨p, (Fact.out : p.Prime).pos,
          (hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).pow_eq_one⟩)
  have hconj_inv :
      NumberField.IsCMField.complexConj K
          (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K)⁻¹ := by
    have hconj :=
      NumberField.IsCMField.complexConj_torsion
        (K := K) ⟨hunit, hzeta_torsion⟩
    simpa [hunit] using hconj
  have hζ_inv :
      (IsCyclotomicExtension.zeta p ℚ K)⁻¹ =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_one_add_one (Fact.out : p.Prime).ne_zero]
    exact hζ.pow_eq_one
  have hc :
      c (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    simpa [c, cyclotomicComplexConjGal, hζ_inv] using hconj_inv
  have hpow :
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    calc
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val
          = c (IsCyclotomicExtension.zeta p ℚ K) := by
              symm
              exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n := p) (K := K) c hζ.pow_eq_one
      _ = (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := hc
  apply Units.ext
  have hpow' := hpow
  rw [(hζ.isOfFinOrder (Fact.out : p.Prime).ne_zero).pow_inj_mod, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val,
    Nat.cast_sub (Fact.out : p.Prime).one_le,
    ZMod.natCast_self, zero_sub, Nat.cast_one] at hpow'
  simpa [c, cyclotomicGalEquivZMod] using hpow'

/-- The Galois automorphism indexed by `-1` is complex conjugation. -/
theorem cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal
    (hp_gt_two : 2 < p) :
    cyclotomicSigmaOfUnit (p := p) K (-1) =
      cyclotomicComplexConjGal (p := p) K hp_gt_two := by
  apply (cyclotomicGalEquivZMod (p := p) K).injective
  rw [cyclotomicGalEquivZMod_sigmaOfUnit,
    cyclotomicGalEquivZMod_complexConjGal_eq_neg_one (p := p) (K := K) hp_gt_two]

/-- Complex conjugation fixes every infinite place, so `-1 ∈ Delta` acts
trivially on the full logarithmic permutation representation. -/
theorem cyclotomicFullLogSpaceDeltaAction_neg_one_apply
    (hp_gt_two : 2 < p) (f : CyclotomicFullLogSpace K) :
    cyclotomicFullLogSpaceDeltaAction (p := p) K (-1) f = f := by
  ext w
  rw [cyclotomicFullLogSpaceDeltaAction_apply,
    cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal (p := p) (K := K) hp_gt_two]
  congr 1
  ext x
  rw [InfinitePlace.smul_apply]
  change w (cyclotomicComplexConjGal (p := p) K hp_gt_two x) = w x
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  simp [cyclotomicComplexConjGal]

/-- The packaged augmentation-hyperplane action also sends `-1` to the
identity. -/
theorem cyclotomicFullLogAugmentationDeltaAction_neg_one_apply
    (hp_gt_two : 2 < p) (f : cyclotomicFullLogAugmentationSubmodule K) :
    cyclotomicFullLogAugmentationDeltaAction (p := p) K (-1) f = f := by
  apply Subtype.ext
  ext w
  change cyclotomicFullLogSpaceDeltaAction (p := p) K (-1) f.1 w = f.1 w
  exact congrFun
    (cyclotomicFullLogSpaceDeltaAction_neg_one_apply
      (p := p) (K := K) hp_gt_two f.1) w

/-- The augmentation-hyperplane permutation action factors through
`Delta / {±1}`. -/
noncomputable def cyclotomicFullLogAugmentationEvenDeltaAction
    (hp_gt_two : 2 < p) :
    CyclotomicEvenDelta p →*
      (cyclotomicFullLogAugmentationSubmodule K ≃ₗ[ℝ]
        cyclotomicFullLogAugmentationSubmodule K) :=
  QuotientGroup.lift
    (CyclotomicEvenDeltaSubgroup p)
    (cyclotomicFullLogAugmentationDeltaAction (p := p) K)
    (by
      apply Subgroup.zpowers_le_of_mem
      rw [MonoidHom.mem_ker]
      ext f w
      exact congrFun
        (congrArg Subtype.val
          (cyclotomicFullLogAugmentationDeltaAction_neg_one_apply
            (p := p) (K := K) hp_gt_two f)) w)

@[simp]
theorem cyclotomicFullLogAugmentationEvenDeltaAction_apply_quotient
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p) :
    cyclotomicFullLogAugmentationEvenDeltaAction (p := p) K hp_gt_two
        (cyclotomicEvenDeltaQuotient p a) =
      cyclotomicFullLogAugmentationDeltaAction (p := p) K a :=
  rfl

/-- The `Delta`-stabilizer of an infinite place, pulled back from the Galois
stabilizer via the cyclotomic Galois equivalence. -/
def cyclotomicInfinitePlaceStabilizer (w : InfinitePlace K) :
    Subgroup (CyclotomicUnitDelta p) :=
  (MulAction.stabilizer (Gal(K / ℚ)) w).comap
    ((cyclotomicGalEquivZMod (p := p) K).symm.toMonoidHom)

@[simp]
theorem mem_cyclotomicInfinitePlaceStabilizer_iff
    (w : InfinitePlace K) (a : CyclotomicUnitDelta p) :
    a ∈ cyclotomicInfinitePlaceStabilizer (p := p) K w ↔
      cyclotomicSigmaOfUnit (p := p) K a • w = w := by
  rw [cyclotomicInfinitePlaceStabilizer, Subgroup.mem_comap,
    MulAction.mem_stabilizer_iff]
  rfl

theorem cyclotomicInfinitePlace_not_isUnramified
    (hp_gt_two : 2 < p) (w : InfinitePlace K) :
    ¬ InfinitePlace.IsUnramified ℚ w := by
  rw [InfinitePlace.not_isUnramified_iff]
  refine ⟨?_, ?_⟩
  · rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw
    have hpos' : 0 < NumberField.InfinitePlace.nrRealPlaces K :=
      by
        classical
        letI : DecidablePred (fun w : InfinitePlace K => InfinitePlace.IsReal w) :=
          Classical.decPred _
        letI : Fintype {w : InfinitePlace K // InfinitePlace.IsReal w} :=
          Subtype.fintype InfinitePlace.IsReal
        rw [NumberField.InfinitePlace.nrRealPlaces]
        exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
    simp [IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := p) K hp_gt_two] at hpos'
  · rw [Subsingleton.elim (w.comap (algebraMap ℚ K)) Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

theorem cyclotomicInfinitePlaceStabilizer_card
    (hp_gt_two : 2 < p) (w : InfinitePlace K) :
    Nat.card (cyclotomicInfinitePlaceStabilizer (p := p) K w) = 2 := by
  let e : cyclotomicInfinitePlaceStabilizer (p := p) K w ≃
      MulAction.stabilizer (Gal(K / ℚ)) w :=
    { toFun := fun a => ⟨cyclotomicSigmaOfUnit (p := p) K a, a.property⟩
      invFun := fun σ => ⟨cyclotomicGalEquivZMod (p := p) K σ, by
        change ((cyclotomicGalEquivZMod (p := p) K).symm
            ((cyclotomicGalEquivZMod (p := p) K) (σ : Gal(K / ℚ)))) • w = w
        rw [(cyclotomicGalEquivZMod (p := p) K).symm_apply_apply (σ : Gal(K / ℚ))]
        exact σ.property⟩
      left_inv := fun a =>
        Subtype.ext <| cyclotomicGalEquivZMod_sigmaOfUnit (p := p) (K := K) a
      right_inv := fun σ =>
        Subtype.ext <| (cyclotomicGalEquivZMod (p := p) K).symm_apply_apply σ }
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  have hcard : Nat.card (MulAction.stabilizer (Gal(K / ℚ)) w) = 2 := by
    simpa [cyclotomicInfinitePlace_not_isUnramified (p := p) (K := K) hp_gt_two w] using
      (InfinitePlace.card_stabilizer (k := ℚ) (K := K) (w := w))
  exact Nat.card_congr e ▸ hcard

theorem cyclotomicEvenDeltaSubgroup_le_cyclotomicInfinitePlaceStabilizer
    (hp_gt_two : 2 < p) (w : InfinitePlace K) :
    CyclotomicEvenDeltaSubgroup p ≤ cyclotomicInfinitePlaceStabilizer (p := p) K w := by
  classical
  apply Subgroup.zpowers_le_of_mem
  rw [mem_cyclotomicInfinitePlaceStabilizer_iff]
  have hwinv : (cyclotomicSigmaOfUnit (p := p) K (-1))⁻¹ • w = w := by
    have hfun := congrFun
      (cyclotomicFullLogSpaceDeltaAction_neg_one_apply
        (p := p) (K := K) hp_gt_two ((Pi.basisFun ℝ (InfinitePlace K)) w)) w
    by_contra hne
    simp [cyclotomicFullLogSpaceDeltaAction_apply, Pi.basisFun_apply, hne] at hfun
  calc
    cyclotomicSigmaOfUnit (p := p) K (-1) • w =
        cyclotomicSigmaOfUnit (p := p) K (-1) •
          ((cyclotomicSigmaOfUnit (p := p) K (-1))⁻¹ • w) := by rw [hwinv]
    _ = w := by rw [smul_inv_smul]

theorem cyclotomicInfinitePlaceStabilizer_eq_evenSubgroup
    (hp_gt_two : 2 < p) (w : InfinitePlace K) :
    cyclotomicInfinitePlaceStabilizer (p := p) K w =
      CyclotomicEvenDeltaSubgroup p := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact cyclotomicEvenDeltaSubgroup_le_cyclotomicInfinitePlaceStabilizer
      (p := p) (K := K) hp_gt_two w
  · rw [cyclotomicInfinitePlaceStabilizer_card (p := p) (K := K) hp_gt_two w,
      Nat.card_eq_fintype_card, cyclotomicEvenDeltaSubgroup_card (p := p) hp_gt_two]

theorem cyclotomicInfinitePlace_fix_iff_mem_evenSubgroup
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p) (w : InfinitePlace K) :
    cyclotomicSigmaOfUnit (p := p) K a • w = w ↔
      a ∈ CyclotomicEvenDeltaSubgroup p := by
  rw [← cyclotomicInfinitePlaceStabilizer_eq_evenSubgroup (p := p) (K := K) hp_gt_two w,
    mem_cyclotomicInfinitePlaceStabilizer_iff]

theorem cyclotomicFullLogSpaceDeltaAction_trace
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p) :
    LinearMap.trace ℝ (CyclotomicFullLogSpace K)
        ((cyclotomicFullLogSpaceDeltaAction (p := p) K a).toLinearMap) =
      if cyclotomicEvenDeltaQuotient p a = 1 then Fintype.card (InfinitePlace K) else 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace (b := Pi.basisFun ℝ (InfinitePlace K))]
  by_cases hq : cyclotomicEvenDeltaQuotient p a = 1
  · rw [if_pos hq]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      Pi.basisFun_apply]
    calc
      (∑ x : InfinitePlace K,
          (cyclotomicFullLogSpaceDeltaAction (p := p) K a
            ((Pi.single x (1 : ℝ) : InfinitePlace K → ℝ))) x)
          = ∑ x : InfinitePlace K, (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro w _
              have hw : cyclotomicSigmaOfUnit (p := p) K a • w = w :=
                (cyclotomicInfinitePlace_fix_iff_mem_evenSubgroup
                  (p := p) (K := K) hp_gt_two a w).2 ((QuotientGroup.eq_one_iff a).1 hq)
              have hwinv : (cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w = w := by
                calc
                  (cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w =
                      (cyclotomicSigmaOfUnit (p := p) K a)⁻¹ •
                        (cyclotomicSigmaOfUnit (p := p) K a • w) := by rw [hw]
                  _ = w := by rw [inv_smul_smul]
              rw [cyclotomicFullLogSpaceDeltaAction_apply, hwinv]
              simp
      _ = Fintype.card (InfinitePlace K) := by simp
  · rw [if_neg hq]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      Pi.basisFun_apply]
    calc
      (∑ x : InfinitePlace K,
          (cyclotomicFullLogSpaceDeltaAction (p := p) K a
            ((Pi.single x (1 : ℝ) : InfinitePlace K → ℝ))) x)
          = ∑ x : InfinitePlace K, (0 : ℝ) := by
              apply Finset.sum_congr rfl
              intro w _
              have hnot : (cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w ≠ w := by
                intro hw
                have hfix : cyclotomicSigmaOfUnit (p := p) K a • w = w := by
                  calc
                    cyclotomicSigmaOfUnit (p := p) K a • w =
                        cyclotomicSigmaOfUnit (p := p) K a •
                          ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w) := by rw [hw]
                    _ = w := by rw [smul_inv_smul]
                have ha_mem : a ∈ CyclotomicEvenDeltaSubgroup p :=
                  (cyclotomicInfinitePlace_fix_iff_mem_evenSubgroup
                    (p := p) (K := K) hp_gt_two a w).1 hfix
                exact hq ((QuotientGroup.eq_one_iff a).2 ha_mem)
              rw [cyclotomicFullLogSpaceDeltaAction_apply]
              simp [hnot]
      _ = ((0 : ℕ) : ℝ) := by simp

theorem cyclotomicFullLogAugmentationLinearEquiv_trace_formula
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p) :
    LinearMap.trace ℝ (cyclotomicFullLogAugmentationSubmodule K)
        ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap) =
      if cyclotomicEvenDeltaQuotient p a = 1 then
        (NumberField.Units.rank K : ℝ) else -1 := by
  have hfull := cyclotomicFullLogSpaceDeltaAction_trace
    (p := p) (K := K) hp_gt_two a
  have hsplit := cyclotomicFullLogSpaceDeltaAction_trace_eq_augmentation_trace_add_one
    (p := p) (K := K) a
  have hcard_pos : 0 < Fintype.card (InfinitePlace K) :=
    Fintype.card_pos_iff.mpr ⟨NumberField.Units.dirichletUnitTheorem.w₀⟩
  have hrank :
      (NumberField.Units.rank K : ℝ) =
        (Fintype.card (InfinitePlace K) : ℝ) - 1 := by
    rw [NumberField.Units.rank]
    rw [Nat.cast_sub (Nat.succ_le_of_lt hcard_pos)]
    norm_num
  by_cases hq : cyclotomicEvenDeltaQuotient p a = 1
  · rw [if_pos hq]
    have hfull' :
        LinearMap.trace ℝ (CyclotomicFullLogSpace K)
            ((cyclotomicFullLogSpaceDeltaAction (p := p) K a).toLinearMap) =
          (Fintype.card (InfinitePlace K) : ℝ) := by
      rw [if_pos hq] at hfull
      simpa using hfull
    linarith
  · rw [if_neg hq]
    have hfull' :
        LinearMap.trace ℝ (CyclotomicFullLogSpace K)
            ((cyclotomicFullLogSpaceDeltaAction (p := p) K a).toLinearMap) = 0 := by
      rw [if_neg hq] at hfull
      simpa using hfull
    linarith


end BernoulliRegular

end
