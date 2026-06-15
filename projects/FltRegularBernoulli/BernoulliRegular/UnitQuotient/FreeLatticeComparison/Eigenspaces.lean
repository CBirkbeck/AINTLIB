module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ModPRepresentation

/-!
# Unit quotients: actual free quotient eigenspaces

This file packages the actual Delta and even-Delta eigenspaces in the reduced
free quotient, proves projector landing and decomposition statements, and
records the odd-character vanishing result.
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

/-- The actual `χ`-eigenspace of the reduced free quotient for the
`Delta` action. -/
def cyclotomicUnitFreePartModPDeltaCharacterEigenspace
    (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Submodule (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) where
  carrier := {x | ∀ a,
    cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K a x = χ a • x}
  zero_mem' := by
    intro a
    simp
  add_mem' hx hy := by
    intro a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    rw [map_smul, hx a, smul_smul, smul_smul, mul_comm]

/-- The actual `χ`-eigenspace of the reduced free quotient for the factored
`Delta / {±1}` action. -/
def cyclotomicUnitFreePartModPEvenCharacterEigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p)) :
    Submodule (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) where
  carrier := {x | ∀ a,
    cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two a x =
      χ a • x}
  zero_mem' := by
    intro a
    simp
  add_mem' hx hy := by
    intro a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    rw [map_smul, hx a, smul_smul, smul_smul, mul_comm]

/-- The endomorphism of the reduced free quotient induced by the chosen
generator of `Delta / {±1}`. -/
noncomputable def cyclotomicUnitFreePartModPEvenGeneratorEnd
    (hp_gt_two : 2 < p) :
    Module.End (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) :=
  (cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two
    (cyclotomicEvenDeltaGenerator p) :
      CyclotomicUnitFreePartModP (p := p) K →ₗ[ZMod p]
        CyclotomicUnitFreePartModP (p := p) K)

/-- Because `Delta / {±1}` is cyclic, membership in the actual even-character
eigenspace is equivalent to the single generator equation. -/
theorem mem_cyclotomicUnitFreePartModPEvenCharacterEigenspace_iff_generator
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    (x : CyclotomicUnitFreePartModP (p := p) K) :
    x ∈ cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ ↔
      cyclotomicUnitFreePartModPEvenGeneratorEnd (p := p) K hp_gt_two x =
        χ (cyclotomicEvenDeltaGenerator p) • x := by
  constructor
  · intro hx
    exact hx (cyclotomicEvenDeltaGenerator p)
  · intro hx a
    obtain ⟨n, rfl⟩ :=
      (Submonoid.mem_powers_iff a (cyclotomicEvenDeltaGenerator p)).mp
        (cyclotomicEvenDeltaGenerator_spec (p := p) a)
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
              ((cyclotomicEvenDeltaGenerator p) ^ (n + 1)) x
              = cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
                  (cyclotomicEvenDeltaGenerator p)
                  (cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
                    ((cyclotomicEvenDeltaGenerator p) ^ n) x) := by
                      rw [pow_succ', map_mul, LinearEquiv.mul_apply]
          _ = cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
                (cyclotomicEvenDeltaGenerator p)
                (χ ((cyclotomicEvenDeltaGenerator p) ^ n) • x) := by rw [ih]
          _ = χ ((cyclotomicEvenDeltaGenerator p) ^ n) •
                cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
                  (cyclotomicEvenDeltaGenerator p) x := by rw [map_smul]
          _ = χ ((cyclotomicEvenDeltaGenerator p) ^ n) •
                (χ (cyclotomicEvenDeltaGenerator p) • x) := by
              simpa [cyclotomicUnitFreePartModPEvenGeneratorEnd] using congrArg
                (fun y => χ ((cyclotomicEvenDeltaGenerator p) ^ n) • y) hx
          _ = (χ ((cyclotomicEvenDeltaGenerator p) ^ n) *
                χ (cyclotomicEvenDeltaGenerator p)) • x := by rw [smul_smul]
          _ = χ ((cyclotomicEvenDeltaGenerator p) ^ (n + 1)) • x := by
                rw [pow_succ, map_mul]

/-- The actual even-character eigenspace is the kernel of the generator
endomorphism minus the corresponding scalar. -/
theorem cyclotomicUnitFreePartModPEvenCharacterEigenspace_eq_generator_ker
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p)) :
    cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ =
      LinearMap.ker
        (cyclotomicUnitFreePartModPEvenGeneratorEnd (p := p) K hp_gt_two -
          χ (cyclotomicEvenDeltaGenerator p) • LinearMap.id) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
  exact mem_cyclotomicUnitFreePartModPEvenCharacterEigenspace_iff_generator
    (p := p) (K := K) hp_gt_two χ x

/-- The character idempotent projector lands in the corresponding actual
eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x ∈
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  letI : Invertible (2 : ZMod p) :=
    twoInvertibleZModOfPrimeGtTwo (p := p) hp_gt_two
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicEvenDelta p)) :=
    cyclotomicEvenDelta_hasEnoughRootsOfUnity_zmod (p := p)
  intro a
  change
    cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two a
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) =
      χ a • cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x
  rw [← Representation.asAlgebraHom_single_one
    (cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two) a]
  simp only [cyclotomicUnitFreePartModPEvenCharacterProjector]
  rw [← Module.End.mul_apply, ← map_mul,
    single_mul_charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) a χ, map_smul]
  rfl

/-- The character idempotent projectors sum to the identity on the reduced
free quotient. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_sum_apply
    (hp_gt_two : 2 < p) (x : CyclotomicUnitFreePartModP (p := p) K) :
    (∑ χ : MulChar (CyclotomicEvenDelta p) (ZMod p),
        cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) = x := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicEvenDelta p)) :=
    cyclotomicEvenDelta_hasEnoughRootsOfUnity_zmod (p := p)
  let ρ := cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two
  calc
    (∑ χ : MulChar (CyclotomicEvenDelta p) (ZMod p),
        cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x)
        = (ρ.asAlgebraHom
            (∑ χ : MulChar (CyclotomicEvenDelta p) (ZMod p),
              charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ)) x := by
            simp [cyclotomicUnitFreePartModPEvenCharacterProjector, ρ, map_sum]
    _ = x := by
      rw [charIdempotent_sum_eq_one (G := CyclotomicEvenDelta p) (R := ZMod p)]
      simp [ρ]

/-- The actual reduced free quotient is the sum of its even-character
eigenspaces. -/
theorem cyclotomicUnitFreePartModPEvenCharacterEigenspace_iSup_eq_top
    (hp_gt_two : 2 < p) :
    (⨆ χ : MulChar (CyclotomicEvenDelta p) (ZMod p),
        cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ) =
      ⊤ := by
  classical
  apply le_antisymm le_top
  intro x hx
  rw [← cyclotomicUnitFreePartModPEvenCharacterProjector_sum_apply
    (p := p) (K := K) hp_gt_two x]
  exact Submodule.sum_mem _
    (fun χ _ => Submodule.mem_iSup_of_mem χ
      (cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace
        (p := p) (K := K) hp_gt_two χ x))

/-- Passing from the factored `Delta / {±1}` action to the original `Delta`
action identifies eigenspaces by pulling characters back along the quotient
map. -/
theorem cyclotomicUnitFreePartModPDeltaCharacterEigenspace_pullback
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p)) :
    cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K
        (evenDeltaCharacterPullback (p := p) χ) =
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ := by
  ext x
  constructor
  · intro hx a
    refine QuotientGroup.induction_on a ?_
    intro b
    change cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
        (cyclotomicEvenDeltaQuotient p b) x =
      χ (cyclotomicEvenDeltaQuotient p b) • x
    rw [cyclotomicUnitFreePartModPEvenDeltaActionZMod_apply_quotient]
    exact hx b
  · intro hx a
    rw [evenDeltaCharacterPullback_apply]
    rw [cyclotomicUnitFreePartModPDeltaActionZMod_apply]
    rw [← cyclotomicUnitFreePartModPEvenDeltaActionZMod_apply_quotient
      (p := p) (K := K) hp_gt_two a x]
    exact hx (cyclotomicEvenDeltaQuotient p a)

/-- The free part has no odd `Delta`-character eigenspace: complex
conjugation is already trivial on `E/E_tors`, hence on its mod-`p`
reduction. -/
theorem cyclotomicUnitFreePartModPDeltaCharacterEigenspace_eq_bot_of_odd
    (hp_gt_two : 2 < p) {χ : MulChar (CyclotomicUnitDelta p) (ZMod p)}
    (hχ_odd : χ (-1 : CyclotomicUnitDelta p) = -1) :
    cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K χ = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_bot]
    have hact := hx (-1 : CyclotomicUnitDelta p)
    rw [cyclotomicUnitFreePartModPDeltaActionZMod_apply,
      cyclotomicUnitFreePartModPLinearEquiv_neg_one_apply
        (p := p) (K := K) hp_gt_two, hχ_odd] at hact
    have hsum : x + x = 0 := by
      calc
        x + x = (-x) + x := by
          nth_rw 1 [hact]
          simp
        _ = 0 := neg_add_cancel x
    have htwo_smul : (2 : ZMod p) • x = 0 := by
      simpa [two_smul (ZMod p) x] using hsum
    have hp_not_dvd_two : ¬ p ∣ 2 := fun hdiv =>
      not_le_of_gt hp_gt_two (Nat.le_of_dvd (by decide) hdiv)
    have htwo_ne : (2 : ZMod p) ≠ 0 := by
      change ¬ ((2 : ℕ) : ZMod p) = 0
      rw [ZMod.natCast_eq_zero_iff (a := 2) (b := p)]
      exact hp_not_dvd_two
    exact (smul_eq_zero.mp htwo_smul).resolve_left htwo_ne
  · intro hx
    rw [Submodule.mem_bot] at hx
    rw [hx]
    intro a
    simp

/-- Distinct even characters have disjoint actual eigenspaces in the reduced
free quotient. -/
theorem cyclotomicUnitFreePartModPEvenCharacterEigenspace_inf_eq_bot_of_ne
    (hp_gt_two : 2 < p)
    {χ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p)} (hχψ : χ ≠ ψ) :
    cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ ⊓
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two ψ =
        ⊥ := by
  classical
  have hsep : ∃ a, χ a ≠ ψ a := by
    by_contra h
    apply hχψ
    ext a
    by_contra ha
    exact h ⟨a, ha⟩
  rcases hsep with ⟨a, ha⟩
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_bot]
    have hxχ := hx.1 a
    have hxψ := hx.2 a
    have hsame : χ a • x = ψ a • x := by
      rw [← hxχ, ← hxψ]
    have hzero : (χ a - ψ a) • x = 0 := by
      rw [sub_smul, hsame, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ha)
  · intro hx
    rw [Submodule.mem_bot] at hx
    rw [hx]
    exact Submodule.zero_mem _


end BernoulliRegular

end
