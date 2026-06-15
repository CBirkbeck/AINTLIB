module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison
public import Mathlib.LinearAlgebra.Projection

/-!
# Unit quotients: ranges of free-unit character projectors

This file continues `REF-07c6c2b`.  The actual reduced free-unit quotient has
character idempotent projectors for the factored action of `Delta / {±1}`.
Here we prove that these projectors are precisely the projections onto the
actual character eigenspaces.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite

private theorem LinearMap.trace_eq_finrank_range_of_isIdempotentElem
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : Module.End F V) (he : IsIdempotentElem e) :
    LinearMap.trace F V e = (Module.finrank F (LinearMap.range e) : F) := by
  classical
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    LinearMap.IsIdempotentElem.isProj_range e he
  calc
    LinearMap.trace F V e =
        LinearMap.trace F V
          (((LinearMap.range e).prodEquivOfIsCompl (LinearMap.ker e) hproj.isCompl).conj
            (LinearMap.prodMap LinearMap.id 0)) :=
          congrArg (LinearMap.trace F V)
            (LinearMap.IsProj.eq_conj_prodMap hproj)
    _ = LinearMap.trace F ((LinearMap.range e) × (LinearMap.ker e))
          (LinearMap.prodMap LinearMap.id 0) := by
          rw [LinearMap.trace_conj']
    _ = (Module.finrank F (LinearMap.range e) : F) := by
          rw [LinearMap.trace_prodMap']
          simp

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Character projectors commute with the factored even `Delta` action. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_commute_action
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    (a : CyclotomicEvenDelta p)
    (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two a
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) =
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ
        (cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two a x) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  let ρ := cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two
  change ρ a
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) =
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ (ρ a x)
  rw [← Representation.asAlgebraHom_single_one ρ a]
  change
    ρ.asAlgebraHom (MonoidAlgebra.single a (1 : ZMod p))
        ((ρ.asAlgebraHom
          (charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ)) x) =
      (ρ.asAlgebraHom
        (charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ))
        (ρ.asAlgebraHom (MonoidAlgebra.single a (1 : ZMod p)) x)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

/-- A character projector preserves every actual even-character eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace_of_mem
    (hp_gt_two : 2 < p)
    (χ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    {x : CyclotomicUnitFreePartModP (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartModPEvenCharacterEigenspace
      (p := p) K hp_gt_two ψ) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x ∈
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two ψ := by
  intro a
  rw [cyclotomicUnitFreePartModPEvenCharacterProjector_commute_action
    (p := p) (K := K) hp_gt_two χ a x, hx a, map_smul]

/-- On the `χ`-eigenspace, every different character projector vanishes. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_apply_eq_zero_of_mem_ne
    (hp_gt_two : 2 < p)
    {χ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p)} (hχψ : χ ≠ ψ)
    {x : CyclotomicUnitFreePartModP (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartModPEvenCharacterEigenspace
      (p := p) K hp_gt_two χ) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x = 0 := by
  have hmem :
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x ∈
        cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ ⊓
          cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two ψ :=
    ⟨cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace_of_mem
        (p := p) (K := K) hp_gt_two ψ χ hx,
      cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace
        (p := p) (K := K) hp_gt_two ψ x⟩
  have hbot := cyclotomicUnitFreePartModPEvenCharacterEigenspace_inf_eq_bot_of_ne
    (p := p) (K := K) hp_gt_two hχψ
  have hzero :
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x ∈
        (⊥ : Submodule (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)) := by
    rwa [← hbot]
  simpa using hzero

/-- The `χ`-projector is the identity on the actual `χ`-eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_apply_of_mem_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    {x : CyclotomicUnitFreePartModP (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartModPEvenCharacterEigenspace
      (p := p) K hp_gt_two χ) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x = x := by
  calc
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x =
        ∑ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p),
          cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x :=
          (Finset.sum_eq_single χ
            (fun ψ _hψ hψχ =>
              cyclotomicUnitFreePartModPEvenCharacterProjector_apply_eq_zero_of_mem_ne
                (p := p) (K := K) hp_gt_two (Ne.symm hψχ) hx)
            (fun hχ => (hχ (Finset.mem_univ χ)).elim)).symm
    _ = x := cyclotomicUnitFreePartModPEvenCharacterProjector_sum_apply
      (p := p) (K := K) hp_gt_two x

/-- The range of a character idempotent projector is exactly the corresponding
actual even-character eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_range_eq_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p)) :
    LinearMap.range
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ) =
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace
      (p := p) (K := K) hp_gt_two χ y
  · intro hx
    exact ⟨x,
      cyclotomicUnitFreePartModPEvenCharacterProjector_apply_of_mem_eigenspace
        (p := p) (K := K) hp_gt_two χ hx⟩

theorem cyclotomicUnitFreePartModPEvenCharacterEigenspace_finrank_of_ne_one
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (hp_gt_two : 2 < p)
    {χ : MulChar (CyclotomicEvenDelta p) (ZMod p)} (hχ : χ ≠ 1) :
    Module.finrank (ZMod p)
        (cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ) = 1 := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  let P := cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ
  have hPidem : IsIdempotentElem P := by
    let ρ := cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two
    change IsIdempotentElem
      (ρ.asAlgebraHom (charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ))
    exact (isIdempotentElem_charIdempotent
      (G := CyclotomicEvenDelta p) (R := ZMod p) χ).map ρ.asAlgebraHom
  have hcast :
      (Module.finrank (ZMod p)
          (cyclotomicUnitFreePartModPEvenCharacterEigenspace
            (p := p) K hp_gt_two χ) : ZMod p) = 1 := by
    calc
      (Module.finrank (ZMod p)
          (cyclotomicUnitFreePartModPEvenCharacterEigenspace
            (p := p) K hp_gt_two χ) : ZMod p)
          = (Module.finrank (ZMod p) (LinearMap.range P) : ZMod p) := by
              rw [cyclotomicUnitFreePartModPEvenCharacterProjector_range_eq_eigenspace
                (p := p) (K := K) hp_gt_two χ]
      _ = LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) P := by
              rw [LinearMap.trace_eq_finrank_range_of_isIdempotentElem P hPidem]
      _ = 1 := cyclotomicUnitFreePartModPEvenCharacterProjector_trace_of_ne_one
        (p := p) (K := K) hp_gt_two hχ
  have hfin_le :
      Module.finrank (ZMod p)
          (cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ) ≤
        (p - 3) / 2 := by
    rw [← cyclotomicUnitFreePartModP_finrank_eq (p := p) (K := K) hp_gt_two]
    exact Submodule.finrank_le _
  have hfin_lt :
      Module.finrank (ZMod p)
          (cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ) < p := by
    omega
  have hp_one : 1 < p := lt_trans Nat.one_lt_two hp_gt_two
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hfin_lt, ZMod.val_one''] at hval
  · exact hval
  · omega

theorem cyclotomicUnitFreePartModPDeltaCharacterEigenspace_pullback_finrank_of_ne_one
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (hp_gt_two : 2 < p)
    {χ : MulChar (CyclotomicEvenDelta p) (ZMod p)} (hχ : χ ≠ 1) :
    Module.finrank (ZMod p)
        (cyclotomicUnitFreePartModPDeltaCharacterEigenspace
          (p := p) K (evenDeltaCharacterPullback (p := p) χ)) = 1 := by
  rw [cyclotomicUnitFreePartModPDeltaCharacterEigenspace_pullback
    (p := p) (K := K) hp_gt_two χ]
  exact cyclotomicUnitFreePartModPEvenCharacterEigenspace_finrank_of_ne_one
    (p := p) (K := K) hp_gt_two hχ

theorem cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (hp_gt_two : 2 < p)
    {χ : MulChar (CyclotomicUnitDelta p) (ZMod p)}
    (hχ_even : IsEvenDeltaCharacter (p := p) χ)
    (hχ_ne : χ ≠ (1 : MulChar (CyclotomicUnitDelta p) (ZMod p))) :
    Module.finrank (ZMod p)
        (cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K χ) = 1 := by
  rw [← evenDeltaCharacterPullback_descend (p := p) χ hχ_even]
  exact cyclotomicUnitFreePartModPDeltaCharacterEigenspace_pullback_finrank_of_ne_one
    (p := p) (K := K) hp_gt_two
    (evenDeltaCharacterDescend_ne_one (p := p) χ hχ_even hχ_ne)

theorem cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_odd
    (hp_gt_two : 2 < p)
    {χ : MulChar (CyclotomicUnitDelta p) (ZMod p)}
    (hχ_odd : χ (-1 : CyclotomicUnitDelta p) = -1) :
    Module.finrank (ZMod p)
        (cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K χ) = 0 := by
  rw [cyclotomicUnitFreePartModPDeltaCharacterEigenspace_eq_bot_of_odd
    (p := p) (K := K) hp_gt_two hχ_odd]
  simp

end BernoulliRegular

end
