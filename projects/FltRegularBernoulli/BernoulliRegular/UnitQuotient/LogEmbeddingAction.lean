module

public import BernoulliRegular.UnitQuotient.FreeAction
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Unit quotients: logarithmic embedding and permutation action

This file proves `REF-07c2`.

The Dirichlet logarithmic embedding in mathlib uses a deleted coordinate
`NumberField.Units.logSpace K`, where one infinite place is omitted.  That
space is convenient for Dirichlet's unit theorem, but it is not literally
stable under the Galois permutation of infinite places.

Here we first use the full logarithmic space

```text
InfinitePlace K → ℝ.
```

On this full space the comparison is clean: the cyclotomic action on units is
intertwined by the logarithmic embedding with the permutation action on
infinite places.  Later steps can pass from this full permutation
representation to the usual deleted-coordinate Dirichlet lattice.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The full real logarithmic space indexed by all infinite places of `K`. -/
abbrev CyclotomicFullLogSpace : Type _ :=
  InfinitePlace K → ℝ

/-- The full logarithmic embedding of units.  This is the same formula as
`NumberField.Units.logEmbedding`, but before deleting one coordinate. -/
def cyclotomicFullLogEmbedding :
    Additive (CyclotomicUnitGroup K) →+ CyclotomicFullLogSpace K where
  toFun u w := InfinitePlace.mult w * Real.log (w (u.toMul : K))
  map_zero' := by
    ext w
    simp
  map_add' u v := by
    ext w
    simp [Real.log_mul, mul_add]

@[simp]
theorem cyclotomicFullLogEmbedding_apply
    (u : CyclotomicUnitGroup K) (w : InfinitePlace K) :
    cyclotomicFullLogEmbedding K (Additive.ofMul u) w =
      InfinitePlace.mult w * Real.log (w (u : K)) :=
  rfl

/-- The multiplicity of an infinite place is unchanged by the Galois action. -/
theorem infinitePlace_mult_smul (σ : Gal(K/ℚ)) (w : InfinitePlace K) :
    InfinitePlace.mult (σ • w) = InfinitePlace.mult w := by
  unfold InfinitePlace.mult
  by_cases hw : InfinitePlace.IsReal w
  · rw [if_pos ((InfinitePlace.isReal_smul_iff (σ := σ) (w := w)).2 hw), if_pos hw]
  · rw [if_neg (by
        intro h
        exact hw ((InfinitePlace.isReal_smul_iff (σ := σ) (w := w)).1 h)),
      if_neg hw]

/-- The permutation action of `Gal(K/Q)` on the full logarithmic space. -/
def cyclotomicFullLogSpacePermutation (σ : Gal(K/ℚ)) :
    CyclotomicFullLogSpace K ≃ₗ[ℝ] CyclotomicFullLogSpace K where
  toFun f w := f (σ⁻¹ • w)
  invFun f w := f (σ • w)
  left_inv f := by
    ext w
    change f (σ⁻¹ • (σ • w)) = f w
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv f := by
    ext w
    change f (σ • (σ⁻¹ • w)) = f w
    rw [← mul_smul, mul_inv_cancel, one_smul]
  map_add' f g := by
    ext w
    rfl
  map_smul' c f := by
    ext w
    rfl

@[simp]
theorem cyclotomicFullLogSpacePermutation_apply
    (σ : Gal(K/ℚ)) (f : CyclotomicFullLogSpace K) (w : InfinitePlace K) :
    cyclotomicFullLogSpacePermutation K σ f w = f (σ⁻¹ • w) :=
  rfl

/-- The cyclotomic `Delta = (ZMod p)^*` permutation action on the full
logarithmic space. -/
def cyclotomicFullLogSpaceDeltaAction :
    CyclotomicUnitDelta p →*
      (CyclotomicFullLogSpace K ≃ₗ[ℝ] CyclotomicFullLogSpace K) where
  toFun a :=
    cyclotomicFullLogSpacePermutation K (cyclotomicSigmaOfUnit (p := p) K a)
  map_one' := by
    ext f w
    change f ((cyclotomicSigmaOfUnit (p := p) K 1)⁻¹ • w) = f w
    rw [cyclotomicSigmaOfUnit_one, inv_one, one_smul]
  map_mul' a b := by
    ext f w
    change f ((cyclotomicSigmaOfUnit (p := p) K (a * b))⁻¹ • w) =
      f ((cyclotomicSigmaOfUnit (p := p) K b)⁻¹ •
        ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w))
    rw [cyclotomicSigmaOfUnit_mul, ← mul_smul, mul_inv_rev]

@[simp]
theorem cyclotomicFullLogSpaceDeltaAction_apply
    (a : CyclotomicUnitDelta p) (f : CyclotomicFullLogSpace K) (w : InfinitePlace K) :
    cyclotomicFullLogSpaceDeltaAction (p := p) K a f w =
      f ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w) :=
  rfl

@[simp]
theorem cyclotomicUnitEquiv_coe
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    ((cyclotomicUnitEquiv (p := p) K a u : CyclotomicUnitGroup K) : K) =
      cyclotomicSigmaOfUnit (p := p) K a (u : K) :=
  rfl

/-- The full logarithmic embedding intertwines the cyclotomic unit action with
the permutation action on infinite places. -/
theorem cyclotomicFullLogEmbedding_cyclotomicUnitEquiv
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicFullLogEmbedding K
        (Additive.ofMul (cyclotomicUnitEquiv (p := p) K a u)) =
      cyclotomicFullLogSpaceDeltaAction (p := p) K a
        (cyclotomicFullLogEmbedding K (Additive.ofMul u)) := by
  ext w
  change InfinitePlace.mult w *
      Real.log (w (cyclotomicSigmaOfUnit (p := p) K a (u : K))) =
    InfinitePlace.mult ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w) *
      Real.log (((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w) (u : K))
  rw [infinitePlace_mult_smul]
  rw [InfinitePlace.smul_apply]
  rw [show ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ : Gal(K/ℚ)).symm =
      cyclotomicSigmaOfUnit (p := p) K a by
    rfl]

/-- The kernel of the full logarithmic embedding is the torsion subgroup of
global units. -/
theorem cyclotomicFullLogEmbedding_eq_zero_iff
    {u : CyclotomicUnitGroup K} :
    cyclotomicFullLogEmbedding K (Additive.ofMul u) = 0 ↔
      u ∈ CyclotomicUnitTorsion K := by
  rw [CyclotomicUnitTorsion, NumberField.Units.mem_torsion]
  constructor
  · intro h w
    exact NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero.mp (by
      simpa [cyclotomicFullLogEmbedding] using congrFun h w)
  · intro h
    ext w
    exact NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero.mpr (h w)

/-- The full logarithmic embedding after quotienting units by torsion. -/
def cyclotomicFullLogEmbeddingFreePart :
    CyclotomicUnitFreePart K →+ CyclotomicFullLogSpace K :=
  MonoidHom.toAdditiveLeft <|
    (QuotientGroup.kerLift
        (AddMonoidHom.toMultiplicativeRight (cyclotomicFullLogEmbedding K))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext u
        rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply,
          ofAdd_eq_one, ← cyclotomicFullLogEmbedding_eq_zero_iff (K := K)])).toMonoidHom

@[simp]
theorem cyclotomicFullLogEmbeddingFreePart_apply
    (u : CyclotomicUnitGroup K) :
    cyclotomicFullLogEmbeddingFreePart K
        (Additive.ofMul (cyclotomicUnitFreeClass K u)) =
      cyclotomicFullLogEmbedding K (Additive.ofMul u) :=
  rfl

/-- The full logarithmic embedding on the torsion-free unit quotient is
equivariant for the cyclotomic action and the permutation action on infinite
places. -/
theorem cyclotomicFullLogEmbeddingFreePart_equivariant
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePart K) :
    cyclotomicFullLogEmbeddingFreePart K
        (cyclotomicUnitFreePartDeltaAction (p := p) K a x) =
      cyclotomicFullLogSpaceDeltaAction (p := p) K a
        (cyclotomicFullLogEmbeddingFreePart K x) := by
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro u
      change cyclotomicFullLogEmbeddingFreePart K
          (cyclotomicUnitFreePartDeltaAction (p := p) K a
            (Additive.ofMul (cyclotomicUnitFreeClass K u))) =
        cyclotomicFullLogSpaceDeltaAction (p := p) K a
          (cyclotomicFullLogEmbeddingFreePart K
            (Additive.ofMul (cyclotomicUnitFreeClass K u)))
      rw [cyclotomicUnitFreePartDeltaAction_apply_class,
        cyclotomicFullLogEmbeddingFreePart_apply,
        cyclotomicFullLogEmbeddingFreePart_apply,
        cyclotomicFullLogEmbedding_cyclotomicUnitEquiv]

end BernoulliRegular

end
