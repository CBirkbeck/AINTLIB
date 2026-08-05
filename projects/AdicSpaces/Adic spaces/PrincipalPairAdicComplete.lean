/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicCompletionNoetherian
import «Adic spaces».AdicSpectrum
import «Adic spaces».RestrictedPowerSeries

/-!
# Adic completeness of the canonical principal pair

For a strongly noetherian Tate ring `A`, the canonical principal pair
`(IsTateRing.principalPair A).toPairOfDefinition` is adically complete with
respect to its principal ideal of definition.

## Main results

* `principalPair_A₀_completeSpace_of_stronglyNoetherianTate`: the ring of
  definition `A₀` is a complete uniform space for the subspace uniformity
  inherited from `A`'s canonical right uniformity.
* `principalPair_isAdicComplete_of_stronglyNoetherianTate`: the principal pair
  is `IsAdicComplete`, obtained from the completeness above via
  `IsAdic.isAdicComplete_iff`.

These are the strongly-noetherian Tate analogues of the completeness condition
needed by Prop 7.14 (`spanTop_iff_noCommonZero_spa`), and mirror
`Cor832.presheafValue_isAdicComplete` at the level of the principal pair on `A`
rather than on `presheafValue D`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

omit [PlusSubring A] in
/-- **Completeness of `A₀` for the canonical principal pair.** The ring of
definition of a strongly noetherian Tate ring is a complete uniform space, when
`A₀` is equipped with the subspace uniformity inherited (via `Subtype.val`) from
`A`'s canonical right-uniform structure as a topological additive group.

This is the "completeness" half of Hausdorff + complete ⇔ `IsAdicComplete`
(via `IsAdic.isAdicComplete_iff`). The analogous claim at the
completion-presheaf level is `presheafValue_isAdicComplete` in `Cor832.lean`
(discharged via the closed-subring-of-complete pattern); the principal-pair
case for `A` itself is the corresponding Wedhorn obligation. -/
theorem principalPair_A₀_completeSpace_of_stronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    letI : UniformSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
      UniformSpace.comap Subtype.val ‹UniformSpace A›
    CompleteSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  set P := (IsTateRing.principalPair A).toPairOfDefinition
  have hclosed : IsClosed (P.A₀ : Set A) :=
    AddSubgroup.isClosed_of_isOpen P.A₀.toAddSubgroup P.isOpen
  have : IsClosed ((P.A₀ : Set A) : Set A) := hclosed
  exact IsClosed.completeSpace_coe (s := (P.A₀ : Set A))

omit [PlusSubring A] in
/-- **Adic-completeness of the canonical principal pair.** The principal pair of
a (strongly noetherian) Tate ring is adically complete with respect to its
principal ideal of definition.

**Discharge**: via Mathlib's `IsAdic.isAdicComplete_iff`
(`AdicCompletion/Topology.lean`), the I-adic completeness of `(A₀, I)` is
equivalent to `CompleteSpace A₀ ∧ T2Space A₀` once the canonical uniform
structure is installed. The `T2Space` factor is automatic (subspace of T₂); the
`CompleteSpace` factor is
`principalPair_A₀_completeSpace_of_stronglyNoetherianTate`. -/
theorem principalPair_isAdicComplete_of_stronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    IsAdicComplete
      (IsTateRing.principalPair A).toPairOfDefinition.I
      (IsTateRing.principalPair A).toPairOfDefinition.A₀ := by
  -- Equip the ambient `A` with its canonical (right) uniform structure as a
  -- topological additive group; on an additive _commutative_ topological
  -- group this canonical uniformity makes `A` an `IsUniformAddGroup`.
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  -- `A₀` inherits the subspace uniformity via `Subtype.val`.
  letI : UniformSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    UniformSpace.comap Subtype.val ‹UniformSpace A›
  -- Inherit `IsUniformAddGroup` via the canonical subring/addsubgroup inclusion.
  have : IsUniformAddGroup
      ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    AddSubgroup.isUniformAddGroup
      (IsTateRing.principalPair A).toPairOfDefinition.A₀.toAddSubgroup
  -- Apply the `IsAdic.isAdicComplete_iff` equivalence; `T2Space` is automatic
  -- as a subspace of `T2Space A`, `CompleteSpace` is the named sub-atom.
  exact ((IsTateRing.principalPair A).toPairOfDefinition.isAdic.isAdicComplete_iff).mpr
    ⟨principalPair_A₀_completeSpace_of_stronglyNoetherianTate,
     inferInstance⟩

end ValuationSpectrum
