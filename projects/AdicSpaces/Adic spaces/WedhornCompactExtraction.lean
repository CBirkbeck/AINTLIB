/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».SpaCompact

/-!
# Wedhorn Compactness Extraction (C1 → finite `mk_S_D`)

The minimal missing wrapper from the C1 audit
(`WEDHORN-C1-API-AUDIT`): given a pointwise C1 single-`f` refinement
witness on a single rational-locale piece `D`, extract a finite
`Finset A` covering `D`'s rational open and providing the per-D data
consumed by `StandardCover.exists_refines_cover_per_E_of_per_D_construction`.

## What this file gives

`mk_S_D_of_C1_and_compactness` — for a fixed `D ∈ C.covers`, given
the pointwise C1 hypothesis

  ∀ v ∈ rationalOpen D.T D.s, ∃ f : A,
    v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s

produce a finite `S : Finset A` satisfying the per-D shape consumed
by `exists_refines_cover_per_E_of_per_D_construction`:

* `∀ f ∈ S, rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`,
* `∀ v ∈ rationalOpen D.T D.s,
    ∃ f ∈ S, v ∈ rationalOpen (insert f C.base.T) C.base.s`.

## Proof ingredients (no Lane B / Cor 8.32 / Jacobson / T001)

1. `SpaCompact.isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` —
   `Subtype.val ⁻¹' rationalOpen D.T D.s ⊆ ↥(Spa A A⁺)` is compact under
   the Tate pseudouniformizer hypotheses.
2. `RationalSubsets.rationalOpen_isOpen` — each
   `Subtype.val ⁻¹' rationalOpen (insert f C.base.T) C.base.s` is open.
3. `IsCompact.elim_finite_subcover` — the standard mathlib finite-subcover
   extraction; produces a finset of indices.

The witness function `g : K → A` is chosen by `Classical.choose` from the
pointwise C1 existential. The output `S := T₀.image g` for the finite
subcover-index `T₀ : Finset K`.

This is **purely a topological extraction wrapper**: no Lane B content, no
Cor 8.32, no Jacobson, no T001, no faithful-flatness, no final acyclicity
hypotheses propagate. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

omit [HasLocLiftPowerBounded A] in
/-- **Compactness extraction wrapper for the C1 → per-D refinement step**.

For a fixed cover piece `D` and a pointwise C1 single-`f` refinement
witness on every `v ∈ rationalOpen D.T D.s`, quasi-compactness of the
rational open in `↥(Spa A A⁺)` (`isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`)
extracts a finite `S : Finset A` providing the per-D containment and
coverage data consumed by
`StandardCover.exists_refines_cover_per_E_of_per_D_construction`.

No Lane B / Cor 8.32 / Jacobson / T001 / final acyclicity content. -/
theorem mk_S_D_of_C1_and_compactness
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (D : RationalLocData A)
    (hC1 : ∀ v ∈ rationalOpen D.T D.s, ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) :
    ∃ S : Finset A,
      (∀ f ∈ S, rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ S, v ∈ rationalOpen (insert f C.base.T) C.base.s) := by
  classical
  -- The compact set in `↥(Spa A A⁺)`.
  let K : Set ↥(Spa A A⁺) := Subtype.val ⁻¹' rationalOpen D.T D.s
  have hK_compact : IsCompact K :=
    isCompact_preimage_rationalOpen_of_tate_pseudouniformizer
      P hA₀_le π hI hπ_tn hπ_unit hArch D.T D.s
  -- Lift the pointwise C1 hypothesis to a Subtype-indexed witness function.
  have hC1_K : ∀ w : K, ∃ f : A,
      (w.1.1 : Spv A) ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s := by
    intro w
    have hmem : (w.1.1 : Spv A) ∈ rationalOpen D.T D.s := w.2
    exact hC1 w.1.1 hmem
  -- Choose a witness function g : K → A.
  let g : K → A := fun w => Classical.choose (hC1_K w)
  have hg_self : ∀ w : K, (w.1.1 : Spv A) ∈
      rationalOpen (insert (g w) C.base.T) C.base.s :=
    fun w => (Classical.choose_spec (hC1_K w)).1
  have hg_sub : ∀ w : K,
      rationalOpen (insert (g w) C.base.T) C.base.s ⊆ rationalOpen D.T D.s :=
    fun w => (Classical.choose_spec (hC1_K w)).2
  -- The K-indexed open cover of K.
  let V : K → Set ↥(Spa A A⁺) := fun w =>
    Subtype.val ⁻¹' rationalOpen (insert (g w) C.base.T) C.base.s
  have hV_open : ∀ w, IsOpen (V w) := fun _ => rationalOpen_isOpen _ _
  have hK_cover : K ⊆ ⋃ w, V w := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact hg_self ⟨x, hx⟩
  -- Finite subcover via mathlib's `IsCompact.elim_finite_subcover`.
  obtain ⟨T₀, hT₀_cover⟩ := hK_compact.elim_finite_subcover V hV_open hK_cover
  refine ⟨T₀.image g, ?_, ?_⟩
  · -- Containment: each `f ∈ T₀.image g` comes from some `w ∈ T₀` via `hg_sub`.
    intro f hf
    obtain ⟨w, _hw_T₀, hg_eq⟩ := Finset.mem_image.mp hf
    rw [← hg_eq]
    exact hg_sub w
  · -- Coverage: `v ∈ rationalOpen D.T D.s` lifts to a point of `K`, then
    -- the finite subcover supplies a `w ∈ T₀` with `v ∈ V w`, and `g w ∈ T₀.image g`.
    intro v hv
    have hv_spa : v ∈ Spa A A⁺ := rationalOpen_subset_spa hv
    let x : ↥(Spa A A⁺) := ⟨v, hv_spa⟩
    have hx_K : x ∈ K := hv
    have hmem : x ∈ ⋃ w ∈ T₀, V w := hT₀_cover hx_K
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨w₀, hw₀_T₀, hx_in⟩ := hmem
    exact ⟨g w₀, Finset.mem_image.mpr ⟨w₀, hw₀_T₀, rfl⟩, hx_in⟩

end ValuationSpectrum
