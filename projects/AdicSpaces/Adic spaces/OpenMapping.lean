/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import «Adic spaces».NoetherianTateModules

/-!
# Open Mapping and Strict Exactness for Tate Modules

Open mapping framework for completed Tate rings, following Wedhorn Thm 6.16 / Prop 6.18.

## Main results

* `isEmbedding_of_isStrictMap` : strict injective continuous map is a topological embedding
* `isOpenMap_of_isFiltrationOpen` : filtration-open group homomorphism is an open map
* `strictExact_package` : strict-exactness package for short exact sequences

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 6.16, Proposition 6.18
-/

open Filter Topology

/-! ### Embedding from strict injective map -/

/-- A strict, continuous, injective map is a topological embedding. -/
theorem isEmbedding_of_isStrictMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hstrict : IsStrictMap f) (hcont : Continuous f)
    (hinj : Function.Injective f) : Topology.IsEmbedding f := by
  have hoe : Topology.IsOpenEmbedding (Set.rangeFactorization f) :=
    .of_continuous_injective_isOpenMap (hcont.subtype_mk _)
      (fun a b h => hinj (Subtype.ext_iff.mp h)) hstrict
  change Topology.IsEmbedding (Subtype.val ∘ Set.rangeFactorization f)
  exact Topology.IsEmbedding.subtypeVal.comp hoe.isEmbedding

/-! ### Filtration-open framework -/

section Filtration

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]

/-- A group homomorphism is **filtration-open** if the image of each basis neighborhood of
zero is a neighborhood of zero in the target. -/
def IsFiltrationOpen {ι : Type*} (f : G →+ H) (U : ι → Set G)
    (_hU : ∀ i, U i ∈ nhds 0) : Prop :=
  ∀ i, f '' (U i) ∈ nhds (0 : H)

/-- A filtration-open group homomorphism is an open map. -/
theorem isOpenMap_of_isFiltrationOpen {ι : Type*}
    (f : G →+ H) (U : ι → Set G) (hU_nhds : ∀ i, U i ∈ nhds (0 : G))
    (hU_basis : Filter.HasBasis (nhds (0 : G)) (fun _ => True) U)
    (hfilt : IsFiltrationOpen f U hU_nhds) : IsOpenMap f := by
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  intro S hS
  rw [Filter.mem_map] at hS
  obtain ⟨i, -, hi⟩ := hU_basis.mem_iff.mp hS
  exact Filter.mem_of_superset (hfilt i)
    ((Set.image_mono hi).trans (Set.image_preimage_subset f S))

/-- Variant of `isOpenMap_of_isFiltrationOpen` with `ℕ`-indexed filtration. -/
theorem isOpenMap_of_filtration_nhds (f : G →+ H)
    (U : ℕ → Set G) (hU_nhds : ∀ n, U n ∈ nhds (0 : G))
    (hU_basis : Filter.HasBasis (nhds (0 : G)) (fun _ => True) U)
    (himage : ∀ n, f '' (U n) ∈ nhds (0 : H)) :
    IsOpenMap f :=
  isOpenMap_of_isFiltrationOpen f U hU_nhds hU_basis himage

end Filtration

/-! ### Closed kernel -/

section ClosedKernel

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [T1Space H]

/-- The kernel of a continuous group homomorphism to a T1 space is closed. -/
theorem AddMonoidHom.isClosed_ker' (f : G →+ H) (hf : Continuous f) :
    IsClosed (f ⁻¹' {0}) :=
  (T1Space.t1 0).preimage hf

end ClosedKernel

/-! ### Strict exactness package -/

section StrictExactPackage

/-- Strict exactness package: embedding, openness, and closed kernel for a short exact
sequence of topological groups. -/
theorem strictExact_package {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [TopologicalSpace M₁] [IsTopologicalAddGroup M₁]
    [AddCommGroup M₂] [TopologicalSpace M₂] [IsTopologicalAddGroup M₂]
    [AddCommGroup M₃] [TopologicalSpace M₃] [IsTopologicalAddGroup M₃] [T1Space M₃]
    (f : M₁ →+ M₂) (g : M₂ →+ M₃) (hf_inj : Function.Injective f)
    (hf_cont : Continuous f) (hf_strict : IsStrictMap f) (hg_cont : Continuous g)
    (_hg_surj : Function.Surjective g) (hg_open : IsOpenMap g) :
    Topology.IsEmbedding f ∧ IsOpenMap g ∧ IsClosed (g ⁻¹' {0}) :=
  ⟨isEmbedding_of_isStrictMap hf_strict hf_cont hf_inj, hg_open, g.isClosed_ker' hg_cont⟩

end StrictExactPackage

/-! ### Module topology corollaries -/

section ModuleTopologyCorollaries

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
/-- In a short exact sequence of modules with `IsModuleTopology R`, the surjection is open
and the injection is continuous. -/
theorem shortExact_openSurjection_moduleTopology {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [IsModuleTopology R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [IsModuleTopology R M₂]
    [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [IsModuleTopology R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (_hf_inj : Function.Injective f)
    (hg_surj : Function.Surjective g) (_hfg : Function.Exact f g) :
    IsOpenMap g ∧ Continuous f := by
  have := IsModuleTopology.toContinuousAdd R M₂
  have := IsModuleTopology.toContinuousSMul R M₂
  exact ⟨IsModuleTopology.isOpenMap_of_surjective_of_finite g hg_surj,
    IsModuleTopology.continuous_of_linearMap (R := R) f⟩

omit [IsTopologicalRing R] in
/-- When the injection in a module-topology short exact sequence is strict, it is an
embedding. -/
theorem shortExact_isEmbedding_of_strict_moduleTopology {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [IsModuleTopology R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [IsModuleTopology R M₂]
    [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [IsModuleTopology R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf_inj : Function.Injective f)
    (hf_strict : IsStrictMap f) (hg_surj : Function.Surjective g)
    (_hfg : Function.Exact f g) : Topology.IsEmbedding f ∧ IsOpenMap g := by
  have := IsModuleTopology.toContinuousAdd R M₂
  have := IsModuleTopology.toContinuousSMul R M₂
  exact ⟨isEmbedding_of_isStrictMap hf_strict
      (IsModuleTopology.continuous_of_linearMap (R := R) f) hf_inj,
    IsModuleTopology.isOpenMap_of_surjective_of_finite g hg_surj⟩

end ModuleTopologyCorollaries
