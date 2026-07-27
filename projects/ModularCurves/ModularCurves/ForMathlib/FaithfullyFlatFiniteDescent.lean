/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Faithfully flat descent of module finiteness and finite presentation

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(leaf `[HG-A2]`; Stacks
`algebra-lemma-descend-properties-modules`, tag 03C4, parts (1)–(2)): if `S` is a faithfully
flat `R`-algebra and the base change `S ⊗[R] M` is finite (resp. finitely presented) over
`S`, then `M` is finite (resp. finitely presented) over `R`.

* `Module.Finite.of_finite_tensorProduct` — write finitely many generators of `S ⊗[R] M` as
  finite sums of pure tensors, span the `M`-legs over `R`, and descend the surjectivity of
  the inclusion by faithful flatness (`lTensor_surjective_iff_surjective`).
* `Module.FinitePresentation.of_finitePresentation_tensorProduct` — present `M` by a finite
  free cover `π : (Fin n → R) → M`; by flatness the kernel base-changes to the kernel
  (`Module.Flat.ker_lTensor_eq`), which is finitely generated over `S`
  (`Module.FinitePresentation.fg_ker`), so the finiteness descent applies to `ker π`.

In the Hopf-Galois endgame (`[HG-B6]`) this is the step turning the Galois isomorphism
`B ⊗_C B ≅ B ⊗[R] A` (free of finite rank over `B`) plus faithful flatness of `C → B` into
`B` finitely presented over `C`, whence finite locally free
(`Module.Flat.projective_of_finitePresentation`).
-/

open TensorProduct

section Finite

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]

/-- **Faithfully flat descent of module finiteness** (Stacks 03C4 (1)): if `S ⊗[R] M` is a
finite `S`-module and `S` is faithfully flat over `R`, then `M` is a finite `R`-module. -/
theorem Module.Finite.of_finite_tensorProduct [h : Module.Finite S (S ⊗[R] M)] :
    Module.Finite R M := by
  classical
  obtain ⟨T, hT⟩ := h.fg_top
  choose F hF using fun t : S ⊗[R] M => TensorProduct.exists_finset t
  set N : Submodule R M :=
    Submodule.span R (⋃ t ∈ T, Prod.snd '' (F t : Set (S × M))) with hNdef
  have hsurj : Function.Surjective (N.subtype.lTensor S) := by
    show Function.Surjective ⇑(AlgebraTensorModule.lTensor S S N.subtype)
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro t ht
    rw [SetLike.mem_coe, LinearMap.mem_range]
    have hmem : ∀ p ∈ F t, p.2 ∈ N := fun p hp =>
      Submodule.subset_span (Set.mem_biUnion ht ⟨p, hp, rfl⟩)
    refine ⟨∑ p ∈ (F t).attach, p.1.1 ⊗ₜ[R] (⟨p.1.2, hmem p.1 p.2⟩ : N), ?_⟩
    rw [map_sum]
    calc ∑ p ∈ (F t).attach,
          (AlgebraTensorModule.lTensor S S N.subtype) (p.1.1 ⊗ₜ[R] (⟨p.1.2, hmem p.1 p.2⟩ : N))
        = ∑ p ∈ (F t).attach, p.1.1 ⊗ₜ[R] p.1.2 := Finset.sum_congr rfl fun p _ => rfl
      _ = ∑ p ∈ F t, p.1 ⊗ₜ[R] p.2 :=
          Finset.sum_attach (F t) (fun p => p.1 ⊗ₜ[R] p.2)
      _ = t := (hF t).symm
  have hNsurj : Function.Surjective N.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S N.subtype).mp hsurj
  have hNtop : N = ⊤ := by
    rw [← Submodule.range_subtype N, LinearMap.range_eq_top]
    exact hNsurj
  refine ⟨?_⟩
  rw [← hNtop, hNdef]
  refine Submodule.fg_span (Set.Finite.biUnion T.finite_toSet fun t _ => ?_)
  exact Set.Finite.image _ (F t).finite_toSet

end Finite

section FinitePresentation

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]

/-- **Faithfully flat descent of finite presentation** (Stacks 03C4 (2)): if `S ⊗[R] M` is a
finitely presented `S`-module and `S` is faithfully flat over `R`, then `M` is a finitely
presented `R`-module. Present `M` by a finite free cover; by flatness the kernel base-changes
to the kernel of the base-changed cover, which is finitely generated
(`Module.FinitePresentation.fg_ker`), so `Module.Finite.of_finite_tensorProduct` descends its
generation and the free cover presents `M`. -/
theorem Module.FinitePresentation.of_finitePresentation_tensorProduct
    [hfp : Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := by
  haveI hMfin : Module.Finite R M := Module.Finite.of_finite_tensorProduct R S M
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  refine Module.finitePresentation_of_free_of_surjective π hπ ?_
  -- the base-changed cover is surjective, so its kernel is finitely generated
  have hπS : Function.Surjective ⇑(AlgebraTensorModule.lTensor S S π) := by
    show Function.Surjective ⇑(π.lTensor S)
    exact LinearMap.lTensor_surjective S hπ
  have hker : (LinearMap.ker (AlgebraTensorModule.lTensor S S π)).FG :=
    Module.FinitePresentation.fg_ker _ hπS
  -- flatness: that kernel is the image of the base-changed kernel
  have hkereq := Module.Flat.ker_lTensor_eq (M := S) S π
  -- so S ⊗ ker π surjects onto a f.g. module; descend finiteness to ker π
  haveI : Module.Finite S
      (LinearMap.range (AlgebraTensorModule.lTensor S S (LinearMap.ker π).subtype)) := by
    rw [← hkereq]
    exact Module.Finite.iff_fg.mpr hker
  have hinj : Function.Injective ⇑(AlgebraTensorModule.lTensor S S (LinearMap.ker π).subtype) := by
    show Function.Injective ⇑((LinearMap.ker π).subtype.lTensor S)
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _)
  haveI : Module.Finite S (S ⊗[R] LinearMap.ker π) := by
    set e := LinearEquiv.ofInjective
      (AlgebraTensorModule.lTensor S S (LinearMap.ker π).subtype) hinj with he
    exact Module.Finite.equiv e.symm
  haveI : Module.Finite R (LinearMap.ker π) :=
    Module.Finite.of_finite_tensorProduct R S (LinearMap.ker π)
  exact Module.Finite.iff_fg.mp inferInstance

end FinitePresentation
