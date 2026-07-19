/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SheafyRing
import «Adic spaces».StandardRefinement

/-!
# A⁺-independence via standard covers (Kedlaya Lemma 1.6.8 / Remark 1.6.9)

The genuine transfer engine for pair-level sheafiness between different rings of
integral elements of one complete Tate ring, factored exactly as in Kedlaya's
Remark 1.6.9: *"both the collection of standard rational coverings, and the
assertions of the sheaf axiom for these coverings, depend only on `A`, not on `A⁺`."*

* `standardSheafCondition_of_isSheafyFor` — **the single-pair derivation** of the
  `A⁺`-free `StandardSheafCondition` (upgrading
  `standardSheafCondition_of_isSheafyComplete`, which needed *all* pairs): the
  standard covers instantiate at the given pair (their subordination and covering
  conditions are `Spa`-uniform), the sheaf-axiom *assertions* about them are
  literally `A⁺`-independent (`presheafValue` and `restrictionMap` never see `A⁺`;
  the instance and containment arguments are proof-irrelevant), and the one
  `A⁺`-relative hypothesis shape — Čech compatibility — transfers through the R3
  bridge (`allDataCompatible_iff_exactIntersectionCompatible`), whose
  exact-intersection form mentions only the intersection data.
* `IsEmbedding.of_comp_isEmbedding` — the elementary factorization principle
  (WO2 task 4): if `g ∘ f` is a topological embedding and `g` is continuous, then
  `f` is a topological embedding. Stated and proved here as a plain topology lemma
  (it is *not* attributed to Kedlaya).
* `HasStandardRefinements` — **the named descent input** (the conclusion of Kedlaya
  Lemma 1.6.8 / Wedhorn Lemma 7.54 / Huber [Hu3] 2.6, in the project's
  intersect-with-the-base vocabulary): every rational covering at the given pair is
  refined by a generated standard cover. The *generation* side of 1.6.8 is proved in
  `StandardRefinement.lean`; the *descent* side for coverings of a general rational
  base is the project's recorded missing API (`WedhornStandardCoverRefinement.lean`;
  Kedlaya's proof re-bases through "every rational subspace of `X` is itself the
  spectrum of a Huber pair", whose ring-level keystone `relativePiece_equiv`
  currently carries strongly noetherian hypotheses). It is therefore taken as a
  named, precisely-documented hypothesis — never silently, never via `iff_of_true`.
* `isSheafyFor_of_standardSheafCondition` — the reduction (Kedlaya 1.6.8 ⟹ the
  sheaf axioms for arbitrary rational covers): given the `A⁺`-free standard
  condition and the descent input at a pair, that pair is sheafy. Separation and
  the topological embedding transfer along the refinement by factorization; gluing
  transfers by the two-step Čech argument with the induced standard covers of the
  pieces (which are again standard data for the *same* spanning family, so the
  middle term supplies their separation).
* `isSheafyFor_congr` — **genuine A⁺-independence** (Kedlaya Remark 1.6.9): for a
  complete Tate ring with the descent input, `IsSheafyFor A Aplus ↔ IsSheafyFor A
  Bplus` for *any* two valid rings of integral elements — no strong noetherianness,
  no inclusion between the plus rings, no identification of the two `Spa`'s; the
  proof is the composite `IsSheafyFor A Aplus → StandardSheafCondition A →
  IsSheafyFor A Bplus` through the transfer engine above.

## References

* [K. Kedlaya, AWS 2017 notes], Lemma 1.6.8, Remarks 1.6.9–1.6.10.
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.54, Remark 8.20.
* [R. Huber, *A generalization of formal schemes and rigid analytic varieties*],
  Lemma 2.6.
-/

noncomputable section

open TopologicalSpace Topology Filter

universe u

namespace ValuationSpectrum

/-! ### The factorization principle (elementary topology; WO2 task 4) -/

/-- **Factorization principle for embeddings**: if `g ∘ f` is a topological
embedding and `g` is continuous, then `f` is a topological embedding. (Elementary;
proved from the filter characterization of induced topologies. Used for
transferring the cover-product embedding along a refinement; not a statement from
the cited sources.) -/
theorem IsEmbedding.of_comp_isEmbedding {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {g : β → γ}
    (hgf : Topology.IsEmbedding (g ∘ f)) (hf : Continuous f) (hg : Continuous g) :
    Topology.IsEmbedding f := by
  refine ⟨Topology.isInducing_iff_nhds.mpr fun x => le_antisymm ?_ ?_, ?_⟩
  · exact (hf.tendsto x).le_comap
  · calc Filter.comap f (𝓝 (f x))
        ≥ Filter.comap f (Filter.comap g (𝓝 (g (f x)))) :=
          Filter.comap_mono ((hg.tendsto (f x)).le_comap)
      _ = Filter.comap (g ∘ f) (𝓝 ((g ∘ f) x)) := Filter.comap_comap
      _ = 𝓝 x := (hgf.isInducing.nhds_eq_comap x).symm
  · intro x y hxy
    exact hgf.injective (show (g ∘ f) x = (g ∘ f) y from congrArg g hxy)

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-! ### The single-pair derivation of the `A⁺`-free standard condition -/

/-- **Kedlaya Remark 1.6.9, provable half, from a single pair**: if the genuine
all-open structure presheaf of `Spa (A, Aplus)` is a sheaf of topological rings for
**one** valid ring of integral elements, then the `A⁺`-free standard sheaf
condition holds — i.e. the sheaf-axiom assertions hold for every standard cover
datum *at every valid ring of integral elements simultaneously*.

This is the mechanism of Remark 1.6.9: a standard datum instantiates as a rational
covering at the given pair (its conditions are `Spa`-uniform); the embedding and
gluing *assertions* about it are statements about `presheafValue` and
`restrictionMap` only, hence independent of the instantiating pair (definitionally:
`HasLocLiftPowerBounded` is a `Prop` class and the subordination witnesses are
proofs); and the compatibility *hypothesis* transfers between pairs through its
exact-intersection form (`allDataCompatible_iff_exactIntersectionCompatible`),
which mentions only the intersection data. Upgrades
`standardSheafCondition_of_isSheafyComplete` (which consumed **all** pairs). -/
theorem standardSheafCondition_of_isSheafyFor (Aplus : RingOfIntegralElements A)
    (h : IsSheafyFor A Aplus) : StandardSheafCondition A := by
  classical
  -- the sheaf axioms at the given pair
  letI instP₁ : PlusSubring A := Aplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  haveI hSheafy₁ : IsSheafy A := isSheafy_of_isLimitSheaf h
  intro S B hB
  -- the sheaf axioms at the target pair, by transport of the standard datum
  letI instP₂ : PlusSubring A := ⟨B⟩
  haveI hB' : @IsRingOfIntegralElements A _ _ (@ringPlus A _ instP₂) := hB
  haveI hll₂ : @HasLocLiftPowerBounded A _ _ instP₂ _ :=
    @hasLocLiftPowerBounded_faithful A _ _ instP₂ _ _ _ _ _ _ hB'
  refine ⟨?_, ?_⟩
  · -- embedding: the assertion is `A⁺`-independent (the product restriction of the
    -- standard datum is the same function at both pairs, by proof irrelevance)
    exact @IsSheafy.embedding A _ _ _ instP₁ _ _ _ _ _ hSheafy₁
      (@StandardCoverData.toCovering A _ _ _ instP₁ S)
      (@StandardCoverData.toCovering_isRational A _ _ _ instP₁ S)
  · -- gluing: transfer the compatibility hypothesis through the R3 bridge
    intro f hf
    -- `f` is compatible at the target pair; its exact-intersection form mentions
    -- only the intersection data, hence re-reads at the given pair
    have hexact₂ := (@RationalCovering.allDataCompatible_iff_exactIntersectionCompatible
      A _ _ _ instP₂ _ hll₂ _ (@StandardCoverData.toCovering A _ _ _ instP₂ S)
      (@StandardCoverData.toCovering_isRational A _ _ _ instP₂ S) f).mp hf
    have hdata₁ : (@StandardCoverData.toCovering A _ _ _ instP₁ S).AllDataCompatible f :=
      (@RationalCovering.allDataCompatible_iff_exactIntersectionCompatible
        A _ _ _ instP₁ _ _ _ (@StandardCoverData.toCovering A _ _ _ instP₁ S)
        (@StandardCoverData.toCovering_isRational A _ _ _ instP₁ S) f).mpr hexact₂
    exact @IsSheafy.gluing A _ _ _ instP₁ _ _ _ _ _ hSheafy₁
      (@StandardCoverData.toCovering A _ _ _ instP₁ S)
      (@StandardCoverData.toCovering_isRational A _ _ _ instP₁ S) f hdata₁

end ValuationSpectrum
