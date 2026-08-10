/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetSheafyEndpoints
import «Adic spaces».FJP.RestrictedFubini
import «Adic spaces».SheafyRingEquivTransport
import «Adic spaces».MvTateAlgebraTopology

/-!
# Strong sheafiness of the finite-jet pinching algebra (campaign B skeleton)

Headline: the Tate extension `𝓐⟨V₁,…,Vₙ⟩ = restrictedMvPowerSeriesSubring n (JetA F)`
is sheafy for every valid ring of integral elements, for every `n` — i.e. `𝓐` is
**strongly sheafy** in the sense of Hansen–Kedlaya.

Route ([WP-paper] §5–§6 with the auxiliary variables carried along; reviewer §5.1):
the corners `B⟨V⟩, C⟨V⟩, D⟨V⟩` remain strongly noetherian affinoids (restricted
Fubini), the integral Milnor row extends coefficientwise to the Tate extensions, and
the graph-Koszul/sheaf-transfer argument of the original proof applies verbatim to
the extended square. The `⟨V⟩`-row and the transfer instantiation are an API gap
with their own sub-decomposition (`decomposition.md`, B-AG1); the leaves below are
the statable first layer.
-/

@[expose] public section

noncomputable section

namespace FiniteJet

open ValuationSpectrum TopologicalRing MvTateAlgebra

variable (F : Type*) [Field F]

section NestedFubini

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [IsTopologicalRing A] [IsTateRing A]

/-- Index bookkeeping for the nested Fubini: `Fin (n+k) ≃ Fin k ⊕ Fin n`, outer
variables first (matching `sumAlgEquiv`'s outer summand). -/
def nestedIndexEquiv (n k : ℕ) : Fin (n + k) ≃ (Fin k ⊕ Fin n) :=
  (finCongr (Nat.add_comm n k)).trans (finSumFinEquiv (m := k) (n := n)).symm

/-- The ambient nested-Fubini ring equivalence
`MvPowerSeries (Fin (n+k)) A ≃+* MvPowerSeries (Fin k) (MvPowerSeries (Fin n) A)`
(reindex + `sumAlgEquiv`). -/
noncomputable def nestedAmbientEquiv (n k : ℕ) :
    MvPowerSeries (Fin (n + k)) A ≃+* MvPowerSeries (Fin k) (MvPowerSeries (Fin n) A) :=
  ((MvPowerSeries.renameEquiv A (nestedIndexEquiv n k)).trans
    (MvPowerSeries.sumAlgEquiv (Fin k) (Fin n) A)).toRingEquiv

omit [TopologicalSpace A] [NonarchimedeanRing A] [IsTopologicalRing A] [IsTateRing A] in
/-- Coefficient formula for the ambient nested equivalence: the `(ν, μ)` nested
coefficient is the joint coefficient at the reindexed `sumElim`. -/
theorem coeff_coeff_nestedAmbientEquiv (n k : ℕ) (g : MvPowerSeries (Fin (n + k)) A)
    (ν : Fin k →₀ ℕ) (μ : Fin n →₀ ℕ) :
    MvPowerSeries.coeff μ (MvPowerSeries.coeff ν (nestedAmbientEquiv n k g)) =
      MvPowerSeries.coeff
        (Finsupp.embDomain (nestedIndexEquiv n k).symm.toEmbedding (ν.sumElim μ)) g := by
  show MvPowerSeries.coeff μ (MvPowerSeries.coeff ν
    (MvPowerSeries.sumToIter _ _ _ (MvPowerSeries.rename (⇑(nestedIndexEquiv n k)) g))) = _
  rw [MvPowerSeries.coeff_sumToIter]
  conv_lhs => rw [← GraphKoszul.embDomain_symm_embDomain (nestedIndexEquiv n k) (ν.sumElim μ)]
  exact MvPowerSeries.coeff_embDomain_rename (nestedIndexEquiv n k).toEmbedding g _

theorem isRestricted_coeff_nestedAmbientEquiv (n k : ℕ)
    {g : MvPowerSeries (Fin (n + k)) A} (hg : MvPowerSeries.IsRestricted g)
    (ν : Fin k →₀ ℕ) :
    MvPowerSeries.IsRestricted (MvPowerSeries.coeff ν (nestedAmbientEquiv n k g)) := by
  have hinj : Function.Injective (fun μ : Fin n →₀ ℕ =>
      Finsupp.embDomain (nestedIndexEquiv n k).symm.toEmbedding (ν.sumElim μ)) := by
    intro μ μ' h
    have h2 := Finsupp.embDomain_injective _ h
    ext j
    have := congrArg (fun s : (Fin k ⊕ Fin n) →₀ ℕ => s (Sum.inr j)) h2
    simpa using this
  exact (hg.comp hinj.tendsto_cofinite).congr
    (fun μ => (coeff_coeff_nestedAmbientEquiv n k g ν μ).symm)

/-- **T617 leg 2 (joint ⟹ outer null)**: the outer coefficient family of the nested
image of a jointly-restricted series tends to zero in the canonical mv-Tate topology
of `A⟨X₁,…,Xₙ⟩` (finite-exceptional-pair combinatorics against `mvTateAlgNhd`,
entering the pair via `mvTateAlgNhd_of_coeff_mem_principal`). -/
theorem tendsto_coeff_nestedAmbientEquiv (n k : ℕ)
    {g : MvPowerSeries (Fin (n + k)) A} (hg : MvPowerSeries.IsRestricted g) :
    letI := mvTateAlgebraTopology' (A := A) n
    Filter.Tendsto
      (fun ν : Fin k →₀ ℕ =>
        (⟨MvPowerSeries.coeff ν (nestedAmbientEquiv n k g),
          isRestricted_coeff_nestedAmbientEquiv n k hg ν⟩ :
          ↥(restrictedMvPowerSeriesSubring n A)))
      Filter.cofinite (nhds 0) := by
  letI := mvTateAlgebraTopology' (A := A) n
  set P := (IsTateRing.principalPair A).toPairOfDefinition with hP
  refine (mvTateAlgBasis' (A := A) n).hasBasis_nhds_zero.tendsto_right_iff.mpr ?_
  intro j _
  have hU : (Subtype.val '' ((P.I ^ j : Ideal P.A₀) : Set P.A₀)) ∈ nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  have hfin : ((fun l : Fin (n + k) →₀ ℕ => MvPowerSeries.coeff l g) ⁻¹'
      (Subtype.val '' ((P.I ^ j : Ideal P.A₀) : Set P.A₀)))ᶜ.Finite := by
    have h1 := hg hU
    rwa [Filter.mem_map, Filter.mem_cofinite] at h1
  refine Filter.eventually_cofinite.mpr ((hfin.image (fun l =>
    Finsupp.comapDomain Sum.inl
      (Finsupp.embDomain (nestedIndexEquiv n k).toEmbedding l)
      Sum.inl_injective.injOn)).subset ?_)
  intro ν hν
  by_contra hν_im
  apply hν
  have hcoeffU : ∀ μ : Fin n →₀ ℕ,
      MvPowerSeries.coeff μ (MvPowerSeries.coeff ν (nestedAmbientEquiv n k g)) ∈
        Subtype.val '' ((P.I ^ j : Ideal P.A₀) : Set P.A₀) := by
    intro μ
    by_contra hbad
    refine hν_im ⟨Finsupp.embDomain (nestedIndexEquiv n k).symm.toEmbedding (ν.sumElim μ),
      ?_, ?_⟩
    · simpa [coeff_coeff_nestedAmbientEquiv n k g ν μ] using hbad
    · simp [GraphKoszul.embDomain_symm_embDomain,
        Finsupp.comapDomain_inl_sumElim]
  refine mvTateAlgNhd_of_coeff_mem_principal n P j (IsTateRing.principalPair A).π
    (IsTateRing.principalPair A).I_eq_span (IsTateRing.principalPair A).π_isUnit
    (fun s => ?_) (fun l => ?_)
  · obtain ⟨b, -, hb⟩ := hcoeffU s
    exact hb ▸ b.2
  · obtain ⟨b, hbI, hb⟩ := hcoeffU l
    exact ⟨b, hbI, hb⟩

/-- **T617 leg 3 (nested ⟹ joint)**: a series over `A⟨X₁,…,Xₙ⟩` whose outer family
is restricted (w.r.t. the canonical topology) flattens to a jointly-restricted
series over `A` (cofinitely many outer indices land entirely in any basic
neighbourhood via `mvTateAlgNhd_coeff_mem`; the finitely many exceptional outer
slices are each inner-restricted). -/
theorem isRestricted_symm_nestedAmbientEquiv (n k : ℕ)
    (f : MvPowerSeries (Fin k) ↥(restrictedMvPowerSeriesSubring n A))
    (hf : letI := mvTateAlgebraTopology' (A := A) n
      Filter.Tendsto (fun ν : Fin k →₀ ℕ => MvPowerSeries.coeff ν f)
        Filter.cofinite (nhds 0)) :
    MvPowerSeries.IsRestricted ((nestedAmbientEquiv n k).symm
      (MvPowerSeries.map (restrictedMvPowerSeriesSubring n A).subtype f)) := by
  sorry

/-- **T617: the topological nested Fubini** — the `k`-variable restricted power
series over the Tate extension `A⟨X₁,…,Xₙ⟩` (with its canonical topology) are the
`(n+k)`-variable restricted power series over `A`. The standard
`A⟨X⟩⟨Y⟩ = A⟨X,Y⟩` (Wedhorn §5.3 vocabulary; the normed-field instance is
`restrictedFubini`), via `MvPowerSeries.sumAlgEquiv` + the `finSumFinEquiv`
reindex, with the two restrictedness transports proved by the
finite-exceptional-pair combinatorics. -/
noncomputable def restrictedNestedEquiv (n k : ℕ) :
    letI := mvTateAlgebraTopology' (A := A) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := A) n
    haveI := mvTate_nonarchimedean (A := A) n
    ↥(restrictedMvPowerSeriesSubring k ↥(restrictedMvPowerSeriesSubring n A)) ≃+*
      ↥(restrictedMvPowerSeriesSubring (n + k) A) := by
  sorry

end NestedFubini

/-- **B-L3 (generic): the Tate extension of a strongly noetherian Tate ring is
strongly noetherian.** Content: restricted Fubini
`A⟨X₁,…,X_{n+m}⟩ ≅ (A⟨X₁,…,Xₙ⟩)⟨T₁,…,Tₘ⟩` flattens the extension's own Tate
algebras back into those of `A` (Wedhorn Example 6.38 vocabulary; the FJP-side
Fubini legs are `FJP/RestrictedFubini.lean`). -/
theorem mvTate_isStronglyNoetherian {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTateRing A] [IsStronglyNoetherian A] (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := A) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := A) n
    haveI := mvTate_nonarchimedean (A := A) n
    IsStronglyNoetherian ↥(restrictedMvPowerSeriesSubring n A) := by
  sorry

/-- **B-L6 (uniformity bridge, JetA instance)**: the Tate extension of `𝓐` is
complete for the right uniformity of its canonical topology. -/
theorem finiteJet_tateExt_completeSpace (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA F) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA F) n
    @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA F))
      (IsTopologicalAddGroup.rightUniformSpace _) := by
  exact mvTate_completeSpace (A := JetA F) n inferInstance

/-- **B headline: `𝓐` is strongly sheafy** — every finite Tate extension of the
finite-jet pinching algebra is sheafy for every valid ring of integral elements
(reviewer §5.1; [WP-paper] §5–§6 with auxiliary variables). -/
theorem finiteJet_tateExt_isSheafyComplete (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA F) n
    haveI := mvTate_isTateRing (A := JetA F) n
    haveI := mvTate_t2Space (A := JetA F) n
    haveI := mvTate_nonarchimedean (A := JetA F) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA F) n
    haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA F))
      (IsTopologicalAddGroup.rightUniformSpace _) := finiteJet_tateExt_completeSpace F n
    IsSheafyComplete ↥(restrictedMvPowerSeriesSubring n (JetA F)) := by
  sorry

end FiniteJet
