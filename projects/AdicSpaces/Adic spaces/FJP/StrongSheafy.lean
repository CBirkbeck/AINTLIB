/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetSheafyEndpoints
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

/-- **B-L3 (generic): the Tate extension of a strongly noetherian Tate ring is
strongly noetherian.** Content: restricted Fubini
`A⟨X₁,…,X_{n+m}⟩ ≅ (A⟨X₁,…,Xₙ⟩)⟨T₁,…,Tₘ⟩` flattens the extension's own Tate
algebras back into those of `A` (Wedhorn Example 6.38 vocabulary; the FJP-side
Fubini legs are `FJP/RestrictedFubini.lean`). -/
theorem mvTate_isStronglyNoetherian {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A] (n : ℕ) :
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
  sorry

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
