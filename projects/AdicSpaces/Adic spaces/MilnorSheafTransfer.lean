/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafFunctoriality
import «Adic spaces».StructureSheaf

/-!
# Abstract Milnor descent for sheafiness (campaign B, AG1.d skeleton)

[WP-paper] lem:sheaf-transfer (l.576–583), verbatim hypothesis: "Suppose that for
every rational domain U ⊂ X_R the section rings satisfy a natural strict exact
sequence 0 → 𝒪_R(U) → 𝒪_B(U_B) ⊕ 𝒪_C(U_C) → 𝒪_D(U_D) → 0. If the Huber pairs
associated with B, C, D are sheafy as complete topological rings, then the Huber
pair associated with R is sheafy as a complete topological ring."

The abstract criterion (reviewer §4.1's "strict Milnor descent") over the generic
value-map machinery of `PresheafFunctoriality.lean`. The bundle `MilnorSquareData`
carries the datum-level pushes explicitly (there is no canonical pushed-datum
constructor in the core; the concrete instantiations — `pushDatumB` etc. in
`FiniteJetFunctoriality.lean`, and their `⟨V⟩`-extensions — supply them), together
with the exactness / strictness / naturality facts the transfer chase consumes.
Instantiations planned: the finite-jet square (regression: re-derive
`isSheafy_JetA`) and the `⟨V₁,…,Vₙ⟩`-extended square (campaign B headline).
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

open TopologicalRing

universe u

variable {R B C D : Type u}
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [PlusSubring R]
  [IsHuberRing R] [T2Space R] [NonarchimedeanRing R]
  [letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R; CompleteSpace R]
  [IsRingOfIntegralElements (R⁺)]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [PlusSubring B]
  [IsHuberRing B] [T2Space B] [NonarchimedeanRing B]
  [letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B; CompleteSpace B]
  [IsRingOfIntegralElements (B⁺)]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [PlusSubring C]
  [IsHuberRing C] [T2Space C] [NonarchimedeanRing C]
  [letI : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C; CompleteSpace C]
  [IsRingOfIntegralElements (C⁺)]
  [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [PlusSubring D]
  [IsHuberRing D] [T2Space D] [NonarchimedeanRing D]
  [letI : UniformSpace D := IsTopologicalAddGroup.rightUniformSpace D; CompleteSpace D]
  [IsRingOfIntegralElements (D⁺)]

/-- **The strict Milnor square-with-rows data** ([WP-paper] eq:sheaf-transfer-row,
per rational datum, natural under refinement). Carries the three structural homs,
per-datum pushes to each vertex with their side conditions, and the
exactness/strictness/naturality of
`0 → 𝒪_R(U) → 𝒪_B(U_B) ⊕ 𝒪_C(U_C) → 𝒪_D(U_D) → 0`. -/
structure MilnorSquareData
    (φB : R →+* B) (φC : R →+* C) (φD : R →+* D)
    (hφB : Continuous φB) (hφC : Continuous φC) (hφD : Continuous φD) where
  /-- The pushed datum at each vertex. -/
  pushB : RationalLocData R → RationalLocData B
  pushC : RationalLocData R → RationalLocData C
  pushD : RationalLocData R → RationalLocData D
  pushB_s : ∀ U, (pushB U).s = φB U.s
  pushC_s : ∀ U, (pushC U).s = φC U.s
  pushD_s : ∀ U, (pushD U).s = φD U.s
  pushB_T : ∀ U, ∀ t ∈ U.T, φB t ∈ (pushB U).T
  pushC_T : ∀ U, ∀ t ∈ U.T, φC t ∈ (pushC U).T
  pushD_T : ∀ U, ∀ t ∈ U.T, φD t ∈ (pushD U).T
  /-- Pushes of rational data are rational. -/
  pushB_isRational : ∀ U, U.IsRational → (pushB U).IsRational
  pushC_isRational : ∀ U, U.IsRational → (pushC U).IsRational
  pushD_isRational : ∀ U, U.IsRational → (pushD U).IsRational
  /-- The `D`-vertex maps of the two legs, from the pushed `B`/`C` data. -/
  legB : B →+* D
  legC : C →+* D
  hlegB : Continuous legB
  hlegC : Continuous legC
  legB_s : ∀ U, (pushD U).s = legB (pushB U).s
  legC_s : ∀ U, (pushD U).s = legC (pushC U).s
  legB_T : ∀ U, ∀ t ∈ (pushB U).T, legB t ∈ (pushD U).T
  legC_T : ∀ U, ∀ t ∈ (pushC U).T, legC t ∈ (pushD U).T
  /-- Row exactness at the left: the pair of value pushes is jointly injective. -/
  row_injective : ∀ (U : RationalLocData R), U.IsRational →
    ∀ x y : presheafValue U,
      presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U) (pushB_T U) x =
        presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U) (pushB_T U) y →
      presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U) (pushC_T U) x =
        presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U) (pushC_T U) y →
      x = y
  /-- Row exactness in the middle: a `D`-matching pair comes from the base. -/
  row_glue : ∀ (U : RationalLocData R), U.IsRational →
    ∀ (b : presheafValue (pushB U)) (c : presheafValue (pushC U)),
      presheafValueMapOfHom legB hlegB (pushB U) (pushD U) (legB_s U) (legB_T U) b =
        presheafValueMapOfHom legC hlegC (pushC U) (pushD U) (legC_s U) (legC_T U) c →
      ∃ x : presheafValue U,
        presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U) (pushB_T U) x = b ∧
        presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U) (pushC_T U) x = c
  /-- Strictness at the left: the base embeds topologically in the product. -/
  row_embedding : ∀ (U : RationalLocData R), U.IsRational →
    Topology.IsEmbedding (fun x : presheafValue U =>
      (presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U) (pushB_T U) x,
       presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U) (pushC_T U) x))
  /-- Naturality under refinement: pushes commute with restriction maps, and the
  pushed datum of a refinement refines the pushed datum. -/
  pushB_mono : ∀ (U U' : RationalLocData R),
    rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s →
    rationalOpen (pushB U').T (pushB U').s ⊆ rationalOpen (pushB U).T (pushB U).s
  pushC_mono : ∀ (U U' : RationalLocData R),
    rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s →
    rationalOpen (pushC U').T (pushC U').s ⊆ rationalOpen (pushC U).T (pushC U).s
  push_natural_B : ∀ (U U' : RationalLocData R)
    (h : rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s) (x : presheafValue U),
    presheafValueMapOfHom φB hφB U' (pushB U') (pushB_s U') (pushB_T U')
        (restrictionMap U U' h x) =
      restrictionMap (pushB U) (pushB U') (pushB_mono U U' h)
        (presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U) (pushB_T U) x)
  push_natural_C : ∀ (U U' : RationalLocData R)
    (h : rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s) (x : presheafValue U),
    presheafValueMapOfHom φC hφC U' (pushC U') (pushC_s U') (pushC_T U')
        (restrictionMap U U' h x) =
      restrictionMap (pushC U) (pushC U') (pushC_mono U U' h)
        (presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U) (pushC_T U) x)

/-- **Abstract Milnor descent for sheafiness** ([WP-paper] lem:sheaf-transfer;
reviewer §4.1): if a strict Milnor square-with-rows exists over `R` and the three
vertices `B`, `C`, `D` are sheafy, then `R` is sheafy. -/
theorem isSheafy_of_milnorSquare
    (φB : R →+* B) (φC : R →+* C) (φD : R →+* D)
    (hφB : Continuous φB) (hφC : Continuous φC) (hφD : Continuous φD)
    (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    (hB : IsSheafy B) (hC : IsSheafy C) (hD : IsSheafy D) :
    IsSheafy R := by
  sorry

end ValuationSpectrum
