/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicMorphisms
import «Adic spaces».StructurePresheafBundled

/-!
# Adic morphisms of adic spaces (Wedhorn Definition 8.38, Prop 8.39, Cor 8.40)

The space-level part of `AdicMorphisms.lean`, split off (WO1, 2026-07-20) because it
consumes `AdicSpace`/`AffinoidAdicSpace`, which now live downstream in
`StructurePresheafBundled.lean` (their sheafiness field is the genuine Definition
8.21 condition). Ring-level adicness (`IsAdicHom` etc.) stays in `AdicMorphisms.lean`.
-/

noncomputable section

namespace ValuationSpectrum

section AdicMorphismDef

universe u

open TopologicalSpace

/-- An open affinoid neighborhood datum for a point in an adic space: an open set `U`,
a point membership proof, an affinoid adic space `Y`, and a homeomorphism
`U ≃ₜ Spa(Y.Ring)`. This packages the local chart data for Definition 8.38. -/
structure AffinoidNeighborhood (X : AdicSpace.{u}) (x : X.carrier) where
  /-- The open set containing `x`. -/
  U : Opens X.carrier
  /-- Proof that `x ∈ U`. -/
  mem : x ∈ U
  /-- The affinoid adic space that `U` is homeomorphic to. -/
  aff : AffinoidAdicSpace.{u}
  /-- The homeomorphism `U ≃ₜ Spa(aff.Ring)`. -/
  homeo : ↥U ≃ₜ aff.toTopCat

/-- **Definition 8.38 of Wedhorn.** A continuous map `f : X.carrier → Y.carrier`
between the carriers of adic spaces is *adic* if for every `x ∈ X`, there exist
open affinoid neighborhoods `U ∋ x` in `X` and `V ∋ f(x)` in `Y` with
`f(U) ⊆ V`, such that the induced ring homomorphism
`𝒪_Y(V) → 𝒪_X(U)` is adic in the sense of Definition 6.23.

In the formal definition, we ask for affinoid neighborhood data (homeomorphisms to
affinoid spectra) and require the ring homomorphism between the witnessing affinoid
rings to be adic. The requirement `f(U) ⊆ V` is encoded by requiring that
`f` maps points of `U` into `V`.

The ring hom goes from the target ring to the source ring (`NY.aff.Ring →+* NX.aff.Ring`),
matching the contravariant nature of `Spa(φ) : Spa(B) → Spa(A)` for `φ : A →+* B`.
We require `IsHuberRing` instances on the affinoid rings since `IsAdicHom` is defined
for Huber ring homomorphisms (Definition 6.23 of Wedhorn). -/
def IsAdicMorphism (X Y : AdicSpace.{u}) (f : C(X.carrier, Y.carrier)) : Prop :=
  ∀ (x : X.carrier),
    ∃ (NX : AffinoidNeighborhood X x)
      (NY : AffinoidNeighborhood Y (f x))
      (_ : ∀ (p : ↥NX.U), f p.val ∈ NY.U)
      (_ : IsHuberRing NX.aff.Ring) (_ : IsHuberRing NY.aff.Ring)
      (φ : NY.aff.Ring →+* NX.aff.Ring),
      IsAdicHom φ

end AdicMorphismDef

section Prop839

/-- **Proposition 8.39(2) of Wedhorn (affinoid case).** Any continuous ring
homomorphism between Huber rings sends non-analytic points to non-analytic
points. This is the affinoid avatar of the statement that any morphism of
adic spaces preserves non-analytic points.

For the full adic space statement, one reduces to the affinoid case by
restricting to an affinoid chart and applying this result (Remark 8.37(2)).

The proof is `nonAnalytic_comap_of_continuous`, restated here for clarity. -/
theorem morphism_preserves_nonAnalytic_affinoid {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) : ¬IsAnalytic (comap φ v) :=
  nonAnalytic_comap_of_continuous hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, forward direction).**
An adic ring homomorphism `φ : A →+* B` between Huber rings induces a map
`Spa(φ)` that preserves analytic points.

This is `analytic_comap_of_isAdicHom` (Lemma 7.46(1)), restated in the
form needed for Proposition 8.39. -/
theorem isAdicHom_preserves_analytic {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B] {φ : A →+* B} (hφ : IsAdicHom φ) :
    ∀ (v : Spv B), IsAnalytic v → IsAnalytic (comap φ v) :=
  fun _ hv ↦ analytic_comap_of_isAdicHom hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, reverse direction).**
If `B` is complete and `Spa(φ)` preserves analytic points, then `φ` is adic.

This is `isAdicHom_of_complete_and_analytic_preserved` (Lemma 7.46(2)),
restated for the iff form.

**Status:** The reverse direction requires Lemma 7.45; see `Lemma745.lean`. -/
theorem isAdicHom_of_preserves_analytic_complete {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B] [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (h_analytic : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) : IsAdicHom φ :=
  isAdicHom_of_complete_and_analytic_preserved hφ hAB h_analytic PB hBplus_le_B₀

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, iff version).** A continuous
ring homomorphism `φ : A →+* B` between Huber rings (with `B` complete) is adic
if and only if the induced map `Spa(φ) : Spv B → Spv A` preserves analytic points
on `Spa(B, B⁺)`.

This combines the forward direction (`isAdicHom_preserves_analytic`, Lemma 7.46(1))
with the reverse direction (`isAdicHom_of_preserves_analytic_complete`, Lemma 7.46(2)).

The full adic space version (Proposition 8.39(1) of Wedhorn) states that a morphism
`f : X → Y` of adic spaces is adic iff `f` maps analytic points of `X` to analytic
points of `Y`. The reduction from the adic space level to the affinoid level uses
Remark 8.37(2) of Wedhorn: it suffices to check the adic property on affinoid charts.
Formalizing that reduction requires connecting the abstract `IsAdicMorphism` definition
(which asks for *some* witnessing affinoid charts) to the pointwise analytic-preservation
property, which is not yet available.

**Status:** Sorry; the forward direction is proved, but the reverse direction
inherits sorries from `isAdicHom_of_complete_and_analytic_preserved` (Lemma 7.46(2)):
1. `exists_pairOfDefinition_le_subring` (Lemma 6.5) -- `IsAdic` property.
2. `exists_nonOpen_prime_of_B_from_B₀_prime` -- prime extension disjointness. -/
theorem isAdicHom_iff_preserves_analytic {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B] [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) : IsAdicHom φ ↔
    (∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v)) := by
  constructor
  · intro hadic v _ hv
    exact analytic_comap_of_isAdicHom hadic hv
  · exact fun h ↦
      isAdicHom_of_complete_and_analytic_preserved hφ hAB h PB hBplus_le_B₀

end Prop839

section Cor840

/-- **Corollary 8.40 of Wedhorn.** Let `f : X → Y` be an adic morphism of adic
spaces. Then for *all* open affinoid subspaces `U ⊆ X` and `V ⊆ Y` with
`f(U) ⊆ V`, the induced ring homomorphism `𝒪_Y(V) → 𝒪_X(U)` is adic -- not
just the witnessing neighborhoods from Definition 8.38.

The proof reduces to Lemma 7.46(2) (`isAdicHom_of_complete_and_analytic_preserved`):
if `Spa(φ)` preserves analytic points and the target ring is complete, then `φ` is
adic. The analytic-preservation hypothesis `hφ_analytic` captures the consequence of
Proposition 8.39(1) at the chart level: the adic morphism `f` preserves analytic
points, and this transfers to `Spa(φ)` via the chart homeomorphisms.

The hypotheses that are stated explicitly (`hφ_analytic`, `hφ_cont`, `hAB`, `PB`,
`hBplus`) would be derivable from `hf` alone once the following infrastructure is
formalized:
1. **Proposition 8.36** (chart-independence of analyticity) connecting `f` to `Spa(φ)`.
2. **Presheaf morphism** infrastructure extracting `φ` from `f` on charts.
3. **Completeness** of affinoid rings (presheaf values are completions).

Following Wedhorn p. 86, the proof is: Prop 8.39(1) gives `f(U_a) ⊆ V_a`
(analytic-preservation), then Lemma 7.46(2) gives that `φ` is adic. -/
theorem IsAdicMorphism.ringHom_isAdic {X Y : AdicSpace}
    {f : C(X.carrier, Y.carrier)} (_hf : IsAdicMorphism X Y f) {x : X.carrier}
    (NX : AffinoidNeighborhood X x) (NY : AffinoidNeighborhood Y (f x))
    (_hfUV : ∀ (p : ↥NX.U), f p.val ∈ NY.U) [IsHuberRing NX.aff.Ring]
    [IsHuberRing NY.aff.Ring] (φ : NY.aff.Ring →+* NX.aff.Ring) (hφ_cont : Continuous φ)
    (hAB : NY.aff.Ring⁺ ≤ (NX.aff.Ring⁺).comap φ)
    (hφ_analytic : ∀ v ∈ Spa NX.aff.Ring NX.aff.Ring⁺,
      IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition NX.aff.Ring) [IsAdicComplete PB.I PB.A₀]
    (hBplus : (NX.aff.Ring⁺ : Set NX.aff.Ring) ⊆ PB.A₀) : IsAdicHom φ :=
  isAdicHom_of_complete_and_analytic_preserved hφ_cont hAB hφ_analytic PB hBplus

end Cor840

end ValuationSpectrum
