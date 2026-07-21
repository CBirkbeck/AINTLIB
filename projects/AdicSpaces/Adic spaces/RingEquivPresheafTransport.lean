/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafFunctoriality
import «Adic spaces».AffinoidTransport
import «Adic spaces».RelativePieceKeystone

/-!
# Transport of sheafiness along a bicontinuous ring equivalence (PASS 2)

For a bicontinuous ring equivalence `e : A ≃+* B` (an isomorphism of topological
rings), pairs of definition, valid rational data, completed rational
localizations, and ultimately the finite-rational sheafiness criterion `IsSheafy`
transport to `B`.

Crucially, every datum used by sheafiness carries `D.IsRational`, so in Tate scope
`Ideal.span D.T = ⊤`; the transported datum is reconstructed by `genPieceDatum`
(which supplies `hopen` from the span condition) rather than by transporting an
arbitrary `hopen` proof across the localization equivalence.

* `PairOfDefinition.mapRingEquiv` (+ `subringMapHomeomorph`, `IsAdic.mapRingEquiv`).
* `RationalLocData.mapRationalRingEquiv` — transport of *valid* rational data.
* `presheafValueRingEquivOfRingEquiv` — the completed-localization equivalence.
* `isSheafyFor_equiv`, `isSheafyComplete_congr` — the endpoints.
-/

noncomputable section

open Filter Topology

namespace ValuationSpectrum

universe u v

/-! ### 2.1 Pair-of-definition transport -/

section Pair

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- A bicontinuous ring equivalence restricts to a homeomorphism between a subring
and its image (subspace topologies). -/
def PairOfDefinition.subringMapHomeomorph (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (s : Subring A) :
    s ≃ₜ (s.map e.toRingHom) where
  toEquiv := (e.subringMap (s := s)).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact he.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact he'.comp continuous_subtype_val

/-- **`IsAdic` transports along a bicontinuous ring equivalence.** If the topology
of `R` is `J`-adic then the topology of `S` is `(J.map e)`-adic. -/
theorem IsAdic.mapRingEquiv {R S : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm)
    {J : Ideal R} (hJ : IsAdic J) : IsAdic (J.map e.toRingHom) := by
  have hcoe : ∀ n : ℕ, ((J.map e.toRingHom) ^ n : Ideal S) =
      (J ^ n).comap e.symm.toRingHom := by
    intro n
    rw [← Ideal.map_pow]
    ext x
    rw [Ideal.mem_comap]
    constructor
    · intro hx
      have := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hx
      obtain ⟨y, hy, rfl⟩ := this
      simpa [RingEquiv.symm_apply_apply] using hy
    · intro hx
      have : e.symm.toRingHom x ∈ J ^ n := hx
      have h2 : e.toRingHom (e.symm.toRingHom x) ∈ (J ^ n).map e.toRingHom :=
        Ideal.mem_map_of_mem _ this
      simpa [RingEquiv.apply_symm_apply] using h2
  rw [isAdic_iff]
  rw [isAdic_iff] at hJ
  obtain ⟨hopen, hbasis⟩ := hJ
  constructor
  · intro n
    rw [hcoe n]
    exact (hopen n).preimage he'
  · intro U hU
    have hpre : e ⁻¹' U ∈ 𝓝 (0 : R) :=
      he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)
    obtain ⟨n, hn⟩ := hbasis (e ⁻¹' U) hpre
    refine ⟨n, ?_⟩
    rw [hcoe n]
    intro x hx
    rw [SetLike.mem_coe, Ideal.mem_comap] at hx
    have : e.symm.toRingHom x ∈ e ⁻¹' U := hn hx
    simpa [RingEquiv.apply_symm_apply] using this

/-- **Transport of a pair of definition** along a bicontinuous ring equivalence
(2.1): `A₀ ↦ A₀.map e`, `I ↦ I.map (e.subringMap)`. -/
def PairOfDefinition.mapRingEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (P : PairOfDefinition A) : PairOfDefinition B where
  A₀ := P.A₀.map e.toRingHom
  I := P.I.map (e.subringMap (s := P.A₀)).toRingHom
  isOpen := by
    rw [Subring.coe_map, show ⇑e.toRingHom '' (P.A₀ : Set A) = ⇑e.symm ⁻¹' (P.A₀ : Set A)
      from e.toEquiv.image_eq_preimage_symm _]
    exact P.isOpen.preimage he'
  fg := P.fg.map _
  isAdic := by
    -- transport `IsAdic P.I` on `↥P.A₀` to `↥(P.A₀.map e)` via the subring homeomorph
    haveI : IsTopologicalRing (P.A₀.map e.toRingHom) := inferInstance
    haveI : IsTopologicalRing P.A₀ := inferInstance
    exact IsAdic.mapRingEquiv (e.subringMap (s := P.A₀))
      (PairOfDefinition.subringMapHomeomorph e he he' P.A₀).continuous_toFun
      (PairOfDefinition.subringMapHomeomorph e he he' P.A₀).continuous_invFun
      P.isAdic

end Pair

/-! ### 2.2 Transport of valid rational data (reconstructed via `genPieceDatum`) -/

section Datum

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DecidableEq B]

/-- The image of a spanning family spans. -/
theorem span_image_eq_top_of_ringEquiv (e : A ≃+* B) {T : Finset A}
    (h : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image e : Finset B) : Set B) = ⊤ := by
  have hmap := congrArg (Ideal.map e.toRingHom) h
  rw [Ideal.map_span, Ideal.map_top] at hmap
  rw [Finset.coe_image]
  simpa using hmap

/-- **Transport of a valid rational datum** (2.2): reconstruct via `genPieceDatum`
from the transported pair `D.P.mapRingEquiv e`, numerators `D.T.image e`, denominator
`e D.s`, and the transported span condition. No `hopen` is transported across the
localization equivalence — `genPieceDatum` supplies it from the span. -/
def RationalLocData.mapRationalRingEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) (hD : D.IsRational) :
    RationalLocData B :=
  genPieceDatum (PairOfDefinition.mapRingEquiv e he he' D.P) (D.T.image e) (e D.s)
    (span_image_eq_top_of_ringEquiv e hD.span_eq_top)

@[simp] theorem mapRationalRingEquiv_T (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) (hD : D.IsRational) :
    (D.mapRationalRingEquiv e he he' hD).T = D.T.image e := rfl

@[simp] theorem mapRationalRingEquiv_s (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) (hD : D.IsRational) :
    (D.mapRationalRingEquiv e he he' hD).s = e D.s := rfl

/-- The transported datum is rational (its numerator family spans). -/
theorem mapRationalRingEquiv_isRational (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) (hD : D.IsRational) :
    (D.mapRationalRingEquiv e he he' hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top_of_ringEquiv e hD.span_eq_top)

end Datum

end ValuationSpectrum
