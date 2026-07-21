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

/-! ### 2.4 The completed rational-localization equivalence -/

section PresheafValue

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DecidableEq B] [DecidableEq A]
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
  (D : RationalLocData A) (hD : D.IsRational)

/-- The forward denominator obligation. -/
private theorem hs_fwd : (D.mapRationalRingEquiv e he he' hD).s = e.toRingHom D.s := by
  rw [mapRationalRingEquiv_s]; rfl

/-- The backward denominator obligation. -/
private theorem hs_bwd : D.s = e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD).s := by
  rw [mapRationalRingEquiv_s]; exact (e.symm_apply_apply D.s).symm

/-- The forward numerator-containment obligation. -/
private theorem hT_fwd :
    ∀ t ∈ D.T, e.toRingHom t ∈ (D.mapRationalRingEquiv e he he' hD).T := by
  intro t ht
  rw [mapRationalRingEquiv_T]
  exact Finset.mem_image_of_mem _ ht

/-- The backward numerator-containment obligation. -/
private theorem hT_bwd :
    ∀ t ∈ (D.mapRationalRingEquiv e he he' hD).T, e.symm.toRingHom t ∈ D.T := by
  intro t ht
  rw [mapRationalRingEquiv_T] at ht
  obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
  rwa [show e.symm.toRingHom (e t₀) = t₀ from e.symm_apply_apply t₀]

/-- The forward completed covariant map `𝒪(D) →+* 𝒪(D')`. -/
private noncomputable def pvFwd :
    presheafValue D →+* presheafValue (D.mapRationalRingEquiv e he he' hD) :=
  presheafValueMapOfHom e.toRingHom he D (D.mapRationalRingEquiv e he he' hD)
    (hs_fwd e he he' D hD) (hT_fwd e he he' D hD)

/-- The backward completed covariant map `𝒪(D') →+* 𝒪(D)`. -/
private noncomputable def pvBwd :
    presheafValue (D.mapRationalRingEquiv e he he' hD) →+* presheafValue D :=
  presheafValueMapOfHom e.symm.toRingHom he' (D.mapRationalRingEquiv e he he' hD) D
    (hs_bwd e he he' D hD) (hT_bwd e he he' D hD)

private theorem pvFwd_continuous : Continuous (pvFwd e he he' D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

private theorem pvBwd_continuous : Continuous (pvBwd e he he' D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

/-- The forward map on the localization image. -/
private theorem pvFwd_coe (l : Localization.Away D.s) :
    pvFwd e he he' D hD (D.coeRingHom l) =
      (D.mapRationalRingEquiv e he he' hD).coeRingHom
        (locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD)
          (hs_fwd e he he' D hD) l) :=
  presheafValueMapOfHom_coe e.toRingHom he D (D.mapRationalRingEquiv e he he' hD)
    (hs_fwd e he he' D hD) (hT_fwd e he he' D hD) l

/-- The backward map on the localization image. -/
private theorem pvBwd_coe (l : Localization.Away (D.mapRationalRingEquiv e he he' hD).s) :
    pvBwd e he he' D hD ((D.mapRationalRingEquiv e he he' hD).coeRingHom l) =
      D.coeRingHom (locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D
        (hs_bwd e he he' D hD) l) :=
  presheafValueMapOfHom_coe e.symm.toRingHom he' (D.mapRationalRingEquiv e he he' hD) D
    (hs_bwd e he he' D hD) (hT_bwd e he he' D hD) l

/-- The localization-level composite (forward then backward) is the identity. -/
private theorem locMap_roundtrip (l : Localization.Away D.s) :
    locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D
        (hs_bwd e he he' D hD)
        (locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD)
          (hs_fwd e he he' D hD) l) = l := by
  have hid : (locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D
        (hs_bwd e he he' D hD)).comp
      (locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD)
        (hs_fwd e he he' D hD)) = RingHom.id (Localization.Away D.s) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, RingHom.id_comp, locMapOfHom_algebraMap]
    rw [show e.symm.toRingHom (e.toRingHom a) = a from e.symm_apply_apply a]
  exact DFunLike.congr_fun hid l

/-- The localization-level composite (backward then forward) is the identity. -/
private theorem locMap_roundtrip_symm
    (l : Localization.Away (D.mapRationalRingEquiv e he he' hD).s) :
    locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD) (hs_fwd e he he' D hD)
        (locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D
          (hs_bwd e he he' D hD) l) = l := by
  have hid : (locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD)
        (hs_fwd e he he' D hD)).comp
      (locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D
        (hs_bwd e he he' D hD)) =
      RingHom.id (Localization.Away (D.mapRationalRingEquiv e he he' hD).s) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers
      (D.mapRationalRingEquiv e he he' hD).s) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, RingHom.id_comp, locMapOfHom_algebraMap]
    rw [show e.toRingHom (e.symm.toRingHom a) = a from e.apply_symm_apply a]
  exact DFunLike.congr_fun hid l

/-- **The completed rational-localization equivalence** (2.4): for a bicontinuous ring
equivalence `e` and a valid rational datum `D`, the completed localizations are
canonically bicontinuously isomorphic. -/
noncomputable def presheafValueRingEquivOfRingEquiv :
    presheafValue D ≃+* presheafValue (D.mapRationalRingEquiv e he he' hD) where
  toFun := pvFwd e he he' D hD
  invFun := pvBwd e he he' D hD
  left_inv x := by
    letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
    have hdense : DenseRange (⇑(D.coeRingHom)) :=
      @UniformSpace.Completion.denseRange_coe _ D.uniformSpace
    have hfun : ⇑(pvBwd e he he' D hD) ∘ ⇑(pvFwd e he he' D hD) =
        (id : presheafValue D → presheafValue D) := by
      refine hdense.equalizer ((pvBwd_continuous e he he' D hD).comp
        (pvFwd_continuous e he he' D hD)) continuous_id ?_
      funext l
      show pvBwd e he he' D hD (pvFwd e he he' D hD (D.coeRingHom l)) = D.coeRingHom l
      rw [pvFwd_coe, pvBwd_coe, locMap_roundtrip]
    exact congr_fun hfun x
  right_inv y := by
    letI : UniformSpace (Localization.Away (D.mapRationalRingEquiv e he he' hD).s) :=
      (D.mapRationalRingEquiv e he he' hD).uniformSpace
    have hdense : DenseRange (⇑((D.mapRationalRingEquiv e he he' hD).coeRingHom)) :=
      @UniformSpace.Completion.denseRange_coe _
        (D.mapRationalRingEquiv e he he' hD).uniformSpace
    have hfun : ⇑(pvFwd e he he' D hD) ∘ ⇑(pvBwd e he he' D hD) =
        (id : presheafValue (D.mapRationalRingEquiv e he he' hD) →
          presheafValue (D.mapRationalRingEquiv e he he' hD)) := by
      refine hdense.equalizer ((pvFwd_continuous e he he' D hD).comp
        (pvBwd_continuous e he he' D hD)) continuous_id ?_
      funext l
      show pvFwd e he he' D hD (pvBwd e he he' D hD
        ((D.mapRationalRingEquiv e he he' hD).coeRingHom l)) =
        (D.mapRationalRingEquiv e he he' hD).coeRingHom l
      rw [pvBwd_coe, pvFwd_coe, locMap_roundtrip_symm]
    exact congr_fun hfun y
  map_mul' := map_mul _
  map_add' := map_add _

theorem presheafValueRingEquivOfRingEquiv_continuous :
    Continuous (presheafValueRingEquivOfRingEquiv e he he' D hD) :=
  pvFwd_continuous e he he' D hD

theorem presheafValueRingEquivOfRingEquiv_symm_continuous :
    Continuous (presheafValueRingEquivOfRingEquiv e he he' D hD).symm :=
  pvBwd_continuous e he he' D hD

/-- The equivalence intertwines the canonical maps from `A`/`B`. -/
theorem presheafValueRingEquivOfRingEquiv_canonicalMap (a : A) :
    presheafValueRingEquivOfRingEquiv e he he' D hD (D.canonicalMap a) =
      (D.mapRationalRingEquiv e he he' hD).canonicalMap (e a) := by
  show pvFwd e he he' D hD (D.canonicalMap a) = _
  rw [show D.canonicalMap a = D.coeRingHom (algebraMap A (Localization.Away D.s) a)
      from rfl, pvFwd_coe, locMapOfHom_algebraMap]
  rfl

end PresheafValue

end ValuationSpectrum
