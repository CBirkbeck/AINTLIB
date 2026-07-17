/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetStrictLocalization
import «Adic spaces».FiniteJetUniformDomain
import «Adic spaces».FaithfulLocLift

/-!
# Functoriality layer: pushing rational data along the square, graph bridges, and
`HasLocLiftPowerBounded 𝓐`

Sources: [FJP] Lemma 1.1 (graph realization of rational localization — the universal
property), Lemma 4.6 (naturality), Lemma 5.1 (naturality on the rational basis: "For every
rational domain `U ⊂ X`, its inverse image `U_E = p_E⁻¹(U)` is the rational domain in `Y_E`
defined by the image of the same datum").

This file supplies what the survey identified as the missing covariant layer:

* pairs of definition for the four rings (unit balls with the pseudouniformizer ideal);
* `pushDatumB/C/D : RationalLocData 𝓐 → RationalLocData E` (image datum; `hopen` via the
  generic span-⊤/principal-pod argument);
* `presheafValueMap : 𝒪_𝓐(D) → 𝒪_E(D_E)` (localization functoriality + completion), and its
  naturality with `restrictionMap`;
* the **graph bridge** `𝒪_E(D) ≃+* P_E ⧸ I_E` ([FJP] Lemma 1.1 + (4.21)), topological in
  both directions — the identification of the project's completed localization with the
  Banach graph quotient, for `E = 𝓐` (closed ideal by Lemma 4.3) and the three vertices
  (closed by Lemma 4.2);
* pushed coverings, intersection data, and the Spa-point coverage transfer (via the
  project's contravariant `spaComap`);
* `HasLocLiftPowerBounded 𝓐`, derived **componentwise through the Milnor square** from the
  vertices' instances (the project discharger is noetherian-bound and 𝓐 is not noetherian).
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum StrictLoc

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

noncomputable section

open scoped Classical

/-! ### Pairs of definition -/

/-- The unit-ball pair of definition of 𝓐 (the generic `unitBallPod` at `tA`). -/
def podA : PairOfDefinition (JetA F) :=
  unitBallPod (tA F) (isUnit_tA F) (norm_tA_lt_one F) (norm_tA_pos F) (norm_tA_mul F)

def podB : PairOfDefinition (JetB F) :=
  unitBallPod (tB F) (isUnit_tB F) (by rw [norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tB]; exact norm_t_pos F) (norm_tB_mul F)

def podC : PairOfDefinition (JetC F) :=
  unitBallPod (tC F) (isUnit_tC F) (by rw [norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tC]; exact norm_t_pos F) (norm_tC_mul F)

def podD : PairOfDefinition (JetD F) :=
  unitBallPod (tD F) (isUnit_tD F) (by rw [norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tD]; exact norm_t_pos F) (norm_tD_mul F)

/-! ### Pushing rational localization data ([FJP] Lemma 5.1)

The `hopen` field for the pushed datum is the generic bounded-denominator statement for
span-⊤ data over a principal pair of definition in a Tate ring (risk item 3 of `plan.md`). -/

variable {F}

/-- Spans of finset images of spanning sets span (the `Ideal.map` argument). -/
theorem span_image_eq_top {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {T : Finset A} (h : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image φ : Finset B) : Set B) = ⊤ := by
  have hmap := congrArg (Ideal.map φ) h
  rw [Ideal.map_span, Ideal.map_top] at hmap
  rw [Finset.coe_image, ← hmap]

/-- Push a rational datum of 𝓐 to 𝓑 (image datum, [FJP] Lemma 5.1). Signature completion
(recorded): rationality of `D` is required to discharge `hopen` via the generic span-⊤
computation `genPiece_hopen`. -/
def pushDatumB (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    RationalLocData (JetB F) where
  P := podB F
  T := D.T.image (jB F)
  s := jB F D.s
  hopen := genPiece_hopen (podB F) (D.T.image (jB F)) (jB F D.s)
    (span_image_eq_top (jB F) hD.span_eq_top)

/-- Push a rational datum of 𝓐 to 𝓒. -/
def pushDatumC (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    RationalLocData (JetC F) where
  P := podC F
  T := D.T.image (iotaC F)
  s := iotaC F D.s
  hopen := genPiece_hopen (podC F) (D.T.image (iotaC F)) (iotaC F D.s)
    (span_image_eq_top (iotaC F) hD.span_eq_top)

/-- Push a rational datum of 𝓐 to 𝓓. -/
def pushDatumD (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    RationalLocData (JetD F) where
  P := podD F
  T := D.T.image ((rhoC F).comp (iotaC F))
  s := rhoC F (iotaC F D.s)
  hopen := genPiece_hopen (podD F) (D.T.image ((rhoC F).comp (iotaC F)))
    (rhoC F (iotaC F D.s))
    (span_image_eq_top ((rhoC F).comp (iotaC F)) hD.span_eq_top)

theorem pushDatumB_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumB D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top (jB F) hD.span_eq_top)

theorem pushDatumC_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumC D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top (iotaC F) hD.span_eq_top)

theorem pushDatumD_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumD D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top ((rhoC F).comp (iotaC F)) hD.span_eq_top)

/-! ### Covariant maps on presheaf values

Generic layer: for a continuous ring homomorphism `φ : R →+* S` and rational data
`D`/`D'` with `D'.s = φ D.s` and `φ(D.T) ⊆ D'.T`, the localization functor gives
`Localization.Away D.s →+* Localization.Away D'.s`; it is continuous for the
localization topologies by the universal property `locTopology_continuous_lift` (the
generators land in `locSubring D'`, hence are power-bounded — no Nullstellensatz input
needed, unlike the restriction maps); completing gives `𝒪(D) →+* 𝒪(D')`. -/

section CovariantPush

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- The localization-level covariant map of a pushed rational datum. -/
noncomputable def locMapOfHom (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) :
    Localization.Away D.s →+* Localization.Away D'.s :=
  IsLocalization.map (Localization.Away D'.s) φ
    (show Submonoid.powers D.s ≤ (Submonoid.powers D'.s).comap φ from
      Submonoid.powers_le.mpr (show φ D.s ∈ Submonoid.powers D'.s from
        ⟨1, by show D'.s ^ 1 = φ D.s; rw [pow_one, hs]⟩))

theorem locMapOfHom_algebraMap (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) (a : R) :
    locMapOfHom φ D D' hs (algebraMap R (Localization.Away D.s) a) =
      algebraMap S (Localization.Away D'.s) (φ a) := by
  unfold locMapOfHom
  rw [IsLocalization.map_eq]

theorem locMapOfHom_divByS (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) (t : R) :
    locMapOfHom φ D D' hs (divByS t D.s) = divByS (φ t) D'.s := by
  rw [divByS, divByS, locMapOfHom, IsLocalization.map_mk']
  exact congrArg _ (Subtype.ext hs.symm)

/-- Continuity of the localization-level covariant map (universal property of the
localization topology; the pushed generators are in `locSubring D'`, hence
power-bounded). -/
theorem locMapOfHom_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    @Continuous _ _ D.topology D'.topology (locMapOfHom φ D D' hs) := by
  letI := D'.topology
  haveI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  haveI : @NonarchimedeanRing _ _ D'.topology :=
    (locBasis D'.P D'.T D'.s D'.hopen).nonarchimedean
  have hf_alg : @Continuous _ _ _ D'.topology
      ((locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s))) := by
    have h_eq : (locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s)) =
        (algebraMap S (Localization.Away D'.s)).comp φ := by
      ext a; exact locMapOfHom_algebraMap φ D D' hs a
    rw [show ⇑((locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s)))
        = ⇑((algebraMap S (Localization.Away D'.s)).comp φ) from congrArg _ h_eq,
      RingHom.coe_comp]
    refine Continuous.comp ?_ hφ
    -- `algebraMap S (Localization.Away D'.s)` is continuous into `D'.topology`
    -- (inlined from `algebraMap_continuous_loc`, avoiding its nonarchimedean variable).
    apply continuous_of_continuousAt_zero
      (algebraMap S (Localization.Away D'.s)).toAddMonoidHom
    rw [ContinuousAt, map_zero, Filter.tendsto_def]
    intro U hU
    obtain ⟨n, -, hn⟩ :=
      (locBasis D'.P D'.T D'.s D'.hopen).hasBasis_nhds_zero.mem_iff.mp hU
    apply Filter.mem_of_superset (D'.P.hasBasis_nhds_zero.mem_of_mem (i := n) trivial)
    intro a ha
    obtain ⟨⟨b, hb⟩, hbn, hab⟩ := ha
    rw [← hab]
    exact hn ⟨algebraMapD D'.P D'.T D'.s ⟨b, hb⟩,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hbn, rfl⟩
  refine locTopology_continuous_lift D.P D.T D.s D.hopen _ hf_alg fun t ht => ?_
  rw [locMapOfHom_divByS]
  exact (locSubring_isBounded_of_pair D'.P D'.T D'.s D'.hopen).isPowerBounded_of_mem
    (divByS_mem_locSubring D'.P D'.T D'.s (hT t ht))

/-- The covariant map into the completion (algebraic side). -/
noncomputable def pushMapAlg (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) :
    Localization.Away D.s →+* presheafValue D' :=
  D'.coeRingHom.comp (locMapOfHom φ D D' hs)

theorem pushMapAlg_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (pushMapAlg φ D D' hs) := by
  letI := D.topology
  letI := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  have hcoe : @Continuous _ _ D'.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      D'.coeRingHom :=
    @UniformSpace.Completion.continuous_coe _ D'.uniformSpace
  exact hcoe.comp (locMapOfHom_continuous φ hφ D D' hs hT)

/-- The covariant presheaf-value map `𝒪(D) →+* 𝒪(D')` along `φ` ([FJP] Lemma 5.1). -/
noncomputable def presheafValueMapOfHom (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    presheafValue D →+* presheafValue D' := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (pushMapAlg φ D D' hs)
    (pushMapAlg_continuous φ hφ D D' hs hT)

theorem presheafValueMapOfHom_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    Continuous (presheafValueMapOfHom φ hφ D D' hs hT) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The covariant map agrees with the algebraic map on the dense image. -/
theorem presheafValueMapOfHom_coe (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) (a : Localization.Away D.s) :
    presheafValueMapOfHom φ hφ D D' hs hT
      (@UniformSpace.Completion.coeRingHom _ _ D.uniformSpace
        D.isTopologicalRing D.isUniformAddGroup a) =
      pushMapAlg φ D D' hs a := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (pushMapAlg φ D D' hs)
    (pushMapAlg_continuous φ hφ D D' hs hT) a

/-- The covariant map intertwines the canonical maps ([FJP] Lemma 5.1 naturality on `A`). -/
theorem presheafValueMapOfHom_canonicalMap (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) (a : R) :
    presheafValueMapOfHom φ hφ D D' hs hT (D.canonicalMap a) =
      D'.canonicalMap (φ a) := by
  have h1 : presheafValueMapOfHom φ hφ D D' hs hT (D.canonicalMap a) =
      pushMapAlg φ D D' hs (algebraMap R (Localization.Away D.s) a) :=
    presheafValueMapOfHom_coe φ hφ D D' hs hT (algebraMap R (Localization.Away D.s) a)
  rw [h1]
  show D'.coeRingHom (locMapOfHom φ D D' hs (algebraMap R (Localization.Away D.s) a)) = _
  rw [locMapOfHom_algebraMap]
  rfl

end CovariantPush

/-! ### Continuity of the square's maps (norm bounds ⇒ 1-Lipschitz) -/

theorem continuous_jB : Continuous (jB F) :=
  AddMonoidHomClass.continuous_of_bound (jB F) 1 fun a => by
    rw [one_mul]; exact norm_jB_le F a

theorem continuous_iotaC : Continuous (iotaC F) :=
  AddMonoidHomClass.continuous_of_bound (iotaC F) 1 fun a => by
    rw [one_mul, norm_iotaC]

theorem continuous_rhoC : Continuous (rhoC F) :=
  AddMonoidHomClass.continuous_of_bound (rhoC F) 1 fun a => by
    rw [one_mul]; exact norm_rhoC_le F a

/-- The induced map on completed rational localizations along `ιC` ([FJP] Lemma 5.1's
`𝒪_X(U) → 𝒪_{Y_C}(U_C)`; built from `IsLocalization` functoriality, continuity for the
localization topologies, and `UniformSpace.Completion` functoriality). -/
noncomputable def presheafValueMapC (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumC D hD) :=
  presheafValueMapOfHom (iotaC F) (continuous_iotaC) D (pushDatumC D hD) rfl
    (fun _ ht => Finset.mem_image_of_mem _ ht)

noncomputable def presheafValueMapB (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumB D hD) :=
  presheafValueMapOfHom (jB F) (continuous_jB) D (pushDatumB D hD) rfl
    (fun _ ht => Finset.mem_image_of_mem _ ht)

noncomputable def presheafValueMapD (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumD D hD) :=
  presheafValueMapOfHom ((rhoC F).comp (iotaC F))
    (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC))
    D (pushDatumD D hD) rfl (fun _ ht => Finset.mem_image_of_mem _ ht)

theorem presheafValueMapC_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    Continuous (presheafValueMapC D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem presheafValueMapB_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    Continuous (presheafValueMapB D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem presheafValueMapC_canonicalMap (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (a : JetA F) :
    presheafValueMapC D hD (D.canonicalMap a) =
      (pushDatumC D hD).canonicalMap (iotaC F a) :=
  presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ a

theorem presheafValueMapB_canonicalMap (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (a : JetA F) :
    presheafValueMapB D hD (D.canonicalMap a) =
      (pushDatumB D hD).canonicalMap (jB F a) :=
  presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ a

/-! ### The graph bridge ([FJP] Lemma 1.1 + (4.21))

For an indexed enumeration `(g, f)` of a rational datum `(T, s)` (with `g = s`), the
project's completed rational localization is topologically the Banach graph quotient. -/

/-- An indexed enumeration of a `RationalLocData`: `f` lists `T`, `g = s`. -/
structure DatumEnum (D : RationalLocData (JetA F)) where
  /-- The arity. -/
  m : ℕ
  /-- The enumeration of `T`. -/
  f : Fin m → JetA F
  /-- Enumeration covers `T`. -/
  hf : ∀ t ∈ D.T, ∃ i, f i = t
  /-- Enumeration lands in `T`. -/
  hf' : ∀ i, f i ∈ D.T

section GraphBridgeInfra

open GraphKoszul

/-- Quotients of ultrametric seminormed rings are ultrametric: the quotient norm
inherits the max inequality up to `ε` via near-optimal representatives. -/
instance instIsUltrametricDistIdealQuotient {R : Type*} [SeminormedCommRing R]
    [IsUltrametricDist R] (I : Ideal R) : IsUltrametricDist (R ⧸ I) where
  dist_triangle_max x y z := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨a, ha, han⟩ := Ideal.Quotient.norm_mk_lt (x - y) hε
    obtain ⟨b, hb, hbn⟩ := Ideal.Quotient.norm_mk_lt (y - z) hε
    have hxz : x - z = Ideal.Quotient.mk I (a + b) := by rw [map_add, ha, hb]; ring
    calc ‖x - z‖ = ‖Ideal.Quotient.mk I (a + b)‖ := by rw [hxz]
      _ ≤ ‖a + b‖ := Ideal.Quotient.norm_mk_le _ _
      _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max a b
      _ ≤ max (‖x - y‖ + ε) (‖y - z‖ + ε) := max_le_max han.le hbn.le
      _ = max ‖x - y‖ ‖y - z‖ + ε := max_add_add_right _ _ _

variable (D : RationalLocData (JetA F)) (e : DatumEnum D)

/-- The enumerated datum spans `({s} ∪ range f) = ⊤` (rationality + covering). -/
theorem DatumEnum.span_eq_top (hD : D.IsRational) :
    Ideal.span ({D.s} ∪ Set.range e.f) = ⊤ := by
  rw [← top_le_iff, ← hD.span_eq_top]
  refine Ideal.span_mono fun t ht => ?_
  obtain ⟨i, rfl⟩ := e.hf t ht
  exact Set.mem_union_right _ ⟨i, rfl⟩

/-- Scalars into `P_𝓐` (constant restricted series). -/
noncomputable def bridgeConst (m : ℕ) : JetA F →+* PA F m :=
  polyToP.comp MvPolynomial.C

/-- The base map `𝓐 → 𝓐_α = P_𝓐 ⧸ I_𝓐` (constants, then the graph quotient). -/
noncomputable def bridgeBase : JetA F →+* locA F e.m D.s e.f :=
  (Ideal.Quotient.mk (IA F e.m D.s e.f)).comp (bridgeConst e.m)

/-- The variable images `X̄ᵢ ∈ 𝓐_α`. -/
noncomputable def bridgeX (i : Fin e.m) : locA F e.m D.s e.f :=
  Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.X i))

/-- The graph relation in the quotient: `s̄ · X̄ᵢ = f̄ᵢ` ([FJP] (4.6)). -/
theorem bridgeBase_s_mul_X (i : Fin e.m) :
    bridgeBase D e D.s * bridgeX D e i = bridgeBase D e (e.f i) := by
  have hmem : polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (e.f i)) ∈ IA F e.m D.s e.f := by
    have hrw : rA F e.m D.s e.f i =
        polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
          polyToP (MvPolynomial.C (e.f i)) := by
      rw [rA, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C D.s)) *
      Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C (e.f i)))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IA F e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

/-- `s̄` is a unit in `𝓐_α` ([FJP] (4.3): the span decomposition
`1 = c·s + Σ dᵢ·fᵢ` becomes `1 = s̄·(c̄ + Σ d̄ᵢ X̄ᵢ)` after the graph relations). -/
theorem isUnit_bridgeBase_s (hD : D.IsRational) : IsUnit (bridgeBase D e D.s) := by
  have h1 : (1 : JetA F) ∈ Ideal.span ({D.s} ∪ Set.range e.f) := by
    rw [e.span_eq_top D hD]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBase D e (d i * e.f i) =
      bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := fun i => by
    rw [RingHom.map_mul (bridgeBase D e), bridgeBase_s_mul_X]
  have happ : bridgeBase D e c * bridgeBase D e D.s +
      ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) = 1 := by
    have h0 := congrArg (bridgeBase D e) hxy
    rw [RingHom.map_one (bridgeBase D e), RingHom.map_add (bridgeBase D e),
      RingHom.map_mul (bridgeBase D e),
      show (bridgeBase D e) (∑ i, d i * e.f i) = ∑ i, bridgeBase D e (d i * e.f i) from
        map_sum (bridgeBase D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBase D e D.s *
      (bridgeBase D e c + ∑ i, bridgeBase D e (d i) * bridgeX D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBase D e D.s * bridgeBase D e c +
        ∑ i, bridgeBase D e D.s * (bridgeBase D e (d i) * bridgeX D e i)
        = bridgeBase D e c * bridgeBase D e D.s +
          ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := by
          rw [mul_comm (bridgeBase D e D.s) (bridgeBase D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

/-- A seminormed ultrametric comm ring is a nonarchimedean topological ring
(generalizes the normed version in `ExampleUnitDisc`). -/
instance instNonarchimedeanRingOfSeminormedUltra {R : Type*} [SeminormedCommRing R]
    [IsUltrametricDist R] : NonarchimedeanRing R :=
  ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩

/-- Norm-≤-1 elements of a seminormed comm ring are power-bounded. -/
theorem isPowerBounded_of_norm_le_one {R : Type*} [SeminormedCommRing R] {x : R}
    (hx : ‖x‖ ≤ 1) : TopologicalRing.IsPowerBounded x := by
  have hM : ∀ n : ℕ, ‖x ^ n‖ ≤ max ‖(1 : R)‖ 1 := by
    intro n
    cases n with
    | zero => simp only [pow_zero]; exact le_max_left _ _
    | succ k =>
      refine le_trans (norm_pow_le' x k.succ_pos) (le_max_of_le_right ?_)
      exact pow_le_one₀ (norm_nonneg _) hx
  have hMpos : (0 : ℝ) < max ‖(1 : R)‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 (ε / max ‖(1 : R)‖ 1),
    Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro z ⟨s, ⟨n, rfl⟩, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖x ^ n * y‖ ≤ ‖x ^ n‖ * ‖y‖ := norm_mul_le _ _
    _ ≤ max ‖(1 : R)‖ 1 * ‖y‖ := by
        exact mul_le_mul_of_nonneg_right (hM n) (norm_nonneg y)
    _ < max ‖(1 : R)‖ 1 * (ε / max ‖(1 : R)‖ 1) :=
        mul_lt_mul_of_pos_left hy hMpos
    _ = ε := mul_div_cancel₀ _ (ne_of_gt hMpos)

/-- The Gauss norm (radius 1) of a variable is at most one. -/
theorem gaussNorm_X_le_one {S : Type*} [NormedCommRing S] [NormOneClass S] {m : ℕ} (i : Fin m) :
    MvPowerSeries.gaussNorm (norm : S → ℝ) (fun _ : Fin m => (1 : ℝ))
      ((MvPolynomial.X i : MvPolynomial (Fin m) S) : MvPowerSeries (Fin m) S) ≤ 1 := by
  classical
  refine Real.iSup_le (fun t => ?_) zero_le_one
  have hprod : (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := by
    simp
  rw [hprod, mul_one, MvPolynomial.coeff_coe, MvPolynomial.coeff_X]
  split
  · simp
  · simp

/-- `‖X̄ᵢ‖ ≤ 1` in the graph quotient. -/
theorem norm_bridgeX_le_one (i : Fin e.m) : ‖bridgeX D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetA F) i

/-- `bridgeBase` is norm-nonincreasing (constants keep their norm, quotients contract). -/
theorem norm_bridgeBase_le (a : JetA F) : ‖bridgeBase D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a) : PA F e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetA F) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The loc-level forward map `A_s → 𝓐_α` (`IsLocalization.Away.lift` at the unit `s̄`). -/
noncomputable def bridgeLocHom (hD : D.IsRational) :
    Localization.Away D.s →+* locA F e.m D.s e.f :=
  IsLocalization.Away.lift D.s (isUnit_bridgeBase_s D e hD)

theorem bridgeLocHom_algebraMap (hD : D.IsRational) (a : JetA F) :
    bridgeLocHom D e hD (algebraMap (JetA F) (Localization.Away D.s) a) =
      bridgeBase D e a :=
  IsLocalization.Away.lift_eq _ _ a

/-- The forward map sends the rational generator `fᵢ/s` to the variable `X̄ᵢ`. -/
theorem bridgeLocHom_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHom D e hD (divByS (e.f i) D.s) = bridgeX D e i := by
  have hu := isUnit_bridgeBase_s D e hD
  have hspec : divByS (e.f i) D.s * algebraMap (JetA F) (Localization.Away D.s) D.s =
      algebraMap (JetA F) (Localization.Away D.s) (e.f i) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHom D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHom D e hD), bridgeLocHom_algebraMap,
    bridgeLocHom_algebraMap, ← bridgeBase_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBase D e D.s) (bridgeLocHom D e hD (divByS (e.f i) D.s))]
  exact happ

set_option maxHeartbeats 800000 in
/-- Continuity of the loc-level forward map (universal property; the generators map to
the norm-≤-1 variables `X̄ᵢ`, which are power-bounded). -/
theorem bridgeLocHom_continuous (hD : D.IsRational) :
    @Continuous _ _ D.topology _ (bridgeLocHom D e hD) := by
  refine locTopology_continuous_lift D.P D.T D.s D.hopen _ ?_ ?_
  · have h_eq : (bridgeLocHom D e hD).comp
        (algebraMap (JetA F) (Localization.Away D.s)) = bridgeBase D e := by
      ext a; exact bridgeLocHom_algebraMap D e hD a
    rw [show ⇑((bridgeLocHom D e hD).comp
        (algebraMap (JetA F) (Localization.Away D.s)))
        = ⇑(bridgeBase D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBase D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBase_le D e a
  · intro t ht
    obtain ⟨i, rfl⟩ := e.hf t ht
    rw [bridgeLocHom_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeX_le_one D e i)

/-- Forward: `𝒪_𝓐(D) → 𝓐_α` (completion extension of the localization lift;
the target is complete Hausdorff since `I_𝓐` is closed, [FJP] (4.21)). -/
noncomputable def bridgeFwd (hD : D.IsRational) :
    presheafValue D →+* locA F e.m D.s e.f := by
  haveI hcl : IsClosed ((IA F e.m D.s e.f : Set (PA F e.m))) :=
    isClosed_IA F e.m D.s e.f (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA F e.m D.s e.f) := locA_t2 F e.m D.s e.f (e.span_eq_top D hD)
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD)

theorem bridgeFwd_coe (hD : D.IsRational) (a : Localization.Away D.s) :
    bridgeFwd D e hD (D.coeRingHom a) = bridgeLocHom D e hD a := by
  haveI hcl : IsClosed ((IA F e.m D.s e.f : Set (PA F e.m))) :=
    isClosed_IA F e.m D.s e.f (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA F e.m D.s e.f) := locA_t2 F e.m D.s e.f (e.span_eq_top D hD)
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD) a

theorem bridgeFwd_canonicalMap (hD : D.IsRational) (a : JetA F) :
    bridgeFwd D e hD (D.canonicalMap a) = bridgeBase D e a := by
  rw [show D.canonicalMap a =
      D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a) from rfl,
    bridgeFwd_coe, bridgeLocHom_algebraMap]

theorem bridgeFwd_continuous (hD : D.IsRational) :
    Continuous (bridgeFwd D e hD) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### The reverse direction: evaluation `P_𝓐 → 𝒪_𝓐(D)` ([FJP] Lemma 1.1, bound (1.3)) -/

/-- Norm-decay restricted series are topologically restricted (the two restricted power
series notions agree over a normed base). -/
noncomputable def bridgeToRestricted (m : ℕ) :
    PA F m →+* ↥(restrictedMvPowerSeriesSubring m (JetA F)) where
  toFun p := ⟨p.1, by
    have hp : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) p.1 := p.2
    rw [MvPowerSeries.IsRestrictedGauss] at hp
    have hprod : ∀ t : Fin m →₀ ℕ, (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := fun t => by simp
    simp only [hprod, mul_one] at hp
    show Filter.Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t p.1)
      Filter.cofinite (nhds 0)
    rwa [tendsto_zero_iff_norm_tendsto_zero]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The rational generators `fᵢ/s ∈ 𝒪_𝓐(D)`. -/
noncomputable def bridgeGen (i : Fin e.m) : presheafValue D :=
  D.coeRingHom (divByS (e.f i) D.s)

/-- Each generator is power-bounded (its powers lie in the image of the bounded
`locSubring`; mirrors `example638_genTuple_isBounded`). -/
theorem bridgeGen_isBounded (i : Fin e.m) :
    TopologicalRing.IsBounded (Set.range (bridgeGen D e i ^ · : ℕ → presheafValue D)) := by
  have hmem : divByS (e.f i) D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (e.hf' i)
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded D
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (e.f i) D.s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The evaluation `P_𝓐 →+* 𝒪_𝓐(D)`: `Σ a_v X^v ↦ Σ ρ(a_v)·(f/s)^v`
(convergent by [FJP] (1.3); built on the project's `mvEvalHomBounded`). -/
noncomputable def bridgeEval : PA F e.m →+* presheafValue D :=
  (mvEvalHomBounded D.canonicalMap (canonicalMap_continuous D)
    (bridgeGen D e) (bridgeGen_isBounded D e)).comp (bridgeToRestricted e.m)

theorem bridgeEval_const (a : JetA F) :
    bridgeEval D e (polyToP (MvPolynomial.C a)) = D.canonicalMap a := by
  have hcast : bridgeToRestricted (F := F) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap (JetA F) ↥(restrictedMvPowerSeriesSubring e.m (JetA F)) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) (JetA F)) = _
    rw [show (polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetA F) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

theorem bridgeEval_X (i : Fin e.m) :
    bridgeEval D e (polyToP (MvPolynomial.X i)) = bridgeGen D e i := by
  have hcast : bridgeToRestricted (F := F) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetA F) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) (JetA F)) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

/-- The evaluation kills the graph ideal (`s·(fᵢ/s) = fᵢ` in the localization). -/
theorem IA_le_ker_bridgeEval : IA F e.m D.s e.f ≤ RingHom.ker (bridgeEval D e) := by
  rw [IA, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have hval : bridgeEval D e (rA F e.m D.s e.f i) =
      D.canonicalMap D.s * bridgeGen D e i - D.canonicalMap (e.f i) :=
    (map_sub ((bridgeEval D e).comp polyToP)
        (MvPolynomial.C D.s * MvPolynomial.X i) (MvPolynomial.C (e.f i))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEval D e).comp polyToP)
            (MvPolynomial.C D.s) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEval_const D e D.s) (bridgeEval_X D e i)))
        (bridgeEval_const D e (e.f i)))
  rw [hval, sub_eq_zero, bridgeGen]
  rw [show D.canonicalMap D.s = D.coeRingHom (algebraMap (JetA F)
      (Localization.Away D.s) D.s) from rfl, ← RingHom.map_mul D.coeRingHom,
    show algebraMap (JetA F) (Localization.Away D.s) D.s * divByS (e.f i) D.s =
      algebraMap (JetA F) (Localization.Away D.s) (e.f i) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- Reverse: `𝓐_α → 𝒪_𝓐(D)` (the evaluation factors through the graph quotient). -/
noncomputable def bridgeRev : locA F e.m D.s e.f →+* presheafValue D :=
  Ideal.Quotient.lift (IA F e.m D.s e.f) (bridgeEval D e)
    (fun _ ha => RingHom.mem_ker.mp (IA_le_ker_bridgeEval D e ha))

theorem bridgeRev_mk (p : PA F e.m) :
    bridgeRev D e (Ideal.Quotient.mk (IA F e.m D.s e.f) p) = bridgeEval D e p := rfl

theorem bridgeRev_bridgeBase (a : JetA F) :
    bridgeRev D e (bridgeBase D e a) = D.canonicalMap a :=
  bridgeEval_const D e a

theorem bridgeRev_bridgeX (i : Fin e.m) :
    bridgeRev D e (bridgeX D e i) = bridgeGen D e i :=
  bridgeEval_X D e i

/-- Sums of open-subgroup members stay in the subgroup (local copy of the private
Wedhorn828 helper). -/
private theorem tsum_mem_of_isOpen_addSubgroup' {ι G₀ : Type*} [AddCommGroup G₀]
    [TopologicalSpace G₀] [IsTopologicalAddGroup G₀] {f : ι → G₀}
    (hf : Summable f) {G : AddSubgroup G₀} (hG : IsOpen (G : Set G₀))
    (hmem : ∀ i, f i ∈ G) : ∑' i, f i ∈ G := by
  have hclosed : IsClosed (G : Set G₀) := AddSubgroup.isClosed_of_isOpen G hG
  refine hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall ?_)
  intro s
  exact G.sum_mem fun i _ => hmem i

/-- The range of the generator product powers is bounded (local copy of the private
Wedhorn828 helper, at our tuple). -/
private theorem bridgeRangeProd_isBounded :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGen D e i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGen D e i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => simpa using TopologicalRing.isBounded_singleton (1 : presheafValue D)
  | insert a s ha ih =>
      refine ((bridgeGen_isBounded D e a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGen D e i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

/-- **Continuity of the evaluation** from the norm topology on `P_𝓐` ([FJP] (1.3) bound;
mirrors `mvEvalHomBounded_continuous` with the Gauss-norm ball basis in place of the
Tate-algebra basis: coefficients of a small series are small). -/
theorem bridgeEval_continuous : Continuous (bridgeEval D e) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEval D e).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProd_isBounded D e (W : Set (presheafValue D))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : D.canonicalMap ⁻¹' V ∈ nhds (0 : JetA F) :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : PA F e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm D.canonicalMap (bridgeGen D e)
    (bridgeToRestricted e.m p) v) ∈ (W : Set (presheafValue D))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable D.canonicalMap (canonicalMap_continuous D)
      (bridgeGen D e) (bridgeGen_isBounded D e) (bridgeToRestricted e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : D.canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v ∈ W
  rw [show mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v =
      (∏ i, bridgeGen D e i ^ (v i)) *
        D.canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

/-- Continuity of the reverse map (the graph quotient carries the quotient topology). -/
theorem bridgeRev_continuous : Continuous (bridgeRev D e) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IA F e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEval_continuous D e

/-! #### Round trips (density + Hausdorff equalizers) -/

/-- Polynomials are dense in `P_𝓐` (truncate below any coefficient-norm level). -/
theorem polyToP_denseRange (m : ℕ) :
    DenseRange (polyToP : MvPolynomial (Fin m) (JetA F) → PA F m) := by
  classical
  rw [Metric.denseRange_iff]
  intro p ε hε
  refine ⟨∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
    MvPolynomial.monomial s (MvPowerSeries.coeff s p.1), ?_⟩
  rw [dist_eq_norm, MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine lt_of_le_of_lt (Real.iSup_le (fun s => ?_) (half_pos hε).le) (half_lt_self hε)
  rw [finsupp_prod_one, mul_one]
  show ‖MvPowerSeries.coeff s ((p - polyToP _ : PA F m)).1‖ ≤ ε / 2
  rw [show ((p - polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1)) : PA F m)).1 =
    p.1 - (polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1) : MvPolynomial (Fin m)
        (JetA F))).1 from rfl, map_sub, coeff_polyToP, MvPolynomial.coeff_sum]
  by_cases hs : ε / 2 ≤ ‖MvPowerSeries.coeff s p.1‖
  · rw [Finset.sum_eq_single s
      (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun hns => absurd ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mpr hs)
        hns), MvPolynomial.coeff_monomial, if_pos rfl, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [Finset.sum_eq_zero fun b hb => ?_, sub_zero]
    · exact (not_le.mp hs).le
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hbs
      rw [hbs] at hb
      exact hs ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mp hb)

/-- `rev ∘ fwd = id` on `𝒪_𝓐(D)` (agreement on the dense localization image; both
composites with `algebraMap` are `canonicalMap`, so the localization universal property
applies, then extend by density to the completion). -/
theorem bridgeRev_bridgeFwd (hD : D.IsRational) (x : presheafValue D) :
    bridgeRev D e (bridgeFwd D e hD x) = x := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue D) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRev D e).comp (bridgeLocHom D e hD) = D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [bridgeLocHom_algebraMap, bridgeRev_bridgeBase]
    rfl
  have hdense : DenseRange (D.coeRingHom :
      Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hagree : (fun y => bridgeRev D e (bridgeFwd D e hD y)) ∘ D.coeRingHom =
      (fun y => y) ∘ (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    funext a
    show bridgeRev D e (bridgeFwd D e hD (D.coeRingHom a)) = D.coeRingHom a
    rw [bridgeFwd_coe]
    exact DFunLike.congr_fun hcomp a
  have h_eq : (fun y => bridgeRev D e (bridgeFwd D e hD y)) = fun y => y :=
    hdense.equalizer ((bridgeRev_continuous D e).comp (bridgeFwd_continuous D e hD))
      continuous_id hagree
  exact congrFun h_eq x

/-- The graph-quotient projection is continuous (`1`-Lipschitz for the quotient norm). -/
theorem mkIA_continuous :
    Continuous (Ideal.Quotient.mk (IA F e.m D.s e.f)) :=
  AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk (IA F e.m D.s e.f)) 1
    fun a => by rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ a

/-- `fwd ∘ rev = id` on `𝓐_α` (agreement on constants and variables, hence on the dense
polynomial image; extend by density to the Banach quotient). -/
theorem bridgeFwd_bridgeRev (hD : D.IsRational) (y : locA F e.m D.s e.f) :
    bridgeFwd D e hD (bridgeRev D e y) = y := by
  haveI hcl : IsClosed ((IA F e.m D.s e.f : Set (PA F e.m))) :=
    isClosed_IA F e.m D.s e.f (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA F e.m D.s e.f) := locA_t2 F e.m D.s e.f (e.span_eq_top D hD)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmkcont : Continuous (Ideal.Quotient.mk (IA F e.m D.s e.f)) :=
    mkIA_continuous D e
  have hpoly : ∀ q : MvPolynomial (Fin e.m) (JetA F),
      bridgeFwd D e hD (bridgeEval D e (polyToP q)) =
        Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP q) := by
    have hhomeq : ((bridgeFwd D e hD).comp ((bridgeEval D e).comp polyToP)) =
        (Ideal.Quotient.mk (IA F e.m D.s e.f)).comp
          (polyToP : MvPolynomial (Fin e.m) (JetA F) →+* PA F e.m) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · show bridgeFwd D e hD (bridgeEval D e (polyToP (MvPolynomial.C a))) =
          Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C a))
        rw [bridgeEval_const, bridgeFwd_canonicalMap]
        rfl
      · show bridgeFwd D e hD (bridgeEval D e (polyToP (MvPolynomial.X i))) =
          Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.X i))
        rw [bridgeEval_X, bridgeGen, bridgeFwd_coe, bridgeLocHom_divByS]
        rfl
    intro q
    exact DFunLike.congr_fun hhomeq q
  have h_eq : (fun z : PA F e.m => bridgeFwd D e hD (bridgeEval D e z)) =
      fun z : PA F e.m => Ideal.Quotient.mk (IA F e.m D.s e.f) z := by
    refine (polyToP_denseRange e.m).equalizer
      ((bridgeFwd_continuous D e hD).comp (bridgeEval_continuous D e)) hmkcont ?_
    funext q
    exact hpoly q
  exact congrFun h_eq p

/-! #### The 𝓒-side forward bridge (for the [FJP] Lemma 5.1 naturality square) -/

/-- The base map `𝓒 → 𝓒_α` (constants into the 𝓒-graph quotient). -/
noncomputable def bridgeBaseC : JetC F →+* locC F e.m D.s e.f :=
  (Ideal.Quotient.mk (IC F e.m D.s e.f)).comp
    ((polyToP : MvPolynomial (Fin e.m) (JetC F) →+* PC F e.m).comp MvPolynomial.C)

/-- The variable images `X̄ᵢ ∈ 𝓒_α`. -/
noncomputable def bridgeXC (i : Fin e.m) : locC F e.m D.s e.f :=
  Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.X i))

theorem bridgeBaseC_s_mul_X (i : Fin e.m) :
    bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i =
      bridgeBaseC D e (iotaC F (e.f i)) := by
  have hmem : polyToP (MvPolynomial.C (iotaC F D.s)) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (iotaC F (e.f i))) ∈ IC F e.m D.s e.f := by
    have hrw : rC F e.m D.s e.f i = polyToP (MvPolynomial.C (iotaC F D.s)) *
        polyToP (MvPolynomial.X i) - polyToP (MvPolynomial.C (iotaC F (e.f i))) := by
      rw [rC_eq, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.C (iotaC F D.s))) *
      Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.C (iotaC F (e.f i))))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IC F e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

theorem isUnit_bridgeBaseC_s (hD : D.IsRational) :
    IsUnit (bridgeBaseC D e (iotaC F D.s)) := by
  have h1 : (1 : JetC F) ∈
      Ideal.span ({iotaC F D.s} ∪ Set.range fun i => iotaC F (e.f i)) := by
    rw [span_pushed_C F e.m D.s e.f (e.span_eq_top D hD)]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBaseC D e (d i * iotaC F (e.f i)) =
      bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i) :=
    fun i => by rw [RingHom.map_mul (bridgeBaseC D e), bridgeBaseC_s_mul_X]
  have happ : bridgeBaseC D e c * bridgeBaseC D e (iotaC F D.s) +
      ∑ i, bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i) = 1 := by
    have h0 := congrArg (bridgeBaseC D e) hxy
    rw [RingHom.map_one (bridgeBaseC D e), RingHom.map_add (bridgeBaseC D e),
      RingHom.map_mul (bridgeBaseC D e),
      show (bridgeBaseC D e) (∑ i, d i * iotaC F (e.f i)) =
        ∑ i, bridgeBaseC D e (d i * iotaC F (e.f i)) from map_sum (bridgeBaseC D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBaseC D e (iotaC F D.s) *
      (bridgeBaseC D e c + ∑ i, bridgeBaseC D e (d i) * bridgeXC D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBaseC D e (iotaC F D.s) * bridgeBaseC D e c +
        ∑ i, bridgeBaseC D e (iotaC F D.s) * (bridgeBaseC D e (d i) * bridgeXC D e i)
        = bridgeBaseC D e c * bridgeBaseC D e (iotaC F D.s) +
          ∑ i, bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i) := by
          rw [mul_comm (bridgeBaseC D e (iotaC F D.s)) (bridgeBaseC D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

theorem norm_bridgeXC_le_one (i : Fin e.m) : ‖bridgeXC D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetC F) i

theorem norm_bridgeBaseC_le (a : JetC F) : ‖bridgeBaseC D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetC F) (m := e.m) (MvPolynomial.C a) : PC F e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetC F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetC F) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The 𝓒-side localization lift. -/
noncomputable def bridgeLocHomC (hD : D.IsRational) :
    Localization.Away (pushDatumC D hD).s →+* locC F e.m D.s e.f :=
  IsLocalization.Away.lift (pushDatumC D hD).s (isUnit_bridgeBaseC_s D e hD)

theorem bridgeLocHomC_algebraMap (hD : D.IsRational) (a : JetC F) :
    bridgeLocHomC D e hD
      (algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) a) =
      bridgeBaseC D e a :=
  IsLocalization.Away.lift_eq _ _ a

theorem bridgeLocHomC_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHomC D e hD (divByS (iotaC F (e.f i)) (pushDatumC D hD).s) =
      bridgeXC D e i := by
  have hu := isUnit_bridgeBaseC_s D e hD
  have hspec : divByS (iotaC F (e.f i)) (pushDatumC D hD).s *
      algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) (pushDatumC D hD).s =
      algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) (iotaC F (e.f i)) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHomC D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHomC D e hD), bridgeLocHomC_algebraMap,
    bridgeLocHomC_algebraMap, ← bridgeBaseC_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBaseC D e (iotaC F D.s))
    (bridgeLocHomC D e hD (divByS (iotaC F (e.f i)) (pushDatumC D hD).s))]
  exact happ

set_option maxHeartbeats 800000 in
theorem bridgeLocHomC_continuous (hD : D.IsRational) :
    @Continuous _ _ (pushDatumC D hD).topology _ (bridgeLocHomC D e hD) := by
  refine locTopology_continuous_lift (pushDatumC D hD).P (pushDatumC D hD).T
    (pushDatumC D hD).s (pushDatumC D hD).hopen _ ?_ ?_
  · have h_eq : (bridgeLocHomC D e hD).comp
        (algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s)) =
        bridgeBaseC D e := by
      ext a; exact bridgeLocHomC_algebraMap D e hD a
    rw [show ⇑((bridgeLocHomC D e hD).comp
        (algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s)))
        = ⇑(bridgeBaseC D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBaseC D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBaseC_le D e a
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    rw [bridgeLocHomC_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeXC_le_one D e i)

/-- `I_𝓒` is closed (noetherian-ball route, as in `isClosed_IA`'s vertex inputs). -/
theorem isClosed_IC' : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := by
  haveI := isNoetherianRing_PC F e.m
  exact isClosed_graphIdeal (tC F) (isUnit_tC F)
    (by rw [norm_tC]; exact norm_t_lt_one F) (by rw [norm_tC]; exact norm_t_pos F)
    (norm_tC_mul F) (isNoetherianRing_unitBall_PC F e.m) (rC F e.m D.s e.f)

/-- The 𝓒-side forward bridge `𝒪_𝓒(D_C) → 𝓒_α`. -/
noncomputable def bridgeFwdC (hD : D.IsRational) :
    presheafValue (pushDatumC D hD) →+* locC F e.m D.s e.f := by
  haveI hcl : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := isClosed_IC' D e
  haveI : NormedAddCommGroup (locC F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumC D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHomC D e hD)
    (bridgeLocHomC_continuous D e hD)

theorem bridgeFwdC_coe (hD : D.IsRational) (a : Localization.Away (pushDatumC D hD).s) :
    bridgeFwdC D e hD ((pushDatumC D hD).coeRingHom a) = bridgeLocHomC D e hD a := by
  haveI hcl : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := isClosed_IC' D e
  haveI : NormedAddCommGroup (locC F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumC D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHomC D e hD)
    (bridgeLocHomC_continuous D e hD) a

theorem bridgeFwdC_continuous (hD : D.IsRational) :
    Continuous (bridgeFwdC D e hD) := by
  letI := (pushDatumC D hD).uniformSpace
  exact UniformSpace.Completion.continuous_extension

end GraphBridgeInfra

/-- The graph bridge for 𝓐 ([FJP] Lemma 1.1: the separated completion of the graph
quotient "is therefore canonically the underlying Tate algebra of Huber's rational
localization `E_α`"; by Lemma 4.3 the ideal is closed so no further completion is needed).
Topological ring isomorphism `𝒪_𝓐(D) ≅ P_𝓐 ⧸ I_𝓐`. -/
def graphBridgeA (D : RationalLocData (JetA F)) (hD : D.IsRational) (e : DatumEnum D) :
    presheafValue D ≃+* locA (F := F) e.m D.s e.f where
  toFun := bridgeFwd D e hD
  invFun := bridgeRev D e
  left_inv := bridgeRev_bridgeFwd D e hD
  right_inv := bridgeFwd_bridgeRev D e hD
  map_mul' := map_mul (bridgeFwd D e hD)
  map_add' := map_add (bridgeFwd D e hD)

theorem graphBridgeA_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA D hD e) :=
  bridgeFwd_continuous D e hD

theorem graphBridgeA_symm_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA D hD e).symm :=
  bridgeRev_continuous D e

set_option synthInstance.maxHeartbeats 400000 in
open GraphKoszul in
/-- The bridge intertwines the covariant maps with the coefficientwise localized square
([FJP] Lemma 4.6 / Lemma 5.1 naturality, 𝓒 side; analogous statements for 𝓑, 𝓓 are
formulated in the transfer file where consumed). Statement fix (recorded, L5.4 attack 3):
the skeleton's `True` stub replaced by the real intertwining
`bridgeFwdC ∘ presheafValueMapC = locIotaC ∘ graphBridgeA`. -/
theorem graphBridge_natural_C (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) :
    (bridgeFwdC D e hD).comp (presheafValueMapC D hD) =
      (locIotaC F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI hcl : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := isClosed_IC' D e
  haveI : NormedAddCommGroup (locC F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((bridgeFwdC D e hD).comp (presheafValueMapC D hD)).comp D.coeRingHom =
      ((locIotaC F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)).comp
        D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show (D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a)) =
        D.canonicalMap a from rfl,
      presheafValueMapC_canonicalMap,
      show (pushDatumC D hD).canonicalMap (iotaC F a) =
        (pushDatumC D hD).coeRingHom (algebraMap (JetC F)
          (Localization.Away (pushDatumC D hD).s) (iotaC F a)) from rfl,
      bridgeFwdC_coe, bridgeLocHomC_algebraMap,
      show (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)
        (D.canonicalMap a) = bridgeFwd D e hD (D.canonicalMap a) from rfl,
      bridgeFwd_canonicalMap]
    -- `bridgeBaseC (ι a) = locIotaC (bridgeBase a)`: both are `mk (polyToP (C (ι a)))`.
    rw [show bridgeBase D e a =
        Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C a)) from rfl,
      locIotaC_mk,
      show extIotaC F e.m (polyToP (MvPolynomial.C a)) =
        polyToP (MvPolynomial.map (iotaC F) (MvPolynomial.C a)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C a),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((bridgeFwdC D e hD).comp (presheafValueMapC D hD)) =
      ⇑((locIotaC F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)) :=
    hdense.equalizer
      ((bridgeFwdC_continuous D e hD).comp (presheafValueMapC_continuous D hD))
      ((locIotaC_lipschitz F e.m D.s e.f).continuous.comp
        (graphBridgeA_continuous D hD e))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

/-! ### Vertices: loc-lift instances (noetherian discharger applies) -/

instance : HasLocLiftPowerBounded (JetB F) := hasLocLiftPowerBounded_faithful

instance : HasLocLiftPowerBounded (JetC F) := hasLocLiftPowerBounded_faithful

instance : HasLocLiftPowerBounded (JetD F) := hasLocLiftPowerBounded_faithful

/-! ### `HasLocLiftPowerBounded 𝓐`, componentwise

𝓐 is not noetherian, so `hasLocLiftPowerBounded_faithful` does not apply. Both fields are
derived through the Milnor description of `𝒪_𝓐(D)` ([FJP] Lemma 5.1 + Prop 4.5): a unit in
both comparison localizations whose inverses match in 𝓓 is a unit in the fiber product, and
power-boundedness in the max norm is componentwise. -/

instance hasLocLiftPowerBounded_JetA : HasLocLiftPowerBounded (JetA F) :=
  hasLocLiftPowerBounded_faithful

/-! ### Naturality with restriction ([FJP] Lemma 4.6, Lemma 5.1)

With the loc-lift instances available, the project's `restrictionMap` vocabulary applies to
all four rings, and the covariant maps commute with it. -/

theorem presheafValueMapC_restriction (D D' : RationalLocData (JetA F))
    (hD : D.IsRational) (hD' : D'.IsRational)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumC D' hD').T (pushDatumC D' hD').s ⊆
      rationalOpen (pushDatumC D hD).T (pushDatumC D hD).s) (x : presheafValue D) :
    presheafValueMapC D' hD' (restrictionMap D D' h x) =
      restrictionMap (pushDatumC D hD) (pushDatumC D' hD') hpush
        (presheafValueMapC D hD x) := by
  sorry

theorem presheafValueMapB_restriction (D D' : RationalLocData (JetA F))
    (hD : D.IsRational) (hD' : D'.IsRational)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumB D' hD').T (pushDatumB D' hD').s ⊆
      rationalOpen (pushDatumB D hD).T (pushDatumB D hD).s) (x : presheafValue D) :
    presheafValueMapB D' hD' (restrictionMap D D' h x) =
      restrictionMap (pushDatumB D hD) (pushDatumB D' hD') hpush
        (presheafValueMapB D hD x) := by
  sorry

/-! ### Coverage transfer ([FJP] Lemma 5.2, first display: `U_E = ⋃ᵢ (Uᵢ)_E`) -/

/-- Power-bounded elements of 𝓐 stay power-bounded under any norm-nonincreasing ring map
(the [FJP] "never bare continuity" transfer: 𝓐° = unit ball by Prop 2.3, and
norm-≤-1 elements are power-bounded in any seminormed ring). -/
theorem plus_le_comap_of_norm_le {E : Type*} [SeminormedCommRing E]
    (φ : JetA F →+* E) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {x : JetA F}
    (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) :=
  isPowerBounded_of_norm_le_one
    (le_trans (hφ x) ((isPowerBounded_JetA_iff F x).mp hx))

/-- Inverse images preserve the rational inequalities: pushed rational opens are the
`spaComap`-preimages. (Pointwise: `v ∈ rationalOpen (T_E, s_E) ↔ v ∘ ι ∈ rationalOpen (T, s)`
for `v` in the vertex spectrum.) -/
theorem mem_rationalOpen_pushDatumC_iff (D : RationalLocData (JetA F))
    (hD : D.IsRational) (v : Spv (JetC F)) (hv : v ∈ Spa (JetC F) (ringPlus (JetC F))) :
    v ∈ rationalOpen (pushDatumC D hD).T (pushDatumC D hD).s ↔
      ValuationSpectrum.comap (iotaC F) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap (iotaC F) v ∈ Spa (JetA F) (ringPlus (JetA F)) :=
    comap_mem_spa (continuous_iotaC) (fun x hx =>
      plus_le_comap_of_norm_le (iotaC F) (fun a => le_of_eq (norm_iotaC F a)) hx) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (iotaC F t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle (iotaC F) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumC D hD).s = iotaC F D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle (iotaC F) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

theorem mem_rationalOpen_pushDatumB_iff (D : RationalLocData (JetA F))
    (hD : D.IsRational) (v : Spv (JetB F)) (hv : v ∈ Spa (JetB F) (ringPlus (JetB F))) :
    v ∈ rationalOpen (pushDatumB D hD).T (pushDatumB D hD).s ↔
      ValuationSpectrum.comap (jB F) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap (jB F) v ∈ Spa (JetA F) (ringPlus (JetA F)) :=
    comap_mem_spa (continuous_jB) (fun x hx =>
      plus_le_comap_of_norm_le (jB F) (norm_jB_le F) hx) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (jB F t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle (jB F) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumB D hD).s = jB F D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle (jB F) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

/-- The 𝓓-side pointwise coverage transfer (supporting lemma for `pushCoveringD`). -/
theorem mem_rationalOpen_pushDatumD_iff (D : RationalLocData (JetA F))
    (hD : D.IsRational) (v : Spv (JetD F)) (hv : v ∈ Spa (JetD F) (ringPlus (JetD F))) :
    v ∈ rationalOpen (pushDatumD D hD).T (pushDatumD D hD).s ↔
      ValuationSpectrum.comap ((rhoC F).comp (iotaC F)) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap ((rhoC F).comp (iotaC F)) v ∈
      Spa (JetA F) (ringPlus (JetA F)) :=
    comap_mem_spa (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC))
      (fun x hx => Subring.mem_comap.mpr
        (plus_le_comap_of_norm_le ((rhoC F).comp (iotaC F))
          (fun a => le_trans (norm_rhoC_le F (iotaC F a)) (le_of_eq (norm_iotaC F a)))
          (show TopologicalRing.IsPowerBounded x from hx))) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (((rhoC F).comp (iotaC F)) t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle ((rhoC F).comp (iotaC F)) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumD D hD).s = ((rhoC F).comp (iotaC F)) D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle ((rhoC F).comp (iotaC F)) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

/-- The pushed covering of a rational covering of 𝓐, at the 𝓒-vertex
([FJP] Lemma 5.2: "Inverse images preserve the defining valuation inequalities and unions.
Hence, for `E = B, C, D`, `U_E = ⋃ᵢ (Uᵢ)_E` is a rational covering"). -/
def pushCoveringC (C : RationalCovering (JetA F)) (hC : C.IsRational) :
    RationalCovering (JetC F) where
  base := pushDatumC C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumC d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetC F) (ringPlus (JetC F)) := hv.1
    exact (mem_rationalOpen_pushDatumC_iff C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumC_iff d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetC F) (ringPlus (JetC F)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumC_iff C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumC D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumC_iff D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

def pushCoveringB (C : RationalCovering (JetA F)) (hC : C.IsRational) :
    RationalCovering (JetB F) where
  base := pushDatumB C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumB d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetB F) (ringPlus (JetB F)) := hv.1
    exact (mem_rationalOpen_pushDatumB_iff C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumB_iff d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetB F) (ringPlus (JetB F)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumB_iff C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumB D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumB_iff D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

def pushCoveringD (C : RationalCovering (JetA F)) (hC : C.IsRational) :
    RationalCovering (JetD F) where
  base := pushDatumD C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumD d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetD F) (ringPlus (JetD F)) := hv.1
    exact (mem_rationalOpen_pushDatumD_iff C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumD_iff d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetD F) (ringPlus (JetD F)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumD_iff C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumD D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumD_iff D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

theorem pushCoveringB_isRational {C : RationalCovering (JetA F)} (hC : C.IsRational) :
    (pushCoveringB C hC).IsRational := by
  refine ⟨pushDatumB_isRational hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumB_isRational (hC.piece d.2)

theorem pushCoveringC_isRational {C : RationalCovering (JetA F)} (hC : C.IsRational) :
    (pushCoveringC C hC).IsRational := by
  refine ⟨pushDatumC_isRational hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumC_isRational (hC.piece d.2)

theorem pushCoveringD_isRational {C : RationalCovering (JetA F)} (hC : C.IsRational) :
    (pushCoveringD C hC).IsRational := by
  refine ⟨pushDatumD_isRational hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumD_isRational (hC.piece d.2)

/-! ### Intersection data ([FJP] Lemma 5.2: `(U_{ij})_E = (U_i)_E ∩ (U_j)_E`) -/

open scoped Pointwise in
/-- Spans of pointwise-product finsets of two spanning sets span (`⊤ * ⊤ = ⊤`).
The `DecidableEq` binder is deliberate: it makes the use site instantiate `Finset.image`
with the ambient instance, so the conclusion matches syntactically (at `JetA` the ambient
instance is `Subtype.instDecidableEq`, not `Classical.decEq`, and defeq-checking the two
unfolds the whole jet tower). -/
theorem span_mul_image_eq_top {A : Type*} [CommRing A] [DecidableEq A] {T₁ T₂ : Finset A}
    (h₁ : Ideal.span (T₁ : Set A) = ⊤) (h₂ : Ideal.span (T₂ : Set A) = ⊤) :
    Ideal.span ((((T₁ ×ˢ T₂).image fun p => p.1 * p.2 : Finset A)) : Set A) = ⊤ := by
  have hcoe : ((((T₁ ×ˢ T₂).image fun p => p.1 * p.2 : Finset A)) : Set A)
      = (T₁ : Set A) * (T₂ : Set A) := by
    rw [Finset.coe_image, Finset.coe_product]
    exact Set.image_mul_prod
  rw [hcoe, ← Ideal.span_mul_span', h₁, h₂, Ideal.top_mul]

/-- The product-datum span fact, stated at 𝓐. -/
theorem interDatum_span_eq_top (D₁ D₂ : RationalLocData (JetA F))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    Ideal.span ((((D₁.T ×ˢ D₂.T).image fun p => p.1 * p.2 : Finset (JetA F))) :
      Set (JetA F)) = ⊤ :=
  span_mul_image_eq_top h₁.span_eq_top h₂.span_eq_top

/-- The product (intersection) datum of two rational data ([FJP] Lemma 5.2 uses
`U_{ij} = U_i ∩ U_j`, "which is again rational"). Signature completion (recorded):
rationality of both data discharges `hopen` via the product-span computation. -/
def interDatum (D₁ D₂ : RationalLocData (JetA F))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : RationalLocData (JetA F) where
  P := podA F
  T := (D₁.T ×ˢ D₂.T).image fun p => p.1 * p.2
  s := D₁.s * D₂.s
  hopen := genPiece_hopen (podA F) ((D₁.T ×ˢ D₂.T).image fun p => p.1 * p.2)
    (D₁.s * D₂.s) (interDatum_span_eq_top D₁ D₂ h₁ h₂)

theorem rationalOpen_interDatum (D₁ D₂ : RationalLocData (JetA F))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    rationalOpen (interDatum D₁ D₂ h₁ h₂).T (interDatum D₁ D₂ h₁ h₂).s =
      rationalOpen D₁.T D₁.s ∩ rationalOpen D₂.T D₂.s := by sorry

theorem interDatum_isRational {D₁ D₂ : RationalLocData (JetA F)}
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : (interDatum D₁ D₂ h₁ h₂).IsRational :=
  RationalLocData.isRational_of_span_eq_top (interDatum_span_eq_top D₁ D₂ h₁ h₂)

end

end FiniteJet
