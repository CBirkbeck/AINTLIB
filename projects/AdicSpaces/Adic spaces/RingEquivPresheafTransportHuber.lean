/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RingEquivPresheafTransport
import «Adic spaces».PresheafFunctoriality

/-!
# Ring-equivalence presheaf transport, general Huber form (D-iii-1)

The Tate-free counterpart of `RingEquivPresheafTransport`'s datum/value layer:
`RationalLocData.mapHuber` transports a rational datum along a bicontinuous
ring equivalence with the `hopen` witness pushed through the datum-free
localization map (`locMapAway`) — no spanning condition. On top of it: validity
transport, the completed value equivalence `presheafValueRingEquivHuber`
(continuous both ways, natural in the canonical maps and in restriction), and
the `comap`-preimage description of the transported rational opens. Consumed by
the Frobenius action on the Fargues–Fontaine `𝒴` (D-iii).
-/

open TopologicalRing ValuationSpectrum Topology Filter

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} {B : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DecidableEq B]

/-- The datum-free localization pushforward `A_s → B_{φ s}`. -/
def locMapAway (φ : A →+* B) (s : A) :
    Localization.Away s →+* Localization.Away (φ s) :=
  IsLocalization.map (Localization.Away (φ s)) φ
    (show Submonoid.powers s ≤ (Submonoid.powers (φ s)).comap φ from
      Submonoid.powers_le.mpr ⟨1, pow_one (φ s)⟩)

theorem locMapAway_algebraMap (φ : A →+* B) (s : A) (a : A) :
    locMapAway φ s (algebraMap A (Localization.Away s) a)
      = algebraMap B (Localization.Away (φ s)) (φ a) := by
  unfold locMapAway
  rw [IsLocalization.map_eq]

theorem locMapAway_divByS (φ : A →+* B) (s : A) (t : A) :
    locMapAway φ s (divByS t s) = divByS (φ t) (φ s) := by
  rw [divByS, divByS, locMapAway, IsLocalization.map_mk']

/-- The datum-free pushforward maps a ring of definition into a ring of
definition (generator-wise closure induction). -/
theorem locMapAway_mem_locSubring (φ : A →+* B)
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (P' : PairOfDefinition B) (T' : Finset B)
    (hA₀ : ∀ a ∈ P.A₀, φ a ∈ P'.A₀) (hT : ∀ t ∈ T, φ t ∈ T')
    {x : Localization.Away s} (hx : x ∈ locSubring P T s) :
    locMapAway φ s x ∈ locSubring P' T' (φ s) := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, haA₀, rfl⟩ | ⟨t, rfl⟩
    · rw [locMapAway_algebraMap]
      exact algebraMap_A₀_subset_locSubring P' T' (φ s)
        ⟨φ a, hA₀ a haA₀, rfl⟩
    · rw [locMapAway_divByS]
      exact divByS_mem_locSubring P' T' (φ s) (hT t t.2)
  | one => rw [map_one]; exact one_mem _
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _

/-- **Transport of a rational datum along a bicontinuous ring equivalence,
general Huber form** (no spanning condition; `hopen` transported through the
datum-free localization pushforward). -/
def RationalLocData.mapHuber (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) : RationalLocData B where
  P := D.P.mapRingEquiv e he he'
  T := D.T.image e
  s := e D.s
  hopen := by
    obtain ⟨N, hN⟩ := D.hopen
    refine ⟨N, fun b hb => ?_⟩
    have hb' : b ∈ Ideal.map (e.subringMap (s := D.P.A₀)).toRingHom
        (D.P.I ^ N) := by
      rw [Ideal.map_pow]
      exact hb
    obtain ⟨a, haI, hab⟩ := Ideal.mem_map_iff_of_surjective _
      (e.subringMap (s := D.P.A₀)).surjective |>.mp hb'
    have hval : (b : B) = e (a : A) := by
      rw [← hab]
      rfl
    have hmem := locMapAway_mem_locSubring e.toRingHom D.P D.T D.s
      (D.P.mapRingEquiv e he he') (D.T.image e)
      (fun x hx => ⟨x, hx, rfl⟩) (fun t ht => Finset.mem_image_of_mem _ ht)
      (hN a haI)
    rw [locMapAway_divByS] at hmem
    rw [show ((b : ↥(D.P.mapRingEquiv e he he').A₀) : B) = e (a : A) from hval]
    exact hmem

@[simp] theorem RationalLocData.mapHuber_P (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) :
    (D.mapHuber e he he').P = D.P.mapRingEquiv e he he' := rfl

@[simp] theorem RationalLocData.mapHuber_T (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) :
    (D.mapHuber e he he').T = D.T.image e := rfl

@[simp] theorem RationalLocData.mapHuber_s (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) :
    (D.mapHuber e he he').s = e D.s := rfl

/-- The Huber-transported datum of a valid datum is valid (openness of the
tray span transports through the homeomorphism). -/
theorem RationalLocData.mapHuber_isRational (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) (hD : D.IsRational) :
    (D.mapHuber e he he').IsRational := by
  have hset : (Ideal.span (((D.mapHuber e he he').T : Finset B) : Set B)
      : Set B) = e '' ((Ideal.span ((D.T : Finset A) : Set A) : Ideal A)
        : Set A) := by
    rw [RationalLocData.mapHuber_T, Finset.coe_image, ← Ideal.map_span]
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha, hab⟩ := Ideal.mem_map_iff_of_surjective _
        e.surjective |>.mp hb
      exact ⟨a, ha, hab⟩
    · rintro ⟨a, ha, rfl⟩
      exact Ideal.mem_map_of_mem _ ha
  show IsOpen ((Ideal.span (((D.mapHuber e he he').T : Finset B) : Set B)
    : Ideal B) : Set B)
  rw [hset]
  exact (IsOpenMap.of_inverse he' e.apply_symm_apply e.symm_apply_apply) _ hD

-- Local copy of the (private) dense-extension identity engine.
private theorem presheafValue_eq_id_of_coeRingHom' {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (E : RationalLocData R)
    {G : presheafValue E → presheafValue E} (hG : Continuous G)
    (h : ∀ l, G (E.coeRingHom l) = E.coeRingHom l) (x : presheafValue E) :
    G x = x := by
  have hdense : DenseRange (⇑(E.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ E.uniformSpace
  exact congr_fun (hdense.equalizer hG continuous_id (funext h)) x

section Value

variable (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
variable (D : RationalLocData A)

private theorem hs_fwd' : (D.mapHuber e he he').s = e.toRingHom D.s := rfl

private theorem hT_fwd' : ∀ t ∈ D.T, e.toRingHom t ∈ (D.mapHuber e he he').T :=
  fun _ ht => Finset.mem_image_of_mem _ ht

private theorem hs_bwd' : D.s = e.symm.toRingHom (D.mapHuber e he he').s :=
  (e.symm_apply_apply D.s).symm

private theorem hT_bwd' : ∀ t ∈ (D.mapHuber e he he').T, e.symm.toRingHom t ∈ D.T := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  rwa [show e.symm.toRingHom (e a) = a from e.symm_apply_apply a]

/-- The forward completed map onto the Huber-transported datum. -/
noncomputable def pvFwdHuber :
    presheafValue D →+* presheafValue (D.mapHuber e he he') :=
  presheafValueMapOfHom e.toRingHom he D (D.mapHuber e he he')
    (hs_fwd' e he he' D) (hT_fwd' e he he' D)

/-- The backward completed map from the Huber-transported datum. -/
noncomputable def pvBwdHuber :
    presheafValue (D.mapHuber e he he') →+* presheafValue D :=
  presheafValueMapOfHom e.symm.toRingHom he' (D.mapHuber e he he') D
    (hs_bwd' e he he' D) (hT_bwd' e he he' D)

private theorem locMapHuber_roundtrip (l : Localization.Away D.s) :
    locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D (hs_bwd' e he he' D)
      (locMapOfHom e.toRingHom D (D.mapHuber e he he') (hs_fwd' e he he' D) l) = l := by
  have hid : ((locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D
      (hs_bwd' e he he' D)).comp (locMapOfHom e.toRingHom D
        (D.mapHuber e he he') (hs_fwd' e he he' D))) =
      RingHom.id (Localization.Away D.s) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s)
      (RingHom.ext fun a => ?_)
    show locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D
        (hs_bwd' e he he' D) (locMapOfHom e.toRingHom D (D.mapHuber e he he')
          (hs_fwd' e he he' D) (algebraMap A (Localization.Away D.s) a))
      = algebraMap A (Localization.Away D.s) a
    rw [locMapOfHom_algebraMap, locMapOfHom_algebraMap]
    exact congrArg (algebraMap A (Localization.Away D.s)) (e.symm_apply_apply a)
  exact DFunLike.congr_fun hid l

private theorem locMapHuber_roundtrip_symm
    (l : Localization.Away (D.mapHuber e he he').s) :
    locMapOfHom e.toRingHom D (D.mapHuber e he he') (hs_fwd' e he he' D)
      (locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D
        (hs_bwd' e he he' D) l) = l := by
  have hid : ((locMapOfHom e.toRingHom D (D.mapHuber e he he') (hs_fwd' e he he' D)).comp
      (locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D
        (hs_bwd' e he he' D))) =
      RingHom.id (Localization.Away (D.mapHuber e he he').s) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (D.mapHuber e he he').s)
      (RingHom.ext fun a => ?_)
    show locMapOfHom e.toRingHom D (D.mapHuber e he he') (hs_fwd' e he he' D)
        (locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D
          (hs_bwd' e he he' D)
          (algebraMap B (Localization.Away (D.mapHuber e he he').s) a))
      = algebraMap B (Localization.Away (D.mapHuber e he he').s) a
    rw [locMapOfHom_algebraMap, locMapOfHom_algebraMap]
    exact congrArg (algebraMap B (Localization.Away (D.mapHuber e he he').s))
      (e.apply_symm_apply a)
  exact DFunLike.congr_fun hid l

/-- **The completed rational-localization equivalence along a bicontinuous
ring equivalence, general Huber form.** -/
noncomputable def presheafValueRingEquivHuber :
    presheafValue D ≃+* presheafValue (D.mapHuber e he he') where
  toFun := pvFwdHuber e he he' D
  invFun := pvBwdHuber e he he' D
  left_inv x := by
    refine presheafValue_eq_id_of_coeRingHom' D
      ((presheafValueMapOfHom_continuous _ he' _ _ _ _).comp
        (presheafValueMapOfHom_continuous _ he _ _ _ _)) (fun l => ?_) x
    show pvBwdHuber e he he' D (pvFwdHuber e he he' D (D.coeRingHom l))
      = D.coeRingHom l
    rw [show pvFwdHuber e he he' D (D.coeRingHom l)
        = (D.mapHuber e he he').coeRingHom (locMapOfHom e.toRingHom D
            (D.mapHuber e he he') (hs_fwd' e he he' D) l) from
        presheafValueMapOfHom_coe _ he _ _ _ _ l,
      show pvBwdHuber e he he' D ((D.mapHuber e he he').coeRingHom
          (locMapOfHom e.toRingHom D (D.mapHuber e he he') (hs_fwd' e he he' D) l))
        = D.coeRingHom (locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D
            (hs_bwd' e he he' D) (locMapOfHom e.toRingHom D
              (D.mapHuber e he he') (hs_fwd' e he he' D) l)) from
        presheafValueMapOfHom_coe _ he' _ _ _ _ _,
      locMapHuber_roundtrip]
  right_inv y := by
    refine presheafValue_eq_id_of_coeRingHom' (D.mapHuber e he he')
      ((presheafValueMapOfHom_continuous _ he _ _ _ _).comp
        (presheafValueMapOfHom_continuous _ he' _ _ _ _)) (fun l => ?_) y
    show pvFwdHuber e he he' D (pvBwdHuber e he he' D
      ((D.mapHuber e he he').coeRingHom l)) = (D.mapHuber e he he').coeRingHom l
    rw [show pvBwdHuber e he he' D ((D.mapHuber e he he').coeRingHom l)
        = D.coeRingHom (locMapOfHom e.symm.toRingHom (D.mapHuber e he he') D
            (hs_bwd' e he he' D) l) from
        presheafValueMapOfHom_coe _ he' _ _ _ _ l,
      show pvFwdHuber e he he' D (D.coeRingHom (locMapOfHom e.symm.toRingHom
          (D.mapHuber e he he') D (hs_bwd' e he he' D) l))
        = (D.mapHuber e he he').coeRingHom (locMapOfHom e.toRingHom D
            (D.mapHuber e he he') (hs_fwd' e he he' D) (locMapOfHom e.symm.toRingHom
              (D.mapHuber e he he') D (hs_bwd' e he he' D) l)) from
        presheafValueMapOfHom_coe _ he _ _ _ _ _,
      locMapHuber_roundtrip_symm]
  map_mul' := map_mul _
  map_add' := map_add _

theorem presheafValueRingEquivHuber_continuous :
    Continuous (presheafValueRingEquivHuber e he he' D) :=
  presheafValueMapOfHom_continuous e.toRingHom he D (D.mapHuber e he he')
    (hs_fwd' e he he' D) (hT_fwd' e he he' D)

theorem presheafValueRingEquivHuber_symm_continuous :
    Continuous (presheafValueRingEquivHuber e he he' D).symm :=
  presheafValueMapOfHom_continuous e.symm.toRingHom he' (D.mapHuber e he he')
    D (hs_bwd' e he he' D) (hT_bwd' e he he' D)

theorem presheafValueRingEquivHuber_canonicalMap (a : A) :
    presheafValueRingEquivHuber e he he' D (D.canonicalMap a)
      = (D.mapHuber e he he').canonicalMap (e a) :=
  presheafValueMapOfHom_canonicalMap e.toRingHom he D (D.mapHuber e he he')
    (hs_fwd' e he he' D) (hT_fwd' e he he' D) a

end Value

section RationalOpenHuber

variable [PlusSubring A] [PlusSubring B]
variable (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

/-- Pointwise rational-open transport for the Huber datum transport. -/
theorem mem_rationalOpen_mapHuber_iff
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom)
    (D : RationalLocData A) {v : Spv B} :
    v ∈ rationalOpen (D.mapHuber e he he').T (D.mapHuber e he he').s
      ↔ comap e.toRingHom v ∈ rationalOpen D.T D.s := by
  constructor
  · rintro ⟨hvspa, hvle, hs0⟩
    refine ⟨comap_mem_spa_map e (A⁺ : Subring A) he (hplus ▸ hvspa),
      fun t ht => hvle (e t) (by simp [ht]), fun h0 => hs0 ?_⟩
    simpa using h0
  · rintro ⟨hwspa, hwle, hws0⟩
    refine ⟨?_, fun t' ht' => ?_, fun h0 => hws0 (by simpa using h0)⟩
    · rw [hplus, ← comap_comap_of_ringEquiv e v]
      exact comap_symm_mem_spa_map e (A⁺ : Subring A) he' hwspa
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (by simpa using ht')
      exact hwle t ht

/-- Set-level rational-open transport for the Huber datum transport. -/
theorem rationalOpen_mapHuber_eq_preimage
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom)
    (D : RationalLocData A) :
    rationalOpen (D.mapHuber e he he').T (D.mapHuber e he he').s
      = comap e.toRingHom ⁻¹' rationalOpen D.T D.s :=
  Set.ext fun _ => mem_rationalOpen_mapHuber_iff e he he' hplus D

/-- One-way subset transport for the Huber datum transport. -/
theorem rationalOpen_mapHuber_subset_of_subset
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom)
    (D E : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    rationalOpen (D.mapHuber e he he').T (D.mapHuber e he he').s ⊆
      rationalOpen (E.mapHuber e he he').T (E.mapHuber e he he').s := by
  rw [rationalOpen_mapHuber_eq_preimage e he he' hplus D,
    rationalOpen_mapHuber_eq_preimage e he he' hplus E]
  exact Set.preimage_mono h

end RationalOpenHuber

section RestrictionHuber

variable [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
variable (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

/-- **Restriction-naturality of the Huber value equivalence.** -/
theorem presheafValueRingEquivHuber_restriction
    (D E : RationalLocData A)
    (h : rationalOpen E.T E.s ⊆ rationalOpen D.T D.s)
    (hBsub : rationalOpen (E.mapHuber e he he').T (E.mapHuber e he he').s ⊆
      rationalOpen (D.mapHuber e he he').T (D.mapHuber e he he').s)
    (x : presheafValue D) :
    presheafValueRingEquivHuber e he he' E (restrictionMap D E h x) =
      restrictionMap (D.mapHuber e he he') (E.mapHuber e he he') hBsub
        (presheafValueRingEquivHuber e he he' D x) :=
  presheafValueMapOfHom_restriction e.toRingHom he D E (D.mapHuber e he he')
    (E.mapHuber e he he') (hs_fwd' e he he' D) (hT_fwd' e he he' D)
    (hs_fwd' e he he' E) (hT_fwd' e he he' E) h hBsub x

end RestrictionHuber

section Roundtrip

/-- Extensionality for rational data from the three data fields (`hopen` is a
proposition). -/
theorem RationalLocData.ext' {D₁ D₂ : RationalLocData A}
    (hP : D₁.P = D₂.P) (hT : D₁.T = D₂.T) (hs : D₁.s = D₂.s) : D₁ = D₂ := by
  cases D₁
  cases D₂
  cases hP
  cases hT
  cases hs
  rfl

variable (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

/-- **The Huber datum roundtrip**: forward along `e`, back along `e.symm`. -/
theorem RationalLocData.mapHuber_symm_map [DecidableEq A]
    (D : RationalLocData A) :
    (D.mapHuber e he he').mapHuber e.symm he' he = D := by
  refine RationalLocData.ext' ?_ ?_ ?_
  · exact PairOfDefinition.mapRingEquiv_symm_map e he he' D.P
  · show (D.T.image e).image e.symm = D.T
    rw [Finset.image_image]
    exact (Finset.image_congr fun x _ => e.symm_apply_apply x).trans
      Finset.image_id
  · exact e.symm_apply_apply D.s

/-- **The Huber datum roundtrip, other direction.** -/
theorem RationalLocData.mapHuber_map_symm [DecidableEq A]
    (D : RationalLocData B) :
    (D.mapHuber e.symm he' he).mapHuber e he he' = D := by
  refine RationalLocData.ext' ?_ ?_ ?_
  · exact PairOfDefinition.mapRingEquiv_map_symm e he he' D.P
  · show (D.T.image e.symm).image e = D.T
    rw [Finset.image_image]
    exact (Finset.image_congr fun x _ => e.apply_symm_apply x).trans
      Finset.image_id
  · exact e.apply_symm_apply D.s

end Roundtrip

section RestrictionHuberSymm

variable [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
variable (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

/-- The inverse-direction restriction square of the Huber value equivalence. -/
theorem presheafValueRingEquivHuber_symm_restriction
    (D E : RationalLocData A)
    (h : rationalOpen E.T E.s ⊆ rationalOpen D.T D.s)
    (hBsub : rationalOpen (E.mapHuber e he he').T (E.mapHuber e he he').s ⊆
      rationalOpen (D.mapHuber e he he').T (D.mapHuber e he he').s)
    (y : presheafValue (D.mapHuber e he he')) :
    (presheafValueRingEquivHuber e he he' E).symm
        (restrictionMap (D.mapHuber e he he') (E.mapHuber e he he') hBsub y)
      = restrictionMap D E h
        ((presheafValueRingEquivHuber e he he' D).symm y) := by
  have hsq := presheafValueRingEquivHuber_restriction e he he' D E h hBsub
    ((presheafValueRingEquivHuber e he he' D).symm y)
  rw [RingEquiv.apply_symm_apply] at hsq
  exact (presheafValueRingEquivHuber e he he' E).symm_apply_eq.mpr hsq.symm

end RestrictionHuberSymm

end ValuationSpectrum

end
