/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AffinoidTransport
import «Adic spaces».FaithfulLocLift
import «Adic spaces».PresheafFunctoriality
import «Adic spaces».RationalIntersection
import «Adic spaces».RelativePieceKeystone
import «Adic spaces».StructureSheaf

/-!
# Transport of the rational-localization layer along a bicontinuous ring equivalence

For a bicontinuous ring equivalence `e : A ≃+* B` (an isomorphism of topological
rings), this file transports the *data layer* of the rational-localization
presheaf: pairs of definition, valid rational data, and the completed rational
localizations, together with the exact equivalences (roundtrips) that make the
transports reversible.

Crucially, every datum used by sheafiness carries `D.IsRational`, so in Tate scope
`Ideal.span D.T = ⊤`; the transported datum is reconstructed by `genPieceDatum`
(which supplies `hopen` from the span condition) rather than by transporting an
arbitrary `hopen` proof across the localization equivalence.

Contents (all delivered in this file):

* `PairOfDefinition.mapRingEquiv` (+ `subringMapHomeomorph`, `IsAdic.map_ringEquiv`),
  its two roundtrips `mapRingEquiv_symm_map` / `mapRingEquiv_map_symm`, and the
  packaged equivalence `PairOfDefinition.ringEquivCongr`.
* `RationalLocData.mapRationalRingEquiv` — transport of *valid* rational data —
  with the field simp lemmas (`_P`, `_T`, `_s`), the instance-free membership
  characterization `mem_mapRationalRingEquiv_T`, both roundtrips, and the packaged
  equivalence `validRationalLocDataEquiv : ValidRationalLocData A ≃
  ValidRationalLocData B` (the exact, injective transport that cover
  constructions use through `Finset.map`).
* `presheafValueRingEquivOfRingEquiv` — the completed-localization equivalence
  (with `_continuous`, `_symm_continuous`, `_canonicalMap`).

Downstream (same campaign): rational-open transport, restriction conjugation, the
cover pullback, the product homeomorphism, and the internal `IsSheafy` transport
continue in this file; the public `IsSheafyFor`/`IsSheafyComplete` endpoints
(`isSheafyFor_equiv`, `isSheafyComplete_congr`) live in
`SheafyRingEquivTransport.lean` (they need `SheafyRing.lean`, which sits above
this file in the import graph).

`Finset.image` computations are performed under the file-local scoped `Classical`
instance — no `DecidableEq` binder appears in any signature.
-/

noncomputable section

open Filter Topology

open scoped Classical

namespace ValuationSpectrum

universe u v

/-! ### 2.1 Pair-of-definition transport -/

section Pair

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- A bicontinuous ring equivalence restricts to a homeomorphism between a subring
and its image (subspace topologies). -/
def PairOfDefinition.subringMapHomeomorph (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (s : Subring A) : s ≃ₜ (s.map e.toRingHom) where
  toEquiv := (e.subringMap (s := s)).toEquiv
  continuous_toFun := (he.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (he'.comp continuous_subtype_val).subtype_mk _

/-- **`IsAdic` transports along a bicontinuous ring equivalence.** If the topology
of `R` is `J`-adic then the topology of `S` is `(J.map e)`-adic. -/
theorem _root_.IsAdic.map_ringEquiv {R S : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (e : R ≃+* S)
    (he : Continuous e) (he' : Continuous e.symm) {J : Ideal R} (hJ : IsAdic J) :
    IsAdic (J.map e.toRingHom) := by
  -- powers of the transported ideal are `e.symm`-preimages of the original powers
  have hcoe : ∀ n : ℕ, (J.map e.toRingHom) ^ n = (J ^ n).comap e.symm.toRingHom :=
    fun n ↦ (Ideal.map_pow e.toRingHom J n).symm.trans (Ideal.map_comap_of_equiv e)
  rw [isAdic_iff] at hJ ⊢
  obtain ⟨hopen, hbasis⟩ := hJ
  refine ⟨fun n ↦ hcoe n ▸ (hopen n).preimage he', fun U hU ↦ ?_⟩
  obtain ⟨n, hn⟩ := hbasis (e ⁻¹' U) (he.continuousAt.preimage_mem_nhds (by rwa [map_zero]))
  refine ⟨n, ?_⟩
  rw [hcoe n]
  intro x hx
  simpa using hn hx

/-- **Transport of a pair of definition** along a bicontinuous ring equivalence
(2.1): `A₀ ↦ A₀.map e`, `I ↦ I.map (e.subringMap)`. -/
def PairOfDefinition.mapRingEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (P : PairOfDefinition A) : PairOfDefinition B where
  A₀ := P.A₀.map e.toRingHom
  I := P.I.map (e.subringMap (s := P.A₀)).toRingHom
  isOpen := IsOpenMap.of_inverse he' e.apply_symm_apply e.symm_apply_apply _ P.isOpen
  fg := P.fg.map _
  isAdic :=
    -- transport `IsAdic P.I` on `↥P.A₀` to `↥(P.A₀.map e)` via the subring homeomorph
    let h := subringMapHomeomorph e he he' P.A₀
    IsAdic.map_ringEquiv (e.subringMap (s := P.A₀)) h.continuous_toFun h.continuous_invFun
      P.isAdic

@[simp] theorem PairOfDefinition.mapRingEquiv_A₀ (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (P : PairOfDefinition A) :
    (PairOfDefinition.mapRingEquiv e he he' P).A₀ = P.A₀.map e.toRingHom := rfl

/-! #### The pair roundtrips (T1) -/

omit [IsTopologicalRing A] in
/-- Extensionality for `PairOfDefinition` from the two data fields (the other
fields are propositions); the ideal is compared as a `HEq` across the subring
equality. -/
theorem PairOfDefinition.ext_of_fields {P₁ P₂ : PairOfDefinition A} (hA : P₁.A₀ = P₂.A₀)
    (hI : HEq P₁.I P₂.I) : P₁ = P₂ := by
  cases P₁
  cases P₂
  subst hA
  obtain rfl := eq_of_heq hI
  rfl

omit [TopologicalSpace A] [IsTopologicalRing A] in
-- Mapping an ideal along a coercion-fixing hom between equal subrings is the identity, as a
-- `HEq` across the subring equality (the dependent-ideal collapse used by the pair roundtrips).
private theorem ideal_map_heq_of_coe_fix {S S' : Subring A} (h : S' = S) (φ : S →+* S')
    (hφ : ∀ x : S, ((φ x : S') : A) = (x : A)) (I : Ideal S) : HEq (I.map φ) I := by
  subst h
  rw [show φ = RingHom.id _ from RingHom.ext fun x ↦ Subtype.ext (hφ x), Ideal.map_id]

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
/-- The subring roundtrip: mapping forward along `e` and back along `e.symm`
recovers the subring. -/
theorem PairOfDefinition.subring_map_symm_map (e : A ≃+* B) (s : Subring A) :
    (s.map e.toRingHom).map e.symm.toRingHom = s :=
  SetLike.coe_injective (e.toEquiv.symm_image_image s)

/-- **The pair roundtrip** (T1): transporting a pair of definition forward along
`e` and back along `e.symm` recovers the pair. The subrings agree by the map
roundtrip; the dependent ideals agree because the composite restricted ring
equivalence fixes the ambient coercion. -/
theorem PairOfDefinition.mapRingEquiv_symm_map (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (P : PairOfDefinition A) :
    PairOfDefinition.mapRingEquiv e.symm he' he (PairOfDefinition.mapRingEquiv e he he' P) = P := by
  refine PairOfDefinition.ext_of_fields (PairOfDefinition.subring_map_symm_map e P.A₀) ?_
  change HEq ((P.I.map (e.subringMap (s := P.A₀)).toRingHom).map
    (e.symm.subringMap (s := P.A₀.map e.toRingHom)).toRingHom) P.I
  rw [Ideal.map_map]
  exact ideal_map_heq_of_coe_fix (PairOfDefinition.subring_map_symm_map e P.A₀)
    _ (fun x ↦ e.symm_apply_apply (x : A)) P.I

/-- **The pair roundtrip, other direction** (T1). -/
theorem PairOfDefinition.mapRingEquiv_map_symm (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (Q : PairOfDefinition B) :
    PairOfDefinition.mapRingEquiv e he he' (PairOfDefinition.mapRingEquiv e.symm he' he Q) = Q := by
  refine PairOfDefinition.ext_of_fields (PairOfDefinition.subring_map_symm_map e.symm Q.A₀) ?_
  change HEq ((Q.I.map (e.symm.subringMap (s := Q.A₀)).toRingHom).map
    (e.subringMap (s := Q.A₀.map e.symm.toRingHom)).toRingHom) Q.I
  rw [Ideal.map_map]
  exact ideal_map_heq_of_coe_fix (PairOfDefinition.subring_map_symm_map e.symm Q.A₀)
    _ (fun x ↦ e.apply_symm_apply (x : B)) Q.I

/-- **Pairs of definition as an actual equivalence** (T1): a bicontinuous ring
equivalence induces an equivalence of the types of pairs of definition. -/
def PairOfDefinition.ringEquivCongr (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    PairOfDefinition A ≃ PairOfDefinition B where
  toFun := PairOfDefinition.mapRingEquiv e he he'
  invFun := PairOfDefinition.mapRingEquiv e.symm he' he
  left_inv := PairOfDefinition.mapRingEquiv_symm_map e he he'
  right_inv := PairOfDefinition.mapRingEquiv_map_symm e he he'

@[simp] theorem PairOfDefinition.ringEquivCongr_apply (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (P : PairOfDefinition A) :
    PairOfDefinition.ringEquivCongr e he he' P = PairOfDefinition.mapRingEquiv e he he' P := rfl

@[simp] theorem PairOfDefinition.ringEquivCongr_symm_apply (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (Q : PairOfDefinition B) :
    (PairOfDefinition.ringEquivCongr e he he').symm Q =
      PairOfDefinition.mapRingEquiv e.symm he' he Q := rfl

end Pair

/-! ### 2.2 Transport of valid rational data (reconstructed via `genPieceDatum`) -/

/-- The image of a spanning family spans (pure algebra; stated once with the
file-local classical `Finset.image`). -/
theorem span_image_eq_top_of_ringEquiv {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) {T : Finset A} (h : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image e : Finset B) : Set B) = ⊤ := by
  simpa [Ideal.map_span, Ideal.map_top] using congrArg (Ideal.map e.toRingHom) h

section Datum

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- **Transport of a valid rational datum** (2.2): reconstruct via `genPieceDatum`
from the transported pair `D.P.mapRingEquiv e`, numerators `D.T.image e`, denominator
`e D.s`, and the transported span condition. No `hopen` is transported across the
localization equivalence — `genPieceDatum` supplies it from the span. -/
def RationalLocData.mapRationalRingEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) (hD : D.IsRational) : RationalLocData B :=
  genPieceDatum (PairOfDefinition.mapRingEquiv e he he' D.P) (D.T.image e) (e D.s)
    (span_image_eq_top_of_ringEquiv e hD.span_eq_top)

@[simp] theorem mapRationalRingEquiv_P (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) (hD : D.IsRational) :
    (D.mapRationalRingEquiv e he he' hD).P = PairOfDefinition.mapRingEquiv e he he' D.P := rfl

@[simp] theorem mapRationalRingEquiv_T (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) (hD : D.IsRational) :
    (D.mapRationalRingEquiv e he he' hD).T = D.T.image e := rfl

@[simp] theorem mapRationalRingEquiv_s (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) (hD : D.IsRational) :
    (D.mapRationalRingEquiv e he he' hD).s = e D.s := rfl

/-- Instance-free membership characterization of the transported numerator family:
`b` is a transported numerator iff `e.symm b` is an original one. -/
theorem mem_mapRationalRingEquiv_T (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) (hD : D.IsRational) {b : B} :
    b ∈ (D.mapRationalRingEquiv e he he' hD).T ↔ e.symm b ∈ D.T := by
  simp [← RingEquiv.eq_symm_apply]

/-- The transported datum is rational (its numerator family spans). -/
theorem mapRationalRingEquiv_isRational (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) (hD : D.IsRational) : (D.mapRationalRingEquiv e he he' hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top (span_image_eq_top_of_ringEquiv e hD.span_eq_top)

end Datum

/-! ### 2.3 The valid-datum roundtrips and the exact equivalence (T1) -/

section ValidData

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A **valid rational localization datum**: a `RationalLocData` bundled with
Wedhorn Definition 7.29's openness condition. The sheafiness layer quantifies over
exactly these; bundling makes the ring-equivalence transport an *equivalence* of
types (`validRationalLocDataEquiv`), which is what supplies the injectivity needed
by exact (`Finset.map`) cover transport. -/
abbrev ValidRationalLocData : Type _ := {D : RationalLocData A // D.IsRational}

end ValidData

section Roundtrip

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTateRing B]

omit [TopologicalSpace A] [IsTateRing A] [TopologicalSpace B] [IsTateRing B] in
/-- The `Finset.image` roundtrip along a ring equivalence. -/
theorem finset_symm_image_image (e : A ≃+* B) (T : Finset A) : (T.image e).image e.symm = T := by
  simp [Finset.image_image, Function.comp_def]

/-- **The valid-datum roundtrip** (T1): transporting forward along `e` and back
along `e.symm` recovers the datum — fieldwise, via the pair roundtrip, the
`Finset.image` roundtrip, and the inverse law of `e` (`hopen` and the validity
proofs disappear by proof irrelevance). -/
theorem RationalLocData.mapRationalRingEquiv_symm_map (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (D : RationalLocData A) (hD : D.IsRational)
    (hD' : (D.mapRationalRingEquiv e he he' hD).IsRational) :
    (D.mapRationalRingEquiv e he he' hD).mapRationalRingEquiv e.symm he' he hD' = D :=
  RationalLocData.ext_of_fields (PairOfDefinition.mapRingEquiv_symm_map e he he' D.P)
    (finset_symm_image_image e D.T) (e.symm_apply_apply D.s)

/-- **The valid-datum roundtrip, other direction** (T1). -/
theorem RationalLocData.mapRationalRingEquiv_map_symm (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (E : RationalLocData B) (hE : E.IsRational)
    (hE' : (E.mapRationalRingEquiv e.symm he' he hE).IsRational) :
    (E.mapRationalRingEquiv e.symm he' he hE).mapRationalRingEquiv e he he' hE' = E :=
  RationalLocData.ext_of_fields (PairOfDefinition.mapRingEquiv_map_symm e he he' E.P)
    (finset_symm_image_image e.symm E.T) (e.apply_symm_apply E.s)

variable (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

/-- **Valid rational data as an actual equivalence** (T1): a bicontinuous ring
equivalence induces an equivalence of the types of valid rational localization
data. This is the exact (choice-free, injective) transport that cover
constructions consume through `Finset.map` — never a bare `Finset.image`. -/
def validRationalLocDataEquiv : ValidRationalLocData A ≃ ValidRationalLocData B where
  toFun D := ⟨D.1.mapRationalRingEquiv e he he' D.2,
    mapRationalRingEquiv_isRational e he he' D.1 D.2⟩
  invFun E := ⟨E.1.mapRationalRingEquiv e.symm he' he E.2,
    mapRationalRingEquiv_isRational e.symm he' he E.1 E.2⟩
  left_inv D := Subtype.ext (D.1.mapRationalRingEquiv_symm_map e he he' D.2
    (mapRationalRingEquiv_isRational e he he' D.1 D.2))
  right_inv E := Subtype.ext (E.1.mapRationalRingEquiv_map_symm e he he' E.2
    (mapRationalRingEquiv_isRational e.symm he' he E.1 E.2))

@[simp] theorem validRationalLocDataEquiv_apply_coe (D : ValidRationalLocData A) :
    (validRationalLocDataEquiv e he he' D).1 = D.1.mapRationalRingEquiv e he he' D.2 := rfl

@[simp] theorem validRationalLocDataEquiv_symm_apply_coe (E : ValidRationalLocData B) :
    ((validRationalLocDataEquiv e he he').symm E).1 =
      E.1.mapRationalRingEquiv e.symm he' he E.2 := rfl

end Roundtrip

/-! ### 2.3½ Rational-open transport (T2) -/

section RationalOpen

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [PlusSubring A] [PlusSubring B]
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

omit [TopologicalSpace A] [IsTateRing A] [TopologicalSpace B] [IsTopologicalRing B] in
/-- Corresponding plus rings, read in the other direction: if `B⁺` is the image
of `A⁺` then `A⁺` is the image of `B⁺` under the inverse. -/
theorem ringPlus_map_symm_of_map (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) :
    (A⁺ : Subring A) = (B⁺ : Subring B).map e.symm.toRingHom :=
  hplus ▸ (PairOfDefinition.subring_map_symm_map e (A⁺ : Subring A)).symm

/-- **Pointwise rational-open transport** (T2): for corresponding plus rings, an
upstairs valuation lies in the transported rational open `R(e(T)/e(s))` of
`Spa (B, e(A⁺))` iff its pull-back lies in `R(T/s)` of `Spa (A, A⁺)`. For a
bicontinuous ring equivalence no auxiliary `Spa`-membership hypothesis is needed
(compare the one-sided FJP `mem_rationalOpen_pushDatumC_iff`). -/
theorem mem_rationalOpen_mapRationalRingEquiv_iff
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) (D : RationalLocData A)
    (hD : D.IsRational) {v : Spv B} :
    v ∈ rationalOpen (D.mapRationalRingEquiv e he he' hD).T
        (D.mapRationalRingEquiv e he he' hD).s ↔ comap e.toRingHom v ∈ rationalOpen D.T D.s := by
  constructor
  · rintro ⟨hvspa, hvle, hs0⟩
    refine ⟨comap_mem_spa_map e (A⁺ : Subring A) he (hplus ▸ hvspa),
      fun t ht ↦ hvle (e t) (by simp [ht]), fun h0 ↦ hs0 ?_⟩
    simpa using h0
  · rintro ⟨hwspa, hwle, hws0⟩
    refine ⟨?_, fun t' ht' ↦ ?_, fun h0 ↦ hws0 (by simpa using h0)⟩
    · rw [hplus, ← comap_comap_of_ringEquiv e v]
      exact comap_symm_mem_spa_map e (A⁺ : Subring A) he' hwspa
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (by simpa using ht')
      exact hwle t ht

/-- **Set-level rational-open transport** (T2): the transported rational open is
the `comap`-preimage of the original one. -/
theorem rationalOpen_mapRationalRingEquiv_eq_preimage
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) (D : RationalLocData A)
    (hD : D.IsRational) :
    rationalOpen (D.mapRationalRingEquiv e he he' hD).T (D.mapRationalRingEquiv e he he' hD).s =
      comap e.toRingHom ⁻¹' rationalOpen D.T D.s :=
  Set.ext fun _ ↦ mem_rationalOpen_mapRationalRingEquiv_iff e he he' hplus D hD

/-- **Subset transport** (T2): containment of transported rational opens is
equivalent to containment of the originals. -/
theorem rationalOpen_mapRationalRingEquiv_subset_iff
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) (D : RationalLocData A)
    (hD : D.IsRational) (E : RationalLocData A) (hE : E.IsRational) :
    rationalOpen (D.mapRationalRingEquiv e he he' hD).T (D.mapRationalRingEquiv e he he' hD).s ⊆
      rationalOpen (E.mapRationalRingEquiv e he he' hE).T (E.mapRationalRingEquiv e he he' hE).s ↔
      rationalOpen D.T D.s ⊆ rationalOpen E.T E.s := by
  rw [rationalOpen_mapRationalRingEquiv_eq_preimage e he he' hplus D hD,
    rationalOpen_mapRationalRingEquiv_eq_preimage e he he' hplus E hE]
  exact Function.Surjective.preimage_subset_preimage_iff
    fun w ↦ ⟨comap e.symm.toRingHom w, comap_symm_comap_of_ringEquiv e w⟩

/-- One-way subset transport, downstairs to upstairs (the direction cover
constructions consume). -/
theorem rationalOpen_mapRationalRingEquiv_subset_of_subset
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) (D : RationalLocData A)
    (hD : D.IsRational) (E : RationalLocData A) (hE : E.IsRational)
    (h : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    rationalOpen (D.mapRationalRingEquiv e he he' hD).T (D.mapRationalRingEquiv e he he' hD).s ⊆
      rationalOpen (E.mapRationalRingEquiv e he he' hE).T (E.mapRationalRingEquiv e he he' hE).s :=
  (rationalOpen_mapRationalRingEquiv_subset_iff e he he' hplus D hD E hE).mpr h

end RationalOpen

/-! ### 2.4 The completed rational-localization equivalence -/

section PresheafValue

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
  (D : RationalLocData A) (hD : D.IsRational)

-- The forward denominator obligation of `presheafValueMapOfHom` along `e`.
private theorem hs_fwd : (D.mapRationalRingEquiv e he he' hD).s = e.toRingHom D.s := rfl

-- The backward denominator obligation of `presheafValueMapOfHom` along `e.symm`.
private theorem hs_bwd : D.s = e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD).s :=
  (e.symm_apply_apply D.s).symm

-- The forward numerator-containment obligation of `presheafValueMapOfHom` along `e`.
private theorem hT_fwd : ∀ t ∈ D.T, e.toRingHom t ∈ (D.mapRationalRingEquiv e he he' hD).T :=
  fun _ ht ↦ Finset.mem_image_of_mem _ ht

-- The backward numerator-containment obligation of `presheafValueMapOfHom` along `e.symm`.
private theorem hT_bwd : ∀ t ∈ (D.mapRationalRingEquiv e he he' hD).T, e.symm.toRingHom t ∈ D.T :=
  fun _ ht ↦ (mem_mapRationalRingEquiv_T e he he' D hD).mp ht

-- The forward completed covariant map `𝒪(D) →+* 𝒪(D')`.
private def pvFwd : presheafValue D →+* presheafValue (D.mapRationalRingEquiv e he he' hD) :=
  presheafValueMapOfHom e.toRingHom he D (D.mapRationalRingEquiv e he he' hD)
    (hs_fwd e he he' D hD) (hT_fwd e he he' D hD)

-- The backward completed covariant map `𝒪(D') →+* 𝒪(D)`.
private def pvBwd : presheafValue (D.mapRationalRingEquiv e he he' hD) →+* presheafValue D :=
  presheafValueMapOfHom e.symm.toRingHom he' (D.mapRationalRingEquiv e he he' hD) D
    (hs_bwd e he he' D hD) (hT_bwd e he he' D hD)

private theorem pvFwd_continuous : Continuous (pvFwd e he he' D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

private theorem pvBwd_continuous : Continuous (pvBwd e he he' D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

-- The forward map on the localization image.
private theorem pvFwd_coe (l : Localization.Away D.s) : pvFwd e he he' D hD (D.coeRingHom l) =
    (D.mapRationalRingEquiv e he he' hD).coeRingHom
      (locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD) (hs_fwd e he he' D hD) l) :=
  presheafValueMapOfHom_coe e.toRingHom he D (D.mapRationalRingEquiv e he he' hD)
    (hs_fwd e he he' D hD) (hT_fwd e he he' D hD) l

-- The backward map on the localization image.
private theorem pvBwd_coe (l : Localization.Away (D.mapRationalRingEquiv e he he' hD).s) :
    pvBwd e he he' D hD ((D.mapRationalRingEquiv e he he' hD).coeRingHom l) =
      D.coeRingHom (locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D
        (hs_bwd e he he' D hD) l) :=
  presheafValueMapOfHom_coe e.symm.toRingHom he' (D.mapRationalRingEquiv e he he' hD) D
    (hs_bwd e he he' D hD) (hT_bwd e he he' D hD) l

-- Generic localization-level roundtrip: `locMapOfHom` along a hom followed by
-- `locMapOfHom` along a one-sided inverse is the identity (the shared engine
-- for the two directions below).
private theorem locMapOfHom_roundtrip {R : Type*} {S : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] (f : R →+* S) (g : S →+* R) (hgf : ∀ a, g (f a) = a)
    (DR : RationalLocData R) (DS : RationalLocData S) (hs : DS.s = f DR.s)
    (hs' : DR.s = g DS.s) (l : Localization.Away DR.s) :
    locMapOfHom g DS DR hs' (locMapOfHom f DR DS hs l) = l := by
  have hid : (locMapOfHom g DS DR hs').comp (locMapOfHom f DR DS hs) =
      RingHom.id (Localization.Away DR.s) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers DR.s) (RingHom.ext fun a ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.id_comp, locMapOfHom_algebraMap]
    exact congrArg _ (hgf a)
  exact DFunLike.congr_fun hid l

-- The localization-level composite (forward then backward) is the identity.
private theorem locMap_roundtrip (l : Localization.Away D.s) :
    locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D (hs_bwd e he he' D hD)
      (locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD)
        (hs_fwd e he he' D hD) l) = l :=
  locMapOfHom_roundtrip e.toRingHom e.symm.toRingHom e.symm_apply_apply D
    (D.mapRationalRingEquiv e he he' hD) (hs_fwd e he he' D hD) (hs_bwd e he he' D hD) l

-- The localization-level composite (backward then forward) is the identity.
private theorem locMap_roundtrip_symm
    (l : Localization.Away (D.mapRationalRingEquiv e he he' hD).s) :
    locMapOfHom e.toRingHom D (D.mapRationalRingEquiv e he he' hD) (hs_fwd e he he' D hD)
      (locMapOfHom e.symm.toRingHom (D.mapRationalRingEquiv e he he' hD) D
        (hs_bwd e he he' D hD) l) = l :=
  locMapOfHom_roundtrip e.symm.toRingHom e.toRingHom e.apply_symm_apply
    (D.mapRationalRingEquiv e he he' hD) D (hs_bwd e he he' D hD) (hs_fwd e he he' D hD) l

-- A continuous self-map of a completed localization agreeing with the identity
-- on the dense localization image is the identity (the shared dense-extension
-- uniqueness engine for the two inverse-law fields below).
private theorem presheafValue_eq_id_of_coeRingHom {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (E : RationalLocData R)
    {F : presheafValue E → presheafValue E} (hF : Continuous F)
    (h : ∀ l, F (E.coeRingHom l) = E.coeRingHom l) (x : presheafValue E) : F x = x := by
  have hdense : DenseRange (⇑(E.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ E.uniformSpace
  exact congr_fun (hdense.equalizer hF continuous_id (funext h)) x

/-- **The completed rational-localization equivalence** (2.4): for a bicontinuous ring
equivalence `e` and a valid rational datum `D`, the completed localizations are
canonically bicontinuously isomorphic. -/
noncomputable def presheafValueRingEquivOfRingEquiv :
    presheafValue D ≃+* presheafValue (D.mapRationalRingEquiv e he he' hD) where
  toFun := pvFwd e he he' D hD
  invFun := pvBwd e he he' D hD
  left_inv x :=
    presheafValue_eq_id_of_coeRingHom D
      ((pvBwd_continuous e he he' D hD).comp (pvFwd_continuous e he he' D hD))
      (fun l ↦ by
        show pvBwd e he he' D hD (pvFwd e he he' D hD (D.coeRingHom l)) = D.coeRingHom l
        rw [pvFwd_coe, pvBwd_coe, locMap_roundtrip]) x
  right_inv y :=
    presheafValue_eq_id_of_coeRingHom (D.mapRationalRingEquiv e he he' hD)
      ((pvFwd_continuous e he he' D hD).comp (pvBwd_continuous e he he' D hD))
      (fun l ↦ by
        show pvFwd e he he' D hD (pvBwd e he he' D hD
          ((D.mapRationalRingEquiv e he he' hD).coeRingHom l)) =
          (D.mapRationalRingEquiv e he he' hD).coeRingHom l
        rw [pvBwd_coe, pvFwd_coe, locMap_roundtrip_symm]) y
  map_mul' := map_mul _
  map_add' := map_add _

/-- The completed rational-localization equivalence is continuous. -/
theorem presheafValueRingEquivOfRingEquiv_continuous :
    Continuous (presheafValueRingEquivOfRingEquiv e he he' D hD) := pvFwd_continuous e he he' D hD

/-- The inverse of the completed rational-localization equivalence is continuous. -/
theorem presheafValueRingEquivOfRingEquiv_symm_continuous :
    Continuous (presheafValueRingEquivOfRingEquiv e he he' D hD).symm :=
  pvBwd_continuous e he he' D hD

/-- The equivalence intertwines the canonical maps from `A`/`B`. -/
theorem presheafValueRingEquivOfRingEquiv_canonicalMap (a : A) :
    presheafValueRingEquivOfRingEquiv e he he' D hD (D.canonicalMap a) =
      (D.mapRationalRingEquiv e he he' hD).canonicalMap (e a) :=
  presheafValueMapOfHom_canonicalMap e.toRingHom he D (D.mapRationalRingEquiv e he he' hD)
    (hs_fwd e he he' D hD) (hT_fwd e he he' D hD) a

/-- **The completed rational-localization homeomorphism** (T3): the bundled
topological form of `presheafValueRingEquivOfRingEquiv`. -/
noncomputable def presheafValueHomeomorphOfRingEquiv :
    presheafValue D ≃ₜ presheafValue (D.mapRationalRingEquiv e he he' hD) where
  toEquiv := (presheafValueRingEquivOfRingEquiv e he he' D hD).toEquiv
  continuous_toFun := presheafValueRingEquivOfRingEquiv_continuous e he he' D hD
  continuous_invFun := presheafValueRingEquivOfRingEquiv_symm_continuous e he he' D hD

@[simp] theorem presheafValueHomeomorphOfRingEquiv_apply (x : presheafValue D) :
    presheafValueHomeomorphOfRingEquiv e he he' D hD x =
      presheafValueRingEquivOfRingEquiv e he he' D hD x := rfl

@[simp] theorem presheafValueHomeomorphOfRingEquiv_symm_apply
    (y : presheafValue (D.mapRationalRingEquiv e he he' hD)) :
    (presheafValueHomeomorphOfRingEquiv e he he' D hD).symm y =
      (presheafValueRingEquivOfRingEquiv e he he' D hD).symm y := rfl

end PresheafValue

/-! ### 2.5 Restriction conjugation (T3) -/

section Restriction

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [PlusSubring A] [HasLocLiftPowerBounded A]
  [CommRing B] [TopologicalSpace B] [IsHuberRing B] [PlusSubring B]
  [HasLocLiftPowerBounded B]
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

/-- **The restriction conjugation square** (T3): the completed-localization
equivalence commutes with restriction maps — for valid `D`, `E` with
`R(E) ⊆ R(D)` (and the transported containment), the square

    O(D)  ─────────────→ O(eD)
     │ restriction          │ restriction
     ▼                      ▼
    O(E)  ─────────────→ O(eE)

commutes. Direct specialization of `presheafValueMapOfHom_restriction`. -/
theorem presheafValueRingEquivOfRingEquiv_restriction (D : RationalLocData A) (hD : D.IsRational)
    (E : RationalLocData A) (hE : E.IsRational) (h : rationalOpen E.T E.s ⊆ rationalOpen D.T D.s)
    (hBsub : rationalOpen (E.mapRationalRingEquiv e he he' hE).T
        (E.mapRationalRingEquiv e he he' hE).s ⊆
      rationalOpen (D.mapRationalRingEquiv e he he' hD).T (D.mapRationalRingEquiv e he he' hD).s)
    (x : presheafValue D) :
    presheafValueRingEquivOfRingEquiv e he he' E hE (restrictionMap D E h x) =
      restrictionMap (D.mapRationalRingEquiv e he he' hD) (E.mapRationalRingEquiv e he he' hE) hBsub
        (presheafValueRingEquivOfRingEquiv e he he' D hD x) :=
  presheafValueMapOfHom_restriction e.toRingHom he D E (D.mapRationalRingEquiv e he he' hD)
    (E.mapRationalRingEquiv e he he' hE) (hs_fwd e he he' D hD) (hT_fwd e he he' D hD)
    (hs_fwd e he he' E hE) (hT_fwd e he he' E hE) h hBsub x

/-- The inverse-direction restriction square (T3, corollary). -/
theorem presheafValueRingEquivOfRingEquiv_symm_restriction
    (D : RationalLocData A) (hD : D.IsRational) (E : RationalLocData A) (hE : E.IsRational)
    (h : rationalOpen E.T E.s ⊆ rationalOpen D.T D.s)
    (hBsub : rationalOpen (E.mapRationalRingEquiv e he he' hE).T
        (E.mapRationalRingEquiv e he he' hE).s ⊆
      rationalOpen (D.mapRationalRingEquiv e he he' hD).T (D.mapRationalRingEquiv e he he' hD).s)
    (y : presheafValue (D.mapRationalRingEquiv e he he' hD)) :
    (presheafValueRingEquivOfRingEquiv e he he' E hE).symm
        (restrictionMap (D.mapRationalRingEquiv e he he' hD)
          (E.mapRationalRingEquiv e he he' hE) hBsub y) = restrictionMap D E h
        ((presheafValueRingEquivOfRingEquiv e he he' D hD).symm y) := by
  have hsq := presheafValueRingEquivOfRingEquiv_restriction e he he' D hD E hE h hBsub
    ((presheafValueRingEquivOfRingEquiv e he he' D hD).symm y)
  rw [RingEquiv.apply_symm_apply] at hsq
  exact (presheafValueRingEquivOfRingEquiv e he he' E hE).symm_apply_eq.mpr hsq.symm

end Restriction

/-! ### 2.6 Pulling back a valid cover with an exact index equivalence (T4) -/

section Pullback

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTateRing B]
  [PlusSubring A] [PlusSubring B]
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)

/-- The **piece embedding** of a valid cover over `B` into the rational data of
`A`: each piece is pulled back through (the inverse of) `validRationalLocDataEquiv`.
Injectivity comes from the equivalence — this is the exact transport that
`Finset.map` requires (never a bare `Finset.image`). -/
def RationalCoveringData.pullbackPieceEmbedding (C : RationalCoveringData B) (hC : C.IsRational) :
    {D // D ∈ C.covers} ↪ RationalLocData A where
  toFun D := D.1.mapRationalRingEquiv e.symm he' he (hC.piece D.2)
  inj' D₁ D₂ hDD := Subtype.ext <| congrArg (α := ValidRationalLocData B) Subtype.val <|
    (validRationalLocDataEquiv e he he').symm.injective
      (Subtype.ext hDD :
        (validRationalLocDataEquiv e he he').symm ⟨D₁.1, hC.piece D₁.2⟩ =
        (validRationalLocDataEquiv e he he').symm ⟨D₂.1, hC.piece D₂.2⟩)

omit [PlusSubring A] in
@[simp] theorem RationalCoveringData.pullbackPieceEmbedding_apply (C : RationalCoveringData B)
    (hC : C.IsRational) (D : {D // D ∈ C.covers}) :
    C.pullbackPieceEmbedding e he he' hC D =
      D.1.mapRationalRingEquiv e.symm he' he (hC.piece D.2) := rfl

/-- **Pull back a valid cover along a bicontinuous ring equivalence** (T4): the
base and the pieces are pulled back through `validRationalLocDataEquiv`; the
subordination and covering conditions transport through the pointwise
rational-open correspondence (T2). The pieces are indexed *exactly* — by
`C.covers.attach.map` of an embedding — so the cover has a genuine index
equivalence (`pullbackIndexEquiv`) with no choice and no collapsing. -/
def RationalCoveringData.pullbackRingEquiv (C : RationalCoveringData B) (hC : C.IsRational)
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) : RationalCoveringData A where
  base := C.base.mapRationalRingEquiv e.symm he' he hC.base
  covers := C.covers.attach.map (C.pullbackPieceEmbedding e he he' hC)
  hsubset := by
    intro D' hD'
    obtain ⟨D₀, -, rfl⟩ := Finset.mem_map.mp hD'
    exact rationalOpen_mapRationalRingEquiv_subset_of_subset e.symm he' he
      (ringPlus_map_symm_of_map e hplus) D₀.1 (hC.piece D₀.2) C.base hC.base
      (C.hsubset D₀.1 D₀.2)
  hcover := by
    intro v hv
    obtain ⟨D₀, hD₀, hvD₀⟩ := C.hcover _ ((mem_rationalOpen_mapRationalRingEquiv_iff e.symm he'
      he (ringPlus_map_symm_of_map e hplus) C.base hC.base).mp hv)
    refine ⟨C.pullbackPieceEmbedding e he he' hC ⟨D₀, hD₀⟩,
      Finset.mem_map_of_mem _ (Finset.mem_attach _ _), ?_⟩
    exact (mem_rationalOpen_mapRationalRingEquiv_iff e.symm he' he
      (ringPlus_map_symm_of_map e hplus) D₀ (hC.piece hD₀)).mpr hvD₀

variable (C : RationalCoveringData B) (hC : C.IsRational)
  (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom)

@[simp] theorem RationalCoveringData.pullbackRingEquiv_base :
    (C.pullbackRingEquiv e he he' hC hplus).base =
      C.base.mapRationalRingEquiv e.symm he' he hC.base := rfl

@[simp] theorem RationalCoveringData.pullbackRingEquiv_covers :
    (C.pullbackRingEquiv e he he' hC hplus).covers =
      C.covers.attach.map (C.pullbackPieceEmbedding e he he' hC) := rfl

/-- Every piece of the pulled-back cover is valid. -/
theorem RationalCoveringData.pullbackRingEquiv_covers_isRational {D' : RationalLocData A}
    (hD' : D' ∈ (C.pullbackRingEquiv e he he' hC hplus).covers) : D'.IsRational := by
  obtain ⟨D₀, -, rfl⟩ := Finset.mem_map.mp hD'
  exact mapRationalRingEquiv_isRational e.symm he' he D₀.1 (hC.piece D₀.2)

/-- **The pulled-back cover is rational** (T4). -/
theorem RationalCoveringData.pullbackRingEquiv_isRational :
    (C.pullbackRingEquiv e he he' hC hplus).IsRational :=
  ⟨mapRationalRingEquiv_isRational e.symm he' he C.base hC.base,
   fun _ ↦ C.pullbackRingEquiv_covers_isRational e he he' hC hplus⟩

/-- **The exact index equivalence of the pulled-back cover** (T4): the pieces of
`C` and of its pullback are in canonical bijection — choice-free in the function
values (only membership/validity proofs are recovered from `Finset.mem_map`). -/
def RationalCoveringData.pullbackIndexEquiv :
    ↥C.covers ≃ ↥(C.pullbackRingEquiv e he he' hC hplus).covers where
  toFun D := ⟨D.1.mapRationalRingEquiv e.symm he' he (hC.piece D.2),
    Finset.mem_map_of_mem (C.pullbackPieceEmbedding e he he' hC) (Finset.mem_attach _ D)⟩
  invFun D' := ⟨((validRationalLocDataEquiv e he he')
      ⟨D'.1, C.pullbackRingEquiv_covers_isRational e he he' hC hplus D'.2⟩).1, by
    obtain ⟨D₀, -, hval⟩ := Finset.mem_map.mp D'.2
    have hvalid : (⟨D'.1, C.pullbackRingEquiv_covers_isRational e he he' hC hplus D'.2⟩ :
        ValidRationalLocData A) =
        (validRationalLocDataEquiv e he he').symm ⟨D₀.1, hC.piece D₀.2⟩ :=
      Subtype.ext hval.symm
    rw [hvalid, Equiv.apply_symm_apply]
    exact D₀.2⟩
  left_inv D := Subtype.ext
    (RationalLocData.mapRationalRingEquiv_map_symm e he he' D.1 (hC.piece D.2)
      (mapRationalRingEquiv_isRational e.symm he' he D.1 (hC.piece D.2)))
  right_inv D' := Subtype.ext
    (RationalLocData.mapRationalRingEquiv_symm_map e he he' D'.1
      (C.pullbackRingEquiv_covers_isRational e he he' hC hplus D'.2)
      (mapRationalRingEquiv_isRational e he he' D'.1
        (C.pullbackRingEquiv_covers_isRational e he he' hC hplus D'.2)))

/-- The underlying datum of a forward-transported index (T4 simp interface). -/
@[simp] theorem RationalCoveringData.pullbackIndexEquiv_val (D : ↥C.covers) :
    ((C.pullbackIndexEquiv e he he' hC hplus D :
        ↥(C.pullbackRingEquiv e he he' hC hplus).covers) : RationalLocData A) =
      D.1.mapRationalRingEquiv e.symm he' he (hC.piece D.2) := rfl

/-- The underlying datum of a backward-transported index (T4 simp interface). -/
@[simp] theorem RationalCoveringData.pullbackIndexEquiv_symm_val
    (D' : ↥(C.pullbackRingEquiv e he he' hC hplus).covers) :
    (((C.pullbackIndexEquiv e he he' hC hplus).symm D' : ↥C.covers) : RationalLocData B) =
      D'.1.mapRationalRingEquiv e he he'
        (C.pullbackRingEquiv_covers_isRational e he he' hC hplus D'.2) := rfl

end Pullback

/-! ### 2.7 The product homeomorphism and the central conjugation square (T5) -/

section ProductConj

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [PlusSubring A] [HasLocLiftPowerBounded A]
  [CommRing B] [TopologicalSpace B] [IsTateRing B] [PlusSubring B]
  [HasLocLiftPowerBounded B]
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
  (C : RationalCoveringData B) (hC : C.IsRational)
  (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom)

/-- **The product-of-sections homeomorphism** (T5): `Homeomorph.piCongr` along
the exact index equivalence of the pulled-back cover, with the per-piece
completed localization homeomorphisms in the fibers. -/
noncomputable def RationalCoveringData.productSectionsHomeomorph :
    (∀ D : ↥C.covers, presheafValue D.1) ≃ₜ
      (∀ D' : ↥(C.pullbackRingEquiv e he he' hC hplus).covers, presheafValue D'.1) :=
  Homeomorph.piCongr (C.pullbackIndexEquiv e he he' hC hplus) fun D ↦
    presheafValueHomeomorphOfRingEquiv e.symm he' he D.1 (hC.piece D.2)

omit [HasLocLiftPowerBounded A] [HasLocLiftPowerBounded B] in
/-- Evaluation of the product homeomorphism at a forward-transported index: no
cast appears because the index equivalence's value is definitionally the
transported datum. -/
theorem RationalCoveringData.productSectionsHomeomorph_apply_index
    (f : ∀ D : ↥C.covers, presheafValue D.1) (D : ↥C.covers) :
    C.productSectionsHomeomorph e he he' hC hplus f (C.pullbackIndexEquiv e he he' hC hplus D) =
      presheafValueRingEquivOfRingEquiv e.symm he' he D.1 (hC.piece D.2) (f D) :=
  Equiv.piCongr_apply_apply (W := fun D : ↥C.covers ↦ presheafValue D.1)
    (Z := fun D' : ↥(C.pullbackRingEquiv e he he' hC hplus).covers ↦ presheafValue D'.1)
    (C.pullbackIndexEquiv e he he' hC hplus)
    (fun D ↦ (presheafValueHomeomorphOfRingEquiv e.symm he' he D.1 (hC.piece D.2)).toEquiv) f D

omit [HasLocLiftPowerBounded A] [HasLocLiftPowerBounded B] in
/-- Pointwise evaluation of the inverse product homeomorphism: the backward
transport is index-free (`Equiv.piCongr_symm_apply` is definitional). -/
theorem RationalCoveringData.productSectionsHomeomorph_symm_apply
    (g : ∀ D' : ↥(C.pullbackRingEquiv e he he' hC hplus).covers, presheafValue D'.1)
    (D : ↥C.covers) :
    (C.productSectionsHomeomorph e he he' hC hplus).symm g D =
      (presheafValueRingEquivOfRingEquiv e.symm he' he D.1 (hC.piece D.2)).symm
        (g (C.pullbackIndexEquiv e he he' hC hplus D)) := rfl

/-- **The central conjugation square** (T5, the one theorem the `IsSheafy`
transport consumes). Orientation:

    productSectionsHomeomorph (productRestrictionSub B C x)
      = productRestrictionSub A Cpull (baseHomeomorph x),

where `baseHomeomorph` is the completed-localization homeomorphism at the base
datum. Proved pointwise from the T3 restriction square; the dependent fibers are
handled by the exact index equivalence (its values are definitionally the
transported data — nothing is cast). -/
theorem RationalCoveringData.productRestrictionSub_conj (x : presheafValue C.base) :
    C.productSectionsHomeomorph e he he' hC hplus (productRestrictionSub B C x) =
      productRestrictionSub A (C.pullbackRingEquiv e he he' hC hplus)
        (presheafValueRingEquivOfRingEquiv e.symm he' he C.base hC.base x) := by
  funext D'
  obtain ⟨D, rfl⟩ := (C.pullbackIndexEquiv e he he' hC hplus).surjective D'
  rw [RationalCoveringData.productSectionsHomeomorph_apply_index]
  show presheafValueRingEquivOfRingEquiv e.symm he' he D.1 (hC.piece D.2)
      (restrictionMap C.base D.1 (C.hsubset D.1 D.2) x) =
    restrictionMap (C.pullbackRingEquiv e he he' hC hplus).base
      (C.pullbackIndexEquiv e he he' hC hplus D).1
      ((C.pullbackRingEquiv e he he' hC hplus).hsubset _
        (C.pullbackIndexEquiv e he he' hC hplus D).2)
      (presheafValueRingEquivOfRingEquiv e.symm he' he C.base hC.base x)
  exact presheafValueRingEquivOfRingEquiv_restriction e.symm he' he C.base hC.base D.1
    (hC.piece D.2) (C.hsubset D.1 D.2) _ x

end ProductConj

/-! ### 2.8 Transport of the internal `IsSheafy` criterion (T6) -/

section SheafyTransportAux

variable {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [PlusSubring A] [HasLocLiftPowerBounded A]
  [CommRing B] [TopologicalSpace B] [IsTateRing B] [PlusSubring B]
  [HasLocLiftPowerBounded B]
  (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
  (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom)

omit [HasLocLiftPowerBounded A] [HasLocLiftPowerBounded B] in
include hplus in
-- The transported-containment lemma (T6 gluing, step 5): a valid source refinement `E`
-- contained in a pulled-back piece transposes to its pushforward `Ê` being contained in the
-- original piece.
private theorem rationalOpen_mapRationalRingEquiv_subset_transpose (E : RationalLocData A)
    (hE : E.IsRational) (D : RationalLocData B) (hD : D.IsRational)
    (h : rationalOpen E.T E.s ⊆ rationalOpen (D.mapRationalRingEquiv e.symm he' he hD).T
      (D.mapRationalRingEquiv e.symm he' he hD).s) :
    rationalOpen (E.mapRationalRingEquiv e he he' hE).T
      (E.mapRationalRingEquiv e he he' hE).s ⊆ rationalOpen D.T D.s := by
  have hÊ : (E.mapRationalRingEquiv e he he' hE).IsRational :=
    mapRationalRingEquiv_isRational e he he' E hE
  rw [← E.mapRationalRingEquiv_symm_map e he he' hE hÊ] at h
  exact (rationalOpen_mapRationalRingEquiv_subset_iff e.symm he' he
    (ringPlus_map_symm_of_map e hplus) (E.mapRationalRingEquiv e he he' hE) hÊ D hD).mp h

include hplus in
-- The per-side restriction-rewrite lemma (T6 gluing, step 7): restricting a transported
-- section to the source refinement `E` equals transporting its restriction to the
-- pushed-forward refinement `Ê` and reading it back through the roundtrip `Ê ↓ = E`.
private theorem restrictionMap_mapRationalRingEquiv_factor (E : RationalLocData A)
    (hE : E.IsRational) (hÊ : (E.mapRationalRingEquiv e he he' hE).IsRational)
    (D : RationalLocData B) (hD : D.IsRational)
    (hEeq : rationalOpen E.T E.s ⊆
      rationalOpen ((E.mapRationalRingEquiv e he he' hE).mapRationalRingEquiv e.symm he' he hÊ).T
        ((E.mapRationalRingEquiv e he he' hE).mapRationalRingEquiv e.symm he' he hÊ).s)
    (hiA : rationalOpen E.T E.s ⊆ rationalOpen (D.mapRationalRingEquiv e.symm he' he hD).T
      (D.mapRationalRingEquiv e.symm he' he hD).s)
    (hiB : rationalOpen (E.mapRationalRingEquiv e he he' hE).T
      (E.mapRationalRingEquiv e he he' hE).s ⊆ rationalOpen D.T D.s)
    (v : presheafValue D) :
    restrictionMap (D.mapRationalRingEquiv e.symm he' he hD) E hiA
      (presheafValueRingEquivOfRingEquiv e.symm he' he D hD v) =
    restrictionMap ((E.mapRationalRingEquiv e he he' hE).mapRationalRingEquiv e.symm he' he hÊ) E
      hEeq (presheafValueRingEquivOfRingEquiv e.symm he' he (E.mapRationalRingEquiv e he he' hE) hÊ
        (restrictionMap D (E.mapRationalRingEquiv e he he' hE) hiB v)) := by
  have hBsub := rationalOpen_mapRationalRingEquiv_subset_of_subset e.symm he' he
    (ringPlus_map_symm_of_map e hplus) (E.mapRationalRingEquiv e he he' hE) hÊ D hD hiB
  have hcompose := restrictionMap_restrictionMap (D.mapRationalRingEquiv e.symm he' he hD)
    ((E.mapRationalRingEquiv e he he' hE).mapRationalRingEquiv e.symm he' he hÊ) E hBsub hEeq
    (presheafValueRingEquivOfRingEquiv e.symm he' he D hD v)
  rw [presheafValueRingEquivOfRingEquiv_restriction e.symm he' he D hD
    (E.mapRationalRingEquiv e he he' hE) hÊ hiB hBsub v, hcompose]

-- T6 gluing, steps 3–7: the transported family of sections is compatible on every valid
-- rational common refinement of the pulled-back cover.
private theorem rationalRefinementCompatible_productSectionsHomeomorph (C : RationalCoveringData B)
    (hC : C.IsRational) {f : ∀ D : ↥C.covers, presheafValue D.1} (hf : C.AllDataCompatible f) :
    (C.pullbackRingEquiv e he he' hC hplus).RationalRefinementCompatible
      (C.productSectionsHomeomorph e he he' hC hplus f) := by
  intro D₁' D₂' E hE h₁ h₂
  obtain ⟨D₁, rfl⟩ := (C.pullbackIndexEquiv e he he' hC hplus).surjective D₁'
  obtain ⟨D₂, rfl⟩ := (C.pullbackIndexEquiv e he he' hC hplus).surjective D₂'
  -- Step 4: send the valid source refinement forward; the equality-derived containment
  -- `R(E) ⊆ R(Ê ↓)` comes from the roundtrip
  have hÊ : (E.mapRationalRingEquiv e he he' hE).IsRational :=
    mapRationalRingEquiv_isRational e he he' E hE
  have hEeq : rationalOpen E.T E.s ⊆
      rationalOpen ((E.mapRationalRingEquiv e he he' hE).mapRationalRingEquiv e.symm he' he hÊ).T
        ((E.mapRationalRingEquiv e he he' hE).mapRationalRingEquiv e.symm he' he hÊ).s := by
    rw [E.mapRationalRingEquiv_symm_map e he he' hE hÊ]
  -- Step 5: transport the two containments to the target (over `B`)
  have h₁B := rationalOpen_mapRationalRingEquiv_subset_transpose e he he' hplus E hE
    D₁.1 (hC.piece D₁.2) h₁
  have h₂B := rationalOpen_mapRationalRingEquiv_subset_transpose e he he' hplus E hE
    D₂.1 (hC.piece D₂.2) h₂
  -- Step 6: the original family's compatibility at the transported datum
  have hstep := hf D₁ D₂ (E.mapRationalRingEquiv e he he' hE) h₁B h₂B
  -- assemble the two sides
  change restrictionMap (D₁.1.mapRationalRingEquiv e.symm he' he (hC.piece D₁.2)) E h₁
      (C.productSectionsHomeomorph e he he' hC hplus f
        (C.pullbackIndexEquiv e he he' hC hplus D₁)) =
    restrictionMap (D₂.1.mapRationalRingEquiv e.symm he' he (hC.piece D₂.2)) E h₂
      (C.productSectionsHomeomorph e he he' hC hplus f
        (C.pullbackIndexEquiv e he he' hC hplus D₂))
  -- Step 7: rewrite both restrictions through the T3 square + composition
  rw [RationalCoveringData.productSectionsHomeomorph_apply_index,
    RationalCoveringData.productSectionsHomeomorph_apply_index,
    restrictionMap_mapRationalRingEquiv_factor e he he' hplus E hE hÊ D₁.1
      (hC.piece D₁.2) hEeq h₁ h₁B (f D₁),
    restrictionMap_mapRationalRingEquiv_factor e he he' hplus E hE hÊ D₂.1
      (hC.piece D₂.2) hEeq h₂ h₂B (f D₂), hstep]

end SheafyTransportAux

section SheafyTransport

variable {A : Type u} {B : Type v}
  [CommRing A] [TopologicalSpace A] [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
  [PlusSubring A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [CommRing B] [TopologicalSpace B] [IsTateRing B] [T2Space B] [NonarchimedeanRing B]
  [letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B; CompleteSpace B]
  [PlusSubring B] [IsRingOfIntegralElements (B⁺ : Subring B)]

/-- **Transport of the internal finite rational-cover criterion** (T6): if the
pair `(A, A⁺)` satisfies `IsSheafy` and `e : A ≃+* B` is a bicontinuous ring
equivalence matching the plus rings (`B⁺ = e(A⁺)`), then `(B, B⁺)` satisfies
`IsSheafy`. -/
theorem isSheafy_mapRingEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) [IsSheafy A] : IsSheafy B := by
  have : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  have : HasLocLiftPowerBounded B := hasLocLiftPowerBounded_faithful
  constructor
  · -- ——— embedding ———: pull the target cover back (T4), conjugate the product
    -- restriction through the central square (T5), and factor with
    -- `IsEmbedding.of_comp_iff` along the product homeomorphism — the full
    -- topological embedding transports, not merely injectivity.
    intro C hC
    have hconj : ⇑(C.productSectionsHomeomorph e he he' hC hplus) ∘ productRestrictionSub B C =
        productRestrictionSub A (C.pullbackRingEquiv e he he' hC hplus) ∘
          ⇑(presheafValueRingEquivOfRingEquiv e.symm he' he C.base hC.base) :=
      funext (C.productRestrictionSub_conj e he he' hC hplus)
    refine (C.productSectionsHomeomorph e he he' hC hplus).isEmbedding.of_comp_iff.mp ?_
    rw [hconj]
    exact (IsSheafy.embedding _ (C.pullbackRingEquiv_isRational e he he' hC hplus)).comp
      (presheafValueHomeomorphOfRingEquiv e.symm he' he C.base hC.base).isEmbedding
  · -- ——— gluing ———: transport the compatible family through the product
    -- homeomorphism, prove only `RationalRefinementCompatible` on the source (each
    -- valid common refinement is pushed forward through `validRationalLocDataEquiv`
    -- and the original family's `AllDataCompatible` hypothesis is applied there),
    -- convert with the R3 bridge, glue at the source, and push the glued section back.
    intro C hC f hf
    have hCprat := C.pullbackRingEquiv_isRational e he he' hC hplus
    -- Steps 3–7 (extracted above) + Step 8: the transported family
    -- `productSectionsHomeomorph … f` is compatible on every valid rational refinement;
    -- convert to the raw-data form through the R3 bridge
    have hgAll : (C.pullbackRingEquiv e he he' hC hplus).AllDataCompatible
        (C.productSectionsHomeomorph e he he' hC hplus f) :=
      ((C.pullbackRingEquiv e he he' hC hplus).allDataCompatible_iff_rationalRefinementCompatible
        hCprat (C.productSectionsHomeomorph e he he' hC hplus f)).mpr
        (rationalRefinementCompatible_productSectionsHomeomorph e he he' hplus C hC hf)
    -- Step 9: glue at the source
    obtain ⟨x, hx⟩ := IsSheafy.gluing (A := A) (C.pullbackRingEquiv e he he' hC hplus)
      hCprat (C.productSectionsHomeomorph e he he' hC hplus f) hgAll
    -- Step 10: push the glued base section to the target
    refine ⟨(presheafValueRingEquivOfRingEquiv e.symm he' he C.base hC.base).symm x, fun D ↦ ?_⟩
    -- Step 11: verify the restrictions through the central square
    apply (presheafValueRingEquivOfRingEquiv e.symm he' he D.1 (hC.piece D.2)).injective
    have hpt := congr_fun (C.productRestrictionSub_conj e he he' hC hplus
      ((presheafValueRingEquivOfRingEquiv e.symm he' he C.base hC.base).symm x))
      (C.pullbackIndexEquiv e he he' hC hplus D)
    rw [RationalCoveringData.productSectionsHomeomorph_apply_index,
      (presheafValueRingEquivOfRingEquiv e.symm he' he C.base hC.base).apply_symm_apply x] at hpt
    have hxD := hx (C.pullbackIndexEquiv e he he' hC hplus D)
    rw [RationalCoveringData.productSectionsHomeomorph_apply_index] at hxD
    exact hpt.trans hxD

end SheafyTransport

end ValuationSpectrum
