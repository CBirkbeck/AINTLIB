/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetFunctoriality

/-!
# Sheafiness of 𝓐 by Milnor transfer ([FJP] Lemma 5.2 and Theorem 5.3)

Source: [FJP] Lemma 5.2 (topological sheaf transfer for a strictly localizing Milnor
square, verbatim conclusion): "If the Huber pairs `(B,B⁺), (C,C⁺), (D,D⁺)` are sheafy as
complete topological rings, then `(R,R⁺)` is sheafy as a complete topological ring." and
Theorem 5.3: "The structure presheaf on `X = Spa(𝒜, 𝒜°)` is a sheaf of complete topological
rings; equivalently, `(𝒜, 𝒜°)` is sheafy."

Retargeted at the project's `ValuationSpectrum.IsSheafy` (rational coverings; the paper's
arbitrary-opens upgrade (5.9) is not part of the project's class and is not formalised).

Gluing chain (paper's proof, p. 19–20): push the matching family to the vertices; matching
persists on pairwise intersections (`interDatum` + naturality); vertices' `IsSheafy.gluing`
produce `b ∈ B_U`, `c ∈ C_U`; their 𝓓-images agree after restriction to every piece, hence
agree by 𝓓-separatedness; exactness of the localized Milnor row ([FJP] Prop 4.5 via the
graph bridges) produces the unique `x ∈ 𝒪_𝓐(U)`; its restrictions are recovered by
injectivity of the localized rows on the pieces.

Embedding: the range of `productRestrictionSub` is the closed `sectionEqualizer` (project
generic), and the σ-compact-free Tate open mapping route
(`productRestrictionSub_isInducing_via_equalizer` pattern, [FJP] Thm 5.3's "the Banach open
mapping theorem makes the continuous bijection onto that image a homeomorphism") applies once
gluing and injectivity are in hand.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum StrictLoc

open scoped Classical

variable (F : Type*) [Field F]

/-! ### Ingredients of the gluing transfer -/

variable {F}

/-- Injectivity (separation) for 𝓐: the localized Milnor rows are jointly injective on
every rational piece ([FJP] Lemma 5.2: "It equals `J r_R`. Since `J` is itself an
embedding …"; algebraic part). -/
theorem productRestrictionSub_injective_JetA (C : RationalCovering (JetA F))
    (hC : C.IsRational) :
    Function.Injective (productRestrictionSub (JetA F) C) := by
  haveI : IsSheafy (JetB F) := isSheafy_JetB F
  haveI : IsSheafy (JetC F) := isSheafy_JetC F
  intro x y hxy
  set z := x - y with hz
  set e := datumEnum C.base with he
  -- all piece restrictions of `z` vanish
  have hres : ∀ (D : ↥C.covers),
      restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) z = 0 := by
    intro D
    have hDx := congrFun hxy D
    have hsub : restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) (x - y) =
        restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x -
        restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y :=
      RingHom.map_sub _ x y
    rw [hz, hsub,
      show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x =
        productRestrictionSub (JetA F) C x D from rfl,
      show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y =
        productRestrictionSub (JetA F) C y D from rfl, hDx, sub_self]
  -- the 𝓑-pushed global section vanishes (vertex separatedness on the pushed covering)
  have hBz : presheafValueMapB C.base hC.base z = 0 := by
    refine IsSheafy.separationSub (A := JetB F) (pushCoveringB C hC)
      (pushCoveringB_isRational hC) ?_
    funext D'
    obtain ⟨D₀, hD₀⟩ := D'
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD₀
    show restrictionMapHom (pushDatumB C.base hC.base) (pushDatumB d.1 (hC.piece d.2))
      ((pushCoveringB C hC).hsubset _ hD₀) (presheafValueMapB C.base hC.base z) =
      restrictionMapHom (pushDatumB C.base hC.base) (pushDatumB d.1 (hC.piece d.2))
        ((pushCoveringB C hC).hsubset _ hD₀) 0
    rw [RingHom.map_zero (restrictionMapHom (pushDatumB C.base hC.base)
      (pushDatumB d.1 (hC.piece d.2)) ((pushCoveringB C hC).hsubset _ hD₀))]
    show restrictionMap (pushDatumB C.base hC.base) (pushDatumB d.1 (hC.piece d.2))
      ((pushCoveringB C hC).hsubset _ hD₀) (presheafValueMapB C.base hC.base z) = 0
    rw [← presheafValueMapB_restriction C.base d.1 hC.base (hC.piece d.2)
        (C.hsubset d.1 d.2) ((pushCoveringB C hC).hsubset _ hD₀) z,
      show restrictionMap C.base d.1 (C.hsubset d.1 d.2) z =
        restrictionMapHom C.base d.1 (C.hsubset d.1 d.2) z from rfl,
      hres d, RingHom.map_zero (presheafValueMapB d.1 (hC.piece d.2))]
  -- the 𝓒-pushed global section vanishes
  have hCz : presheafValueMapC C.base hC.base z = 0 := by
    refine IsSheafy.separationSub (A := JetC F) (pushCoveringC C hC)
      (pushCoveringC_isRational hC) ?_
    funext D'
    obtain ⟨D₀, hD₀⟩ := D'
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD₀
    show restrictionMapHom (pushDatumC C.base hC.base) (pushDatumC d.1 (hC.piece d.2))
      ((pushCoveringC C hC).hsubset _ hD₀) (presheafValueMapC C.base hC.base z) =
      restrictionMapHom (pushDatumC C.base hC.base) (pushDatumC d.1 (hC.piece d.2))
        ((pushCoveringC C hC).hsubset _ hD₀) 0
    rw [RingHom.map_zero (restrictionMapHom (pushDatumC C.base hC.base)
      (pushDatumC d.1 (hC.piece d.2)) ((pushCoveringC C hC).hsubset _ hD₀))]
    show restrictionMap (pushDatumC C.base hC.base) (pushDatumC d.1 (hC.piece d.2))
      ((pushCoveringC C hC).hsubset _ hD₀) (presheafValueMapC C.base hC.base z) = 0
    rw [← presheafValueMapC_restriction C.base d.1 hC.base (hC.piece d.2)
        (C.hsubset d.1 d.2) ((pushCoveringC C hC).hsubset _ hD₀) z,
      show restrictionMap C.base d.1 (C.hsubset d.1 d.2) z =
        restrictionMapHom C.base d.1 (C.hsubset d.1 d.2) z from rfl,
      hres d, RingHom.map_zero (presheafValueMapC d.1 (hC.piece d.2))]
  -- through the base graph bridge: both localized-row images vanish
  have hbridge : graphBridgeA C.base hC.base e z = 0 := by
    have hpair := loc_pair_injective F e.m C.base.s e.f
      (e.span_eq_top C.base hC.base)
    have hB0 : locJB F e.m C.base.s e.f (graphBridgeA C.base hC.base e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_B C.base hC.base e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA C.base hC.base e :
          presheafValue C.base →+* locA F e.m C.base.s e.f) z =
        graphBridgeA C.base hC.base e z from rfl] at hnat
      rw [← hnat, hBz, RingHom.map_zero (bridgeFwdB C.base e hC.base)]
    have hC0 : locIotaC F e.m C.base.s e.f (graphBridgeA C.base hC.base e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_C C.base hC.base e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA C.base hC.base e :
          presheafValue C.base →+* locA F e.m C.base.s e.f) z =
        graphBridgeA C.base hC.base e z from rfl] at hnat
      rw [← hnat, hCz, RingHom.map_zero (bridgeFwdC C.base e hC.base)]
    have h00 : (fun w : locA F e.m C.base.s e.f =>
        (locJB F e.m C.base.s e.f w, locIotaC F e.m C.base.s e.f w))
          (graphBridgeA C.base hC.base e z) =
        (fun w : locA F e.m C.base.s e.f =>
          (locJB F e.m C.base.s e.f w, locIotaC F e.m C.base.s e.f w)) 0 := by
      simp only [hB0, hC0, RingHom.map_zero]
    exact hpair h00
  -- the bridge is injective, so `z = 0`
  have hz0 : z = 0 := by
    have := (graphBridgeA C.base hC.base e).injective
      (a₁ := z) (a₂ := 0) (by rw [hbridge, map_zero])
    exact this
  rw [← sub_eq_zero]
  exact hz0

/-- Pushed opens of intersection data cut out the intersections of the pushed opens
(𝓑-side; [FJP] Lemma 5.2 `(U_{ij})_E = (U_i)_E ∩ (U_j)_E`). -/
theorem pushDatumB_interOpen (d₁ d₂ : RationalLocData (JetA F))
    (h₁ : d₁.IsRational) (h₂ : d₂.IsRational) :
    rationalOpen (pushDatumB (interDatum d₁ d₂ h₁ h₂)
        (interDatum_isRational h₁ h₂)).T
      (pushDatumB (interDatum d₁ d₂ h₁ h₂) (interDatum_isRational h₁ h₂)).s =
    rationalOpen (pushDatumB d₁ h₁).T (pushDatumB d₁ h₁).s ∩
      rationalOpen (pushDatumB d₂ h₂).T (pushDatumB d₂ h₂).s := by
  ext v
  constructor
  · intro hv
    have hvspa : v ∈ Spa (JetB F) (ringPlus (JetB F)) := hv.1
    have hmem := (mem_rationalOpen_pushDatumB_iff (interDatum d₁ d₂ h₁ h₂)
      (interDatum_isRational h₁ h₂) v hvspa).mp hv
    rw [rationalOpen_interDatum d₁ d₂ h₁ h₂] at hmem
    exact ⟨(mem_rationalOpen_pushDatumB_iff d₁ h₁ v hvspa).mpr hmem.1,
      (mem_rationalOpen_pushDatumB_iff d₂ h₂ v hvspa).mpr hmem.2⟩
  · rintro ⟨hv₁, hv₂⟩
    have hvspa : v ∈ Spa (JetB F) (ringPlus (JetB F)) := hv₁.1
    refine (mem_rationalOpen_pushDatumB_iff (interDatum d₁ d₂ h₁ h₂)
      (interDatum_isRational h₁ h₂) v hvspa).mpr ?_
    rw [rationalOpen_interDatum d₁ d₂ h₁ h₂]
    exact ⟨(mem_rationalOpen_pushDatumB_iff d₁ h₁ v hvspa).mp hv₁,
      (mem_rationalOpen_pushDatumB_iff d₂ h₂ v hvspa).mp hv₂⟩

/-- 𝓒-side analogue of `pushDatumB_interOpen`. -/
theorem pushDatumC_interOpen (d₁ d₂ : RationalLocData (JetA F))
    (h₁ : d₁.IsRational) (h₂ : d₂.IsRational) :
    rationalOpen (pushDatumC (interDatum d₁ d₂ h₁ h₂)
        (interDatum_isRational h₁ h₂)).T
      (pushDatumC (interDatum d₁ d₂ h₁ h₂) (interDatum_isRational h₁ h₂)).s =
    rationalOpen (pushDatumC d₁ h₁).T (pushDatumC d₁ h₁).s ∩
      rationalOpen (pushDatumC d₂ h₂).T (pushDatumC d₂ h₂).s := by
  ext v
  constructor
  · intro hv
    have hvspa : v ∈ Spa (JetC F) (ringPlus (JetC F)) := hv.1
    have hmem := (mem_rationalOpen_pushDatumC_iff (interDatum d₁ d₂ h₁ h₂)
      (interDatum_isRational h₁ h₂) v hvspa).mp hv
    rw [rationalOpen_interDatum d₁ d₂ h₁ h₂] at hmem
    exact ⟨(mem_rationalOpen_pushDatumC_iff d₁ h₁ v hvspa).mpr hmem.1,
      (mem_rationalOpen_pushDatumC_iff d₂ h₂ v hvspa).mpr hmem.2⟩
  · rintro ⟨hv₁, hv₂⟩
    have hvspa : v ∈ Spa (JetC F) (ringPlus (JetC F)) := hv₁.1
    refine (mem_rationalOpen_pushDatumC_iff (interDatum d₁ d₂ h₁ h₂)
      (interDatum_isRational h₁ h₂) v hvspa).mpr ?_
    rw [rationalOpen_interDatum d₁ d₂ h₁ h₂]
    exact ⟨(mem_rationalOpen_pushDatumC_iff d₁ h₁ v hvspa).mp hv₁,
      (mem_rationalOpen_pushDatumC_iff d₂ h₂ v hvspa).mp hv₂⟩

/-- The gluing transfer ([FJP] Lemma 5.2, gluing half). -/
theorem gluing_JetA (C : RationalCovering (JetA F)) (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (JetA F))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ D : ↥C.covers,
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by sorry

/-- The embedding transfer ([FJP] Lemma 5.2, topological half; Theorem 5.3's OMT step). -/
theorem productRestrictionSub_isEmbedding_JetA (C : RationalCovering (JetA F))
    (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub (JetA F) C) := by sorry

variable (F)

/-- **The finite-jet pinching algebra is sheafy** ([FJP] Theorem 5.3). This is the
priority theorem of the campaign. -/
theorem isSheafy_JetA : ValuationSpectrum.IsSheafy (JetA F) where
  embedding := fun C hC => productRestrictionSub_isEmbedding_JetA C hC
  gluing := fun C hC f hcompat => gluing_JetA C hC f hcompat

end FiniteJet
