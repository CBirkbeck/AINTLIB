/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetFunctoriality

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

/-- If every piece restriction of `z` vanishes then so does its B-pushed global section, by
separatedness on the pushed covering. -/
private theorem presheafValueMapB_eq_zero_of_pieces (C : RationalCoveringData (JetA F))
    (hC : C.IsRational) (z : presheafValue C.base)
    (hres : ∀ D : ↥C.covers, restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) z = 0) :
    presheafValueMapB C.base hC.base z = 0 := by
  haveI : IsSheafy (JetB F) := isSheafy_JetB F
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

/-- If every piece restriction of `z` vanishes then so does its C-pushed global section, by
separatedness on the pushed covering. -/
private theorem presheafValueMapC_eq_zero_of_pieces (C : RationalCoveringData (JetA F))
    (hC : C.IsRational) (z : presheafValue C.base)
    (hres : ∀ D : ↥C.covers, restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) z = 0) :
    presheafValueMapC C.base hC.base z = 0 := by
  haveI : IsSheafy (JetC F) := isSheafy_JetC F
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

/-- Injectivity (separation) for 𝓐: the localized Milnor rows are jointly injective on
every rational piece ([FJP] Lemma 5.2: "It equals `J r_R`. Since `J` is itself an
embedding …"; algebraic part). -/
theorem productRestrictionSub_injective_JetA (C : RationalCoveringData (JetA F))
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
  have hBz := presheafValueMapB_eq_zero_of_pieces C hC z hres
  -- the 𝓒-pushed global section vanishes
  have hCz := presheafValueMapC_eq_zero_of_pieces C hC z hres
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

-- `restrictionMap_cast` was extracted to `PresheafFunctoriality.lean` (T0,
-- 2026-07-21): it is fully generic (no jet structure); uses below resolve to
-- `ValuationSpectrum.restrictionMap_cast` through the `open ValuationSpectrum`.

section Gluing

variable (C : RationalCoveringData (JetA F)) (hC : C.IsRational)
  (f : ∀ D : ↥C.covers, presheafValue D.1)
  (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (JetA F))
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
    restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂))

include hcompat in
/-- Compatibility of the 𝓑-pushed family at an ARBITRARY vertex refinement
([FJP] Lemma 5.2 / L6.2 attack 1: factor through the pushed intersection). -/
theorem pushedCompatB (d₁ d₂ : ↥C.covers) (D₃ : RationalLocData (JetB F))
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumB d₁.1 (hC.piece d₁.2)).T
        (pushDatumB d₁.1 (hC.piece d₁.2)).s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumB d₂.1 (hC.piece d₂.2)).T
        (pushDatumB d₂.1 (hC.piece d₂.2)).s) :
    restrictionMap (pushDatumB d₁.1 (hC.piece d₁.2)) D₃ h₃₁
      (presheafValueMapB d₁.1 (hC.piece d₁.2) (f d₁)) =
    restrictionMap (pushDatumB d₂.1 (hC.piece d₂.2)) D₃ h₃₂
      (presheafValueMapB d₂.1 (hC.piece d₂.2) (f d₂)) := by
  haveI : IsSheafy (JetB F) := isSheafy_JetB F
  set hIrat := interDatum_isRational (hC.piece d₁.2) (hC.piece d₂.2) with hIratdef
  have hsub₁ : rationalOpen (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₁.1.T d₁.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₂.1.T d₂.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumB d₁.1 (hC.piece d₁.2)).T
        (pushDatumB d₁.1 (hC.piece d₁.2)).s := by
    rw [pushDatumB_interOpen]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumB d₂.1 (hC.piece d₂.2)).T
        (pushDatumB d₂.1 (hC.piece d₂.2)).s := by
    rw [pushDatumB_interOpen]
    exact Set.inter_subset_right
  have h₃I : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s := by
    rw [pushDatumB_interOpen]
    exact Set.subset_inter h₃₁ h₃₂
  have hpushed := congrArg (presheafValueMapB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) (hcompat d₁ d₂ (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hsub₁ hsub₂)
  rw [presheafValueMapB_restriction d₁.1 (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₁.2) hIrat hsub₁ hpush₁ (f d₁),
    presheafValueMapB_restriction d₂.1 (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₂.2) hIrat hsub₂ hpush₂ (f d₂)]
    at hpushed
  have hfac₁ := congrFun (restrictionMap_comp (pushDatumB d₁.1 (hC.piece d₁.2))
    (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₁ h₃I) (presheafValueMapB d₁.1 (hC.piece d₁.2) (f d₁))
  have hfac₂ := congrFun (restrictionMap_comp (pushDatumB d₂.1 (hC.piece d₂.2))
    (pushDatumB (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₂ h₃I) (presheafValueMapB d₂.1 (hC.piece d₂.2) (f d₂))
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

include hcompat in
/-- 𝓒-side analogue of `pushedCompatB`. -/
theorem pushedCompatC (d₁ d₂ : ↥C.covers) (D₃ : RationalLocData (JetC F))
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumC d₁.1 (hC.piece d₁.2)).T
        (pushDatumC d₁.1 (hC.piece d₁.2)).s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumC d₂.1 (hC.piece d₂.2)).T
        (pushDatumC d₂.1 (hC.piece d₂.2)).s) :
    restrictionMap (pushDatumC d₁.1 (hC.piece d₁.2)) D₃ h₃₁
      (presheafValueMapC d₁.1 (hC.piece d₁.2) (f d₁)) =
    restrictionMap (pushDatumC d₂.1 (hC.piece d₂.2)) D₃ h₃₂
      (presheafValueMapC d₂.1 (hC.piece d₂.2) (f d₂)) := by
  haveI : IsSheafy (JetC F) := isSheafy_JetC F
  set hIrat := interDatum_isRational (hC.piece d₁.2) (hC.piece d₂.2) with hIratdef
  have hsub₁ : rationalOpen (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₁.1.T d₁.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₂.1.T d₂.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumC d₁.1 (hC.piece d₁.2)).T
        (pushDatumC d₁.1 (hC.piece d₁.2)).s := by
    rw [pushDatumC_interOpen]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumC d₂.1 (hC.piece d₂.2)).T
        (pushDatumC d₂.1 (hC.piece d₂.2)).s := by
    rw [pushDatumC_interOpen]
    exact Set.inter_subset_right
  have h₃I : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s := by
    rw [pushDatumC_interOpen]
    exact Set.subset_inter h₃₁ h₃₂
  have hpushed := congrArg (presheafValueMapC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) (hcompat d₁ d₂ (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hsub₁ hsub₂)
  rw [presheafValueMapC_restriction d₁.1 (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₁.2) hIrat hsub₁ hpush₁ (f d₁),
    presheafValueMapC_restriction d₂.1 (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₂.2) hIrat hsub₂ hpush₂ (f d₂)]
    at hpushed
  have hfac₁ := congrFun (restrictionMap_comp (pushDatumC d₁.1 (hC.piece d₁.2))
    (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₁ h₃I) (presheafValueMapC d₁.1 (hC.piece d₁.2) (f d₁))
  have hfac₂ := congrFun (restrictionMap_comp (pushDatumC d₂.1 (hC.piece d₂.2))
    (pushDatumC (interDatum d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₂ h₃I) (presheafValueMapC d₂.1 (hC.piece d₂.2) (f d₂))
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

/-- Joint injectivity of the vertex pushes at a single rational datum
([FJP] `j_{U_i}`-injectivity; the L6.1 kernel chase at one datum). -/
theorem pairMapBC_injective (D : RationalLocData (JetA F)) (hD : D.IsRational)
    {u₁ u₂ : presheafValue D}
    (hB : presheafValueMapB D hD u₁ = presheafValueMapB D hD u₂)
    (hCeq : presheafValueMapC D hD u₁ = presheafValueMapC D hD u₂) : u₁ = u₂ := by
  set e := datumEnum D with he
  set z := u₁ - u₂ with hz
  have hBz : presheafValueMapB D hD z = 0 := by
    rw [hz]
    exact (RingHom.map_sub (presheafValueMapB D hD) u₁ u₂).trans
      (sub_eq_zero.mpr hB)
  have hCz : presheafValueMapC D hD z = 0 := by
    rw [hz]
    exact (RingHom.map_sub (presheafValueMapC D hD) u₁ u₂).trans
      (sub_eq_zero.mpr hCeq)
  have hbridge : graphBridgeA D hD e z = 0 := by
    have hpair := loc_pair_injective F e.m D.s e.f (e.span_eq_top D hD)
    have hB0 : locJB F e.m D.s e.f (graphBridgeA D hD e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_B D hD e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA D hD e :
          presheafValue D →+* locA F e.m D.s e.f) z =
        graphBridgeA D hD e z from rfl] at hnat
      rw [← hnat, hBz, RingHom.map_zero (bridgeFwdB D e hD)]
    have hC0 : locIotaC F e.m D.s e.f (graphBridgeA D hD e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_C D hD e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA D hD e :
          presheafValue D →+* locA F e.m D.s e.f) z =
        graphBridgeA D hD e z from rfl] at hnat
      rw [← hnat, hCz, RingHom.map_zero (bridgeFwdC D e hD)]
    have h00 : (fun w : locA F e.m D.s e.f =>
        (locJB F e.m D.s e.f w, locIotaC F e.m D.s e.f w)) (graphBridgeA D hD e z) =
        (fun w : locA F e.m D.s e.f =>
          (locJB F e.m D.s e.f w, locIotaC F e.m D.s e.f w)) 0 := by
      simp only [hB0, hC0, RingHom.map_zero]
    exact hpair h00
  have hz0 : z = 0 := (graphBridgeA D hD e).injective (by rw [hbridge, map_zero])
  rw [← sub_eq_zero]
  exact hz0

/-- **𝓓-matching of the two pushed vertex gluings** ([FJP] Lemma 5.2, the middle step of the
gluing half): the 𝓑- and 𝓒-glued sections agree after pushing to 𝓓.

Proved by 𝓓-separation on the pushed covering: both sides restrict, at every piece, to the
𝓓-push of the same 𝓐-section, so they agree piecewise and separation finishes.

Extracted from `gluing_JetA`, where it was an 84-line `have` — the single largest
contribution to that proof's heartbeat cost. -/
private theorem mapBD_eq_mapCD_of_pushed_gluing
    (gB : ∀ D' : ↥(pushCoveringB C hC).covers, presheafValue D'.1)
    (gC : ∀ D' : ↥(pushCoveringC C hC).covers, presheafValue D'.1)
    (bB : presheafValue (pushCoveringB C hC).base)
    (bC : presheafValue (pushCoveringC C hC).base)
    (hbB : ∀ D' : ↥(pushCoveringB C hC).covers,
      restrictionMap (pushCoveringB C hC).base D'.1
        ((pushCoveringB C hC).hsubset D'.1 D'.2) bB = gB D')
    (hbC : ∀ D' : ↥(pushCoveringC C hC).covers,
      restrictionMap (pushCoveringC C hC).base D'.1
        ((pushCoveringC C hC).hsubset D'.1 D'.2) bC = gC D')
    (hgBd : ∀ d : ↥C.covers, gB ⟨pushDatumB d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ =
      presheafValueMapB d.1 (hC.piece d.2) (f d))
    (hgCd : ∀ d : ↥C.covers, gC ⟨pushDatumC d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ =
      presheafValueMapC d.1 (hC.piece d.2) (f d)) :
    mapBD C.base hC.base bB = mapCD C.base hC.base bC := by
  classical
  haveI : IsSheafy (JetD F) := isSheafy_JetD F
  refine IsSheafy.separationSub (A := JetD F) (pushCoveringD C hC)
    (pushCoveringD_isRational hC) ?_
  funext D'
  obtain ⟨DD, hDD⟩ := D'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hDD
  show restrictionMapHom (pushDatumD C.base hC.base) (pushDatumD d.1 (hC.piece d.2))
    ((pushCoveringD C hC).hsubset _ hDD) (mapBD C.base hC.base bB) =
    restrictionMapHom (pushDatumD C.base hC.base) (pushDatumD d.1 (hC.piece d.2))
      ((pushCoveringD C hC).hsubset _ hDD) (mapCD C.base hC.base bC)
  have hpushB : rationalOpen (pushDatumB d.1 (hC.piece d.2)).T
      (pushDatumB d.1 (hC.piece d.2)).s ⊆
      rationalOpen (pushDatumB C.base hC.base).T (pushDatumB C.base hC.base).s :=
    (pushCoveringB C hC).hsubset _
      (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
  have hpushC : rationalOpen (pushDatumC d.1 (hC.piece d.2)).T
      (pushDatumC d.1 (hC.piece d.2)).s ⊆
      rationalOpen (pushDatumC C.base hC.base).T (pushDatumC C.base hC.base).s :=
    (pushCoveringC C hC).hsubset _
      (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
  -- restriction commutes with mapBD/mapCD (generic naturality at ρ)
  have hnatB : restrictionMap (pushDatumD C.base hC.base)
      (pushDatumD d.1 (hC.piece d.2)) ((pushCoveringD C hC).hsubset _ hDD)
      (mapBD C.base hC.base bB) =
      mapBD d.1 (hC.piece d.2) (restrictionMap (pushDatumB C.base hC.base)
        (pushDatumB d.1 (hC.piece d.2)) hpushB bB) :=
    (presheafValueMapOfHom_restriction (rhoB F) (continuous_rhoB)
      (pushDatumB C.base hC.base) (pushDatumB d.1 (hC.piece d.2))
      (pushDatumD C.base hC.base) (pushDatumD d.1 (hC.piece d.2))
      ((square_commutes F C.base.s).symm)
      (by
        intro t ht
        obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
        rw [square_commutes F t₀]
        exact Finset.mem_image_of_mem _ ht₀)
      ((square_commutes F d.1.s).symm)
      (by
        intro t ht
        obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
        rw [square_commutes F t₀]
        exact Finset.mem_image_of_mem _ ht₀)
      hpushB ((pushCoveringD C hC).hsubset _ hDD) bB).symm
  have hnatC : restrictionMap (pushDatumD C.base hC.base)
      (pushDatumD d.1 (hC.piece d.2)) ((pushCoveringD C hC).hsubset _ hDD)
      (mapCD C.base hC.base bC) =
      mapCD d.1 (hC.piece d.2) (restrictionMap (pushDatumC C.base hC.base)
        (pushDatumC d.1 (hC.piece d.2)) hpushC bC) :=
    (presheafValueMapOfHom_restriction (rhoC F) (continuous_rhoC)
      (pushDatumC C.base hC.base) (pushDatumC d.1 (hC.piece d.2))
      (pushDatumD C.base hC.base) (pushDatumD d.1 (hC.piece d.2))
      rfl
      (by
        intro t ht
        obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_image_of_mem _ ht₀)
      rfl
      (by
        intro t ht
        obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_image_of_mem _ ht₀)
      hpushC ((pushCoveringD C hC).hsubset _ hDD) bC).symm
  show restrictionMap (pushDatumD C.base hC.base) (pushDatumD d.1 (hC.piece d.2))
    ((pushCoveringD C hC).hsubset _ hDD) (mapBD C.base hC.base bB) =
    restrictionMap (pushDatumD C.base hC.base) (pushDatumD d.1 (hC.piece d.2))
      ((pushCoveringD C hC).hsubset _ hDD) (mapCD C.base hC.base bC)
  rw [hnatB, hnatC]
  -- restrictions of the glued sections are the pushed piece-values
  have hbBd := hbB ⟨pushDatumB d.1 (hC.piece d.2),
    Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
  have hbCd := hbC ⟨pushDatumC d.1 (hC.piece d.2),
    Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
  rw [show restrictionMap (pushDatumB C.base hC.base)
      (pushDatumB d.1 (hC.piece d.2)) hpushB bB =
      gB ⟨pushDatumB d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from hbBd,
    show restrictionMap (pushDatumC C.base hC.base)
      (pushDatumC d.1 (hC.piece d.2)) hpushC bC =
      gC ⟨pushDatumC d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from hbCd]
  -- both sides are the 𝓓-pushes of chosen 𝓐-sections; identify via self-restriction
  -- + pushed compatibility + the coherence square
  rw [hgBd d, hgCd d]
  -- finish with the 𝓓-coherence at the piece
  exact DFunLike.congr_fun (mapBD_mapB_eq_mapCD_mapC d.1 (hC.piece d.2)) (f d)

-- `gluing_JetA` needed `set_option maxHeartbeats 1600000` until the decomposition below.
-- History, so the ladder is not re-climbed:
--   * two per-step `whnf` blow-ups fixed first (`restrictionMap_cast_restrictionMap` for the
--     transport rewrites; `simp only` in place of `rw [congrFun ..] at h`);
--   * `hDmatch` (84 lines) extracted to `mapBD_eq_mapCD_of_pushed_gluing`.
-- After those the cost was purely CUMULATIVE (the error pointed at the declaration head, not
-- at any inner step), so the fix was to give each stage its own declaration and hence its own
-- budget: the pushed families `pushedFamilyB`/`C` became real defs, and their properties, the
-- two vertex gluings and the closing piecewise identification each became a lemma.  A closing
-- bullet also turned out to re-derive `pushedFamily*_apply_piece` verbatim, so the same
-- expensive rewrite was being elaborated twice.  The proof now compiles at the DEFAULT 200k;
-- do not reintroduce a raise here.
/-- The family on the pushed 𝓑-covering induced by `f`: on a piece of `pushCoveringB C hC`,
choose a preimage piece of `C` and take the 𝓑-push of `f` there, transported along the
chosen equality. -/
private noncomputable def pushedFamilyB :
    ∀ D' : ↥(pushCoveringB C hC).covers, presheafValue D'.1 := fun D' =>
  (Finset.mem_image.mp D'.2).choose_spec.2 ▸
    presheafValueMapB (Finset.mem_image.mp D'.2).choose.1
      (hC.piece (Finset.mem_image.mp D'.2).choose.2)
      (f (Finset.mem_image.mp D'.2).choose)

/-- The 𝓒-mirror of `pushedFamilyB`. -/
private noncomputable def pushedFamilyC :
    ∀ D' : ↥(pushCoveringC C hC).covers, presheafValue D'.1 := fun D' =>
  (Finset.mem_image.mp D'.2).choose_spec.2 ▸
    presheafValueMapC (Finset.mem_image.mp D'.2).choose.1
      (hC.piece (Finset.mem_image.mp D'.2).choose.2)
      (f (Finset.mem_image.mp D'.2).choose)

/-- Restricting a `pushedFamilyB` value factors through the chosen preimage piece: the
`choose_spec` transport is eliminated by `restrictionMap_cast_restrictionMap`. -/
private theorem pushedFamilyB_restrictionMap
    (D' : ↥(pushCoveringB C hC).covers) (D₃ : RationalLocData (JetB F))
    (h₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D'.1.T D'.1.s) :
    restrictionMap D'.1 D₃ h₃ (pushedFamilyB C hC f D') =
      restrictionMap (pushDatumB (Finset.mem_image.mp D'.2).choose.1
          (hC.piece (Finset.mem_image.mp D'.2).choose.2)) D₃
        (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]; exact h₃)
        (presheafValueMapB (Finset.mem_image.mp D'.2).choose.1
          (hC.piece (Finset.mem_image.mp D'.2).choose.2)
          (f (Finset.mem_image.mp D'.2).choose)) := by
  show restrictionMap D'.1 D₃ h₃
    ((Finset.mem_image.mp D'.2).choose_spec.2 ▸
      presheafValueMapB (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)
        (f (Finset.mem_image.mp D'.2).choose)) = _
  exact restrictionMap_cast_restrictionMap _ D₃ h₃ _

/-- The 𝓒-mirror of `pushedFamilyB_restrictionMap`. -/
private theorem pushedFamilyC_restrictionMap
    (D' : ↥(pushCoveringC C hC).covers) (D₃ : RationalLocData (JetC F))
    (h₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D'.1.T D'.1.s) :
    restrictionMap D'.1 D₃ h₃ (pushedFamilyC C hC f D') =
      restrictionMap (pushDatumC (Finset.mem_image.mp D'.2).choose.1
          (hC.piece (Finset.mem_image.mp D'.2).choose.2)) D₃
        (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]; exact h₃)
        (presheafValueMapC (Finset.mem_image.mp D'.2).choose.1
          (hC.piece (Finset.mem_image.mp D'.2).choose.2)
          (f (Finset.mem_image.mp D'.2).choose)) := by
  show restrictionMap D'.1 D₃ h₃
    ((Finset.mem_image.mp D'.2).choose_spec.2 ▸
      presheafValueMapC (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)
        (f (Finset.mem_image.mp D'.2).choose)) = _
  exact restrictionMap_cast_restrictionMap _ D₃ h₃ _

include hcompat in
/-- At the canonical piece `pushDatumB d.1 (hC.piece d.2)`, the pushed family is exactly the
𝓑-push of `f d` — independent of which preimage the choice picked, by `hcompat`. -/
private theorem pushedFamilyB_apply_piece (d : ↥C.covers) :
    pushedFamilyB C hC f ⟨pushDatumB d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ =
      presheafValueMapB d.1 (hC.piece d.2) (f d) := by
  have hselfB := pushedFamilyB_restrictionMap C hC f ⟨pushDatumB d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
    (pushDatumB d.1 (hC.piece d.2)) (subset_refl _)
  simp only [restrictionMap_id, id_eq] at hselfB
  rw [hselfB,
    pushedCompatB C hC f hcompat
      (Finset.mem_image.mp (Finset.mem_image.mpr
        ⟨d, Finset.mem_attach _ _, rfl⟩ : pushDatumB d.1 (hC.piece d.2) ∈
          (pushCoveringB C hC).covers)).choose d
      (pushDatumB d.1 (hC.piece d.2)) _ (subset_refl _)]
  exact congrFun (restrictionMap_id (pushDatumB d.1 (hC.piece d.2))) _

include hcompat in
/-- The 𝓒-mirror of `pushedFamilyB_apply_piece`. -/
private theorem pushedFamilyC_apply_piece (d : ↥C.covers) :
    pushedFamilyC C hC f ⟨pushDatumC d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ =
      presheafValueMapC d.1 (hC.piece d.2) (f d) := by
  have hselfC := pushedFamilyC_restrictionMap C hC f ⟨pushDatumC d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
    (pushDatumC d.1 (hC.piece d.2)) (subset_refl _)
  simp only [restrictionMap_id, id_eq] at hselfC
  rw [hselfC,
    pushedCompatC C hC f hcompat
      (Finset.mem_image.mp (Finset.mem_image.mpr
        ⟨d, Finset.mem_attach _ _, rfl⟩ : pushDatumC d.1 (hC.piece d.2) ∈
          (pushCoveringC C hC).covers)).choose d
      (pushDatumC d.1 (hC.piece d.2)) _ (subset_refl _)]
  exact congrFun (restrictionMap_id (pushDatumC d.1 (hC.piece d.2))) _

include hcompat in
/-- **The 𝓑-vertex gluing**: the pushed family is compatible (by `pushedCompatB`, after
`pushedFamilyB_restrictionMap` clears the transports), so sheafiness of `JetB` glues it. -/
private theorem exists_gluing_pushedFamilyB :
    ∃ bB : presheafValue (pushCoveringB C hC).base,
      ∀ D' : ↥(pushCoveringB C hC).covers,
        restrictionMap (pushCoveringB C hC).base D'.1
          ((pushCoveringB C hC).hsubset D'.1 D'.2) bB = pushedFamilyB C hC f D' := by
  haveI : IsSheafy (JetB F) := isSheafy_JetB F
  exact IsSheafy.gluing (A := JetB F) (pushCoveringB C hC)
    (pushCoveringB_isRational hC) (pushedFamilyB C hC f) (by
      intro D₁' D₂' D₃ h₃₁ h₃₂
      rw [pushedFamilyB_restrictionMap C hC f D₁' D₃ h₃₁,
        pushedFamilyB_restrictionMap C hC f D₂' D₃ h₃₂]
      exact pushedCompatB C hC f hcompat _ _ D₃ _ _)

include hcompat in
/-- The 𝓒-mirror of `exists_gluing_pushedFamilyB`. -/
private theorem exists_gluing_pushedFamilyC :
    ∃ bC : presheafValue (pushCoveringC C hC).base,
      ∀ D' : ↥(pushCoveringC C hC).covers,
        restrictionMap (pushCoveringC C hC).base D'.1
          ((pushCoveringC C hC).hsubset D'.1 D'.2) bC = pushedFamilyC C hC f D' := by
  haveI : IsSheafy (JetC F) := isSheafy_JetC F
  exact IsSheafy.gluing (A := JetC F) (pushCoveringC C hC)
    (pushCoveringC_isRational hC) (pushedFamilyC C hC f) (by
      intro D₁' D₂' D₃ h₃₁ h₃₂
      rw [pushedFamilyC_restrictionMap C hC f D₁' D₃ h₃₁,
        pushedFamilyC_restrictionMap C hC f D₂' D₃ h₃₂]
      exact pushedCompatC C hC f hcompat _ _ D₃ _ _)

include hcompat in
/-- **The piecewise identification** ([FJP] Lemma 5.2, closing step of the gluing half): a
candidate section `x` whose 𝓑- and 𝓒-pushes are the two vertex gluings restricts, at every
piece `d`, to `f d`.

Both vertices are checked separately and combined by `pairMapBC_injective`; the two bullets
are 𝓑/𝓒 mirrors of one another. Extracted from `gluing_JetA` so that it carries its own
elaboration budget. -/
private theorem restrictionMap_eq_of_vertex_pushes
    (x : presheafValue C.base)
    (bB : presheafValue (pushCoveringB C hC).base)
    (bC : presheafValue (pushCoveringC C hC).base)
    (hbB : ∀ D' : ↥(pushCoveringB C hC).covers,
      restrictionMap (pushCoveringB C hC).base D'.1
        ((pushCoveringB C hC).hsubset D'.1 D'.2) bB = pushedFamilyB C hC f D')
    (hbC : ∀ D' : ↥(pushCoveringC C hC).covers,
      restrictionMap (pushCoveringC C hC).base D'.1
        ((pushCoveringC C hC).hsubset D'.1 D'.2) bC = pushedFamilyC C hC f D')
    (hmapBx : presheafValueMapB C.base hC.base x = bB)
    (hmapCx : presheafValueMapC C.base hC.base x = bC)
    (d : ↥C.covers) :
    restrictionMap C.base d.1 (C.hsubset d.1 d.2) x = f d := by
  have hpushB : rationalOpen (pushDatumB d.1 (hC.piece d.2)).T
      (pushDatumB d.1 (hC.piece d.2)).s ⊆
      rationalOpen (pushDatumB C.base hC.base).T (pushDatumB C.base hC.base).s :=
    (pushCoveringB C hC).hsubset _
      (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
  have hpushC : rationalOpen (pushDatumC d.1 (hC.piece d.2)).T
      (pushDatumC d.1 (hC.piece d.2)).s ⊆
      rationalOpen (pushDatumC C.base hC.base).T (pushDatumC C.base hC.base).s :=
    (pushCoveringC C hC).hsubset _
      (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
  refine pairMapBC_injective d.1 (hC.piece d.2) ?_ ?_
  · rw [presheafValueMapB_restriction C.base d.1 hC.base (hC.piece d.2)
      (C.hsubset d.1 d.2) hpushB x, hmapBx]
    rw [show restrictionMap (pushDatumB C.base hC.base)
        (pushDatumB d.1 (hC.piece d.2)) hpushB bB =
        pushedFamilyB C hC f ⟨pushDatumB d.1 (hC.piece d.2),
          Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from
      hbB ⟨pushDatumB d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩]
    exact pushedFamilyB_apply_piece C hC f hcompat d
  · rw [presheafValueMapC_restriction C.base d.1 hC.base (hC.piece d.2)
      (C.hsubset d.1 d.2) hpushC x, hmapCx]
    rw [show restrictionMap (pushDatumC C.base hC.base)
        (pushDatumC d.1 (hC.piece d.2)) hpushC bC =
        pushedFamilyC C hC f ⟨pushDatumC d.1 (hC.piece d.2),
          Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from
      hbC ⟨pushDatumC d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩]
    exact pushedFamilyC_apply_piece C hC f hcompat d

include hC hcompat in
/-- The gluing transfer ([FJP] Lemma 5.2, gluing half). -/
theorem gluing_JetA :
    ∃ x : presheafValue C.base, ∀ D : ↥C.covers,
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  classical
  haveI : IsSheafy (JetB F) := isSheafy_JetB F
  haveI : IsSheafy (JetC F) := isSheafy_JetC F
  haveI : IsSheafy (JetD F) := isSheafy_JetD F
  set e := datumEnum C.base with he
  -- the pushed families, their vertex gluings and the closing identification are all
  -- standalone now, so each carries its own elaboration budget
  obtain ⟨bB, hbB⟩ := exists_gluing_pushedFamilyB C hC f hcompat
  obtain ⟨bC, hbC⟩ := exists_gluing_pushedFamilyC C hC f hcompat
  -- 𝓓-matching by 𝓓-separation on the pushed covering
  have hDmatch : mapBD C.base hC.base bB = mapCD C.base hC.base bC :=
    mapBD_eq_mapCD_of_pushed_gluing C hC f (pushedFamilyB C hC f) (pushedFamilyC C hC f)
      bB bC hbB hbC (pushedFamilyB_apply_piece C hC f hcompat)
      (pushedFamilyC_apply_piece C hC f hcompat)
  -- transport through the base bridges: loc-level row exactness gives the pullback
  have hloc : locRhoB F e.m C.base.s e.f (bridgeFwdB C.base e hC.base bB) =
      locRhoC F e.m C.base.s e.f (bridgeFwdC C.base e hC.base bC) := by
    have hB : locRhoB F e.m C.base.s e.f (bridgeFwdB C.base e hC.base bB) =
        bridgeFwdD C.base e hC.base (mapBD C.base hC.base bB) :=
      DFunLike.congr_fun (locRhoB_bridgeFwdB C.base e hC.base) bB
    have hCq : locRhoC F e.m C.base.s e.f (bridgeFwdC C.base e hC.base bC) =
        bridgeFwdD C.base e hC.base (mapCD C.base hC.base bC) :=
      DFunLike.congr_fun (locRhoC_bridgeFwdC C.base e hC.base) bC
    rw [hB, hCq, hDmatch]
  obtain ⟨w, ⟨hwB, hwC⟩, -⟩ := loc_row_exact F e.m C.base.s e.f
    (e.span_eq_top C.base hC.base) (bridgeFwdB C.base e hC.base bB)
    (bridgeFwdC C.base e hC.base bC) hloc
  set x := (graphBridgeA C.base hC.base e).symm w with hx
  have hAx : graphBridgeA C.base hC.base e x = w :=
    (graphBridgeA C.base hC.base e).apply_symm_apply w
  have hmapBx : presheafValueMapB C.base hC.base x = bB := by
    refine bridgeFwdB_injective C.base e hC.base ?_
    have hnat : bridgeFwdB C.base e hC.base (presheafValueMapB C.base hC.base x) =
        locJB F e.m C.base.s e.f (graphBridgeA C.base hC.base e x) :=
      DFunLike.congr_fun (graphBridge_natural_B C.base hC.base e) x
    rw [hnat, hAx, hwB]
  have hmapCx : presheafValueMapC C.base hC.base x = bC := by
    refine bridgeFwdC_injective C.base e hC.base ?_
    have hnat : bridgeFwdC C.base e hC.base (presheafValueMapC C.base hC.base x) =
        locIotaC F e.m C.base.s e.f (graphBridgeA C.base hC.base e x) :=
      DFunLike.congr_fun (graphBridge_natural_C C.base hC.base e) x
    rw [hnat, hAx, hwC]
  exact ⟨x, fun d => restrictionMap_eq_of_vertex_pushes C hC f hcompat x bB bC hbB hbC
    hmapBx hmapCx d⟩

end Gluing

/-- The range of `productRestrictionSub` is exactly the section equalizer: one inclusion is
`productRestrictionSub_mem_sectionEqualizer`, the other is gluing. -/
private theorem range_productRestrictionSub_eq_sectionEqualizer
    (C : RationalCoveringData (JetA F)) (hC : C.IsRational) :
    Set.range (productRestrictionSub (JetA F) C) = sectionEqualizer (JetA F) C := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    exact productRestrictionSub_mem_sectionEqualizer (JetA F) C x
  · intro hs
    obtain ⟨x, hx⟩ := gluing_JetA C hC s hs
    exact ⟨x, funext fun D => hx D⟩

/-- The embedding transfer ([FJP] Lemma 5.2, topological half; Theorem 5.3's "the Banach
open mapping theorem makes the continuous bijection onto that image a homeomorphism" —
the σ-compact-free 828b-assembly mirrored at 𝓐). -/
theorem productRestrictionSub_isEmbedding_JetA (C : RationalCoveringData (JetA F))
    (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub (JetA F) C) := by
  classical
  refine ⟨?_, productRestrictionSub_injective_JetA C hC⟩
  letI instModPiD : ∀ D : ↥C.covers, Module (JetA F) (presheafValue D.1) :=
    fun D => RingHom.toModule (RationalLocData.canonicalMap D.1)
  letI instModBase : Module (JetA F) (presheafValue C.base) :=
    RingHom.toModule (RationalLocData.canonicalMap C.base)
  letI instModPi : Module (JetA F) (∀ D : ↥C.covers, presheafValue D.1) := Pi.module _ _ _
  let rho : presheafValue C.base →ₗ[JetA F] (∀ D : ↥C.covers, presheafValue D.1) :=
    { toFun := productRestrictionSub (JetA F) C
      map_add' := fun x y => by
        funext D
        exact map_add (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) x y
      map_smul' := fun a x => by
        funext D
        show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)
            ((RationalLocData.canonicalMap C.base) a * x) =
          (RationalLocData.canonicalMap D.1) a *
            restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x
        rw [map_mul]
        congr 1
        exact productRestriction_comp_canonicalMap (A := JetA F) C a D.1 D.2 }
  have hrange : (LinearMap.range rho : Set (∀ D : ↥C.covers, presheafValue D.1)) =
      sectionEqualizer (JetA F) C :=
    range_productRestrictionSub_eq_sectionEqualizer C hC
  have hclosed : IsClosed
      (LinearMap.range rho : Set (∀ D : ↥C.covers, presheafValue D.1)) := by
    rw [hrange]; exact sectionEqualizer_isClosed (JetA F) C
  haveI : (uniformity (presheafValue C.base)).IsCountablyGenerated :=
    presheafValue_uniformity_isCountablyGenerated (A := JetA F) C.base
  haveI : ∀ D : ↥C.covers, (uniformity (presheafValue D.1)).IsCountablyGenerated :=
    fun D => presheafValue_uniformity_isCountablyGenerated (A := JetA F) D.1
  haveI : ContinuousSMul (JetA F) (presheafValue C.base) :=
    ⟨continuous_mul.comp (((canonicalMap_continuous C.base).comp continuous_fst).prodMk
      continuous_snd)⟩
  haveI : ∀ D : ↥C.covers, ContinuousSMul (JetA F) (presheafValue D.1) :=
    fun D => ⟨continuous_mul.comp
      (((canonicalMap_continuous D.1).comp continuous_fst).prodMk continuous_snd)⟩
  haveI : ContinuousSMul (JetA F) (∀ D : ↥C.covers, presheafValue D.1) := inferInstance
  have hrho_cont : Continuous rho :=
    continuous_pi fun D => restrictionMapHom_continuous C.base D.1 (C.hsubset D.1 D.2)
  have hinj : Function.Injective (rho : presheafValue C.base → _) := fun x y h =>
    productRestrictionSub_injective_JetA C hC h
  obtain ⟨ϖ, hϖ⟩ := (inferInstance : IsTateRing (JetA F)).exists_topologicallyNilpotent_unit
  exact @isInducing_of_closedRange_of_topNilpUnit (JetA F) _ _
    (presheafValue C.base) _ instModBase _ _ _ _ _
    (∀ D : ↥C.covers, presheafValue D.1) _ instModPi _ _ _ _ _ _
    ϖ hϖ ϖ.isUnit rho hrho_cont hinj hclosed

variable (F)

/-- **The finite-jet pinching algebra is sheafy** ([FJP] Theorem 5.3). This is the
priority theorem of the campaign. -/
theorem isSheafy_JetA : ValuationSpectrum.IsSheafy (JetA F) where
  embedding := fun C hC => productRestrictionSub_isEmbedding_JetA C hC
  gluing := fun C hC f hcompat => gluing_JetA C hC f hcompat

end FiniteJet
