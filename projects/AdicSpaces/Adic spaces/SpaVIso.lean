/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI contributors
-/
import «Adic spaces».RelativePieceKeystoneOpen
import «Adic spaces».NonTateRationalOpenHomeomorph
import «Adic spaces».SpaVObj
import «Adic spaces».VRestrict

/-!
# `Spa` of a rational localization as a `𝒱`-object over the base (Campaign 9, P5-K)

Towards Wedhorn Definition 8.22 for the Fargues–Fontaine curve: the
comparison `(Spa A)|_{spaOpens D₀} ≅ Spa 𝒪_X(D₀)` in `𝒱`.

This file builds the substrate:
* `spaOpensHomeoInter` — the double-subtype presentation `↥(spaOpens D)`
  and the intersection presentation inside `Spv A` agree topologically;
* `imgDatum` / `imgIdx` — the `B`-side rational datum (and projective-limit
  index) attached to a valid `A`-side datum, with the open correspondence
  `mem_imgDatum_iff`;
* `pieceEquiv` — the keystone ring comparison
  `𝒪_A(E) ≃+* 𝒪_B(im E)` at `hopen`-only data (`OpenKeystone`), and
  `pieceEquiv_restrict`, the square saying these comparisons intertwine the
  restriction maps on both sides.
-/


open CategoryTheory TopologicalSpace Opposite

noncomputable section

universe u

namespace ValuationSpectrum

namespace SpaVIso

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [IsRingOfIntegralElements (A⁺ : Subring A)]

/-- The two presentations of a rational subset as a topological space —
the double subtype `↥(spaOpens D)` inside `↥(Spa A A⁺)` and the
intersection subtype inside `Spv A` — agree. -/
def spaOpensEquivInter (D : RationalLocData A) :
    ↥(spaOpens D) ≃ ↥(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) where
  toFun v := ⟨((v : ↥(Spa A A⁺)) : Spv A), v.2, (v : ↥(Spa A A⁺)).2⟩
  invFun w := ⟨⟨(w : Spv A), w.2.2⟩, w.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem spaOpensEquivInter_continuous (D : RationalLocData A) :
    Continuous (spaOpensEquivInter D) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.comp continuous_subtype_val

theorem spaOpensEquivInter_symm_continuous (D : RationalLocData A) :
    Continuous (spaOpensEquivInter D).symm := by
  exact ((continuous_subtype_val (p := fun w : Spv A =>
    w ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))).subtype_mk _).subtype_mk _

/-- The double-subtype and intersection presentations are homeomorphic. -/
def spaOpensHomeoInter (D : RationalLocData A) :
    ↥(spaOpens D) ≃ₜ ↥(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) :=
  { toEquiv := spaOpensEquivInter D
    continuous_toFun := spaOpensEquivInter_continuous D
    continuous_invFun := spaOpensEquivInter_symm_continuous D }

section Comparison

variable [T2Space A] [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
    CompleteSpace A]

variable (D₀ : RationalLocData A) [IsTateRing (presheafValue D₀)]
  [IsNoetherianRing (presheafValue D₀)] [IsStronglyNoetherian (presheafValue D₀)]

open OpenKeystone

/-- The power certificate of a valid datum at the base pair of `D₀`. -/
def certExp {E : RationalLocData A} (hE : E.IsRational) : ℕ :=
  (exists_pow_le_of_isRational_pair D₀.P E hE).choose

theorem certExp_spec {E : RationalLocData A} (hE : E.IsRational) :
    (Ideal.span (D₀.P.A₀.subtype '' (D₀.P.I : Set D₀.P.A₀))) ^ certExp D₀ hE
      ≤ Ideal.span ((E.T : Finset A) : Set A) :=
  (exists_pow_le_of_isRational_pair D₀.P E hE).choose_spec

/-- **The image datum of a valid `A`-side datum** — the `B`-side rational
datum presenting the same subset through the canonical homeomorphism. -/
noncomputable def imgDatum {E : RationalLocData A} (hE : E.IsRational) :
    RationalLocData (presheafValue D₀) :=
  OpenKeystone.imagePieceDatumOpen D₀ E.T E.s (certExp D₀ hE) (certExp_spec D₀ hE)

theorem imgDatum_isRational {E : RationalLocData A} (hE : E.IsRational) :
    (imgDatum D₀ hE).IsRational :=
  OpenKeystone.imagePieceDatum_isRational D₀ E.T E.s (certExp D₀ hE) (certExp_spec D₀ hE)

/-- **The open correspondence**: a `Spa B`-point lies in the image datum's
rational open exactly when its `A`-shadow lies in the original one. -/
theorem mem_imgDatum_iff {E : RationalLocData A} (hE : E.IsRational)
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) :
    (w : Spv (presheafValue D₀)) ∈ rationalOpen (imgDatum D₀ hE).T (imgDatum D₀ hE).s
      ↔ comap D₀.canonicalMap (w : Spv (presheafValue D₀))
          ∈ rationalOpen E.T E.s := by
  have h := OpenKeystone.imagePieceDatum_mem_rationalOpen_iff D₀ E (certExp D₀ hE)
    (certExp_spec D₀ hE) (w : Spv (presheafValue D₀))
  exact ⟨fun hw => (h.mp hw).2, fun hw => h.mpr ⟨w.2, hw⟩⟩

/-- The `B`-side index attached to a valid `A`-side datum whose shadow-preimage
lands in `W`. -/
def imgIdx (W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    {E : RationalLocData A} (hE : E.IsRational)
    (hsub : ∀ w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺),
      comap D₀.canonicalMap (w : Spv (presheafValue D₀)) ∈ rationalOpen E.T E.s →
      w ∈ W) :
    RationalIndex W where
  D := imgDatum D₀ hE
  isRational := imgDatum_isRational D₀ hE
  subset := fun w hw => hsub w ((mem_imgDatum_iff D₀ hE w).mp hw)

@[simp] theorem imgIdx_D
    (W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    {E : RationalLocData A} (hE : E.IsRational)
    (hsub : ∀ w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺),
      comap D₀.canonicalMap (w : Spv (presheafValue D₀)) ∈ rationalOpen E.T E.s →
      w ∈ W) :
    (imgIdx D₀ W hE hsub).D = imgDatum D₀ hE := rfl

/-- The keystone comparison at a valid `A`-side datum inside `D₀`. -/
noncomputable def pieceEquiv {E : RationalLocData A} (hE : E.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s) :
    presheafValue E ≃+* presheafValue (imgDatum D₀ hE) :=
  OpenKeystone.relativePiece_equiv D₀ E hE_sub (certExp D₀ hE) (certExp_spec D₀ hE)

/-- **The comparison square**: the keystone comparisons intertwine the `A`-side
and `B`-side restriction maps. -/
theorem pieceEquiv_restrict {E E' : RationalLocData A} (hE : E.IsRational)
    (hE' : E'.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (hE'_sub : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s)
    (y : presheafValue E) :
      haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
    pieceEquiv D₀ hE' (hE'_sub.trans hE_sub) (restrictionMap E E' hE'_sub y)
      = restrictionMap (imgDatum D₀ hE) (imgDatum D₀ hE')
          (OpenKeystone.imagePieceDatum_rationalOpen_mono D₀ E E'
            (certExp D₀ hE) (certExp_spec D₀ hE)
            (certExp D₀ hE') (certExp_spec D₀ hE') hE'_sub)
          (pieceEquiv D₀ hE hE_sub y) :=
  OpenKeystone.relativePiece_equiv_restrict_square D₀ E E' hE_sub hE'_sub
    (certExp D₀ hE) (certExp_spec D₀ hE) (certExp D₀ hE') (certExp_spec D₀ hE') y

end Comparison

section Phi


variable [T2Space A] [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
    CompleteSpace A]

variable (D₀ : RationalLocData A) [IsTateRing (presheafValue D₀)]
  [IsNoetherianRing (presheafValue D₀)] [IsStronglyNoetherian (presheafValue D₀)]

/-- The `A`-shadow of a `Spa B`-point is a `Spa A`-point. -/
theorem comap_mem_spa (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) :
    comap D₀.canonicalMap (w : Spv (presheafValue D₀)) ∈ Spa A A⁺ :=
  ValuationSpectrum.comap_mem_spa (canonicalMap_continuous D₀)
    D₀.canonicalMap_integral w.2

/-- The `A`-shadow as a `Spa A`-point. -/
def shadow (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) : ↥(Spa A A⁺) :=
  ⟨comap D₀.canonicalMap (w : Spv (presheafValue D₀)), comap_mem_spa D₀ w⟩

/-- `W` is the shadow-preimage of `V`: a `Spa B`-point lies in `W` exactly
when its `A`-shadow lies in `V`. -/
def Paired (V : Opens ↥(Spa A A⁺))
    (W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) : Prop :=
  ∀ w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺),
    (shadow D₀ w ∈ V ↔ w ∈ W)

theorem paired_apply {V : Opens ↥(Spa A A⁺)}
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (h : Paired D₀ V W) (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    (hw : shadow D₀ w ∈ V) : w ∈ W :=
  (h w).mp hw

theorem paired_shadow {V : Opens ↥(Spa A A⁺)}
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (h : Paired D₀ V W) (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    (hw : w ∈ W) : shadow D₀ w ∈ V :=
  (h w).mpr hw

/-- Under a pairing, a valid `A`-index of `V` produces a `B`-index of `W`. -/
def idxOf {V : Opens ↥(Spa A A⁺)}
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (i : RationalIndex V) : RationalIndex W :=
  imgIdx D₀ W i.isRational fun w hw =>
    paired_apply D₀ hVW w (i.subset (show shadow D₀ w ∈ spaOpen i.D from hw))

@[simp] theorem idxOf_D {V : Opens ↥(Spa A A⁺)}
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (i : RationalIndex V) :
    (idxOf D₀ hVW i).D = imgDatum D₀ i.isRational := rfl

/-- An `A`-index of an open inside `spaOpens D₀` sits inside `D₀`. -/
theorem index_sub {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    (i : RationalIndex V) :
    rationalOpen i.D.T i.D.s ⊆ rationalOpen D₀.T D₀.s :=
  spaOpen_subset_iff.mp (i.subset.trans hV)

/-- **The comparison map, componentwise**: the `A`-side value of a `B`-side
compatible family at a valid `A`-index. -/
noncomputable def phiComp {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (x : ↥(limitSections W)) (i : RationalIndex V) :
    presheafValue i.D :=
  (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm
    (limitEvalHom (idxOf D₀ hVW i) x)

/-- **The comparison map is a compatible family**: the keystone square
transports the `B`-side compatibility to the `A` side. -/
theorem phiComp_compat {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (x : ↥(limitSections W))
    (i j : RationalIndex V)
    (h : rationalOpen j.D.T j.D.s ⊆ rationalOpen i.D.T i.D.s) :
    restrictionMap i.D j.D h (phiComp D₀ hV hVW x i) = phiComp D₀ hV hVW x j := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  -- the B-side compatibility of `x` at the two image indices
  have hB : restrictionMap (imgDatum D₀ i.isRational) (imgDatum D₀ j.isRational)
      (OpenKeystone.imagePieceDatum_rationalOpen_mono D₀ i.D j.D
        (certExp D₀ i.isRational) (certExp_spec D₀ i.isRational)
        (certExp D₀ j.isRational) (certExp_spec D₀ j.isRational) h)
      (limitEvalHom (idxOf D₀ hVW i) x)
      = limitEvalHom (idxOf D₀ hVW j) x :=
    x.2 (idxOf D₀ hVW i) (idxOf D₀ hVW j) _
  -- the keystone square at the A-side value
  have hsq := pieceEquiv_restrict D₀ i.isRational j.isRational
    (index_sub D₀ hV i) h (phiComp D₀ hV hVW x i)
  have hcancel : pieceEquiv D₀ i.isRational (index_sub D₀ hV i)
      (phiComp D₀ hV hVW x i) = limitEvalHom (idxOf D₀ hVW i) x :=
    RingEquiv.apply_symm_apply _ _
  rw [hcancel] at hsq
  rw [hB] at hsq
  have := congrArg (pieceEquiv D₀ j.isRational (index_sub D₀ hV j)).symm hsq
  rwa [RingEquiv.symm_apply_apply] at this

/-- **The comparison ring homomorphism** `𝒪_B(W) → 𝒪_A(V)`: componentwise the
inverse keystone comparison at the image index. -/
noncomputable def phiHom {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) :
    ↥(limitSections W) →+* ↥(limitSections V) where
  toFun x := ⟨phiComp D₀ hV hVW x, phiComp_compat D₀ hV hVW x⟩
  map_one' := Subtype.ext (funext fun i =>
    ((pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm.congr_arg
        (map_one (limitEvalHom (idxOf D₀ hVW i)))).trans
      (map_one (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm))
  map_mul' x y := Subtype.ext (funext fun i =>
    ((pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm.congr_arg
        (map_mul (limitEvalHom (idxOf D₀ hVW i)) x y)).trans
      (map_mul (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm _ _))
  map_zero' := Subtype.ext (funext fun i =>
    ((pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm.congr_arg
        (map_zero (limitEvalHom (idxOf D₀ hVW i)))).trans
      (map_zero (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm))
  map_add' x y := Subtype.ext (funext fun i =>
    ((pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm.congr_arg
        (map_add (limitEvalHom (idxOf D₀ hVW i)) x y)).trans
      (map_add (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm _ _))

@[simp] theorem phiHom_apply_component {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (x : ↥(limitSections W)) (i : RationalIndex V) :
    limitEvalHom i (phiHom D₀ hV hVW x)
      = (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm
          (limitEvalHom (idxOf D₀ hVW i) x) := rfl

/-- **The image opens are a basis** (P5-K2): every `Spa B`-point of a rational
open of `B` has a neighbourhood of the form `spaOpen_B (imgDatum E)` for a
valid `A`-side datum `E` inside `D₀`, still inside the given rational open.

Huber's approximation argument (`exists_A_level_open_presentation'`) captures
the `B`-side conditions by an `A`-level open; the `A`-rational basis
(`exists_isRational_spaOpen_subset_huber`) then produces `E`. -/
theorem exists_imgDatum_subset [DecidableEq A]
    (F : RationalLocData (presheafValue D₀))
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    (hw : (w : Spv (presheafValue D₀)) ∈ rationalOpen F.T F.s) :
    ∃ (E : RationalLocData A) (hE : E.IsRational),
      rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s ∧
      (w : Spv (presheafValue D₀)) ∈
        rationalOpen (imgDatum D₀ hE).T (imgDatum D₀ hE).s ∧
      rationalOpen (imgDatum D₀ hE).T (imgDatum D₀ hE).s
        ⊆ rationalOpen F.T F.s := by
  classical
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  obtain ⟨u, hu⟩ := (inferInstance : IsTateRing (presheafValue D₀)
    ).exists_topologicallyNilpotent_unit
  -- the `B`-side conditions defining `F` at `w`
  have hmem : ∀ t ∈ insert F.s F.T,
      (w : Spv (presheafValue D₀)) ∈ basicOpen t F.s := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact ⟨vle_refl _, hw.2.2⟩
    · exact ⟨hw.2.1 t ht', hw.2.2⟩
  obtain ⟨Wset, hWopen, hWmem, hWcap⟩ := exists_A_level_open_presentation'
    D₀ u hu w.2 (ι := presheafValue D₀) (fam := insert F.s F.T)
    (F := fun t => t) (G := fun _ => F.s) hmem
  -- the `A`-level open neighbourhood of the shadow, inside `D₀`
  have hshadow : shadow D₀ w ∈ (Subtype.val ⁻¹' Wset ∩ spaOpen D₀
      : Set ↥(Spa A A⁺)) :=
    ⟨hWmem, (comap_canonicalMap_mem_rationalOpen_inter_spa D₀ w).1⟩
  obtain ⟨E, hE, hEmem, hEsub⟩ := exists_isRational_spaOpen_subset_huber
    (V := (Subtype.val ⁻¹' Wset ∩ spaOpen D₀ : Set ↥(Spa A A⁺)))
    (IsOpen.inter (hWopen.preimage continuous_subtype_val) (isOpen_spaOpen D₀))
    hshadow
  refine ⟨E, hE, spaOpen_subset_iff.mp (hEsub.trans Set.inter_subset_right), ?_, ?_⟩
  · exact (mem_imgDatum_iff D₀ hE w).mpr hEmem
  · intro w' hw'
    have hw'spa : w' ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ := hw'.1
    have hshad : shadow D₀ ⟨w', hw'spa⟩ ∈ spaOpen E :=
      (mem_imgDatum_iff D₀ hE ⟨w', hw'spa⟩).mp hw'
    have hin : comap D₀.canonicalMap w' ∈ Wset := (hEsub hshad).1
    have hcap := hWcap w' hw'spa hin
    exact ⟨hw'spa, fun t ht => (hcap t (Finset.mem_insert_of_mem ht)).1,
      (hcap F.s (Finset.mem_insert_self _ _)).2⟩

/-- **The image opens cover** (P5-K2b): every point of `W` lies in the image
open of some valid `A`-index of `V`. -/
theorem exists_index_mem [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W)
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) (hw : w ∈ W) :
    ∃ i : RationalIndex V, (w : Spv (presheafValue D₀))
      ∈ rationalOpen (imgDatum D₀ i.isRational).T (imgDatum D₀ i.isRational).s := by
  classical
  obtain ⟨E, hE, hEmem, hEsub⟩ := exists_isRational_spaOpen_subset_huber
    (V := (V : Set ↥(Spa A A⁺))) V.2 (paired_shadow D₀ hVW w hw)
  exact ⟨⟨E, hE, hEsub⟩, (mem_imgDatum_iff D₀ hE w).mpr hEmem⟩

/-- The `B`-side open of an `A`-index. -/
def imgOpens {V : Opens ↥(Spa A A⁺)} (i : RationalIndex V) :
    Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺) :=
  spaOpens (imgDatum D₀ i.isRational)

theorem imgOpens_le {V : Opens ↥(Spa A A⁺)}
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (i : RationalIndex V) : imgOpens D₀ i ≤ W :=
  (idxOf D₀ hVW i).subset

theorem imgOpens_cover [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) :
    (W : Set ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
      ⊆ ⋃ i : RationalIndex V,
          (imgOpens D₀ i : Set ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) := by
  intro w hw
  obtain ⟨i, hi⟩ := exists_index_mem D₀ hV hVW w hw
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The projective-limit sheaf condition for the value ring. -/
theorem isLimitSheaf_value : IsLimitSheaf (presheafValue D₀) := by
  classical
  haveI : IsNoetherianRing (presheafValue D₀) :=
    IsStronglyNoetherian.isNoetherianRing (presheafValue D₀)
  haveI : IsSheafy (presheafValue D₀) := isSheafy_of_stronglyNoetherian_828b
  exact isLimitSheaf_of_isSheafy

/-- **The comparison map kills nothing** (P5-K4): a `B`-side family whose
`A`-side comparison vanishes vanishes on every image open, hence everywhere
by separatedness of `𝒪_B` on the image-open cover. -/
theorem phiHom_injective [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) :
    Function.Injective (phiHom D₀ hV hVW) := by
  classical
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  -- the components at image indices vanish
  have hzero : ∀ i : RationalIndex V, limitEvalHom (idxOf D₀ hVW i) x = 0 := by
    intro i
    have h1 : (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm
        (limitEvalHom (idxOf D₀ hVW i) x) = 0 := by
      rw [← phiHom_apply_component D₀ hV hVW x i, hx]
      exact map_zero (limitEvalHom i)
    exact ((RingEquiv.apply_symm_apply
        (pieceEquiv D₀ i.isRational (index_sub D₀ hV i))
        (limitEvalHom (idxOf D₀ hVW i) x)).symm.trans
      (congrArg (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)) h1)).trans
      (map_zero _)
  -- hence the restriction to every image open vanishes
  refine (isLimitSheaf_value D₀).injective (U := imgOpens D₀ (A := A) (V := V))
    (imgOpens_le D₀ hVW) (imgOpens_cover D₀ hV hVW) fun i => ?_
  refine Subtype.ext (funext fun k => ?_)
  show (x : ∀ j : RationalIndex W, presheafValue j.D)
      (k.mono (imgOpens_le D₀ hVW i)) = _
  have hsub : rationalOpen k.D.T k.D.s
      ⊆ rationalOpen (idxOf D₀ hVW i).D.T (idxOf D₀ hVW i).D.s :=
    spaOpen_subset_iff.mp k.subset
  have hcompat := x.2 (idxOf D₀ hVW i) (k.mono (imgOpens_le D₀ hVW i)) hsub
  rw [← hcompat]
  show restrictionMap _ _ _ (limitEvalHom (idxOf D₀ hVW i) x) = _
  rw [hzero i]
  exact map_zero (restrictionMapHom (idxOf D₀ hVW i).D
    (RationalIndex.mono (imgOpens_le D₀ hVW i) k).D hsub)

end Phi

end SpaVIso

end ValuationSpectrum

end
