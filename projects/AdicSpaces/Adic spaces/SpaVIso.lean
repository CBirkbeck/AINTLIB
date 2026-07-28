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

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace ValuationSpectrum

namespace SpaVIso

/-- The inverse of a bijective ring hom is any two-sided-inverse ring hom. -/
theorem ofBijective_symm_apply {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f) (g : S →+* R)
    (h : ∀ x, g (f x) = x) (y : S) :
    (RingEquiv.ofBijective f hf).symm y = g y := by
  obtain ⟨x, rfl⟩ := hf.2 y
  rw [h x]
  exact (RingEquiv.ofBijective f hf).symm_apply_apply x

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

/-- The image-open comparison is monotone in the `A`-side datum. -/
theorem imgDatum_mono {E E' : RationalLocData A} (hE : E.IsRational)
    (hE' : E'.IsRational)
    (h : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s) :
    rationalOpen (imgDatum D₀ hE').T (imgDatum D₀ hE').s
      ⊆ rationalOpen (imgDatum D₀ hE).T (imgDatum D₀ hE).s := by
  intro w hw
  have hspa : w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ := hw.1
  exact (mem_imgDatum_iff D₀ hE ⟨w, hspa⟩).mpr
    (h ((mem_imgDatum_iff D₀ hE' ⟨w, hspa⟩).mp hw))

/-- **The comparison transports restrictions**: the keystone comparison of a
smaller `A`-datum is the `B`-side restriction of the bigger one. -/
theorem pieceEquiv_restrict' {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    (y : ↥(limitSections V)) (i j : RationalIndex V)
    (h : rationalOpen j.D.T j.D.s ⊆ rationalOpen i.D.T i.D.s) :
    restrictionMap (imgDatum D₀ i.isRational) (imgDatum D₀ j.isRational)
        (imgDatum_mono D₀ i.isRational j.isRational h)
        (pieceEquiv D₀ i.isRational (index_sub D₀ hV i) (limitEvalHom i y))
      = pieceEquiv D₀ j.isRational (index_sub D₀ hV j) (limitEvalHom j y) := by
  have hsq := pieceEquiv_restrict D₀ i.isRational j.isRational
    (index_sub D₀ hV i) h (limitEvalHom i y)
  have hy : restrictionMap i.D j.D h (limitEvalHom i y) = limitEvalHom j y :=
    y.2 i j h
  rw [hy] at hsq
  exact hsq.symm

variable [DecidableEq A]

/-- Membership in the intersection datum's open implies membership in the
left one (extracted so `interIdx`'s field is a one-liner). -/
theorem interDatumOpen_left_aux {V : Opens ↥(Spa A A⁺)} (i j : RationalIndex V)
    (v : ↥(Spa A A⁺))
    (hv : v ∈ spaOpen (i.D.interDatumOpen j.D
      (exists_pow_le_of_isRational_pair i.D.P i.D i.isRational).choose
      (exists_pow_le_of_isRational_pair i.D.P j.D j.isRational).choose
      (exists_pow_le_of_isRational_pair i.D.P i.D i.isRational).choose_spec
      (exists_pow_le_of_isRational_pair i.D.P j.D j.isRational).choose_spec)) :
    v ∈ spaOpen i.D :=
  ((Set.ext_iff.mp (RationalLocData.interDatumOpen_rationalOpen i.D j.D _ _ _ _)
    ((v : ↥(Spa A A⁺)) : Spv A)).mp hv).1

/-- The `A`-index of the intersection of two indices (openness certificates
from `exists_pow_le_of_isRational_pair` at the shared pair `i.D.P`). -/
noncomputable def interIdx {V : Opens ↥(Spa A A⁺)} (i j : RationalIndex V) :
    RationalIndex V where
  D := i.D.interDatumOpen j.D
    (exists_pow_le_of_isRational_pair i.D.P i.D i.isRational).choose
    (exists_pow_le_of_isRational_pair i.D.P j.D j.isRational).choose
    (exists_pow_le_of_isRational_pair i.D.P i.D i.isRational).choose_spec
    (exists_pow_le_of_isRational_pair i.D.P j.D j.isRational).choose_spec
  isRational := RationalLocData.isRational_of_pow_le _
    (RationalLocData.interDatumOpen_pow_le _ _ _ _ _ _)
  subset := fun v hv => i.subset (interDatumOpen_left_aux i j v hv)

theorem interIdx_rationalOpen {V : Opens ↥(Spa A A⁺)} (i j : RationalIndex V) :
    rationalOpen (interIdx i j).D.T (interIdx i j).D.s
      = rationalOpen i.D.T i.D.s ∩ rationalOpen j.D.T j.D.s :=
  RationalLocData.interDatumOpen_rationalOpen i.D j.D
    (exists_pow_le_of_isRational_pair i.D.P i.D i.isRational).choose
    (exists_pow_le_of_isRational_pair i.D.P j.D j.isRational).choose
    (exists_pow_le_of_isRational_pair i.D.P i.D i.isRational).choose_spec
    (exists_pow_le_of_isRational_pair i.D.P j.D j.isRational).choose_spec

theorem interIdx_le_left {V : Opens ↥(Spa A A⁺)} (i j : RationalIndex V) :
    rationalOpen (interIdx i j).D.T (interIdx i j).D.s
      ⊆ rationalOpen i.D.T i.D.s := by
  rw [interIdx_rationalOpen]
  exact Set.inter_subset_left

theorem interIdx_le_right {V : Opens ↥(Spa A A⁺)} (i j : RationalIndex V) :
    rationalOpen (interIdx i j).D.T (interIdx i j).D.s
      ⊆ rationalOpen j.D.T j.D.s := by
  rw [interIdx_rationalOpen]
  exact Set.inter_subset_right

/-- The image open of the intersection index is the intersection of the
image opens. -/
theorem mem_imgDatum_interIdx {V : Opens ↥(Spa A A⁺)} (i j : RationalIndex V)
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) :
    (w : Spv (presheafValue D₀))
        ∈ rationalOpen (imgDatum D₀ (interIdx i j).isRational).T
            (imgDatum D₀ (interIdx i j).isRational).s
      ↔ ((w : Spv (presheafValue D₀))
            ∈ rationalOpen (imgDatum D₀ i.isRational).T
                (imgDatum D₀ i.isRational).s
          ∧ (w : Spv (presheafValue D₀))
            ∈ rationalOpen (imgDatum D₀ j.isRational).T
                (imgDatum D₀ j.isRational).s) := by
  rw [mem_imgDatum_iff D₀ (interIdx i j).isRational w,
    mem_imgDatum_iff D₀ i.isRational w, mem_imgDatum_iff D₀ j.isRational w]
  rw [show rationalOpen (interIdx i j).D.T (interIdx i j).D.s
      = rationalOpen i.D.T i.D.s ∩ rationalOpen j.D.T j.D.s from
    interIdx_rationalOpen i j]
  exact Set.mem_inter_iff _ _ _

/-- The candidate `B`-side section on the image open of an `A`-index. -/
noncomputable def imgSection {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    (y : ↥(limitSections V)) (i : RationalIndex V) :
    ↥(limitSections (imgOpens D₀ i)) :=
  limitOfValue (imgDatum D₀ i.isRational)
    (pieceEquiv D₀ i.isRational (index_sub D₀ hV i) (limitEvalHom i y))

/-- **The candidate sections agree on overlaps** — via the intersection index
and the keystone square. -/
theorem imgSection_compat {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    (y : ↥(limitSections V)) (i j : RationalIndex V) :
    limitRestrict (inf_le_left (a := imgOpens D₀ i) (b := imgOpens D₀ j))
        (imgSection D₀ hV y i)
      = limitRestrict (inf_le_right (a := imgOpens D₀ i) (b := imgOpens D₀ j))
          (imgSection D₀ hV y j) := by
  refine Subtype.ext (funext fun k => ?_)
  -- `k` sits inside the image open of the intersection index
  have hk : rationalOpen k.D.T k.D.s
      ⊆ rationalOpen (imgDatum D₀ (interIdx i j).isRational).T
          (imgDatum D₀ (interIdx i j).isRational).s := by
    intro w hw
    have hspa : w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ := hw.1
    have hkw : (⟨w, hspa⟩ : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
        ∈ (imgOpens D₀ i ⊓ imgOpens D₀ j) := k.subset hw
    exact (mem_imgDatum_interIdx D₀ i j ⟨w, hspa⟩).mpr ⟨hkw.1, hkw.2⟩
  have hmi : rationalOpen (imgDatum D₀ (interIdx i j).isRational).T
      (imgDatum D₀ (interIdx i j).isRational).s
      ⊆ rationalOpen (imgDatum D₀ i.isRational).T
          (imgDatum D₀ i.isRational).s :=
    imgDatum_mono D₀ i.isRational (interIdx i j).isRational (interIdx_le_left i j)
  have hmj : rationalOpen (imgDatum D₀ (interIdx i j).isRational).T
      (imgDatum D₀ (interIdx i j).isRational).s
      ⊆ rationalOpen (imgDatum D₀ j.isRational).T
          (imgDatum D₀ j.isRational).s :=
    imgDatum_mono D₀ j.isRational (interIdx i j).isRational (interIdx_le_right i j)
  have hi := pieceEquiv_restrict' D₀ hV y i (interIdx i j) (interIdx_le_left i j)
  have hj := pieceEquiv_restrict' D₀ hV y j (interIdx i j) (interIdx_le_right i j)
  show restrictionMap (imgDatum D₀ i.isRational) k.D _ _
    = restrictionMap (imgDatum D₀ j.isRational) k.D _ _
  have hfi := congrFun (restrictionMap_comp (imgDatum D₀ i.isRational)
    (imgDatum D₀ (interIdx i j).isRational) k.D hmi hk)
    (pieceEquiv D₀ i.isRational (index_sub D₀ hV i) (limitEvalHom i y))
  have hfj := congrFun (restrictionMap_comp (imgDatum D₀ j.isRational)
    (imgDatum D₀ (interIdx i j).isRational) k.D hmj hk)
    (pieceEquiv D₀ j.isRational (index_sub D₀ hV j) (limitEvalHom j y))
  rw [← hfi, ← hfj]
  simp only [Function.comp_apply]
  rw [hi, hj]

/-- **The comparison map hits everything** (P5-K5): the keystone comparisons
of an `A`-side family glue over the image-open cover to a `B`-side family
mapping back to it. -/
theorem phiHom_surjective {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) :
    Function.Surjective (phiHom D₀ hV hVW) := by
  classical
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  intro y
  obtain ⟨x, hx⟩ := (isLimitSheaf_value D₀).glue
    (U := imgOpens D₀ (A := A) (V := V)) (imgOpens_le D₀ hVW)
    (imgOpens_cover D₀ hV hVW) (imgSection D₀ hV y)
    (imgSection_compat D₀ hV y)
  refine ⟨x, Subtype.ext (funext fun i => ?_)⟩
  -- read off the top component of the `i`-th piece
  have htop := congrArg (fun z : ↥(limitSections (imgOpens D₀ i)) =>
      (z : ∀ k : RationalIndex (imgOpens D₀ i), presheafValue k.D)
        (RationalIndex.self (imgDatum D₀ i.isRational)
          (imgDatum_isRational D₀ i.isRational))) (hx i)
  have hid : restrictionMap (imgDatum D₀ i.isRational)
      (imgDatum D₀ i.isRational) (subset_refl _)
      (pieceEquiv D₀ i.isRational (index_sub D₀ hV i) (limitEvalHom i y))
      = pieceEquiv D₀ i.isRational (index_sub D₀ hV i) (limitEvalHom i y) :=
    congrFun (restrictionMap_id (imgDatum D₀ i.isRational)) _
  have hcomp : limitEvalHom (idxOf D₀ hVW i) x
      = pieceEquiv D₀ i.isRational (index_sub D₀ hV i) (limitEvalHom i y) :=
    htop.trans hid
  show (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm
      (limitEvalHom (idxOf D₀ hVW i) x) = _
  rw [hcomp, RingEquiv.symm_apply_apply]
  rfl

/-- `genPiece_rel_forward` is continuous (it is a completion extension). -/
theorem genPiece_rel_forward_continuous
    (T : Finset A) (t : A) (M : ℕ)
    (hle : (Ideal.span (D₀.P.A₀.subtype '' (D₀.P.I : Set D₀.P.A₀))) ^ M
      ≤ Ideal.span ((T : Finset A) : Set A)) :
    Continuous (OpenKeystone.genPiece_rel_forward D₀ T t M hle) := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  letI : UniformSpace (Localization.Away
    (D₀.interSamePair (OpenKeystone.genPieceDatumOpen D₀.P T t M hle) rfl).s) :=
    (D₀.interSamePair (OpenKeystone.genPieceDatumOpen D₀.P T t M hle) rfl).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- `genPiece_rel_backward` is continuous (it is a completion extension). -/
theorem genPiece_rel_backward_continuous
    (T : Finset A) (t : A) (M : ℕ)
    (hle : (Ideal.span (D₀.P.A₀.subtype '' (D₀.P.I : Set D₀.P.A₀))) ^ M
      ≤ Ideal.span ((T : Finset A) : Set A)) :
    Continuous (OpenKeystone.genPiece_rel_backward D₀ T t M hle) := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  letI : UniformSpace (Localization.Away
    (OpenKeystone.imagePieceDatumOpen D₀ T t M hle).s) :=
    (OpenKeystone.imagePieceDatumOpen D₀ T t M hle).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The keystone comparison is continuous. -/
theorem pieceEquiv_continuous {E : RationalLocData A} (hE : E.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s) :
    Continuous (pieceEquiv D₀ hE hE_sub) := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  exact (genPiece_rel_forward_continuous D₀ E.T E.s (certExp D₀ hE)
    (certExp_spec D₀ hE)).comp (restrictionMapHom_continuous _ _ _)

/-- The open-equality behind the keystone comparison. -/
theorem pieceEquiv_open_eq {E : RationalLocData A} (hE : E.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s) :
    rationalOpen E.T E.s
      = rationalOpen (D₀.interSamePair
          (OpenKeystone.genPieceDatumOpen D₀.P E.T E.s (certExp D₀ hE)
            (certExp_spec D₀ hE)) rfl).T
        (D₀.interSamePair (OpenKeystone.genPieceDatumOpen D₀.P E.T E.s
          (certExp D₀ hE) (certExp_spec D₀ hE)) rfl).s := by
  have h := RationalLocData.interSamePair_rationalOpen D₀
    (OpenKeystone.genPieceDatumOpen D₀.P E.T E.s (certExp D₀ hE)
      (certExp_spec D₀ hE))
    (OpenKeystone.genPieceDatumOpen_P D₀.P E.T E.s (certExp D₀ hE)
      (certExp_spec D₀ hE))
  rw [OpenKeystone.genPieceDatumOpen_T, OpenKeystone.genPieceDatumOpen_s] at h
  exact (h.trans (Set.inter_eq_right.mpr hE_sub)).symm

/-- The keystone comparison has continuous inverse. -/
theorem pieceEquiv_symm_continuous {E : RationalLocData A} (hE : E.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s) :
    Continuous (pieceEquiv D₀ hE hE_sub).symm := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  have hEeq := pieceEquiv_open_eq D₀ hE hE_sub
  have hbij := restrictionMap_bijective_of_rationalOpen_eq E
    (D₀.interSamePair (OpenKeystone.genPieceDatumOpen D₀.P E.T E.s
      (certExp D₀ hE) (certExp_spec D₀ hE)) rfl) hEeq
  have hfun : ∀ z, (pieceEquiv D₀ hE hE_sub).symm z
      = restrictionMapHom _ E hEeq.le
          (OpenKeystone.genPiece_rel_backward D₀ E.T E.s (certExp D₀ hE)
            (certExp_spec D₀ hE) z) := by
    intro z
    show (RingEquiv.ofBijective (restrictionMapHom E _ hEeq.symm.le) hbij).symm
        (OpenKeystone.genPiece_rel_backward D₀ E.T E.s (certExp D₀ hE)
          (certExp_spec D₀ hE) z) = _
    refine ofBijective_symm_apply _ hbij (restrictionMapHom _ E hEeq.le)
      (fun x => ?_) _
    exact congrFun (restrictionMap_comp E _ E hEeq.symm.le hEeq.le) x |>.trans
      (congrFun (restrictionMap_id E) x)
  rw [show ((pieceEquiv D₀ hE hE_sub).symm : _ → _) = _ from funext hfun]
  exact (restrictionMapHom_continuous _ _ _).comp
    (genPiece_rel_backward_continuous D₀ E.T E.s (certExp D₀ hE)
      (certExp_spec D₀ hE))

/-- **The comparison map is continuous.** -/
theorem phiHom_continuous {V : Opens ↥(Spa A A⁺)} (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) : Continuous (phiHom D₀ hV hVW) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  exact (pieceEquiv_symm_continuous D₀ i.isRational (index_sub D₀ hV i)).comp
    (limitEvalHom_continuous (idxOf D₀ hVW i))

/-- **The comparison ring isomorphism** (P5-K6). -/
noncomputable def phiEquiv [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) :
    ↥(limitSections W) ≃+* ↥(limitSections V) :=
  RingEquiv.ofBijective (phiHom D₀ hV hVW)
    ⟨phiHom_injective D₀ hV hVW, phiHom_surjective D₀ hV hVW⟩

/-- The inverse of the comparison restricts to the candidate sections. -/
theorem phiEquiv_symm_restrict [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (y : ↥(limitSections V)) (i : RationalIndex V) :
    limitRestrict (imgOpens_le D₀ hVW i) ((phiEquiv D₀ hV hVW).symm y)
      = imgSection D₀ hV y i := by
  refine Subtype.ext (funext fun k => ?_)
  set x := (phiEquiv D₀ hV hVW).symm y with hx
  have hxy : phiHom D₀ hV hVW x = y := (phiEquiv D₀ hV hVW).apply_symm_apply y
  -- the `k`-component of both sides is a restriction of the `i`-th value
  have hki : rationalOpen k.D.T k.D.s
      ⊆ rationalOpen (imgDatum D₀ i.isRational).T
          (imgDatum D₀ i.isRational).s := spaOpen_subset_iff.mp k.subset
  have hcompat := x.2 (idxOf D₀ hVW i) (k.mono (imgOpens_le D₀ hVW i)) hki
  have hval : limitEvalHom (idxOf D₀ hVW i) x
      = pieceEquiv D₀ i.isRational (index_sub D₀ hV i) (limitEvalHom i y) := by
    have h1 : (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)).symm
        (limitEvalHom (idxOf D₀ hVW i) x) = limitEvalHom i y := by
      rw [← phiHom_apply_component D₀ hV hVW x i, hxy]
    exact ((RingEquiv.apply_symm_apply
        (pieceEquiv D₀ i.isRational (index_sub D₀ hV i))
        (limitEvalHom (idxOf D₀ hVW i) x)).symm.trans
      (congrArg (pieceEquiv D₀ i.isRational (index_sub D₀ hV i)) h1))
  show (x : ∀ j : RationalIndex W, presheafValue j.D)
      (k.mono (imgOpens_le D₀ hVW i)) = _
  rw [← hcompat]
  show restrictionMap _ _ _ (limitEvalHom (idxOf D₀ hVW i) x) = _
  rw [hval]
  rfl

/-- **The comparison inverse is continuous** — via the embedding of sections
into the product over the image-open cover. -/
theorem phiEquiv_symm_continuous [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) : Continuous (phiEquiv D₀ hV hVW).symm := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  refine ((isLimitSheaf_value D₀).isEmbedding (imgOpens_le D₀ hVW)
    (imgOpens_cover D₀ hV hVW)).continuous_iff.mpr ?_
  refine continuous_pi fun i => ?_
  show Continuous fun y => limitRestrictProd (imgOpens_le D₀ hVW)
    ((phiEquiv D₀ hV hVW).symm y) i
  rw [show (fun y => limitRestrictProd (imgOpens_le D₀ hVW)
      ((phiEquiv D₀ hV hVW).symm y) i)
      = fun y => imgSection D₀ hV y i from
    funext fun y => phiEquiv_symm_restrict D₀ hV hVW y i]
  exact (limitOfValue_continuous (imgDatum D₀ i.isRational)).comp
    ((pieceEquiv_continuous D₀ i.isRational (index_sub D₀ hV i)).comp
      (limitEvalHom_continuous i))

/-- **The base homeomorphism**: `Spa B` is the rational subset, as a subspace
of `Spa A`. -/
def baseHomeo (u : (presheafValue D₀)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀)) :
    ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺) ≃ₜ ↥(spaOpens D₀) :=
  (spaPresheafValueHomeomorphRationalOpen' D₀ u hu).trans
    (spaOpensHomeoInter D₀).symm

@[simp] theorem baseHomeo_coe (u : (presheafValue D₀)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀))
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) :
    ((baseHomeo D₀ u hu w : ↥(spaOpens D₀)) : ↥(Spa A A⁺)) = shadow D₀ w := rfl

variable (u : (presheafValue D₀)ˣ)
  (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀))

/-- The `A`-side open attached to an open of the restricted space. -/
def aOpen (U : Opens ↥(spaOpens D₀)) : Opens ↥(Spa A A⁺) where
  carrier := Subtype.val '' (U : Set ↥(spaOpens D₀))
  is_open' := ((spaOpens D₀).2.isOpenEmbedding_subtypeVal).isOpenMap _ U.2

/-- The `B`-side open attached to an open of the restricted space. -/
def bOpen (U : Opens ↥(spaOpens D₀)) :
    Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺) where
  carrier := (baseHomeo D₀ u hu) ⁻¹' (U : Set ↥(spaOpens D₀))
  is_open' := U.2.preimage (baseHomeo D₀ u hu).continuous

theorem aOpen_le (U : Opens ↥(spaOpens D₀)) : aOpen D₀ U ≤ spaOpens D₀ := by
  rintro v ⟨z, -, rfl⟩
  exact z.2

theorem paired_aOpen_bOpen (U : Opens ↥(spaOpens D₀)) :
    Paired D₀ (aOpen D₀ U) (bOpen D₀ u hu U) := by
  intro w
  constructor
  · rintro ⟨z, hz, hzeq⟩
    show baseHomeo D₀ u hu w ∈ U
    have hz' : z = baseHomeo D₀ u hu w := Subtype.ext hzeq
    exact hz' ▸ hz
  · intro hw
    exact ⟨baseHomeo D₀ u hu w, hw, rfl⟩

/-- **Naturality of the comparison map**: it commutes with restriction on
both sides. Componentwise both sides are the same keystone comparison of the
same `B`-component (the two `RationalIndex` spellings differ only in
`Prop`-valued fields). -/
theorem phiHom_naturality {V V' : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀) (hV' : V' ≤ spaOpens D₀) (hVV' : V' ≤ V)
    {W W' : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (hVW' : Paired D₀ V' W') (hWW' : W' ≤ W)
    (x : ↥(limitSections W)) :
    limitRestrict hVV' (phiHom D₀ hV hVW x)
      = phiHom D₀ hV' hVW' (limitRestrict hWW' x) :=
  rfl

/-- The keystone comparison factors the canonical maps: the `A`-side
canonical map of `E` followed by the comparison is the `B`-side canonical map
of the image datum precomposed with `D₀`'s canonical map. -/
theorem pieceEquiv_canonicalMap {E : RationalLocData A} (hE : E.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s) (a : A) :
    pieceEquiv D₀ hE hE_sub (E.canonicalMap a)
      = (imgDatum D₀ hE).canonicalMap (D₀.canonicalMap a) := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  rw [← restrictionMapHom_canonicalMap_generic D₀ E hE_sub a]
  exact OpenKeystone.relativePiece_equiv_restrictionMap D₀ E hE_sub
    (certExp D₀ hE) (certExp_spec D₀ hE) (D₀.canonicalMap a)

/-- **The comparison intertwines the point valuations** (the stalk-valuation
core): the `B`-side point value of the image datum pulls back along the
keystone comparison to the `A`-side point value of `E`. -/
theorem comap_pieceEquiv_pointValue [DecidableEq A]
    {E : RationalLocData A} (hE : E.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    (hwB : (w : Spv (presheafValue D₀))
      ∈ (rationalOpen (imgDatum D₀ hE).T (imgDatum D₀ hE).s
        ∩ Spa (presheafValue D₀) (presheafValue D₀)⁺
        : Set (Spv (presheafValue D₀))))
    (hwA : comap D₀.canonicalMap (w : Spv (presheafValue D₀))
      ∈ (rationalOpen E.T E.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap ((pieceEquiv D₀ hE hE_sub).toRingHom)
        (pointValue (imgDatum D₀ hE) hwB)
      = pointValue E hwA := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  refine eq_pointValue_of_comap_eq E hwA ?_ ?_
  · exact comap_isContinuous (pieceEquiv_continuous D₀ hE hE_sub)
      (pointValue_isContinuous (imgDatum D₀ hE) hwB)
  · have hfac : ((pieceEquiv D₀ hE hE_sub).toRingHom).comp E.canonicalMap
        = ((imgDatum D₀ hE).canonicalMap).comp D₀.canonicalMap :=
      RingHom.ext (pieceEquiv_canonicalMap D₀ hE hE_sub)
    have h1 := congr_fun (comap_comp E.canonicalMap
      ((pieceEquiv D₀ hE hE_sub).toRingHom)) (pointValue (imgDatum D₀ hE) hwB)
    have h2 := congr_fun (comap_comp D₀.canonicalMap
      ((imgDatum D₀ hE).canonicalMap)) (pointValue (imgDatum D₀ hE) hwB)
    rw [hfac] at h1
    rw [h2] at h1
    rw [show comap E.canonicalMap (comap ((pieceEquiv D₀ hE hE_sub).toRingHom)
        (pointValue (imgDatum D₀ hE) hwB))
        = comap D₀.canonicalMap (comap ((imgDatum D₀ hE).canonicalMap)
            (pointValue (imgDatum D₀ hE) hwB)) from h1.symm]
    rw [comap_pointValue (imgDatum D₀ hE) hwB]

/-- The comparison carries the `A`-side point value of an index to the
`B`-side point value of its image index. -/
theorem comap_pieceEquiv_symm_pointValue [DecidableEq A]
    {E : RationalLocData A} (hE : E.IsRational)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    (hwB : (w : Spv (presheafValue D₀))
      ∈ (rationalOpen (imgDatum D₀ hE).T (imgDatum D₀ hE).s
        ∩ Spa (presheafValue D₀) (presheafValue D₀)⁺
        : Set (Spv (presheafValue D₀))))
    (hwA : comap D₀.canonicalMap (w : Spv (presheafValue D₀))
      ∈ (rationalOpen E.T E.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap ((pieceEquiv D₀ hE hE_sub).symm.toRingHom) (pointValue E hwA)
      = pointValue (imgDatum D₀ hE) hwB := by
  have hK := comap_pieceEquiv_pointValue D₀ hE hE_sub w hwB hwA
  have hcomp : ((pieceEquiv D₀ hE hE_sub).toRingHom).comp
      ((pieceEquiv D₀ hE hE_sub).symm.toRingHom) = RingHom.id _ :=
    RingHom.ext fun z => (pieceEquiv D₀ hE hE_sub).apply_symm_apply z
  rw [← hK]
  rw [show comap ((pieceEquiv D₀ hE hE_sub).symm.toRingHom)
        (comap ((pieceEquiv D₀ hE hE_sub).toRingHom)
          (pointValue (imgDatum D₀ hE) hwB))
      = comap (((pieceEquiv D₀ hE hE_sub).toRingHom).comp
          ((pieceEquiv D₀ hE hE_sub).symm.toRingHom))
        (pointValue (imgDatum D₀ hE) hwB) from rfl, hcomp]
  exact congr_fun comap_id _

/-- **The comparison intertwines the open values** — the presheaf-level form
of the stalk-valuation agreement. -/
theorem comap_phiHom_openValue [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W)
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) (hw : w ∈ W) :
    comap (phiHom D₀ hV hVW) (openValue V (paired_shadow D₀ hVW w hw))
      = openValue W hw := by
  classical
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  -- an `A`-index of `V` around the shadow, and its image index
  obtain ⟨E, hE, hEmem, hEsub⟩ := exists_isRational_spaOpen_subset_huber
    (V := (V : Set ↥(Spa A A⁺))) V.2 (paired_shadow D₀ hVW w hw)
  set i : RationalIndex V := ⟨E, hE, hEsub⟩ with hi
  have hwB : (w : Spv (presheafValue D₀))
      ∈ (rationalOpen (imgDatum D₀ hE).T (imgDatum D₀ hE).s
        ∩ Spa (presheafValue D₀) (presheafValue D₀)⁺
        : Set (Spv (presheafValue D₀))) :=
    ⟨(mem_imgDatum_iff D₀ hE w).mpr hEmem, w.2⟩
  have hwA : comap D₀.canonicalMap (w : Spv (presheafValue D₀))
      ∈ (rationalOpen E.T E.s ∩ Spa A A⁺ : Set (Spv A)) :=
    ⟨hEmem, (shadow D₀ w).2⟩
  -- both sides computed at that index
  rw [← comap_limitEvalHom_pointValue (paired_shadow D₀ hVW w hw) i hwA,
    ← comap_limitEvalHom_pointValue hw (idxOf D₀ hVW i) hwB]
  -- the componentwise formula for the comparison
  have hcomp : (limitEvalHom i).comp (phiHom D₀ hV hVW)
      = ((pieceEquiv D₀ hE (index_sub D₀ hV i)).symm.toRingHom).comp
          (limitEvalHom (idxOf D₀ hVW i)) :=
    RingHom.ext fun x => phiHom_apply_component D₀ hV hVW x i
  refine Eq.trans ?_ (congrArg (comap (limitEvalHom (idxOf D₀ hVW i)))
    (comap_pieceEquiv_symm_pointValue D₀ hE (index_sub D₀ hV i) w hwB hwA))
  exact congrFun (congrArg comap hcomp) (pointValue i.D hwA)

/-- **The inverse comparison intertwines the open values.** -/
theorem comap_phiEquiv_symm_openValue [DecidableEq A] {V : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀)
    {W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W)
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) (hw : w ∈ W) :
    comap ((phiEquiv D₀ hV hVW).symm.toRingHom) (openValue W hw)
      = openValue V (paired_shadow D₀ hVW w hw) := by
  have hK := comap_phiHom_openValue D₀ hV hVW w hw
  have hcomp : (phiHom D₀ hV hVW).comp
      ((phiEquiv D₀ hV hVW).symm.toRingHom) = RingHom.id _ :=
    RingHom.ext fun z => (phiEquiv D₀ hV hVW).apply_symm_apply z
  rw [← hK]
  rw [show comap ((phiEquiv D₀ hV hVW).symm.toRingHom)
        (comap (phiHom D₀ hV hVW) (openValue V (paired_shadow D₀ hVW w hw)))
      = comap ((phiHom D₀ hV hVW).comp
          ((phiEquiv D₀ hV hVW).symm.toRingHom))
        (openValue V (paired_shadow D₀ hVW w hw))
    from rfl, hcomp]
  exact congr_fun comap_id _

end Phi

section Assembly

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [T2Space A] [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
    CompleteSpace A]

/-- The ambient `Spa (A, A⁺)` as a presheafed space of complete topological
rings (no Tate hypothesis). -/
def spaSpace : TopRingPresheafedSpace where
  carrier := SpaTop A
  presheaf := structurePresheaf A

/-- The inclusion of an open of `Spa (A, A⁺)`. -/
def spaOpensIncl (U : Opens ↥(Spa A A⁺)) : TopCat.of ↥U ⟶ SpaTop A :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem spaOpensIncl_isOpenEmbedding (U : Opens ↥(Spa A A⁺)) :
    Topology.IsOpenEmbedding (spaOpensIncl U) :=
  U.2.isOpenEmbedding_subtypeVal

/-- The restriction of the ambient space to an open. -/
def spaRestrict (U : Opens ↥(Spa A A⁺)) : TopRingPresheafedSpace :=
  (spaSpace (A := A)).restrict (spaOpensIncl_isOpenEmbedding U)

variable (D₀ : RationalLocData A) [IsTateRing (presheafValue D₀)]
  [IsNoetherianRing (presheafValue D₀)] [IsStronglyNoetherian (presheafValue D₀)]

/-- `Spa B` as a presheafed space. -/
def bSpace : TopRingPresheafedSpace where
  carrier := SpaTop (presheafValue D₀)
  presheaf := structurePresheaf (presheafValue D₀)

variable (u : (presheafValue D₀)ˣ)
  (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀))

/-- The base isomorphism in `TopCat`. -/
def baseIso : (bSpace D₀).carrier ≅ (spaRestrict (spaOpens D₀)).carrier :=
  TopCat.isoOfHomeo (baseHomeo D₀ u hu)

variable [DecidableEq A]

/-- The comparison as an isomorphism in `CompleteTopCommRingCat`. -/
def phiCatIso (U : Opens ↥(spaOpens D₀)) :
    CompleteTopCommRingCat.of ↥(limitSections (bOpen D₀ u hu U))
      ≅ CompleteTopCommRingCat.of ↥(limitSections (aOpen D₀ U)) where
  hom := ⟨(phiEquiv D₀ (aOpen_le D₀ U) (paired_aOpen_bOpen D₀ u hu U)).toRingHom,
    phiHom_continuous D₀ (aOpen_le D₀ U) (paired_aOpen_bOpen D₀ u hu U)⟩
  inv := ⟨(phiEquiv D₀ (aOpen_le D₀ U)
      (paired_aOpen_bOpen D₀ u hu U)).symm.toRingHom,
    phiEquiv_symm_continuous D₀ (aOpen_le D₀ U)
      (paired_aOpen_bOpen D₀ u hu U)⟩
  hom_inv_id := Subtype.ext (RingHom.ext fun x =>
    (phiEquiv D₀ (aOpen_le D₀ U) (paired_aOpen_bOpen D₀ u hu U)).symm_apply_apply x)
  inv_hom_id := Subtype.ext (RingHom.ext fun x =>
    (phiEquiv D₀ (aOpen_le D₀ U) (paired_aOpen_bOpen D₀ u hu U)).apply_symm_apply x)

/-- **The presheaf comparison as a natural isomorphism**. -/
def presheafIso :
    (baseIso D₀ u hu).hom _* (bSpace D₀).presheaf ≅ (spaRestrict (spaOpens D₀)).presheaf :=
  NatIso.ofComponents (fun U => phiCatIso D₀ u hu U.unop) (by
    intro U U' f
    refine Subtype.ext (RingHom.ext fun x => ?_)
    exact phiHom_naturality D₀ (aOpen_le D₀ U.unop) (aOpen_le D₀ U'.unop)
      (fun v hv => by
        obtain ⟨z, hz, rfl⟩ := hv
        exact ⟨z, leOfHom f.unop hz, rfl⟩)
      (paired_aOpen_bOpen D₀ u hu U.unop) (paired_aOpen_bOpen D₀ u hu U'.unop)
      (fun w hw => leOfHom f.unop hw) x)

/-- **Wedhorn 8.15 at the presheafed-space level** (P5-K7): `Spa 𝒪_X(D₀)` is
the rational subset `R(T/s)` of `Spa (A, A⁺)`, with its structure presheaf. -/
def spaRestrictIso : bSpace D₀ ≅ spaRestrict (spaOpens D₀) :=
  AlgebraicGeometry.PresheafedSpace.isoOfComponents (baseIso D₀ u hu)
    (presheafIso D₀ u hu)

/-- The shadow-preimage of an ambient open. -/
def shadowPre (U : Opens ↥(Spa A A⁺)) :
    Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺) where
  carrier := {w | shadow D₀ w ∈ U}
  is_open' := by
    have : {w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺) | shadow D₀ w ∈ U}
        = (baseHomeo D₀ u hu) ⁻¹' (Subtype.val ⁻¹' (U : Set ↥(Spa A A⁺))) := rfl
    rw [this]
    exact (U.2.preimage continuous_subtype_val).preimage
      (baseHomeo D₀ u hu).continuous

theorem shadowPre_paired (U : Opens ↥(Spa A A⁺)) :
    Paired D₀ (U ⊓ spaOpens D₀) (shadowPre D₀ u hu U) := by
  intro w
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, (comap_canonicalMap_mem_rationalOpen_inter_spa D₀ w).1⟩

/-- **The ambient comparison**: sections over an ambient open restrict and
compare to `B`-side sections over the shadow-preimage. -/
noncomputable def ambComp [DecidableEq A] (U : Opens ↥(Spa A A⁺)) :
    ↥(limitSections U) →+* ↥(limitSections (shadowPre D₀ u hu U)) :=
  ((phiEquiv D₀ (inf_le_right : U ⊓ spaOpens D₀ ≤ spaOpens D₀)
      (shadowPre_paired D₀ u hu U)).symm.toRingHom).comp
    (limitRestrict (inf_le_left : U ⊓ spaOpens D₀ ≤ U))

/-- **The ambient comparison intertwines the open values.** -/
theorem comap_ambComp_openValue [DecidableEq A] (U : Opens ↥(Spa A A⁺))
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    (hw : w ∈ shadowPre D₀ u hu U) :
    comap (ambComp D₀ u hu U) (openValue (shadowPre D₀ u hu U) hw)
      = openValue U hw := by
  have h1 := comap_phiEquiv_symm_openValue D₀
    (inf_le_right : U ⊓ spaOpens D₀ ≤ spaOpens D₀)
    (shadowPre_paired D₀ u hu U) w hw
  have h2 := comap_limitRestrict_openValue
    (inf_le_left : U ⊓ spaOpens D₀ ≤ U)
    (paired_shadow D₀ (shadowPre_paired D₀ u hu U) w hw)
  rw [show comap (ambComp D₀ u hu U) (openValue (shadowPre D₀ u hu U) hw)
      = comap (limitRestrict (inf_le_left : U ⊓ spaOpens D₀ ≤ U))
        (comap ((phiEquiv D₀ (inf_le_right : U ⊓ spaOpens D₀ ≤ spaOpens D₀)
          (shadowPre_paired D₀ u hu U)).symm.toRingHom)
          (openValue (shadowPre D₀ u hu U) hw)) from rfl, h1, h2]

/-- Naturality of the inverse comparison. -/
theorem phiEquiv_symm_naturality [DecidableEq A] {V V' : Opens ↥(Spa A A⁺)}
    (hV : V ≤ spaOpens D₀) (hV' : V' ≤ spaOpens D₀) (hVV' : V' ≤ V)
    {W W' : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)}
    (hVW : Paired D₀ V W) (hVW' : Paired D₀ V' W') (hWW' : W' ≤ W)
    (y : ↥(limitSections V)) :
    limitRestrict hWW' ((phiEquiv D₀ hV hVW).symm y)
      = (phiEquiv D₀ hV' hVW').symm (limitRestrict hVV' y) := by
  have hnat := phiHom_naturality D₀ hV hV' hVV' hVW hVW' hWW'
    ((phiEquiv D₀ hV hVW).symm y)
  rw [show phiHom D₀ hV hVW ((phiEquiv D₀ hV hVW).symm y) = y from
    (phiEquiv D₀ hV hVW).apply_symm_apply y] at hnat
  exact (((phiEquiv D₀ hV' hVW').symm_apply_eq).mpr hnat).symm

/-- The shadow map as a morphism of topological spaces. -/
def shadowMap : SpaTop (presheafValue D₀) ⟶ SpaTop A :=
  TopCat.ofHom ⟨fun w => shadow D₀ w,
    (baseHomeo D₀ u hu).continuous.subtype_val⟩

theorem ambComp_continuous [DecidableEq A] (U : Opens ↥(Spa A A⁺)) :
    Continuous (ambComp D₀ u hu U) :=
  (phiEquiv_symm_continuous D₀ _ (shadowPre_paired D₀ u hu U)).comp
    (limitRestrict_continuous _)

/-- **The comparison morphism** `Spa B ⟶ Spa A` of presheafed spaces: the
shadow map on points, the ambient comparison on sections. -/
noncomputable def spaCompHom [DecidableEq A] :
    bSpace D₀ ⟶ spaSpace (A := A) where
  base := shadowMap D₀ u hu
  c :=
    { app := fun U => ⟨ambComp D₀ u hu U.unop, ambComp_continuous D₀ u hu U.unop⟩
      naturality := fun U U' f => by
        refine Subtype.ext (RingHom.ext fun x => ?_)
        show ambComp D₀ u hu U'.unop (limitRestrict (leOfHom f.unop) x)
          = limitRestrict (leOfHom ((Opens.map (shadowMap D₀ u hu)).map
              f.unop)) (ambComp D₀ u hu U.unop x)
        exact (phiEquiv_symm_naturality D₀ _ _
          (inf_le_inf_right (spaOpens D₀) (leOfHom f.unop))
          (shadowPre_paired D₀ u hu U.unop) (shadowPre_paired D₀ u hu U'.unop)
          (leOfHom ((Opens.map (shadowMap D₀ u hu)).map f.unop))
          (limitRestrict inf_le_left x)).symm }

/-- Germ naturality for the comparison morphism, in the concrete
`spaRingPresheaf` spelling. -/
theorem ringStalkMap_spaCompHom_germ [DecidableEq A]
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
    (U : Opens ↥(Spa A A⁺)) (hw : shadow D₀ w ∈ U)
    (f : ↥(limitSections U)) :
    (ringStalkMap (spaCompHom D₀ u hu) w).hom'
        ((spaRingPresheaf A).germ U (shadow D₀ w) hw f)
      = (spaRingPresheaf (presheafValue D₀)).germ (shadowPre D₀ u hu U) w hw
          (ambComp D₀ u hu U f) := by
  have h := AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply
    (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map
      (spaCompHom D₀ u hu)) U w hw f
  exact h

theorem shadow_injective (u : (presheafValue D₀)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀)) :
    Function.Injective (shadow D₀) := by
  intro w₁ w₂ h
  have h1 : baseHomeo D₀ u hu w₁ = baseHomeo D₀ u hu w₂ := Subtype.ext h
  exact (baseHomeo D₀ u hu).injective h1

theorem shadow_isOpenMap (u : (presheafValue D₀)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀)) :
    IsOpenMap (shadow D₀ (A := A)) := by
  intro s hs
  have h1 : shadow D₀ '' s = Subtype.val '' ((baseHomeo D₀ u hu) '' s) := by
    rw [Set.image_image]
    rfl
  rw [h1]
  exact ((spaOpens D₀).2.isOpenEmbedding_subtypeVal).isOpenMap _
    ((baseHomeo D₀ u hu).isOpenMap _ hs)

/-- Every open of `Spa B` is the shadow-preimage of an ambient open. -/
def shadowImage (u : (presheafValue D₀)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀))
    (W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) :
    Opens ↥(Spa A A⁺) where
  carrier := shadow D₀ '' (W : Set ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
  is_open' := shadow_isOpenMap D₀ u hu _ W.2

theorem shadowPre_shadowImage (u : (presheafValue D₀)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D₀)ˣ) : presheafValue D₀))
    (W : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) :
    shadowPre D₀ u hu (shadowImage D₀ u hu W) = W := by
  refine Opens.ext (Set.ext fun w => ?_)
  constructor
  · rintro ⟨w', hw', heq⟩
    exact (shadow_injective D₀ u hu heq) ▸ hw'
  · exact fun hw => ⟨w, hw, rfl⟩

theorem shadowPre_mono {U U' : Opens ↥(Spa A A⁺)} (h : U' ≤ U) :
    shadowPre D₀ u hu U' ≤ shadowPre D₀ u hu U :=
  fun w hw => h hw

/-- Naturality of the ambient comparison. -/
theorem ambComp_naturality [DecidableEq A] {U U' : Opens ↥(Spa A A⁺)}
    (h : U' ≤ U) (x : ↥(limitSections U)) :
    ambComp D₀ u hu U' (limitRestrict h x)
      = limitRestrict (shadowPre_mono D₀ u hu h) (ambComp D₀ u hu U x) :=
  (phiEquiv_symm_naturality D₀ _ _ (inf_le_inf_right (spaOpens D₀) h)
    (shadowPre_paired D₀ u hu U) (shadowPre_paired D₀ u hu U')
    (shadowPre_mono D₀ u hu h) (limitRestrict inf_le_left x)).symm

/-- **The comparison morphism intertwines the stalk valuations** (P5-K12,
the last mathematical step of Wedhorn 8.15 at the `𝒱` level). -/
theorem comap_ringStalkMap_spaCompHom_stalkValue [DecidableEq A]
    (w : ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺)) :
    stalkValue (shadow D₀ w)
      = comap (ringStalkMap (spaCompHom D₀ u hu) w).hom' (stalkValue w) := by
  refine ValuationSpectrum.ext (funext₂ fun a b => propext ?_)
  obtain ⟨U, hwU, f, g, hf, hg⟩ := exists_common_rep (shadow D₀ w) a b
  subst hf
  subst hg
  constructor
  · intro hab
    obtain ⟨W, hwW, hWU, hvle⟩ := stalkVle_elim hab hwU rfl rfl
    -- push the comparison down to `W`
    have hBvle : (openValue (shadowPre D₀ u hu W)
          (show w ∈ shadowPre D₀ u hu W from hwW)).vle
        (ambComp D₀ u hu W (limitRestrict hWU f))
        (ambComp D₀ u hu W (limitRestrict hWU g)) := by
      have := comap_ambComp_openValue D₀ u hu W w hwW
      rw [← this] at hvle
      exact hvle
    have hgerm := stalkVle_intro (v := w)
      (U := shadowPre D₀ u hu W) (hvU := hwW) hBvle
    -- rewrite the germs through naturality
    have hnatf := ringStalkMap_spaCompHom_germ D₀ u hu w W hwW (limitRestrict hWU f)
    have hnatg := ringStalkMap_spaCompHom_germ D₀ u hu w W hwW (limitRestrict hWU g)
    have hresf := TopCat.Presheaf.germ_res_apply (spaRingPresheaf A)
      (homOfLE hWU) (shadow D₀ w) hwW f
    have hresg := TopCat.Presheaf.germ_res_apply (spaRingPresheaf A)
      (homOfLE hWU) (shadow D₀ w) hwW g
    show stalkVle w _ _
    rw [show (ringStalkMap (spaCompHom D₀ u hu) w).hom'
          ((spaRingPresheaf A).germ U (shadow D₀ w) hwU f)
        = (spaRingPresheaf (presheafValue D₀)).germ (shadowPre D₀ u hu W) w hwW
            (ambComp D₀ u hu W (limitRestrict hWU f)) from by
        rw [← hnatf]; exact congrArg _ hresf.symm,
      show (ringStalkMap (spaCompHom D₀ u hu) w).hom'
          ((spaRingPresheaf A).germ U (shadow D₀ w) hwU g)
        = (spaRingPresheaf (presheafValue D₀)).germ (shadowPre D₀ u hu W) w hwW
            (ambComp D₀ u hu W (limitRestrict hWU g)) from by
        rw [← hnatg]; exact congrArg _ hresg.symm]
    exact hgerm
  · intro hab
    have hnatf := ringStalkMap_spaCompHom_germ D₀ u hu w U hwU f
    have hnatg := ringStalkMap_spaCompHom_germ D₀ u hu w U hwU g
    have hab' : stalkVle w
        ((spaRingPresheaf (presheafValue D₀)).germ (shadowPre D₀ u hu U) w hwU
          (ambComp D₀ u hu U f))
        ((spaRingPresheaf (presheafValue D₀)).germ (shadowPre D₀ u hu U) w hwU
          (ambComp D₀ u hu U g)) := by
      rw [← hnatf, ← hnatg]
      exact hab
    obtain ⟨W', hwW', hW'sub, hvle⟩ := stalkVle_elim hab' hwU rfl rfl
    -- descend to the ambient open `shadowImage W'`
    set W : Opens ↥(Spa A A⁺) := shadowImage D₀ u hu W' with hW
    have hWU : W ≤ U := by
      rintro v ⟨w'', hw'', rfl⟩
      exact hW'sub hw''
    have hpre : shadowPre D₀ u hu W = W' := shadowPre_shadowImage D₀ u hu W'
    have hwW : shadow D₀ w ∈ W := ⟨w, hwW', rfl⟩
    have hkey : (openValue W hwW).vle (limitRestrict hWU f) (limitRestrict hWU g) := by
      have h2 := comap_ambComp_openValue D₀ u hu W w (by rw [hpre]; exact hwW')
      have hAf : ambComp D₀ u hu W (limitRestrict hWU f)
          = limitRestrict (shadowPre_mono D₀ u hu hWU) (ambComp D₀ u hu U f) :=
        ambComp_naturality D₀ u hu hWU f
      have hAg : ambComp D₀ u hu W (limitRestrict hWU g)
          = limitRestrict (shadowPre_mono D₀ u hu hWU) (ambComp D₀ u hu U g) :=
        ambComp_naturality D₀ u hu hWU g
      rw [← h2]
      show (openValue (shadowPre D₀ u hu W)
          (show w ∈ shadowPre D₀ u hu W from by rw [hpre]; exact hwW')).vle
        (ambComp D₀ u hu W (limitRestrict hWU f))
        (ambComp D₀ u hu W (limitRestrict hWU g))
      rw [hAf, hAg]
      have key : ∀ (Z : Opens ↥(Spa (presheafValue D₀) (presheafValue D₀)⁺))
          (_ : Z = W') (hwZ : w ∈ Z)
          (hZU : Z ≤ shadowPre D₀ u hu U),
          (openValue Z hwZ).vle (limitRestrict hZU (ambComp D₀ u hu U f))
            (limitRestrict hZU (ambComp D₀ u hu U g)) := by
        intro Z hZ hwZ hZU
        subst hZ
        exact hvle
      exact key (shadowPre D₀ u hu W) hpre _ (shadowPre_mono D₀ u hu hWU)
    have hgerm := stalkVle_intro (v := shadow D₀ w) (U := W) (hvU := hwW) hkey
    have hresf : (spaRingPresheaf A).germ W (shadow D₀ w) hwW
        (limitRestrict hWU f)
        = (spaRingPresheaf A).germ U (shadow D₀ w) hwU f :=
      TopCat.Presheaf.germ_res_apply (spaRingPresheaf A)
        (homOfLE hWU) (shadow D₀ w) hwW f
    have hresg : (spaRingPresheaf A).germ W (shadow D₀ w) hwW
        (limitRestrict hWU g)
        = (spaRingPresheaf A).germ U (shadow D₀ w) hwU g :=
      TopCat.Presheaf.germ_res_apply (spaRingPresheaf A)
        (homOfLE hWU) (shadow D₀ w) hwW g
    rw [hresf, hresg] at hgerm
    exact hgerm

end Assembly

end SpaVIso

end ValuationSpectrum

end
