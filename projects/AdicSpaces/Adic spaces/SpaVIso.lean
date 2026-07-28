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

end SpaVIso

end ValuationSpectrum

end
