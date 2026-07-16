/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The fibre rank of a fibre product of finite flat morphisms

**[KM-W0 / F3-prodrank] ForMathlib brick (mathlib-PR shape — belongs next to
`Scheme.Hom.finrank_pullback_snd`).** For finite flat `f : X ⟶ S`, `g : Y ⟶ S`:

`(pullback.fst f g ≫ f).finrank s = f.finrank s * g.finrank s`.

mathlib's `finrank` API keeps its affine auxiliary (`IsAffine.finrank`) and the
chart-reduction lemmas PRIVATE, so we rebuild the short private layer here verbatim
(FlatRank.lean:56–115) and then prove the product formula in the same style: reduce to
the affine auxiliary over a chart, identify the product's global sections with the
tensor product through the pushout square of the pullback, and finish with
`Module.rankAtStalk_tensorProduct`.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

universe u

noncomputable section

namespace ModularCurves

variable {X Y S T : Scheme.{u}}

/-- Rebuild of mathlib's private `IsAffine.finrank`: the rank of `f : X ⟶ S` at `s`,
`S` affine, through the global-sections ring map. -/
def affineFinrank [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  f.appTop.hom.finrank (S.isoSpec.hom s)

/-- Rebuild of mathlib's private `IsAffine.finrank_of_isPullback`. -/
lemma affineFinrank_of_isPullback [IsAffine S] [IsAffine T] (f : X ⟶ S)
    (f' : Y ⟶ T) (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [Flat f] [IsFinite f]
    (s : S) (t : T) (hs : g t = s) :
    affineFinrank f' t = affineFinrank f s := by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [affineFinrank]
  rw [CommRingCat.finrank_eq_of_isPushout this f.flat_appTop f.finite_appTop (T.isoSpec.hom t),
    ← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality]
  rfl

/-- Rebuild of mathlib's private `IsAffine.finrank_snd`. -/
lemma affineFinrank_snd [IsAffine S] [IsAffine T] (f : X ⟶ S)
    (g : T ⟶ S) [Flat f] [IsFinite f] (x : T) :
    affineFinrank (pullback.snd f g) x = affineFinrank f (g x) :=
  affineFinrank_of_isPullback f _ _ _ (.of_hasPullback _ _) _ _ rfl

/-- Rebuild of mathlib's private `Scheme.Hom.finrank_eq_finrank_snd_of_isAffine`. -/
lemma finrank_eq_affineFinrank_snd (f : X ⟶ S) (g : T ⟶ S) [IsAffine T] (t : T)
    [Flat f] [IsFinite f] :
    f.finrank (g t) = affineFinrank (pullback.snd f g) t := by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  trans affineFinrank (pullback.snd (pullback.snd f g) (u ≫ pullback.snd _ _)) z
  · refine (affineFinrank_of_isPullback _ _ ?_ ?_ ?_ _ _ ?_).symm
    · exact pullback.map _ _ _ _ (pullback.fst f g) (u ≫ pullback.fst _ _) g
        pullback.condition.symm (by simp [← pullback.condition]; rfl)
    · exact u ≫ pullback.fst _ _
    · apply IsPullback.map_fst_comp_fst_snd_comp_fst
    · exact hyl
  · simp_rw [← hyr]
    exact affineFinrank_snd (pullback.snd f g) (u ≫ pullback.snd _ _) z

end ModularCurves
