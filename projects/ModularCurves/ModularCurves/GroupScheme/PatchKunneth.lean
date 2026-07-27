/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The affine Künneth identification over a base patch

Construction support for `[CHARTER-HOPF]` Wave C (`.mathlib-quality/decomposition-hopf-crux.md`,
leaf `[HG-C1c-1]`, prerequisite): given an affine open `V` of a base scheme `S` and two
affine opens `W₁ ⊆ X`, `W₂ ⊆ Y` lying over `V` along structure maps `f : X ⟶ S`,
`g : Y ⟶ S`, the fibre product of the restricted structure maps is the `Spec` of the
tensor product of the section rings:

  `pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂) ≅ Spec (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂))`

whenever the `Γ(S,V)`-algebra structures on the section rings are the restriction
(`appLE`) maps. That hypothesis is what makes the legs match `pullbackSpecIso` on the
nose.

Instantiations: with `(f, g) = (G.π, E.π)` and `(W₁, W₂) = (G|_V, U)` this is the chart
Künneth of the translation co-action; with `(f, g) = (G.π, G.π)` and
`(W₁, W₂) = (G|_V, G|_V)` it is the target of the comultiplication of the Hopf algebra of
`G` over the patch.
-/

open CategoryTheory Limits TensorProduct

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}} {V : S.Opens} {W₁ : X.Opens} {W₂ : Y.Opens}

/-- An affine open is isomorphic to the `Spec` of its sections, via `toSpecΓ`. -/
theorem IsAffineOpen.isIso_toSpecΓ {W : X.Opens} (hW : IsAffineOpen W) :
    IsIso W.toSpecΓ :=
  hW.isoSpec_hom ▸ inferInstanceAs (IsIso hW.isoSpec.hom)

section

variable (f : X ⟶ S) (g : Y ⟶ S) {e₁ : W₁ ≤ f ⁻¹ᵁ V} {e₂ : W₂ ≤ g ⁻¹ᵁ V}
variable [Algebra Γ(S, V) Γ(X, W₁)] [Algebra Γ(S, V) Γ(Y, W₂)]

/-- **The affine Künneth identification over a base patch.** -/
noncomputable def patchKunneth
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
      ≅ Spec (.of (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂))) := by
  haveI := hV.isIso_toSpecΓ
  haveI := hW₁.isIso_toSpecΓ
  haveI := hW₂.isIso_toSpecΓ
  refine (asIso (pullback.map (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂))))
    W₁.toSpecΓ W₂.toSpecΓ V.toSpecΓ ?_ ?_))
    ≪≫ pullbackSpecIso Γ(S, V) Γ(X, W₁) Γ(Y, W₂)
  · rw [h₁]
    exact (Scheme.Opens.toSpecΓ_SpecMap_appLE f V W₁ e₁).symm
  · rw [h₂]
    exact (Scheme.Opens.toSpecΓ_SpecMap_appLE g V W₂ e₂).symm

/-- The Künneth identification carries `Spec` of the left inclusion to the first
projection (composed with the affine identification of the first factor). -/
@[reassoc]
theorem patchKunneth_hom_comp_includeLeft
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    (patchKunneth f g hV hW₁ hW₂ h₁ h₂).hom
        ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := Γ(S, V)) (A := Γ(X, W₁)) (B := Γ(Y, W₂))))
      = pullback.fst (f.resLE V W₁ e₁) (g.resLE V W₂ e₂) ≫ W₁.toSpecΓ := by
  haveI := hV.isIso_toSpecΓ
  haveI := hW₁.isIso_toSpecΓ
  haveI := hW₂.isIso_toSpecΓ
  rw [patchKunneth, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSpecIso_hom_fst]
  exact pullback.lift_fst _ _ _

/-- The Künneth identification carries `Spec` of the right inclusion to the second
projection. -/
@[reassoc]
theorem patchKunneth_hom_comp_includeRight
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    (patchKunneth f g hV hW₁ hW₂ h₁ h₂).hom
        ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := Γ(S, V)) (A := Γ(X, W₁))
            (B := Γ(Y, W₂))).toRingHom)
      = pullback.snd (f.resLE V W₁ e₁) (g.resLE V W₂ e₂) ≫ W₂.toSpecΓ := by
  haveI := hV.isIso_toSpecΓ
  haveI := hW₁.isIso_toSpecΓ
  haveI := hW₂.isIso_toSpecΓ
  rw [patchKunneth, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := Γ(S, V)) (A := Γ(X, W₁))
          (B := Γ(Y, W₂))).toRingHom)
      = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := Γ(S, V)) (A := Γ(X, W₁))
          (B := Γ(Y, W₂))))) from rfl]
  rw [pullbackSpecIso_hom_snd]
  exact pullback.lift_snd _ _ _

/-- The Künneth identification is compatible with the structure maps to the base patch:
`Spec` of the canonical algebra map of the tensor product is the first projection into
the base. -/
@[reassoc]
theorem patchKunneth_hom_base
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    (patchKunneth f g hV hW₁ hW₂ h₁ h₂).hom
        ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, V) (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂))))
      = pullback.fst (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
        ≫ f.resLE V W₁ e₁ ≫ V.toSpecΓ := by
  haveI := hV.isIso_toSpecΓ
  haveI := hW₁.isIso_toSpecΓ
  haveI := hW₂.isIso_toSpecΓ
  rw [patchKunneth, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSpecIso_hom_base, ← Category.assoc]
  rw [show pullback.map (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂))))
        W₁.toSpecΓ W₂.toSpecΓ V.toSpecΓ _ _
        ≫ pullback.fst _ _
      = pullback.fst (f.resLE V W₁ e₁) (g.resLE V W₂ e₂) ≫ W₁.toSpecΓ from
    pullback.lift_fst _ _ _]
  rw [Category.assoc, h₁]
  exact congrArg _ (Scheme.Opens.toSpecΓ_SpecMap_appLE f V W₁ e₁)

/-- The section-level transport across the Künneth identification:
`Γ(pullback, ⊤) ≅ Γ(X,W₁) ⊗ Γ(Y,W₂)`. -/
noncomputable def patchKunnethΓ
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    Γ(pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂), ⊤)
      ⟶ CommRingCat.of (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂)) :=
  (patchKunneth f g hV hW₁ hW₂ h₁ h₂).inv.appTop
    ≫ (Scheme.ΓSpecIso (.of (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂)))).hom

/-- **The `Γ`-dual of the left leg**: the first projection, transported, is the left
inclusion into the tensor product. -/
theorem topIso_inv_fst_appTop_patchKunnethΓ
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    W₁.topIso.inv
        ≫ (pullback.fst (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)).appTop
        ≫ patchKunnethΓ f g hV hW₁ hW₂ h₁ h₂
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := Γ(S, V)) (A := Γ(X, W₁)) (B := Γ(Y, W₂))) := by
  set K := patchKunneth f g hV hW₁ hW₂ h₁ h₂ with hK
  set ιL := CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
    (R := Γ(S, V)) (A := Γ(X, W₁)) (B := Γ(Y, W₂))) with hιL
  -- take `appTop` of the Spec-side leg lemma
  have hleg := congrArg (fun m : pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
      ⟶ (Spec Γ(X, W₁) : Scheme) => Scheme.Hom.appTop m)
    (patchKunneth_hom_comp_includeLeft f g hV hW₁ hW₂ h₁ h₂)
  simp only [Scheme.Hom.comp_appTop] at hleg
  -- rewrite the two `appTop`s that have closed forms
  rw [show (Spec.map ιL).appTop
      = (Scheme.ΓSpecIso Γ(X, W₁)).hom ≫ ιL
        ≫ (Scheme.ΓSpecIso (.of (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂)))).inv from by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality ιL] at hleg
  rw [Scheme.Opens.toSpecΓ_appTop] at hleg
  -- cancel the leading `ΓSpecIso` and transport across `K`
  rw [patchKunnethΓ, ← Category.assoc, ← Category.assoc]
  rw [show W₁.topIso.inv ≫ (pullback.fst (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)).appTop
      = (Scheme.ΓSpecIso Γ(X, W₁)).inv
        ≫ ((Scheme.ΓSpecIso Γ(X, W₁)).hom ≫ W₁.topIso.inv)
        ≫ (pullback.fst (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)).appTop from by
    rw [Category.assoc, Iso.inv_hom_id_assoc]]
  rw [Category.assoc, Category.assoc, ← hleg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((patchKunneth f g hV hW₁ hW₂ h₁ h₂).hom.appTop),
    ← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
    AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

/-- **The `Γ`-dual of the right leg**: the second projection, transported, is the right
inclusion into the tensor product. -/
theorem topIso_inv_snd_appTop_patchKunnethΓ
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    W₂.topIso.inv
        ≫ (pullback.snd (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)).appTop
        ≫ patchKunnethΓ f g hV hW₁ hW₂ h₁ h₂
      = CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := Γ(S, V)) (A := Γ(X, W₁))
            (B := Γ(Y, W₂))).toRingHom := by
  set ιR := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := Γ(S, V)) (A := Γ(X, W₁))
      (B := Γ(Y, W₂))).toRingHom with hιR
  have hleg := congrArg (fun m : pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
      ⟶ (Spec Γ(Y, W₂) : Scheme) => Scheme.Hom.appTop m)
    (patchKunneth_hom_comp_includeRight f g hV hW₁ hW₂ h₁ h₂)
  simp only [Scheme.Hom.comp_appTop] at hleg
  rw [show (Spec.map ιR).appTop
      = (Scheme.ΓSpecIso Γ(Y, W₂)).hom ≫ ιR
        ≫ (Scheme.ΓSpecIso (.of (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂)))).inv from by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality ιR] at hleg
  rw [Scheme.Opens.toSpecΓ_appTop] at hleg
  rw [patchKunnethΓ, ← Category.assoc, ← Category.assoc]
  rw [show W₂.topIso.inv ≫ (pullback.snd (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)).appTop
      = (Scheme.ΓSpecIso Γ(Y, W₂)).inv
        ≫ ((Scheme.ΓSpecIso Γ(Y, W₂)).hom ≫ W₂.topIso.inv)
        ≫ (pullback.snd (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)).appTop from by
    rw [Category.assoc, Iso.inv_hom_id_assoc]]
  rw [Category.assoc, Category.assoc, ← hleg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((patchKunneth f g hV hW₁ hW₂ h₁ h₂).hom.appTop),
    ← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
    AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

/-- The section-level transport is an isomorphism. -/
instance isIso_patchKunnethΓ
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    IsIso (patchKunnethΓ f g hV hW₁ hW₂ h₁ h₂) := by
  rw [patchKunnethΓ]
  haveI : IsIso ((patchKunneth f g hV hW₁ hW₂ h₁ h₂).inv.appTop) := by
    refine ⟨(patchKunneth f g hV hW₁ hW₂ h₁ h₂).hom.appTop, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
        AlgebraicGeometry.Scheme.Hom.id_appTop]
    · rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
        AlgebraicGeometry.Scheme.Hom.id_appTop]
  infer_instance

/-- **Ext principle for maps out of a tensor product** of `CommRingCat` objects: two ring
maps agreeing on both inclusions agree. -/
theorem tensor_hom_ext {R A B C : CommRingCat.{u}} [Algebra R A] [Algebra R B]
    {φ ψ : CommRingCat.of (A ⊗[R] B) ⟶ C}
    (hL : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := A) (B := B)) ≫ φ
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := A) (B := B)) ≫ ψ)
    (hR : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := A) (B := B)).toRingHom ≫ φ
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := A) (B := B)).toRingHom ≫ ψ) :
    φ = ψ := by
  have hL' : ∀ a : A, φ.hom (a ⊗ₜ[R] 1) = ψ.hom (a ⊗ₜ[R] 1) := fun a =>
    congrArg (fun m : A ⟶ C => m.hom a) hL
  have hR' : ∀ b : B, φ.hom (1 ⊗ₜ[R] b) = ψ.hom (1 ⊗ₜ[R] b) := fun b =>
    congrArg (fun m : B ⟶ C => m.hom b) hR
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
      rw [show (a ⊗ₜ[R] b : A ⊗[R] B) = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] b) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      rw [map_mul, map_mul, hL' a, hR' b]

end

/-! ### The affine Künneth identification

The `⊤`-level version: two affine schemes over an affine base. This is the reusable
citizen (the opens-level `patchKunneth` is the special case `W.toScheme → V.toScheme`),
and it iterates — which is what the coassociativity of the group-scheme's Hopf algebra
needs (a triple product). -/

section Affine

variable {B X Y : Scheme.{u}} [IsAffine B] [IsAffine X] [IsAffine Y]
variable (f : X ⟶ B) (g : Y ⟶ B)
variable [Algebra Γ(B, ⊤) Γ(X, ⊤)] [Algebra Γ(B, ⊤) Γ(Y, ⊤)]

/-- **The affine Künneth identification**: `X ×_B Y ≅ Spec (Γ(X) ⊗[Γ(B)] Γ(Y))`, when the
algebra structures are the pullbacks of sections. -/
noncomputable def affineKunneth
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    pullback f g ≅ Spec (.of (Γ(X, ⊤) ⊗[Γ(B, ⊤)] Γ(Y, ⊤))) :=
  (asIso (pullback.map f g
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤))))
    X.isoSpec.hom Y.isoSpec.hom B.isoSpec.hom
    (by rw [h₁]; exact (Scheme.isoSpec_hom_naturality f).symm)
    (by rw [h₂]; exact (Scheme.isoSpec_hom_naturality g).symm)))
    ≪≫ pullbackSpecIso Γ(B, ⊤) Γ(X, ⊤) Γ(Y, ⊤)

@[reassoc]
theorem affineKunneth_hom_comp_includeLeft
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    (affineKunneth f g h₁ h₂).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := Γ(B, ⊤)) (A := Γ(X, ⊤)) (B := Γ(Y, ⊤))))
      = pullback.fst f g ≫ X.isoSpec.hom := by
  rw [affineKunneth, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSpecIso_hom_fst]
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem affineKunneth_hom_comp_includeRight
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    (affineKunneth f g h₁ h₂).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := Γ(B, ⊤)) (A := Γ(X, ⊤)) (B := Γ(Y, ⊤))).toRingHom)
      = pullback.snd f g ≫ Y.isoSpec.hom := by
  rw [affineKunneth, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := Γ(B, ⊤)) (A := Γ(X, ⊤))
          (B := Γ(Y, ⊤))).toRingHom)
      = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := Γ(B, ⊤)) (A := Γ(X, ⊤))
          (B := Γ(Y, ⊤))))) from rfl]
  rw [pullbackSpecIso_hom_snd]
  exact pullback.lift_snd _ _ _

/-- The section-level transport across the affine Künneth identification. -/
noncomputable def affineKunnethΓ
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    Γ(pullback f g, ⊤) ⟶ CommRingCat.of (Γ(X, ⊤) ⊗[Γ(B, ⊤)] Γ(Y, ⊤)) :=
  (affineKunneth f g h₁ h₂).inv.appTop
    ≫ (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⊗[Γ(B, ⊤)] Γ(Y, ⊤)))).hom

instance isIso_affineKunnethΓ
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    IsIso (affineKunnethΓ f g h₁ h₂) := by
  rw [affineKunnethΓ]
  haveI : IsIso ((affineKunneth f g h₁ h₂).inv.appTop) := by
    refine ⟨(affineKunneth f g h₁ h₂).hom.appTop, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
        AlgebraicGeometry.Scheme.Hom.id_appTop]
    · rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
        AlgebraicGeometry.Scheme.Hom.id_appTop]
  infer_instance

/-- **The `Γ`-dual of the left leg**, affine version. -/
theorem fst_appTop_affineKunnethΓ
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    (pullback.fst f g).appTop ≫ affineKunnethΓ f g h₁ h₂
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := Γ(B, ⊤)) (A := Γ(X, ⊤)) (B := Γ(Y, ⊤))) := by
  set ιL := CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
    (R := Γ(B, ⊤)) (A := Γ(X, ⊤)) (B := Γ(Y, ⊤))) with hιL
  have hleg := congrArg (fun m : pullback f g ⟶ (Spec Γ(X, ⊤) : Scheme) =>
      Scheme.Hom.appTop m) (affineKunneth_hom_comp_includeLeft f g h₁ h₂)
  simp only [Scheme.Hom.comp_appTop] at hleg
  rw [show (Spec.map ιL).appTop
      = (Scheme.ΓSpecIso Γ(X, ⊤)).hom ≫ ιL
        ≫ (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⊗[Γ(B, ⊤)] Γ(Y, ⊤)))).inv from by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality ιL] at hleg
  rw [show X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom from
    Scheme.toSpecΓ_appTop X] at hleg
  rw [affineKunnethΓ, ← Category.assoc]
  rw [show (pullback.fst f g).appTop
      = (Scheme.ΓSpecIso Γ(X, ⊤)).inv
        ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom ≫ (pullback.fst f g).appTop from by simp]
  rw [Category.assoc, ← hleg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((affineKunneth f g h₁ h₂).hom.appTop),
    ← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
    AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

/-- **The `Γ`-dual of the right leg**, affine version. -/
theorem snd_appTop_affineKunnethΓ
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    (pullback.snd f g).appTop ≫ affineKunnethΓ f g h₁ h₂
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := Γ(B, ⊤)) (A := Γ(X, ⊤)) (B := Γ(Y, ⊤))).toRingHom := by
  set ιR := CommRingCat.ofHom (Algebra.TensorProduct.includeRight
    (R := Γ(B, ⊤)) (A := Γ(X, ⊤)) (B := Γ(Y, ⊤))).toRingHom with hιR
  have hleg := congrArg (fun m : pullback f g ⟶ (Spec Γ(Y, ⊤) : Scheme) =>
      Scheme.Hom.appTop m) (affineKunneth_hom_comp_includeRight f g h₁ h₂)
  simp only [Scheme.Hom.comp_appTop] at hleg
  rw [show (Spec.map ιR).appTop
      = (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ ιR
        ≫ (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⊗[Γ(B, ⊤)] Γ(Y, ⊤)))).inv from by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality ιR] at hleg
  rw [show Y.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).hom from
    Scheme.toSpecΓ_appTop Y] at hleg
  rw [affineKunnethΓ, ← Category.assoc]
  rw [show (pullback.snd f g).appTop
      = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv
        ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ (pullback.snd f g).appTop from by simp]
  rw [Category.assoc, ← hleg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((affineKunneth f g h₁ h₂).hom.appTop),
    ← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
    AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

/-- **The `Γ`-dual of the base**, affine version: the base algebra map dualises to the
first projection followed by the structure map to `B`. -/
theorem base_appTop_affineKunnethΓ
    (h₁ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(X, ⊤)) = f.appTop)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(B, ⊤) Γ(Y, ⊤)) = g.appTop) :
    f.appTop ≫ (pullback.fst f g).appTop ≫ affineKunnethΓ f g h₁ h₂
      = CommRingCat.ofHom
          (algebraMap Γ(B, ⊤) (Γ(X, ⊤) ⊗[Γ(B, ⊤)] Γ(Y, ⊤))) := by
  rw [fst_appTop_affineKunnethΓ, ← h₁, ← CommRingCat.ofHom_comp]

end Affine

end AlgebraicGeometry
