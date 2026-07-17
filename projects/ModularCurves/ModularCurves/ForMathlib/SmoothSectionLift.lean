/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Sections of a smooth morphism lift along nilpotent thickenings

The scheme-theoretic transport of `Algebra.FormallySmooth.lift`: a section of a smooth
morphism `f : X ⟶ Spec B` from an affine scheme, defined modulo a nilpotent ideal `I ⊆ B`,
extends to a genuine section of `f` restricting to the given one.

Both results are generic (no modular-curve content) and are ForMathlib-bound.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Any `f : X ⟶ Spec B` factors as `X.toSpecΓ` followed by `Spec` of the induced ring map
`(ΓSpecIso B).inv ≫ f.appTop`. -/
theorem toSpecΓ_appTop_triangle {X : Scheme.{u}} {B : CommRingCat.{u}} (f : X ⟶ Spec B) :
    f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso B).inv ≫ f.appTop) := by
  have h1 := Scheme.toSpecΓ_naturality f
  rw [show (Spec B).toSpecΓ = Spec.map (Scheme.ΓSpecIso B).hom from
    Scheme.isoSpec_Spec_hom B] at h1
  have h2 := congrArg (fun m ↦ m ≫ Spec.map (Scheme.ΓSpecIso B).inv) h1
  simp only [Category.assoc, ← Spec.map_comp] at h2
  rw [show Spec.map ((Scheme.ΓSpecIso B).inv ≫ (Scheme.ΓSpecIso B).hom) = 𝟙 _ by
    rw [Iso.inv_hom_id, Spec.map_id], Category.comp_id] at h2
  exact h2

set_option backward.isDefEq.respectTransparency.types false in
/-- Sections of a smooth morphism from an affine scheme to an affine base lift along
nilpotent thickenings of the base: the Γ–Spec transport of `Algebra.FormallySmooth.lift`. -/
theorem exists_section_lift_of_smooth {X : Scheme.{u}} {B : CommRingCat.{u}}
    (f : X ⟶ Spec B) [IsAffine X] [hf : Smooth f] (I : Ideal B) (hI : IsNilpotent I)
    (s₀ : Spec (CommRingCat.of (B ⧸ I)) ⟶ X)
    (hs₀ : s₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ s : Spec B ⟶ X, s ≫ f = 𝟙 (Spec B) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s = s₀ := by
  classical
  have : IsIso X.toSpecΓ := IsAffine.affine
  letI : Algebra ↑B ↑Γ(X, ⊤) := ((Scheme.ΓSpecIso B).inv ≫ f.appTop).hom.toAlgebra
  letI : Algebra ↑B ↑(B ⧸ I) := (Ideal.Quotient.mk I).toAlgebra
  -- the factoring triangle of `f` through the affine identification
  have hftri : f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso B).inv ≫ f.appTop) :=
    toSpecΓ_appTop_triangle f
  -- the Γ-side of `s₀`, as a `B`-algebra map
  set q₀r := Spec.preimage (s₀ ≫ X.toSpecΓ) with hq₀r
  have hq₀spec : Spec.map q₀r = s₀ ≫ X.toSpecΓ := Spec.map_preimage _
  have hq₀comp : ((Scheme.ΓSpecIso B).inv ≫ f.appTop) ≫ q₀r =
      CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hq₀spec, Category.assoc, ← hftri]
    exact hs₀
  set q₀ : ↑Γ(X, ⊤) →ₐ[↑B] ↑(B ⧸ I) :=
    { toRingHom := q₀r.hom
      commutes' := fun b ↦ congrArg
        (fun (m : B ⟶ CommRingCat.of (B ⧸ I)) ↦ m.hom b) hq₀comp } with hq₀
  have hFS : Algebra.FormallySmooth ↑B ↑Γ(X, ⊤) := by
    have h : Smooth f := hf
    rw [hftri] at h
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)] at h
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
    exact h.1
  set ψB := Algebra.FormallySmooth.lift I hI q₀ with hψB
  refine ⟨Spec.map (CommRingCat.ofHom ψB.toRingHom) ≫ CategoryTheory.inv X.toSpecΓ,
    ?_, ?_⟩
  · rw [Category.assoc, hftri, ← Category.assoc (CategoryTheory.inv X.toSpecΓ),
      IsIso.inv_hom_id, Category.id_comp, ← Spec.map_comp]
    rw [show ((Scheme.ΓSpecIso B).inv ≫ f.appTop) ≫ CommRingCat.ofHom ψB.toRingHom =
      𝟙 B from CommRingCat.hom_ext (RingHom.ext fun b ↦ ψB.commutes b)]
    exact Spec.map_id B
  · rw [← Category.assoc, ← Spec.map_comp]
    rw [show CommRingCat.ofHom ψB.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
      q₀r from CommRingCat.hom_ext (RingHom.ext fun c ↦ by
        have := congrArg (fun (m : ↑Γ(X, ⊤) →ₐ[↑B] ↑(B ⧸ I)) ↦ m c)
          (Algebra.FormallySmooth.comp_lift (R := ↑B) I hI q₀)
        exact this)]
    rw [hq₀spec, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry
