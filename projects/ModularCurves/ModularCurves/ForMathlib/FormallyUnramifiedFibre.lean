/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Unramified.Basic

/-!
# A fibrewise criterion for formal unramifiedness

Unlike the smooth analogue (`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`), formal
unramifiedness is a *fibrewise* condition that needs **no flatness**: the module of Kähler
differentials commutes with base change unconditionally
(`KaehlerDifferential.tensorKaehlerEquivBase`),
so a finite morphism whose fibres are all formally unramified is itself formally unramified.

## Main results

* `Algebra.FormallyUnramified.of_forall_residueField_fiber`: if `A` is a module-finite `R`-algebra
  and every fibre `κ(p) ⊗[R] A` is formally unramified over `κ(p)`, then `A` is formally unramified
  over `R`.
* `AlgebraicGeometry.FormallyUnramified.of_finite_fiberToSpecResidueField`: a finite morphism of
  schemes all of whose fibres over residue fields are formally unramified is formally unramified.

The intended consumer is `ModularCurves.EllipticCurve.Torsionπ.formallyUnramified` (leaf T-DISC of
BB-DIFF): `E[N] → S` is finite and — after transporting the HasseWeil separability of `[N]` through
a geometric-fibre comparison — has formally unramified geometric fibres, hence is unramified.
-/

open TensorProduct CategoryTheory Limits

open scoped TensorProduct

/-- If `A` is a module-finite `R`-algebra whose fibre `κ(p) ⊗[R] A` over every prime `p` is formally
unramified over the residue field `κ(p)`, then `A` is formally unramified over `R`.

The proof needs no flatness: `Ω[A⁄R]` is a finite `R`-module, and `κ(p) ⊗[R] Ω[A⁄R] ≃ Ω[(κ(p) ⊗
A)⁄κ(p)]`
(`KaehlerDifferential.tensorKaehlerEquivBase`) vanishes for every `p`, so `Ω[A⁄R]` has empty support
and is therefore trivial. -/
lemma Algebra.FormallyUnramified.of_forall_residueField_fiber
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (H : ∀ (p : Ideal R) [p.IsPrime], Algebra.FormallyUnramified p.ResidueField (p.Fiber A)) :
    Algebra.FormallyUnramified R A := by
  rw [Algebra.formallyUnramified_iff]
  haveI : Module.Finite R Ω[A⁄R] := by
    haveI : Algebra.EssFiniteType R A := inferInstance
    exact Module.Finite.trans A _
  rw [← Module.support_eq_empty_iff (R := R) (M := Ω[A⁄R]), Set.eq_empty_iff_forall_notMem]
  intro p
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct p,
    not_nontrivial_iff_subsingleton]
  haveI : p.asIdeal.IsPrime := p.isPrime
  haveI := H p.asIdeal
  letI : Algebra A (p.asIdeal.Fiber A) := TensorProduct.rightAlgebra
  exact (KaehlerDifferential.tensorKaehlerEquivBase R p.asIdeal.ResidueField A
    (p.asIdeal.Fiber A)).toEquiv.subsingleton

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- A finite morphism of schemes all of whose fibres (over residue fields of points of the base) are
formally unramified is itself formally unramified.

This is the unramified analogue of `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`,
but requires **neither flatness nor local finite presentation** — only finiteness, used to run the
Nakayama argument on `Ω`. -/
lemma FormallyUnramified.of_finite_fiberToSpecResidueField [IsFinite f]
    (h : ∀ y, FormallyUnramified (f.fiberToSpecResidueField y)) :
    FormallyUnramified f := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this (pullback.snd f (Y.affineCover.f i)) (fun y ↦ ?_) ⟨_, rfl⟩
    apply MorphismProperty.of_isPullback
    · exact isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback _ _) _
    · exact h _
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing f X
  · haveI hAff : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @FormallyUnramified) X.isoSpec.inv]
    refine this (X.isoSpec.inv ≫ f) (fun y ↦ ?_) ⟨_, rfl⟩
    apply MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_horiz_isIso
          (⟨by simp⟩ : CommSq X.isoSpec.inv (X.isoSpec.inv ≫ f) f (𝟙 (Spec R)))) y)
    exact h _
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [HasRingHomProperty.Spec_iff, IsFinite.SpecMap_iff] at *
  algebraize [φ.hom]
  refine Algebra.FormallyUnramified.of_forall_residueField_fiber fun p hp ↦ ?_
  rw [← RingHom.formallyUnramified_algebraMap,
    ← CommRingCat.hom_ofHom (algebraMap p.ResidueField (p.Fiber ↑S)),
    ← HasRingHomProperty.Spec_iff (P := @FormallyUnramified),
    ← MorphismProperty.arrow_mk_iso_iff (P := @FormallyUnramified)
      (Spec.fiberToSpecResidueFieldIso R S ⟨p, hp⟩)]
  exact h ⟨p, hp⟩

end AlgebraicGeometry
