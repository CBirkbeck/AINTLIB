/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FiniteProperProduct
import ModularCurves.ForMathlib.ProjectiveFactorizationProduct

/-!
# Finite products of projective factorizations

A nonempty finite product over an affine base has a projective factorization whenever each factor
does.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

private def projectiveOverSpec (R : Type u) [CommRing R] :
    ObjectProperty (Over (Spec (.of R))) :=
  fun X => IsProjectiveFactorization X.hom

private lemma projectiveOverSpec_of_iso {R : Type u} [CommRing R]
    {X Y : Over (Spec (.of R))} (e : X ≅ Y)
    (hX : projectiveOverSpec R X) :
    projectiveOverSpec R Y := by
  unfold projectiveOverSpec at hX ⊢
  have h := hX.comp_isClosedImmersion (Comma.leftIso e).inv (by infer_instance)
  rw [Comma.leftIso_inv e, e.inv.w] at h
  exact h

private lemma projectiveOverSpec_prod {R : Type u} [CommRing R]
    (X Y : Over (Spec (.of R)))
    (hX : projectiveOverSpec R X) (hY : projectiveOverSpec R Y) :
    projectiveOverSpec R (X ⨯ Y) := by
  unfold projectiveOverSpec at hX hY ⊢
  have h := IsProjectiveFactorization.pullback hX hY
  have h' := h.comp_isClosedImmersion
    (Over.prodLeftIsoPullback X Y).hom (by infer_instance)
  rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst] at h'
  rw [← (prod.fst (X := X) (Y := Y)).w]
  exact h'

private lemma projectiveOverSpec_finProduct {R : Type u} [CommRing R] :
    ∀ (n : ℕ) (f : Fin n.succ → Over (Spec (.of R))),
      (∀ i, projectiveOverSpec R (f i)) →
        projectiveOverSpec R (∏ᶜ f)
  | 0, f, hf => by
      apply projectiveOverSpec_of_iso (productUniqueIso f).symm
      exact hf default
  | n + 1, f, hf => by
      let g : Fin n.succ → Over (Spec (.of R)) := fun i => f i.succ
      have hg : projectiveOverSpec R (∏ᶜ g) :=
        projectiveOverSpec_finProduct n g (fun i => hf i.succ)
      have hprod : projectiveOverSpec R (f 0 ⨯ ∏ᶜ g) :=
        projectiveOverSpec_prod (f 0) (∏ᶜ g) (hf 0) hg
      let c₁ : Fan g := Fan.mk (∏ᶜ g) (Pi.π g)
      let c₂ : BinaryFan (f 0) (∏ᶜ g) :=
        BinaryFan.mk prod.fst prod.snd
      let c : Fan f := extendFan c₁ c₂
      have hc : IsLimit c :=
        extendFanIsLimit f (productIsProduct g) (prodIsProd _ _)
      let e : c.pt ≅ ∏ᶜ f :=
        IsLimit.conePointUniqueUpToIso hc (productIsProduct f)
      exact projectiveOverSpec_of_iso e hprod

private lemma projectiveOverSpec_finiteProduct {R : Type u} [CommRing R]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (f : ι → Over (Spec (.of R)))
    (hf : ∀ i, projectiveOverSpec R (f i)) :
    projectiveOverSpec R (∏ᶜ f) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  cases n with
  | zero =>
      exact Fin.elim0 (e (Classical.choice (inferInstance : Nonempty ι)))
  | succ n =>
      have hfin : projectiveOverSpec R (∏ᶜ fun i : Fin n.succ => f (e.symm i)) :=
        projectiveOverSpec_finProduct n _ (fun i => hf (e.symm i))
      exact projectiveOverSpec_of_iso (Pi.reindex e.symm f) hfin

namespace Scheme.FiniteProperProduct

variable {R : Type u} [CommRing R] {ι : Type u} [Finite ι] [Nonempty ι]
variable {Z : ι → Scheme.{u}} (p : ∀ i, Z i ⟶ Spec (.of R))

/-- A nonempty finite product of projectively factored schemes is projectively factored. -/
lemma π_isProjectiveFactorization
    (hp : ∀ i, IsProjectiveFactorization (p i)) :
    IsProjectiveFactorization (π p) :=
  projectiveOverSpec_finiteProduct
    (fun i => Over.mk (p i)) hp

end Scheme.FiniteProperProduct

end AlgebraicGeometry
