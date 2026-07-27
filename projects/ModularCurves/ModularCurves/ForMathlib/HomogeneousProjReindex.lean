/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.MvPolynomialProjectiveClosure
import ModularCurves.ForMathlib.ProjMapClosedImmersion

/-!
# Reindexing polynomial projective space

An equivalence of homogeneous coordinate types induces an isomorphism between the corresponding
polynomial `Proj` schemes. This isomorphism respects their structural maps to the coefficient
spectrum.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {R : Type u} [CommRing R] {σ τ υ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma rename_mem_homogeneousSubmodule (f : σ → τ) {d : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ homogeneousSubmodule σ R d) :
    MvPolynomial.rename f p ∈ homogeneousSubmodule τ R d :=
  hp.rename_isHomogeneous

/-- Renaming polynomial variables preserves the homogeneous grading. -/
def homogeneousRenameGradedHom (R : Type u) [CommRing R] {σ τ : Type}
    (f : σ → τ) :
    homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule τ R where
  __ := (MvPolynomial.rename f).toRingHom
  map_mem := rename_mem_homogeneousSubmodule f

@[simp]
lemma homogeneousRenameGradedHom_apply (f : σ → τ) (p : MvPolynomial σ R) :
    homogeneousRenameGradedHom R f p = MvPolynomial.rename f p :=
  rfl

private lemma homogeneousRenameGradedHom_surjective (e : σ ≃ τ) :
    Function.Surjective (homogeneousRenameGradedHom R e) := by
  intro p
  refine ⟨MvPolynomial.rename e.symm p, ?_⟩
  simp only [homogeneousRenameGradedHom_apply, MvPolynomial.rename_rename,
    e.self_comp_symm, MvPolynomial.rename_id_apply]

private lemma homogeneousRenameGradedHom_irrelevant_le (e : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule τ R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ R)).map
        (homogeneousRenameGradedHom R e) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective
    (homogeneousRenameGradedHom R e)
    (homogeneousRenameGradedHom_surjective e)

private lemma homogeneousRenameGradedHom_comp (f : σ → τ) (g : τ → υ) :
    (homogeneousRenameGradedHom R g).comp (homogeneousRenameGradedHom R f) =
      homogeneousRenameGradedHom R (g ∘ f) := by
  apply GradedRingHom.ext
  intro p
  exact MvPolynomial.rename_rename f g p

private lemma homogeneousRenameGradedHom_id :
    homogeneousRenameGradedHom R (id : σ → σ) =
      GradedRingHom.id (homogeneousSubmodule σ R) := by
  apply GradedRingHom.ext
  intro p
  exact MvPolynomial.rename_id_apply p

private lemma homogeneousProj_map_congr
    {f g : homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule τ R}
    (h : f = g)
    (hf : HomogeneousIdeal.irrelevant (homogeneousSubmodule τ R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ R)).map f)
    (hg : HomogeneousIdeal.irrelevant (homogeneousSubmodule τ R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ R)).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst h
  rfl

/-- An equivalence of coordinate types induces an isomorphism of polynomial projective spaces. -/
noncomputable def homogeneousProjReindexIso (R : Type u) [CommRing R]
    {σ τ : Type} (e : σ ≃ τ) :
    Proj (homogeneousSubmodule σ R) ≅ Proj (homogeneousSubmodule τ R) where
  hom := Proj.map (homogeneousRenameGradedHom R e.symm)
    (homogeneousRenameGradedHom_irrelevant_le e.symm)
  inv := Proj.map (homogeneousRenameGradedHom R e)
    (homogeneousRenameGradedHom_irrelevant_le e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h :
        (homogeneousRenameGradedHom R e.symm).comp
            (homogeneousRenameGradedHom R e) =
          GradedRingHom.id (homogeneousSubmodule σ R) := by
      rw [homogeneousRenameGradedHom_comp, e.symm_comp_self,
        homogeneousRenameGradedHom_id]
    exact (homogeneousProj_map_congr h _ _).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h :
        (homogeneousRenameGradedHom R e).comp
            (homogeneousRenameGradedHom R e.symm) =
          GradedRingHom.id (homogeneousSubmodule τ R) := by
      rw [homogeneousRenameGradedHom_comp, e.self_comp_symm,
        homogeneousRenameGradedHom_id]
    exact (homogeneousProj_map_congr h _ _).trans Proj.map_id

private lemma homogeneousRenameGradedHom_zero_algebraMap
    (e : σ ≃ τ) (r : R) :
    ModularCurves.gradedRingHomZero
          (homogeneousRenameGradedHom R e.symm)
          (algebraMap R (homogeneousSubmodule τ R 0) r) =
      algebraMap R (homogeneousSubmodule σ R 0) r := by
  apply Subtype.ext
  exact (MvPolynomial.rename e.symm).commutes r

private lemma homogeneousRenameGradedHom_zero_comp_algebraMap
    (e : σ ≃ τ) :
    CommRingCat.ofHom
          (algebraMap R (homogeneousSubmodule τ R 0)) ≫
        CommRingCat.ofHom
          (ModularCurves.gradedRingHomZero
            (homogeneousRenameGradedHom R e.symm)) =
      CommRingCat.ofHom
        (algebraMap R (homogeneousSubmodule σ R 0)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact homogeneousRenameGradedHom_zero_algebraMap e r

/-- Reindexing polynomial projective space commutes with its structural morphism. -/
lemma homogeneousProjReindexIso_hom_comp_homogeneousProjπ (e : σ ≃ τ) :
    (homogeneousProjReindexIso R e).hom ≫
        homogeneousProjπ (R := R) (σ := τ) =
      homogeneousProjπ (R := R) (σ := σ) := by
  unfold homogeneousProjReindexIso homogeneousProjπ
  rw [← Category.assoc, ModularCurves.map_comp_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp,
    homogeneousRenameGradedHom_zero_comp_algebraMap]

end

end MvPolynomial
