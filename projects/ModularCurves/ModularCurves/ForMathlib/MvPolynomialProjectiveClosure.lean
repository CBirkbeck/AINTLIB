/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import ModularCurves.ForMathlib.GradedQuotient
import ModularCurves.ForMathlib.MvPolynomialHomogenize
import ModularCurves.ForMathlib.ProjClosedImmersion
import ModularCurves.ForMathlib.ProjectiveSpaceChart

/-!
# Projective closures from homogenized relations

A family of affine polynomial relations determines a homogeneous quotient after adjoining one
variable. With finitely many polynomial variables, its `Proj` is proper over the coefficient ring.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization MorphismProperty

noncomputable section

universe u

variable {R : Type u} {σ κ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective scheme cut out by a family of homogenized polynomial relations. -/
@[reducible]
def homogenizedProj (g : κ → MvPolynomial σ R) (d : κ → ℕ) : Scheme.{u} :=
  Proj (quotientGrading (homogenizedIdeal g d))

/-- The structure morphism of a homogenized projective closure to its coefficient ring. -/
def homogenizedProjπ (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProj g d ⟶ Spec (.of R) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (algebraMapGradeZero (homogenizedIdeal g d)))

/-- A homogenized projective closure in finitely many variables is proper over its coefficient
ring. -/
lemma homogenizedProjπ_isProper [Finite σ] (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    IsProper (homogenizedProjπ g d) := by
  let I := homogenizedIdeal g d
  haveI hfiniteR : Algebra.FiniteType R (MvPolynomial (Option σ) R ⧸ I.toIdeal) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ R I.toIdeal) (Ideal.Quotient.mkₐ_surjective R _)
  haveI hfiniteZero :
      Algebra.FiniteType (↥(quotientGrading I 0))
        (MvPolynomial (Option σ) R ⧸ I.toIdeal) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (↥(quotientGrading I 0)) (MvPolynomial (Option σ) R ⧸ I.toIdeal)
  haveI hproj : IsProper (Proj.toSpecZero (quotientGrading I)) := inferInstance
  haveI hclosed : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMapGradeZero I))) :=
    IsClosedImmersion.spec_of_surjective _
      (algebraMapGradeZero_surjective_mvPolynomial I)
  haveI hbase : IsProper
      (Spec.map (CommRingCat.ofHom (algebraMapGradeZero I))) := inferInstance
  change IsProper
    (Proj.toSpecZero (quotientGrading I) ≫
      Spec.map (CommRingCat.ofHom (algebraMapGradeZero I)))
  exact IsStableUnderComposition.comp_mem _ _ hproj hbase

section OptionChart

local instance : DecidableEq (Option σ) := Classical.decEq _

private def optionNeNoneEquiv (σ : Type*) : {x : Option σ // x ≠ none} ≃ σ where
  toFun x := x.1.get (Option.ne_none_iff_isSome.mp x.2)
  invFun x := ⟨some x, by simp⟩
  left_inv x := Subtype.ext (Option.some_get _)
  right_inv x := Option.get_some _ _

private lemma rename_dehomogenizeAux_none (p : MvPolynomial (Option σ) R) :
    rename (optionNeNoneEquiv σ) (dehomogenizeAux R none p) =
      dehomogenizeOption R p := by
  classical
  apply RingHom.congr_fun
    (f := (rename (optionNeNoneEquiv σ)).toRingHom.comp (dehomogenizeAux R none))
    (g := dehomogenizeOption R)
  refine ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp
  · cases i with
    | none => simp
    | some i => simp [optionNeNoneEquiv]

/-- The standard projective chart at the added homogenizing variable is affine space in the
original variables. -/
noncomputable def optionChartRingEquiv :
    Away (homogeneousSubmodule (Option σ) R) (X none : MvPolynomial (Option σ) R) ≃+*
      MvPolynomial σ R := by
  classical
  exact (chartRingEquiv R (none : Option σ)).trans
    (renameEquiv R (optionNeNoneEquiv σ)).toRingEquiv

/-- On a homogeneous fraction, the option chart is dehomogenization of its numerator. -/
lemma optionChartRingEquiv_apply_mk (n : ℕ) (p : MvPolynomial (Option σ) R)
    (hp : p ∈ homogeneousSubmodule (Option σ) R (n • (1 : ℕ))) :
    optionChartRingEquiv
      (Away.mk _ (X_mem_homogeneousSubmodule_one R (none : Option σ)) n p hp) =
      dehomogenizeOption R p := by
  classical
  change rename (optionNeNoneEquiv σ)
      (dehomogenizeAt R none
        (Away.mk _ (X_mem_homogeneousSubmodule_one R (none : Option σ)) n p hp)) = _
  rw [dehomogenizeAt_mk, rename_dehomogenizeAux_none]

/-- Under the standard chart equivalence, a homogeneous lift divided by the homogenizing
variable to its chosen degree is the original polynomial. -/
lemma optionChartRingEquiv_apply_mk_homogenizeOption
    (p : MvPolynomial σ R) (n : ℕ) (h : p.totalDegree ≤ n) :
    optionChartRingEquiv
      (Away.mk _ (X_mem_homogeneousSubmodule_one R (none : Option σ)) n
        (homogenizeOption p n)
        (by
          simpa using (mem_homogeneousSubmodule _ _).mpr
            (homogenizeOption_isHomogeneous p n))) = p := by
  rw [optionChartRingEquiv_apply_mk,
    dehomogenizeOption_homogenizeOption p n h]

/-- The kernel cutting out the homogenized quotient chart becomes the original affine relation
ideal under the option chart equivalence. -/
lemma map_optionChartRingEquiv_ker_awayMap_homogenizedIdeal
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    Ideal.map (optionChartRingEquiv (R := R) (σ := σ)).toRingHom
        (RingHom.ker (Away.map
          (quotientGradingHom (homogenizedIdeal (R := R) (σ := σ) g d))
          (X none : MvPolynomial (Option σ) R))) =
      Ideal.span (Set.range g) := by
  classical
  let I := homogenizedIdeal g d
  let s : MvPolynomial (Option σ) R := X none
  let hs : s ∈ homogeneousSubmodule (Option σ) R 1 :=
    X_mem_homogeneousSubmodule_one R none
  let φ := Away.map (quotientGradingHom I) s
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, rfl⟩ :=
      (Ideal.mem_map_of_equiv (optionChartRingEquiv (R := R) (σ := σ)) _).mp hx
    obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ hs z
    rw [RingHom.mem_ker, Away.map_mk] at hz
    have hval := congrArg
      (valRingHom (Submonoid.powers ((quotientGradingHom I) s))) hz
    rw [valRingHom_apply, valRingHom_apply, Away.val_mk, val_zero] at hval
    have hzero : algebraMap (MvPolynomial (Option σ) R ⧸ I.toIdeal)
        (Localization (Submonoid.powers ((quotientGradingHom I) s)))
        ((quotientGradingHom I) p) = 0 := by
      rw [← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk',
        IsLocalization.mk'_eq_zero_iff]
      rwa [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers ((quotientGradingHom I) s)) _ _).mp hzero
    have hmem : s ^ k * p ∈ I.toIdeal := by
      have : (quotientGradingHom I) (s ^ k * p) = 0 := by
        rw [map_mul, map_pow]
        exact hc
      rwa [quotientGradingHom_apply, ← RingHom.mem_ker, Ideal.mk_ker] at this
    have hdehom : dehomogenizeOption R (s ^ k * p) ∈ Ideal.span (Set.range g) := by
      rw [← map_dehomogenizeOption_homogenizedIdeal g d hdeg]
      exact Ideal.mem_map_of_mem (dehomogenizeOption R) hmem
    rw [map_mul, map_pow, dehomogenizeOption_X_none, one_pow, one_mul] at hdehom
    rw [optionChartRingEquiv_apply_mk (R := R) (σ := σ)]
    exact hdehom
  · rw [Ideal.span_le]
    intro p hp
    obtain ⟨j, rfl⟩ := hp
    let q := homogenizeOption (g j) (d j)
    have hq : q ∈ homogeneousSubmodule (Option σ) R (d j) :=
      (mem_homogeneousSubmodule _ _).mpr (homogenizeOption_isHomogeneous (g j) (d j))
    have hq' : q ∈ homogeneousSubmodule (Option σ) R ((d j) • (1 : ℕ)) := by
      simpa using hq
    let w := Away.mk _ hs (d j) q hq'
    have hw : w ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, Away.map_mk]
      have hqzero : (quotientGradingHom I) q = 0 := by
        rw [quotientGradingHom_apply, ← RingHom.mem_ker, Ideal.mk_ker]
        exact Ideal.subset_span ⟨j, rfl⟩
      apply val_injective
      rw [Away.val_mk, val_zero, hqzero]
      exact Localization.mk_zero _
    have he : (optionChartRingEquiv (R := R) (σ := σ)) w = g j := by
      rw [optionChartRingEquiv_apply_mk (R := R) (σ := σ),
        dehomogenizeOption_homogenizeOption _ _ (hdeg j)]
    rw [← he]
    exact Ideal.mem_map_of_mem
      (optionChartRingEquiv (R := R) (σ := σ)).toRingHom hw

/-- The chart of a homogenized projective closure at the homogenizing coordinate is the original
affine presentation. -/
noncomputable def homogenizedChartRingEquiv
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) ≃+*
      Away (quotientGrading (homogenizedIdeal g d))
        ((quotientGradingHom (homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R)) :=
  ((Ideal.quotientEquiv
    (RingHom.ker (Away.map (quotientGradingHom (homogenizedIdeal g d))
      (X none : MvPolynomial (Option σ) R)))
    (Ideal.span (Set.range g)) optionChartRingEquiv
    (map_optionChartRingEquiv_ker_awayMap_homogenizedIdeal g d hdeg).symm).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (away_map_quotientGradingHom_surjective (homogenizedIdeal g d)
        (X_mem_homogeneousSubmodule_one R (none : Option σ))))

@[simp]
lemma homogenizedChartRingEquiv_mk
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) (p : MvPolynomial σ R) :
    homogenizedChartRingEquiv g d hdeg
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) p) =
      Away.map (quotientGradingHom (homogenizedIdeal g d))
        (X none : MvPolynomial (Option σ) R) (optionChartRingEquiv.symm p) := by
  rfl

end OptionChart

end

end MvPolynomial
