/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Ideal
import ModularCurves.ForMathlib.GradedQuotient
import ModularCurves.ForMathlib.MvPolynomialHomogenize
import ModularCurves.ForMathlib.ProjClosedImmersion
import ModularCurves.ForMathlib.ProjToSpecZero
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

/-- The monomials of total degree `n` form a basis of the degree-`n` homogeneous
submodule of a multivariate polynomial ring. -/
noncomputable def basisHomogeneousSubmodule (n : ℕ) :
    Module.Basis {d : σ →₀ ℕ // d.degree = n} R (homogeneousSubmodule σ R n) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact basisRestrictSupport R {d : σ →₀ ℕ | d.degree = n}

/-- Every homogeneous piece of a multivariate polynomial ring is a free module over the
coefficient ring. -/
instance homogeneousSubmodule_free (n : ℕ) :
    Module.Free R (homogeneousSubmodule σ R n) :=
  Module.Free.of_basis (basisHomogeneousSubmodule n)

/-- Over finitely many variables, every homogeneous piece is finite over the coefficient ring. -/
instance homogeneousSubmodule_finite [Finite σ] (n : ℕ) :
    Module.Finite R (homogeneousSubmodule σ R n) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg σ R n)

/-- The structure morphism from the polynomial `Proj` to the coefficient ring. -/
def homogeneousProjπ :
    Proj (homogeneousSubmodule σ R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (homogeneousSubmodule σ R) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R (↥(homogeneousSubmodule σ R 0))))

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

/-- A homogenized projective closure as a closed subscheme of polynomial `Proj`. -/
def homogenizedProjι (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProj g d ⟶ Proj (homogeneousSubmodule (Option σ) R) :=
  Proj.map (quotientGradingHom (homogenizedIdeal g d))
    (quotientGradingHom_irrelevant_le (homogenizedIdeal g d))

/-- The projective-closure embedding is a closed immersion. -/
lemma homogenizedProjι_isClosedImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    IsClosedImmersion (homogenizedProjι g d) :=
  isClosedImmersion_proj_map_quotientGradingHom (homogenizedIdeal g d)

/-- The projective-closure embedding commutes with the structure morphisms to the
coefficient ring. -/
lemma homogenizedProjι_comp_homogeneousProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProjι g d ≫ homogeneousProjπ (R := R) (σ := Option σ) =
      homogenizedProjπ g d := by
  unfold homogenizedProjι homogeneousProjπ homogenizedProjπ
  rw [← Category.assoc, ModularCurves.map_comp_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp]
  rfl

lemma irrelevant_toIdeal_le_span_range_X :
    (irrelevant (homogeneousSubmodule σ R)).toIdeal ≤
      Ideal.span (Set.range (X : σ → MvPolynomial σ R)) := by
  rw [toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  rw [← idealOfVars, ← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
  intro m hm
  have hdegree := ((mem_homogeneousSubmodule _ _).mp hp).degree_eq_sum_deg_support hm
  have hn' : 1 ≤ n := hn
  simpa [Finsupp.degree_apply, ← hdegree] using hn'

/-- A standard coordinate open in polynomial projective space. -/
abbrev coordinateOpen (i : σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  Proj.basicOpen (homogeneousSubmodule σ R) (X i)

/-- Every standard coordinate open in polynomial projective space is affine. -/
lemma coordinateOpen_isAffineOpen (i : σ) :
    IsAffineOpen (coordinateOpen (R := R) i) :=
  Proj.isAffineOpen_basicOpen (homogeneousSubmodule σ R) (X i)
    (X_mem_homogeneousSubmodule_one R i) one_pos

/-- The standard coordinate opens cover polynomial projective space. -/
lemma iSup_coordinateOpen_eq_top :
    ⨆ i : σ, coordinateOpen (R := R) i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact irrelevant_toIdeal_le_span_range_X

/-- The standard coordinate open in the `Proj` of a homogeneous polynomial quotient. -/
abbrev quotientCoordinateOpen
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (i : σ) :
    (Proj (quotientGrading I)).Opens :=
  Proj.basicOpen (quotientGrading I) (quotientGradingHom I (X i))

/-- Every standard coordinate open in a homogeneous polynomial quotient is affine. -/
lemma quotientCoordinateOpen_isAffineOpen
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (i : σ) :
    IsAffineOpen (quotientCoordinateOpen I i) :=
  Proj.isAffineOpen_basicOpen (quotientGrading I) (quotientGradingHom I (X i))
    (mk_mem_quotientGrading I (X_mem_homogeneousSubmodule_one R i)) one_pos

/-- The standard coordinate opens cover the `Proj` of a homogeneous polynomial quotient. -/
lemma iSup_quotientCoordinateOpen_eq_top
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    ⨆ i : σ, quotientCoordinateOpen I i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  calc
    (irrelevant (quotientGrading I)).toIdeal ≤
        (HomogeneousIdeal.map (quotientGradingHom I)
          (irrelevant (homogeneousSubmodule σ R))).toIdeal :=
      quotientGradingHom_irrelevant_le I
    _ = Ideal.map (quotientGradingHom I)
        (irrelevant (homogeneousSubmodule σ R)).toIdeal := rfl
    _ ≤ Ideal.map (quotientGradingHom I)
        (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) :=
      Ideal.map_mono irrelevant_toIdeal_le_span_range_X
    _ = Ideal.span (Set.range fun i : σ ↦ quotientGradingHom I (X i)) := by
      rw [Ideal.map_span]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨X i, ⟨i, rfl⟩, rfl⟩

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

private lemma optionChartRingEquiv_symm_C (r : R) :
    (optionChartRingEquiv (R := R) (σ := σ)).symm (C r) =
      awayConst R (none : Option σ) r := by
  simp [optionChartRingEquiv, chartRingEquiv, homogenizeAt, awayConst]
  rfl

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

/-- The coefficient-ring algebra structure on the homogenizing-coordinate chart. -/
noncomputable instance homogenizedChartAwayAlgebra
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    Algebra R
      (Away (quotientGrading (homogenizedIdeal g d))
        ((quotientGradingHom (homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R))) :=
  ((fromZeroRingHom (quotientGrading (homogenizedIdeal g d)) _).comp
    (algebraMapGradeZero (homogenizedIdeal g d))).toAlgebra

/-- The homogenized chart equivalence sends coefficient classes to coefficient sections. -/
lemma homogenizedChartRingEquiv_mk_C
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) (r : R) :
    homogenizedChartRingEquiv g d hdeg
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) (C r)) =
      algebraMap R
        (Away (quotientGrading (homogenizedIdeal g d))
          ((quotientGradingHom (homogenizedIdeal g d))
            (X none : MvPolynomial (Option σ) R))) r := by
  rw [homogenizedChartRingEquiv_mk, optionChartRingEquiv_symm_C, awayConst, Away.map_mk]
  apply val_injective
  rw [Away.val_mk]
  rfl

/-- The affine-chart identification as an equivalence of coefficient-ring algebras. -/
noncomputable def homogenizedChartAlgEquiv
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) ≃ₐ[R]
      Away (quotientGrading (homogenizedIdeal g d))
        ((quotientGradingHom (homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R)) :=
  AlgEquiv.ofRingEquiv (f := homogenizedChartRingEquiv g d hdeg) fun r => by
    have hconst : algebraMap R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) r =
        Ideal.Quotient.mk (Ideal.span (Set.range g)) (C r) := by
      simp [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
        (MvPolynomial σ R ⧸ Ideal.span (Set.range g)), MvPolynomial.algebraMap_eq,
        Ideal.Quotient.algebraMap_eq]
    rw [hconst, homogenizedChartRingEquiv_mk_C]

/-- The original affine presentation as the homogenizing-coordinate chart of its projective
closure. -/
noncomputable def homogenizedChartOpen
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    Spec (.of (MvPolynomial σ R ⧸ Ideal.span (Set.range g))) ⟶
      homogenizedProj g d :=
  Spec.map (homogenizedChartRingEquiv g d hdeg).toCommRingCatIso.inv ≫
    Proj.awayι (quotientGrading (homogenizedIdeal g d))
      ((quotientGradingHom (homogenizedIdeal g d))
        (X none : MvPolynomial (Option σ) R))
      (mk_mem_quotientGrading (homogenizedIdeal g d)
        (X_mem_homogeneousSubmodule_one R (none : Option σ))) one_pos

/-- The affine chart map into the homogenized projective closure is an open immersion. -/
lemma homogenizedChartOpen_isOpenImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    IsOpenImmersion (homogenizedChartOpen g d hdeg) := by
  unfold homogenizedChartOpen
  exact @IsOpenImmersion.comp _ _ _ _ _ (by infer_instance)
    (Proj.instIsOpenImmersionAwayι _ _ _ _)

private lemma homogenizedAwayι_comp_homogenizedProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    Proj.awayι (quotientGrading (homogenizedIdeal g d))
        ((quotientGradingHom (homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R))
        (by
          rw [quotientGradingHom_apply]
          exact mk_mem_quotientGrading (homogenizedIdeal g d)
            (X_mem_homogeneousSubmodule_one R (none : Option σ))) one_pos ≫
      homogenizedProjπ g d =
    Spec.map (CommRingCat.ofHom
      (algebraMap R
        (Away (quotientGrading (homogenizedIdeal g d))
          ((quotientGradingHom (homogenizedIdeal g d))
            (X none : MvPolynomial (Option σ) R))))) := by
  show Proj.awayι _ _ _ _ ≫ Proj.toSpecZero (quotientGrading (homogenizedIdeal g d)) ≫
    Spec.map (CommRingCat.ofHom (algebraMapGradeZero (homogenizedIdeal g d))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The affine chart immersion commutes with the structure morphisms to the coefficient ring. -/
lemma homogenizedChartOpen_comp_homogenizedProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    homogenizedChartOpen g d hdeg ≫ homogenizedProjπ g d =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)))) := by
  unfold homogenizedChartOpen
  rw [Category.assoc, homogenizedAwayι_comp_homogenizedProjπ]
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (homogenizedChartAlgEquiv g d hdeg).symm.toAlgHom.comp_algebraMap

/-- An affine presentation immersed into polynomial `Proj` through its homogenized projective
closure. -/
def homogenizedAffineImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    Spec (.of (MvPolynomial σ R ⧸ Ideal.span (Set.range g))) ⟶
      Proj (homogeneousSubmodule (Option σ) R) :=
  homogenizedChartOpen g d hdeg ≫ homogenizedProjι g d

/-- The affine map into polynomial `Proj` obtained from the homogenized closure is an
immersion. -/
lemma homogenizedAffineImmersion_isImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    IsImmersion (homogenizedAffineImmersion g d hdeg) := by
  letI : IsOpenImmersion (homogenizedChartOpen g d hdeg) :=
    homogenizedChartOpen_isOpenImmersion g d hdeg
  letI : IsClosedImmersion (homogenizedProjι g d) :=
    homogenizedProjι_isClosedImmersion g d
  unfold homogenizedAffineImmersion
  infer_instance

/-- The affine immersion into polynomial `Proj` is a morphism over the coefficient ring. -/
lemma homogenizedAffineImmersion_comp_homogeneousProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    homogenizedAffineImmersion g d hdeg ≫
        homogeneousProjπ (R := R) (σ := Option σ) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)))) := by
  unfold homogenizedAffineImmersion
  rw [Category.assoc, homogenizedProjι_comp_homogeneousProjπ,
    homogenizedChartOpen_comp_homogenizedProjπ]

end OptionChart

end

end MvPolynomial
