/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreImageChartGeneration`.
-/
import ModularCurves.ForMathlib.SegreStandardChartInverse

/-!
# Generators of a standard Segre-image chart

The degree-zero localization of the Segre coordinate algebra is generated
by the standard coordinate ratios. This detects equality of algebra maps
out of a Segre-image chart.
-/

open DirectSum
open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The rank-one quadratic relation among four Segre coordinates. -/
lemma segreImageCoordinate_cross_relation
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageCoordinate R m n (segrePairIndex m n a j) *
        segreImageCoordinate R m n (segrePairIndex m n i b) =
      segreImageCoordinate R m n (segrePairIndex m n a b) *
        segreImageCoordinate R m n (segrePairIndex m n i j) := by
  apply Subtype.ext
  simp [segreImageCoordinate, segrePairIndex,
    Algebra.TensorProduct.tmul_mul_tmul]
  ac_rfl

/-- The product of the two anchor ratios is the corresponding Segre coordinate ratio. -/
lemma segreImageChartRatio_mul_anchorRatios
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageChartRatio R m n i a j j *
        segreImageChartRatio R m n i i j b =
      segreImageChartRatio R m n i a j b := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul,
    segreImageChartRatio, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul,
    one_mul]
  rw [segreImageCoordinate_cross_relation]
  ring

/-- The degree-zero piece of the Segre image consists only of coefficients. -/
lemma segreImageGrading_zero_eq_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (x : segreImageGrading R m n 0) :
    ∃ r : R,
      (x : SegreCoordinateRing R m n) =
        algebraMap R (SegreCoordinateRing R m n) r := by
  obtain ⟨p, hp⟩ :=
    segreRangeCoordinateHom_surjective R m n
      (x : SegreCoordinateRing R m n)
  let p₀ :=
    DirectSum.decompose
      (homogeneousSubmodule (Fin (segreDimension m n + 1)) R) p 0
  have hp₀ :
      segreRangeCoordinateHom R m n p₀ =
        (x : SegreCoordinateRing R m n) := by
    calc
      segreRangeCoordinateHom R m n p₀ =
          DirectSum.decompose
            (segreImageGrading R m n)
            (segreRangeCoordinateHom R m n p) 0 :=
        map_directSumDecompose
          (homogeneousSubmodule (Fin (segreDimension m n + 1)) R)
          (segreImageGrading R m n)
          (segreImageGradedHom R m n)
      _ =
          DirectSum.decompose
            (segreImageGrading R m n)
            (x : SegreCoordinateRing R m n) 0 := by
        rw [hp]
      _ = (x : SegreCoordinateRing R m n) :=
        DirectSum.decompose_of_mem_same
          (segreImageGrading R m n) x.2
  obtain ⟨r, hr⟩ :=
    Submodule.mem_one.mp
      ((MvPolynomial.homogeneousSubmodule_zero
        (σ := Fin (segreDimension m n + 1))
        (R := R)).le
        (DirectSum.decompose
          (homogeneousSubmodule (Fin (segreDimension m n + 1)) R)
          p 0).2)
  refine ⟨r, ?_⟩
  rw [← hp₀]
  have hp₀C :
      (p₀ : MvPolynomial (Fin (segreDimension m n + 1)) R) =
        MvPolynomial.C r := by
    simpa [p₀] using hr.symm
  rw [hp₀C]
  simp

/-- The Segre coordinates generate their image algebra over its degree-zero piece. -/
lemma segreImageCoordinate_adjoin_eq_top
    (R : Type u) [CommRing R] (m n : ℕ) :
    Algebra.adjoin
        (segreImageGrading R m n 0)
        (Set.range (segreImageCoordinate R m n)) =
      (⊤ : Subalgebra
        (segreImageGrading R m n 0)
        (SegreCoordinateRing R m n)) := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨p, rfl⟩ :=
    segreRangeCoordinateHom_surjective R m n x
  induction p using MvPolynomial.induction_on with
  | C r =>
      let r₀ : segreImageGrading R m n 0 :=
        ⟨algebraMap R (SegreCoordinateRing R m n) r,
          SetLike.algebraMap_mem_graded (segreImageGrading R m n) r⟩
      simpa [r₀] using
        algebraMap_mem
          (Algebra.adjoin
            (segreImageGrading R m n 0)
            (Set.range (segreImageCoordinate R m n))) r₀
  | add p q hp hq =>
      simpa only [map_add] using add_mem hp hq
  | mul_X p s hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin ⟨s, rfl⟩)

/-- The ratio of an arbitrary Segre coordinate by the fixed chart coordinate. -/
@[reducible]
def segreImageCoordinateRatio
    (R : Type u) [CommRing R] (m n : ℕ)
    (anchor s : Fin (segreDimension m n + 1)) :
    Away
      (segreImageGrading R m n)
      (segreImageCoordinate R m n anchor) :=
  Away.mk
    (segreImageGrading R m n)
    (segreImageCoordinate_mem_degreeOne R m n anchor)
    1
    (segreImageCoordinate R m n s)
    (by simpa using segreImageCoordinate_mem_degreeOne R m n s)

@[simp]
lemma segreImageCoordinateRatio_segrePairIndex
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageCoordinateRatio R m n
        (segrePairIndex m n i j)
        (segrePairIndex m n a b) =
      segreImageChartRatio R m n i a j b :=
  rfl

lemma segreImageCoordinate_prod_pow_mem
    (R : Type u) [CommRing R] (m n : ℕ)
    (e : Fin (segreDimension m n + 1) → ℕ) :
    (∏ s, segreImageCoordinate R m n s ^ e s) ∈
      segreImageGrading R m n ((∑ s, e s) • 1) := by
  simpa using
    SetLike.prod_pow_mem_graded
      (segreImageGrading R m n)
      (fun _ => 1)
      (segreImageCoordinate R m n)
      e
      (fun s _ => segreImageCoordinate_mem_degreeOne R m n s)

lemma segreImageCoordinateRatio_prod_pow
    (R : Type u) [CommRing R] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1))
    (q : ℕ)
    (e : Fin (segreDimension m n + 1) → ℕ)
    (he : ∑ s, e s = q) :
    ∏ s, segreImageCoordinateRatio R m n anchor s ^ e s =
      Away.mk
        (segreImageGrading R m n)
        (segreImageCoordinate_mem_degreeOne R m n anchor)
        q
        (∏ s, segreImageCoordinate R m n s ^ e s)
        (by simpa [he] using segreImageCoordinate_prod_pow_mem R m n e) := by
  apply HomogeneousLocalization.val_injective
  change
    algebraMap
        (Away
          (segreImageGrading R m n)
          (segreImageCoordinate R m n anchor))
        (Localization.Away (segreImageCoordinate R m n anchor))
        (∏ s, segreImageCoordinateRatio R m n anchor s ^ e s) =
      _
  simp only [map_prod, map_pow,
    HomogeneousLocalization.algebraMap_apply,
    segreImageCoordinateRatio,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_prod, Localization.mk_pow]
  congr 1
  apply Subtype.ext
  simp only [SubmonoidClass.coe_finsetProd,
    SubmonoidClass.coe_pow, pow_one]
  calc
    ∏ x, segreImageCoordinate R m n anchor ^ e x =
        segreImageCoordinate R m n anchor ^ ∑ x, e x := by
      simpa using
        Finset.prod_pow_eq_pow_sum Finset.univ e
          (segreImageCoordinate R m n anchor)
    _ = segreImageCoordinate R m n anchor ^ q := by
      rw [he]

/-- The bounded monomial fractions used by the homogeneous-localization generator theorem. -/
def segreImageChartMonomialGenerators
    (R : Type u) [CommRing R] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1)) :
    Set
      (Away
        (segreImageGrading R m n)
        (segreImageCoordinate R m n anchor)) :=
  { Away.mk
      (segreImageGrading R m n)
      (segreImageCoordinate_mem_degreeOne R m n anchor)
      a
      (∏ s, segreImageCoordinate R m n s ^ e s)
      (he ▸
        SetLike.prod_pow_mem_graded
          (segreImageGrading R m n)
          (fun _ => 1)
          (segreImageCoordinate R m n)
          e
          (fun s _ => segreImageCoordinate_mem_degreeOne R m n s)) |
    (a : ℕ)
    (e : Fin (segreDimension m n + 1) → ℕ)
    (he : ∑ s, e s • 1 = a • 1)
    (_ : ∀ s, e s ≤ 1) }

/-- The bounded monomial fractions generate over the degree-zero component. -/
lemma segreImageChartMonomialGenerators_adjoin_eq_top
    (R : Type u) [CommRing R] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1)) :
    Algebra.adjoin
        (segreImageGrading R m n 0)
        (segreImageChartMonomialGenerators R m n anchor) =
      (⊤ : Subalgebra
        (segreImageGrading R m n 0)
        (Away
          (segreImageGrading R m n)
          (segreImageCoordinate R m n anchor))) := by
  simpa only [segreImageChartMonomialGenerators] using
    HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (segreImageCoordinate_mem_degreeOne R m n anchor)
      (Fin (segreDimension m n + 1))
      (segreImageCoordinate R m n)
      (segreImageCoordinate_adjoin_eq_top R m n)
      (fun _ => 1)
      (fun s => segreImageCoordinate_mem_degreeOne R m n s)

/-- The standard coordinate ratios generate the Segre-image chart over the base ring. -/
lemma segreImageCoordinateRatio_adjoin_eq_top
    (R : Type u) [CommRing R] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1)) :
    Algebra.adjoin R
        (Set.range (segreImageCoordinateRatio R m n anchor)) =
      (⊤ : Subalgebra R
        (Away
          (segreImageGrading R m n)
          (segreImageCoordinate R m n anchor))) := by
  apply top_unique
  intro x hx_top
  clear hx_top
  have hx :
      x ∈ Algebra.adjoin
        (segreImageGrading R m n 0)
        (segreImageChartMonomialGenerators R m n anchor) := by
    rw [segreImageChartMonomialGenerators_adjoin_eq_top]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
      change z ∈
        { Away.mk
            (segreImageGrading R m n)
            (segreImageCoordinate_mem_degreeOne R m n anchor)
            a
            (∏ s, segreImageCoordinate R m n s ^ e s)
            (he ▸
              SetLike.prod_pow_mem_graded
                (segreImageGrading R m n)
                (fun _ => 1)
                (segreImageCoordinate R m n)
                e
                (fun s _ =>
                  segreImageCoordinate_mem_degreeOne R m n s)) |
          (a : ℕ)
          (e : Fin (segreDimension m n + 1) → ℕ)
          (he : ∑ s, e s • 1 = a • 1)
          (_ : ∀ s, e s ≤ 1) } at hz
      obtain ⟨a, e, he, _, rfl⟩ := hz
      have he' : ∑ s, e s = a := by
        simpa using he
      rw [← segreImageCoordinateRatio_prod_pow R m n anchor a e he']
      apply prod_mem
      intro s _
      exact pow_mem
        (Algebra.subset_adjoin (R := R)
          (show
            segreImageCoordinateRatio R m n anchor s ∈
              Set.range (segreImageCoordinateRatio R m n anchor) from
            ⟨s, rfl⟩))
        (e s)
  | algebraMap r₀ =>
      obtain ⟨r, hr⟩ :=
        segreImageGrading_zero_eq_algebraMap R m n r₀
      have hcoeff :
          algebraMap
              (segreImageGrading R m n 0)
              (Away
                (segreImageGrading R m n)
                (segreImageCoordinate R m n anchor))
              r₀ =
            algebraMap R
              (Away
                (segreImageGrading R m n)
                (segreImageCoordinate R m n anchor))
              r := by
        rw [segreImageAway_algebraMap_eq_mk R m n
          (segreImageCoordinate R m n anchor)
          (segreImageCoordinate_mem_degreeOne R m n anchor) r]
        apply HomogeneousLocalization.val_injective
        change
          Localization.mk
              (r₀ : SegreCoordinateRing R m n)
              (1 : Submonoid.powers (segreImageCoordinate R m n anchor)) =
            Localization.mk
              (algebraMap R (SegreCoordinateRing R m n) r)
              (1 : Submonoid.powers (segreImageCoordinate R m n anchor))
        congr 1
      rw [hcoeff]
      exact algebraMap_mem _ r
  | add x y hx hy hx' hy' =>
      exact add_mem hx' hy'
  | mul x y hx hy hx' hy' =>
      exact mul_mem hx' hy'

end MvPolynomial
