/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCech

/-!
# First-anchor Laurent naturality for projective Cech intersections

This file handles the exceptional first Cech face, where deleting the first coordinate changes the
affine chart anchor. It identifies restriction with the induced change of Laurent exponents.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

private theorem coordinateProductPolynomial_first_anchor_factor
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      X (a.1 1).down *
        (coordinateTailPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down) * X (a.1 0).down) := by
  rw [coordinateProductPolynomial_eq_delete_mul (R := R) a 0,
    coordinateProductPolynomial, mul_assoc]
  rfl

private theorem coordinateTailPolynomial_eq_first_mul_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
      X (a.1 1).down * coordinateTailPolynomial (R := R)
        (fun l => ((a.delete 0).1 l).down) := by
  have h := coordinateProductPolynomial_eq_delete_mul (R := R) a 0
  rw [coordinateProductPolynomial, coordinateProductPolynomial] at h
  change X (a.1 0).down *
      coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
    (X (a.1 1).down * coordinateTailPolynomial (R := R)
      (fun l => ((a.delete 0).1 l).down)) * X (a.1 0).down at h
  rw [mul_comm _ (X (a.1 0).down)] at h
  exact X_mul_cancel_left_iff.mp h

private noncomputable def coordinateFirstDirectAwayMap
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    HomogeneousLocalization.Away
        (homogeneousSubmodule σ R) (X (a.1 1).down) →+*
      HomogeneousLocalization.Away
        (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) :=
  HomogeneousLocalization.awayMap
    (homogeneousSubmodule σ R)
    (SetLike.mul_mem_graded
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (X_mem_homogeneousSubmodule_one R (a.1 0).down))
    (coordinateProductPolynomial_first_anchor_factor (R := R) a)

private noncomputable def coordinateTargetTailAwayMap
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    HomogeneousLocalization.Away
        (homogeneousSubmodule σ R) (X (a.1 0).down) →+*
      HomogeneousLocalization.Away
        (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) :=
  HomogeneousLocalization.awayMap
    (homogeneousSubmodule σ R)
    (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down)) rfl

private theorem coordinateFirstDirectAwayMap_awayVar_val
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    (coordinateFirstDirectAwayMap (R := R) a
      (awayVar R (a.1 1).down j)).val =
      Localization.mk
        (X j.1 * (coordinateTailPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down) * X (a.1 0).down) ^ 1)
        (⟨coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) ^ 1,
          1, rfl⟩ : Submonoid.powers
            (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))) := by
  rw [coordinateFirstDirectAwayMap, awayVar,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]

private theorem coordinateTargetTailAwayMap_awayVar_val
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    (coordinateTargetTailAwayMap (R := R) a
      (awayVar R (a.1 0).down j)).val =
      Localization.mk
        (X j.1 * coordinateTailPolynomial (R := R)
          (fun l => (a.1 l).down) ^ 1)
        (⟨coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) ^ 1,
          1, rfl⟩ : Submonoid.powers
            (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))) := by
  change HomogeneousLocalization.val
      (HomogeneousLocalization.awayMap
        (f := X (a.1 0).down)
        (g := coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
        (x := coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))
        (homogeneousSubmodule σ R)
        (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down))
        (show coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
          X (a.1 0).down *
            coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) from rfl)
        (HomogeneousLocalization.Away.mk
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 0).down) 1 (X j.1) _)) = _
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]

private theorem coordinateFirstAwayVar_anchor_mul_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down
          ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩) *
      coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down
          ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  rw [coordinateFirstDirectAwayMap_awayVar_val,
    coordinateTargetTailAwayMap_awayVar_val]
  rw [Localization.mk_mul, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by
    simp only [pow_one, Submonoid.coe_mul, Submonoid.coe_one, one_mul]
    rw [coordinateProductPolynomial,
      coordinateTailPolynomial_eq_first_mul_delete_zero (R := R) a]
    ring⟩

private theorem coordinateFirstAwayVar_mul_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) (hj0 : j.1 ≠ (a.1 0).down) :
    coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down j) *
      coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down
          ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩) =
      coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down ⟨j.1, hj0⟩) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  rw [coordinateFirstDirectAwayMap_awayVar_val,
    coordinateTargetTailAwayMap_awayVar_val,
    coordinateTargetTailAwayMap_awayVar_val]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by
    simp only [pow_one, Submonoid.coe_mul, Submonoid.coe_one, one_mul]
    rw [coordinateProductPolynomial,
      coordinateTailPolynomial_eq_first_mul_delete_zero (R := R) a]
    ring⟩

private theorem coordinateTargetTailAwayMap_awayVar_laurent
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (coordinateTargetTailAwayMap (R := R) a
            (awayVar R (a.1 0).down j))) =
      AddMonoidAlgebra.single
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))
          (Finsupp.single j 1)) 1 := by
  rw [show coordinateTargetTailAwayMap (R := R) a =
      HomogeneousLocalization.awayMap
        (f := X (a.1 0).down)
        (g := coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
        (x := coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))
        (homogeneousSubmodule σ R)
        (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down)) rfl
      from rfl]
  rw [coordinateProductAwayLaurentRingEquiv_awayMap,
    chartRingEquiv_apply_awayVar]
  change AddMonoidAlgebra.mapDomain _
      (AddMonoidAlgebra.single (Finsupp.single j 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

private theorem laurentExponentAwayMap_single_one_degree
    {τ : Type} (m : τ →₀ ℕ) (j : τ) :
    Finsupp.degree
        ((laurentExponentAwayMap m (Finsupp.single j 1) :
          laurentExponentSubmonoid m) : τ →₀ ℤ) = 1 := by
  have h :
      ((laurentExponentAwayMap m (Finsupp.single j 1) :
        laurentExponentSubmonoid m) : τ →₀ ℤ) = Finsupp.single j 1 := by
    ext i
    rw [laurentExponentAwayMap_apply]
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi]
  rw [h, Finsupp.degree_single]

private theorem coordinateFirstAnchorGenerator_global
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateLaurentExponentDeleteEmbedding a 0 1
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete 0).1 l).down) 1
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single
              (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
                {j : σ // j ≠ (a.1 1).down}) 1))) =
      coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1 0 := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (coordinateLaurentExponentEquiv
      (fun l => ((a.delete 0).1 l).down) 1
      (laurentExponentAwayMap
        (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
        (Finsupp.single
          (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
            {j : σ // j ≠ (a.1 1).down}) 1))).1.1 i =
    (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1
      (0 : laurentExponentSubmonoid
        (coordinateTailExponent (fun l => (a.1 l).down)))).1.1 i
  by_cases hi0 : i = (a.1 0).down
  · subst i
    rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _
        (coordinateOpenCechFirstSecond_ne a).symm,
      coordinateLaurentExponentEquiv_apply_anchor,
      laurentExponentAwayMap_apply]
    let j0 : {j : σ // j ≠ (a.1 1).down} :=
      ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
    change ((Finsupp.single j0 1 j0 : ℕ) : ℤ) = 1
    simp
  · by_cases hi1 : i = (a.1 1).down
    · subst i
      change (coordinateLaurentExponentEquiv
          (fun l => ((a.delete 0).1 l).down) 1
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single
              (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
                {j : σ // j ≠ (a.1 1).down}) 1))).1.1
            ((a.delete 0).1 0).down = _
      rw [coordinateLaurentExponentEquiv_apply_anchor,
        coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => (a.1 l).down) (d := 1)
          (e := (0 : laurentExponentSubmonoid
            (coordinateTailExponent (fun l => (a.1 l).down))))
          (i := (a.1 1).down) hi0]
      let j0 : {j : σ // j ≠ (a.1 1).down} :=
        ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
      change 1 - Finsupp.degree
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j0 1)).1 = 0
      have hdeg : Finsupp.degree
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j0 1)).1 = 1 :=
        laurentExponentAwayMap_single_one_degree
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down)) j0
      exact sub_eq_zero.mpr hdeg.symm
    · rw [coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => ((a.delete 0).1 l).down) (d := 1)
          (e := laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single
              (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
                {j : σ // j ≠ (a.1 1).down}) 1))
          (i := i) hi1,
        coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => (a.1 l).down) (d := 1)
          (e := (0 : laurentExponentSubmonoid
            (coordinateTailExponent (fun l => (a.1 l).down))))
          (i := i) hi0,
        laurentExponentAwayMap_apply]
      let j0 : {j : σ // j ≠ (a.1 1).down} :=
        ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
      have hij : (⟨i, hi1⟩ : {j : σ // j ≠ (a.1 1).down}) ≠ j0 := by
        intro h
        exact hi0 (congrArg Subtype.val h)
      change ((Finsupp.single j0 1 ⟨i, hi1⟩ : ℕ) : ℤ) = 0
      simp [hij]

private theorem coordinateFirstGenerator_global
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) (hj0 : j.1 ≠ (a.1 0).down) :
    coordinateLaurentExponentDeleteEmbedding a 0 1
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete 0).1 l).down) 1
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1))) =
      coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))
          (Finsupp.single
            (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1)) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (coordinateLaurentExponentEquiv
      (fun l => ((a.delete 0).1 l).down) 1
      (laurentExponentAwayMap
        (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
        (Finsupp.single j 1))).1.1 i =
    (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1
      (laurentExponentAwayMap
        (coordinateTailExponent (fun l => (a.1 l).down))
        (Finsupp.single
          (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1))).1.1 i
  by_cases hi1 : i = (a.1 1).down
  · subst i
    change (coordinateLaurentExponentEquiv
        (fun l => ((a.delete 0).1 l).down) 1
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1))).1.1 ((a.delete 0).1 0).down = _
    rw [coordinateLaurentExponentEquiv_apply_anchor,
      coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _
        (coordinateOpenCechFirstSecond_ne a)]
    have hdeg : Finsupp.degree
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1)).1 = 1 :=
      laurentExponentAwayMap_single_one_degree
        (coordinateTailExponent (fun l => ((a.delete 0).1 l).down)) j
    rw [hdeg, laurentExponentAwayMap_apply]
    have hne :
        (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
          {j : σ // j ≠ (a.1 0).down}) ≠ ⟨j.1, hj0⟩ := by
      intro h
      exact j.2 (congrArg Subtype.val h).symm
    rw [Finsupp.single_eq_of_ne hne]
    norm_num
  · by_cases hi0 : i = (a.1 0).down
    · subst i
      rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _
          (coordinateOpenCechFirstSecond_ne a).symm,
        coordinateLaurentExponentEquiv_apply_anchor,
        laurentExponentAwayMap_apply]
      have hdeg : Finsupp.degree
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))
            (Finsupp.single
              (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1)).1 = 1 :=
        laurentExponentAwayMap_single_one_degree
          (coordinateTailExponent (fun l => (a.1 l).down)) ⟨j.1, hj0⟩
      rw [hdeg]
      have hne :
          (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
            {j : σ // j ≠ (a.1 1).down}) ≠ j := by
        intro h
        exact hj0 (congrArg Subtype.val h).symm
      let x : {j : σ // j ≠ (a.1 1).down} :=
        ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
      have hx : (Finsupp.single j 1 :
          {j : σ // j ≠ (a.1 1).down} →₀ ℕ) x = 0 :=
        Finsupp.single_eq_of_ne hne
      change (((Finsupp.single j 1 :
        {j : σ // j ≠ (a.1 1).down} →₀ ℕ) x : ℕ) : ℤ) = 0
      exact congrArg (fun z : ℕ => (z : ℤ)) hx
    · rw [coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => ((a.delete 0).1 l).down) (d := 1)
          (e := laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1)) (i := i) hi1,
        coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => (a.1 l).down) (d := 1)
          (e := laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))
            (Finsupp.single
              (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1))
          (i := i) hi0,
        laurentExponentAwayMap_apply, laurentExponentAwayMap_apply]
      by_cases hij : i = j.1
      · subst i
        change ((Finsupp.single j 1 j : ℕ) : ℤ) =
          ((Finsupp.single (⟨j.1, hj0⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1 ⟨j.1, hj0⟩ : ℕ) : ℤ)
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      · have hsource : (⟨i, hi1⟩ : {j : σ // j ≠ (a.1 1).down}) ≠ j := by
          intro h
          exact hij (congrArg Subtype.val h)
        have htarget :
            (⟨i, hi0⟩ : {j : σ // j ≠ (a.1 0).down}) ≠ ⟨j.1, hj0⟩ := by
          intro h
          exact hij (congrArg Subtype.val h)
        let xsource : {j : σ // j ≠ (a.1 1).down} := ⟨i, hi1⟩
        let xtarget : {j : σ // j ≠ (a.1 0).down} := ⟨i, hi0⟩
        have hs : (Finsupp.single j 1 :
            {j : σ // j ≠ (a.1 1).down} →₀ ℕ) xsource = 0 :=
          Finsupp.single_eq_of_ne hsource
        have ht : (Finsupp.single (⟨j.1, hj0⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1 :
            {j : σ // j ≠ (a.1 0).down} →₀ ℕ) xtarget = 0 :=
          Finsupp.single_eq_of_ne htarget
        change (((Finsupp.single j 1 :
            {j : σ // j ≠ (a.1 1).down} →₀ ℕ) xsource : ℕ) : ℤ) =
          (((Finsupp.single (⟨j.1, hj0⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1 :
            {j : σ // j ≠ (a.1 0).down} →₀ ℕ) xtarget : ℕ) : ℤ)
        exact congrArg (fun z : ℕ => (z : ℤ)) (hs.trans ht.symm)

private theorem coordinateFirstAnchorExponent_add_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateLaurentExponentDeleteZeroAddMonoidHom a
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single
            (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
              {j : σ // j ≠ (a.1 1).down}) 1)) +
      coordinateOpenCechFirstTransitionExponent (n := n) a 1 = 0 := by
  apply (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1).injective
  rw [coordinateLaurentExponentEquiv_delete_zero_add_transition]
  exact coordinateFirstAnchorGenerator_global a

private theorem coordinateFirstExponent_add_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) (hj0 : j.1 ≠ (a.1 0).down) :
    coordinateLaurentExponentDeleteZeroAddMonoidHom a
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1)) +
      coordinateOpenCechFirstTransitionExponent (n := n) a 1 =
        laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))
          (Finsupp.single
            (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1) := by
  apply (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1).injective
  rw [coordinateLaurentExponentEquiv_delete_zero_add_transition]
  exact coordinateFirstGenerator_global a j hj0

private theorem coordinateFirstTransitionExponent_one
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    laurentExponentAwayMap
        (coordinateTailExponent (fun l => (a.1 l).down))
        (Finsupp.single
          (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1) =
      coordinateOpenCechFirstTransitionExponent (n := n) a 1 := by
  apply Subtype.ext
  ext i
  rw [laurentExponentAwayMap_apply]
  let j1 : {j : σ // j ≠ (a.1 0).down} :=
    ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩
  change ((Finsupp.single j1 1 i : ℕ) : ℤ) = Finsupp.single j1 1 i
  by_cases hi : i = j1
  · subst i
    simp
  · simp [hi]

private theorem coordinateFirstDirectAwayMap_awayVar_laurent
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (coordinateFirstDirectAwayMap (R := R) a
            (awayVar R (a.1 1).down j))) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1))) 1 := by
  let E : HomogeneousLocalization.Away
        (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) ≃+*
      AddMonoidAlgebra R
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun l => (a.1 l).down))) :=
    (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)).trans
      (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down)))
  let j1 : {j : σ // j ≠ (a.1 0).down} :=
    ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩
  let t := coordinateTargetTailAwayMap (R := R) a
    (awayVar R (a.1 0).down j1)
  change E (coordinateFirstDirectAwayMap (R := R) a
      (awayVar R (a.1 1).down j)) = _
  have ht : E t = AddMonoidAlgebra.single
      (coordinateOpenCechFirstTransitionExponent (n := n) a 1) 1 := by
    change laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (coordinateTargetTailAwayMap (R := R) a
            (awayVar R (a.1 0).down j1))) = _
    rw [coordinateTargetTailAwayMap_awayVar_laurent,
      coordinateFirstTransitionExponent_one]
  have htUnit : IsUnit (E t) := by
    let j0 : {j : σ // j ≠ (a.1 1).down} :=
      ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
    have hrel := congrArg E
      (coordinateFirstAwayVar_anchor_mul_transition (R := R) a)
    change E (coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down j0) * t) = E 1 at hrel
    rw [map_mul, map_one] at hrel
    exact isUnit_iff_exists_inv.mpr
      ⟨E (coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down j0)), (mul_comm _ _).trans hrel⟩
  refine htUnit.mul_right_cancel ?_
  by_cases hj0 : j.1 = (a.1 0).down
  · have hj : j =
        (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
          {j : σ // j ≠ (a.1 1).down}) := Subtype.ext hj0
    subst j
    rw [← map_mul,
      coordinateFirstAwayVar_anchor_mul_transition (R := R) a,
      map_one, ht, AddMonoidAlgebra.single_mul_single,
      coordinateFirstAnchorExponent_add_transition, mul_one]
    rfl
  · let jt : {j : σ // j ≠ (a.1 0).down} := ⟨j.1, hj0⟩
    rw [← map_mul,
      coordinateFirstAwayVar_mul_transition (R := R) a j hj0]
    change E (coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down jt)) = _
    rw [show E (coordinateTargetTailAwayMap (R := R) a
          (awayVar R (a.1 0).down jt)) =
        AddMonoidAlgebra.single
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))
            (Finsupp.single jt 1)) 1 by
          exact coordinateTargetTailAwayMap_awayVar_laurent
            (R := R) a jt]
    rw [ht, AddMonoidAlgebra.single_mul_single,
      coordinateFirstExponent_add_transition a j hj0, mul_one]

private theorem chartRingEquiv_symm_X
    (i : σ) (j : {j : σ // j ≠ i}) :
    (chartRingEquiv R i).symm (X j) = awayVar R i j := by
  apply (chartRingEquiv R i).injective
  rw [RingEquiv.apply_symm_apply, chartRingEquiv_apply_awayVar]

private theorem chartRingEquiv_symm_C (i : σ) (r : R) :
    (chartRingEquiv R i).symm (C r) =
      algebraMap R
        (HomogeneousLocalization.Away
          (homogeneousSubmodule σ R) (X i : MvPolynomial σ R)) r := by
  apply (chartRingEquiv R i).injective
  rw [RingEquiv.apply_symm_apply, chartRingEquiv_algebraMap]

private theorem coordinateFirstDirectAwayMap_algebraMap
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstDirectAwayMap (R := R) a
        (algebraMap R
          (HomogeneousLocalization.Away
            (homogeneousSubmodule σ R) (X (a.1 1).down)) r) =
      algebraMap R
        (HomogeneousLocalization.Away
          (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))) r := by
  change HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (SetLike.mul_mem_graded
        (coordinateTailPolynomial_mem (R := R)
          (fun l => ((a.delete 0).1 l).down))
        (X_mem_homogeneousSubmodule_one R (a.1 0).down))
      (coordinateProductPolynomial_first_anchor_factor (R := R) a)
      (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ R)
        (Submonoid.powers (X (a.1 1).down))
        (algebraMap R (homogeneousSubmodule σ R 0) r)) =
    HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ R)
      (Submonoid.powers
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)))
      (algebraMap R (homogeneousSubmodule σ R 0) r)
  exact HomogeneousLocalization.awayMap_fromZeroRingHom
    (homogeneousSubmodule σ R)
    (SetLike.mul_mem_graded
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (X_mem_homogeneousSubmodule_one R (a.1 0).down))
    (coordinateProductPolynomial_first_anchor_factor (R := R) a)
    (algebraMap R (homogeneousSubmodule σ R 0) r)

private noncomputable def coordinateFirstDirectLaurentRingHom
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :=
  (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))).toRingHom.comp
        ((coordinateProductAwayRingEquiv (R := R)
          (fun l => (a.1 l).down)).toRingHom.comp
          (coordinateFirstDirectAwayMap (R := R) a))

private noncomputable def coordinateFirstTargetLaurentRingHom
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :=
  (AddMonoidAlgebra.mapDomainRingHom R
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a)).comp
        ((AddMonoidAlgebra.mapDomainRingHom R
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom).comp
          (chartRingEquiv R (a.1 1).down).toRingHom)

private theorem coordinateFirstDirectAwayMap_laurent_C_left
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) =
      AddMonoidAlgebra.single 0 r := by
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        (coordinateFirstDirectAwayMap (R := R) a
          ((chartRingEquiv R (a.1 1).down).symm (C r)))) = _
  rw [chartRingEquiv_symm_C,
    coordinateFirstDirectAwayMap_algebraMap,
    coordinateProductAwayRingEquiv_algebraMap,
    laurentMonomialRingEquiv_algebraMap_coeff]
  change AddMonoidAlgebra.single 0 r = AddMonoidAlgebra.single 0 r
  rfl

private theorem coordinateFirstDirectAwayMap_laurent_C_right
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) =
      AddMonoidAlgebra.single 0 r := by
  change
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (chartRingEquiv R (a.1 1).down
          ((chartRingEquiv R (a.1 1).down).symm (C r)))) = _
  rw [RingEquiv.apply_symm_apply]
  change AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (AddMonoidAlgebra.single 0 r)) = _
  rw [AddMonoidAlgebra.mapDomain_single,
    AddMonoidAlgebra.mapDomain_single, map_zero, map_zero]

private theorem coordinateFirstDirectAwayMap_laurent_C
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) =
      coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) :=
  (coordinateFirstDirectAwayMap_laurent_C_left (R := R) a r).trans
    (coordinateFirstDirectAwayMap_laurent_C_right (R := R) a r).symm

private theorem coordinateFirstDirectAwayMap_laurent_X_left
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) =
      AddMonoidAlgebra.single
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1))) 1 := by
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        (coordinateFirstDirectAwayMap (R := R) a
          ((chartRingEquiv R (a.1 1).down).symm (X j)))) = _
  rw [chartRingEquiv_symm_X,
    coordinateFirstDirectAwayMap_awayVar_laurent]

private theorem coordinateFirstDirectAwayMap_laurent_X_right
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1))) 1 := by
  change
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (chartRingEquiv R (a.1 1).down
          ((chartRingEquiv R (a.1 1).down).symm (X j)))) = _
  rw [RingEquiv.apply_symm_apply]
  change AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (AddMonoidAlgebra.single (Finsupp.single j 1) 1)) = _
  rw [AddMonoidAlgebra.mapDomain_single,
    AddMonoidAlgebra.mapDomain_single]
  rfl

private theorem coordinateFirstDirectAwayMap_laurent_X
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) =
      coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) :=
  (coordinateFirstDirectAwayMap_laurent_X_left (R := R) a j).trans
    (coordinateFirstDirectAwayMap_laurent_X_right (R := R) a j).symm

private theorem coordinateFirstDirectAwayMap_laurent_chart
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (coordinateFirstDirectLaurentRingHom (R := R) a).comp
        (chartRingEquiv R (a.1 1).down).symm.toRingHom =
      (coordinateFirstTargetLaurentRingHom (R := R) a).comp
        (chartRingEquiv R (a.1 1).down).symm.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    exact coordinateFirstDirectAwayMap_laurent_C (R := R) a r
  · intro j
    exact coordinateFirstDirectAwayMap_laurent_X (R := R) a j

private theorem coordinateFirstDirectAwayMap_laurent_apply
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (q : HomogeneousLocalization.Away
      (homogeneousSubmodule σ R) (X (a.1 1).down)) :
    coordinateFirstDirectLaurentRingHom (R := R) a q =
      coordinateFirstTargetLaurentRingHom (R := R) a q := by
  have hq := RingHom.congr_fun
    (coordinateFirstDirectAwayMap_laurent_chart (R := R) a)
    (chartRingEquiv R (a.1 1).down q)
  change coordinateFirstDirectLaurentRingHom (R := R) a
      ((chartRingEquiv R (a.1 1).down).symm
        (chartRingEquiv R (a.1 1).down q)) =
    coordinateFirstTargetLaurentRingHom (R := R) a
      ((chartRingEquiv R (a.1 1).down).symm
        (chartRingEquiv R (a.1 1).down q)) at hq
  rw [RingEquiv.symm_apply_apply] at hq
  exact hq

private theorem coordinateProductAwayMap_comp_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateProductPolynomial_eq_delete_mul (R := R) a 0)).comp
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (coordinateTailPolynomial_mem (R := R)
            (fun l => ((a.delete 0).1 l).down)) rfl) =
      coordinateFirstDirectAwayMap (R := R) a := by
  exact HomogeneousLocalization.awayMap_comp
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R (a.1 1).down)
    (coordinateTailPolynomial_mem (R := R)
      (fun l => ((a.delete 0).1 l).down))
    (X_mem_homogeneousSubmodule_one R (a.1 0).down)
    rfl
    (coordinateProductPolynomial_eq_delete_mul (R := R) a 0)
    (coordinateProductPolynomial_first_anchor_factor (R := R) a)

/-- Laurent coordinates identify first-entry restriction with the exponent map that changes from
the second-coordinate chart to the first-coordinate chart. -/
theorem coordinateProductAwayLaurentRingEquiv_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))).toRingHom.comp
        ((coordinateProductAwayRingEquiv (R := R)
          (fun l => (a.1 l).down)).toRingHom.comp
          (HomogeneousLocalization.awayMap
            (homogeneousSubmodule σ R)
            (X_mem_homogeneousSubmodule_one R (a.1 0).down)
            (coordinateProductPolynomial_eq_delete_mul (R := R) a 0))) =
      (AddMonoidAlgebra.mapDomainRingHom R
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a)).comp
        ((laurentMonomialRingEquiv R
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toRingHom.comp
          (coordinateProductAwayRingEquiv (R := R)
            (fun l => ((a.delete 0).1 l).down)).toRingHom) := by
  letI := (HomogeneousLocalization.awayMap
    (f := X (a.1 1).down)
    (g := coordinateTailPolynomial (R := R)
      (fun l => ((a.delete 0).1 l).down))
    (x := coordinateProductPolynomial (R := R)
      (fun l => ((a.delete 0).1 l).down))
    (homogeneousSubmodule σ R)
    (coordinateTailPolynomial_mem (R := R)
      (fun l => ((a.delete 0).1 l).down)) rfl).toAlgebra
  let t : HomogeneousLocalization.Away (homogeneousSubmodule σ R)
      (X (a.1 1).down) :=
    HomogeneousLocalization.Away.isLocalizationElem
      (X_mem_homogeneousSubmodule_one R (a.1 1).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down))
  letI : IsLocalization.Away t
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down))) :=
    HomogeneousLocalization.Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R (a.1 1).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down)) rfl one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply DFunLike.ext _ _
  intro q
  simp only [RingHom.comp_apply]
  rw [show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X (a.1 1).down))
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down))) q =
    HomogeneousLocalization.awayMap
      (f := X (a.1 1).down)
      (g := coordinateTailPolynomial (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (x := coordinateProductPolynomial (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (homogeneousSubmodule σ R)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down)) rfl q from rfl]
  calc
    _ = coordinateFirstDirectLaurentRingHom (R := R) a q := by
      exact congrArg
        (fun y => laurentMonomialRingEquiv R
          (coordinateTailExponent (fun l => (a.1 l).down))
          (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down) y))
        (DFunLike.congr_fun
          (coordinateProductAwayMap_comp_delete_zero (R := R) a) q)
    _ = coordinateFirstTargetLaurentRingHom (R := R) a q :=
      coordinateFirstDirectAwayMap_laurent_apply (R := R) a q
    _ = _ := congrArg
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a))
      (coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (n := n)
        (fun l => ((a.delete 0).1 l).down) q).symm

/-- On sections of standard Cech intersections, deleting the first entry becomes the corresponding
first-anchor Laurent exponent map. -/
theorem coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (x : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenCechIntersection (R := R) (a.delete 0).1)) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a 0).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
        (coordinateOpenCechIntersectionLaurentRingEquiv
          (R := R) (a.delete 0).1 x) := by
  let q := (coordinateOpenCechIntersectionAwayIso
    (R := R) (a.delete 0).1).inv.hom x
  have hNat := coordinateOpenCechIntersectionAwayIso_naturality_delete
    (R := R) a 0
  have hNatq := ConcreteCategory.congr_hom hNat q
  change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
      (HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (X_mem_homogeneousSubmodule_one R (a.1 0).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a 0) q) =
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (coordinateOpenCechDelete (R := R) a 0).op).hom
      ((coordinateOpenCechIntersectionAwayIso
        (R := R) (a.delete 0).1).hom.hom q) at hNatq
  have hq : (coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a 0).op).hom x) =
    HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateProductPolynomial_eq_delete_mul (R := R) a 0) q := by
    apply (coordinateOpenCechIntersectionAwayIso
      (R := R) a.1).commRingCatIsoToRingEquiv.injective
    change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a 0).op).hom x)) =
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 0).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a 0) q)
    rw [Iso.inv_hom_id_apply]
    rw [show (coordinateOpenCechIntersectionAwayIso
      (R := R) (a.delete 0).1).hom.hom q = x by
        simpa only [q] using
          (Iso.inv_hom_id_apply
            (coordinateOpenCechIntersectionAwayIso
              (R := R) (a.delete 0).1) x)] at hNatq
    exact hNatq.symm
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a 0).op).hom x))) = _
  rw [hq]
  exact DFunLike.congr_fun
    (coordinateProductAwayLaurentRingEquiv_naturality_delete_zero
      (R := R) a) q


end

end MvPolynomial
