/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist
import ModularCurves.ForMathlib.ProjectiveLaurentWeight
import ModularCurves.ForMathlib.ProjToSpecZero
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech

/-!
# Cech factors for twists on polynomial projective space

This file begins the ordered standard-cover calculation of the cohomology of
projective-space twists. It identifies the sections of `O(d)` on each ordered
intersection with the sections of the structure sheaf there.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard coordinate cover, lifted to the universe of the projective scheme. -/
abbrev coordinateOpenCover (i : ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  coordinateOpen (R := R) i.down

/-- Every member of the universe-lifted standard coordinate cover is affine. -/
theorem coordinateOpenCover_isAffineOpen (i : ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCover (R := R) i) :=
  coordinateOpen_isAffineOpen i.down

/-- The universe-lifted standard coordinate opens cover projective space. -/
theorem iSup_coordinateOpenCover_eq_top :
    ⨆ i : ULift.{u} σ, coordinateOpenCover (R := R) i = ⊤ := by
  apply top_unique
  rw [← iSup_coordinateOpen_eq_top (R := R)]
  exact iSup_le fun i => le_iSup (coordinateOpenCover (R := R)) (ULift.up i)

/-- The intersection of the standard coordinate charts indexed by a Cech tuple. -/
abbrev coordinateOpenCechIntersection {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  ∏ᶜ fun k : Fin (n + 1) => coordinateOpenCover (R := R) (a k)

/-- A standard Cech intersection is contained in each chart occurring in its tuple. -/
theorem coordinateOpenCechIntersection_le {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (k : Fin (n + 1)) :
    coordinateOpenCechIntersection (R := R) a ≤ coordinateOpenCover (R := R) (a k) :=
  leOfHom (Pi.π (fun l : Fin (n + 1) => coordinateOpenCover (R := R) (a l)) k)

/-- Every finite intersection in the standard coordinate cover is affine. -/
theorem coordinateOpenCechIntersection_isAffineOpen {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCechIntersection (R := R) a) := by
  rw [show coordinateOpenCechIntersection (R := R) a =
      ⨅ k : Fin (n + 1), coordinateOpenCover (R := R) (a k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  exact IsAffineOpen.iInf fun k => coordinateOpenCover_isAffineOpen (R := R) (a k)

private theorem coordinateProductPolynomial_eq_prod {n : ℕ}
    (a : Fin (n + 1) → σ) :
    coordinateProductPolynomial (R := R) a = ∏ k, X (a k) := by
  classical
  rw [coordinateProductPolynomial, coordinateTailPolynomial, Fin.prod_univ_succ]

/-- The coordinate product of a full Cech tuple is the deleted tuple product times the removed
coordinate. -/
theorem coordinateProductPolynomial_eq_delete_mul [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      coordinateProductPolynomial (R := R) (fun l => ((a.delete k).1 l).down) *
        X (a.1 k).down := by
  classical
  rw [coordinateProductPolynomial_eq_prod, coordinateProductPolynomial_eq_prod,
    Fin.prod_univ_succAbove, mul_comm]
  rfl

/-- Deleting a noninitial Cech coordinate removes exactly that factor from the affine-chart tail
product. -/
theorem coordinateTailPolynomial_eq_delete_succ_mul [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
      coordinateTailPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) *
        X (a.1 k.succ).down := by
  have h := coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ
  rw [coordinateProductPolynomial, coordinateProductPolynomial] at h
  change X (a.1 0).down *
      coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
    (X (a.1 0).down *
      coordinateTailPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) *
      X (a.1 k.succ).down at h
  rw [mul_assoc] at h
  exact X_mul_cancel_left_iff.mp h

/-- For a noninitial deletion, localization first at the deleted tail and then at the removed
coordinate is localization directly at the full tail. -/
theorem coordinateTailAwayMap_comp_delete_succ [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (q : HomogeneousLocalization.Away
      (homogeneousSubmodule σ R) (X (a.1 0).down)) :
    HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ)
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (coordinateTailPolynomial_mem (R := R)
            (fun l => ((a.delete k.succ).1 l).down))
          (rfl : coordinateProductPolynomial (R := R)
              (fun l => ((a.delete k.succ).1 l).down) =
            X (a.1 0).down *
              coordinateTailPolynomial (R := R)
                (fun l => ((a.delete k.succ).1 l).down))
          q) =
      HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down))
        (rfl : coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
          X (a.1 0).down *
            coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
        q := by
  have hy' : coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      X (a.1 0).down *
        (coordinateTailPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) * X (a.1 k.succ).down) := by
    rw [coordinateProductPolynomial, coordinateTailPolynomial_eq_delete_succ_mul]
  have h := congrArg
    (fun f : HomogeneousLocalization.Away
        (homogeneousSubmodule σ R) (X (a.1 0).down) →+*
        HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) => f q)
    (HomogeneousLocalization.awayMap_comp
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
      (rfl : coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) =
        X (a.1 0).down *
          coordinateTailPolynomial (R := R)
            (fun l => ((a.delete k.succ).1 l).down))
      (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ)
      hy')
  rw [RingHom.comp_apply] at h
  exact h

private theorem basicOpen_prod {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ R) :
    Proj.basicOpen (homogeneousSubmodule σ R) (∏ i, f i) =
      ⨅ i, Proj.basicOpen (homogeneousSubmodule σ R) (f i) := by
  classical
  ext x
  rw [TopologicalSpace.Opens.coe_iInf]
  simp only [Set.mem_iInter]
  let y : ProjectiveSpectrum (homogeneousSubmodule σ R) := x
  change (∏ i, f i) ∉ y.asHomogeneousIdeal.toIdeal ↔
    ∀ i, f i ∉ y.asHomogeneousIdeal.toIdeal
  have hprod : (∏ i, f i) ∈ y.asHomogeneousIdeal.toIdeal ↔
      ∃ i, f i ∈ y.asHomogeneousIdeal.toIdeal := by
    simpa using (Ideal.IsPrime.prod_mem_iff
      (s := Finset.univ) (x := f) (p := y.asHomogeneousIdeal.toIdeal))
  rw [not_congr hprod]
  simp

/-- A standard Cech intersection is the single basic open at its tuple coordinate product. -/
theorem coordinateOpenCechIntersection_eq_basicOpen {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    coordinateOpenCechIntersection (R := R) a =
      Proj.basicOpen (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun k => (a k).down)) := by
  rw [show coordinateOpenCechIntersection (R := R) a =
      ⨅ k : Fin (n + 1), coordinateOpenCover (R := R) (a k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  rw [coordinateProductPolynomial_eq_prod]
  exact (basicOpen_prod (R := R) (fun k : Fin (n + 1) => X (a k).down)).symm

/-- The canonical homogeneous localization presentation of a standard Cech intersection's
structure-sheaf sections. -/
noncomputable def coordinateOpenCechIntersectionAwayIso {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    CommRingCat.of
        (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun k => (a k).down))) ≅
      Γ(Proj (homogeneousSubmodule σ R), coordinateOpenCechIntersection (R := R) a) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule σ R)
      (coordinateProductPolynomial (R := R) (fun k => (a k).down))
      (coordinateProductPolynomial_mem (R := R) (fun k => (a k).down))
      (Nat.succ_pos n)).trans
    ((Proj (homogeneousSubmodule σ R)).presheaf.mapIso
      (eqToIso (coordinateOpenCechIntersection_eq_basicOpen (R := R) a)).op)

/-- Sections on a standard projective Cech intersection, in Laurent-monomial coordinates. -/
noncomputable def coordinateOpenCechIntersectionLaurentRingEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) ≃+*
      AddMonoidAlgebra R
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun k => (a k).down))) :=
  (coordinateOpenCechIntersectionAwayIso (R := R) a).commRingCatIsoToRingEquiv.symm |>.trans
    ((coordinateProductAwayRingEquiv (R := R) (fun k => (a k).down)).trans
      (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun k => (a k).down))))

/-- Laurent-monomial coordinates with coefficients transported to the global sections of the
affine base. -/
noncomputable def coordinateOpenCechIntersectionBaseLaurentRingEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) ≃+*
      AddMonoidAlgebra Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun k => (a k).down))) :=
  (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a).trans
    (AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm)

/-- The structure morphism on a projective Cech intersection is the coefficient map into its
homogeneous localization presentation. -/
theorem coordinateOpenCechIntersection_structure_section_square {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (homogeneousProjπ (R := R) (σ := σ)).appTop ≫
        (Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op ≫
        (coordinateOpenCechIntersectionAwayIso (R := R) a).inv =
      CommRingCat.ofHom
        (homogeneousAwayCoeffHom
          (coordinateProductPolynomial (R := R) (fun k => (a k).down))) := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_inv,
    Functor.mapIso_inv]
  rw [← Category.assoc
    ((Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op)]
  rw [← Functor.map_comp]
  rw [show (homOfLE le_top).op ≫
      (eqToIso (coordinateOpenCechIntersection_eq_basicOpen (R := R) a)).op.inv =
        (homOfLE le_top).op from Subsingleton.elim _ _]
  simpa [homogeneousProjπ, homogeneousAwayCoeffHom] using
    (ModularCurves.Proj_structure_section_square
      (homogeneousSubmodule σ R)
      (algebraMap R (homogeneousSubmodule σ R 0))
      (coordinateProductPolynomial (R := R) (fun k => (a k).down))
      (coordinateProductPolynomial_mem (R := R) (fun k => (a k).down))
      (Nat.succ_pos n))

/-- The base scalar map into a projective Cech intersection in homogeneous-localization
coordinates. -/
theorem coordinateOpenCechIntersection_baseScalarHom {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (homogeneousProjπ (R := R) (σ := σ)).appTop ≫
        (Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op ≫
        (coordinateOpenCechIntersectionAwayIso (R := R) a).inv =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom
          (homogeneousAwayCoeffHom
            (coordinateProductPolynomial (R := R) (fun k => (a k).down))) := by
  rw [← Iso.inv_comp_eq]
  exact coordinateOpenCechIntersection_structure_section_square (R := R) a

/-- A base scalar is the constant Laurent monomial in coefficient-ring coordinates. -/
@[simp]
theorem coordinateOpenCechIntersectionLaurentRingEquiv_baseScalar {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
        (((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE le_top).op).hom
            ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
      AddMonoidAlgebra.single 0
        ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  change laurentMonomialRingEquiv R _
      (coordinateProductAwayRingEquiv (R := R) _
        ((coordinateOpenCechIntersectionAwayIso (R := R) a).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE le_top).op).hom
              ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)))) = _
  have hscalar := congrArg
    (fun q : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) →+*
        HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun k => (a k).down)) => q r)
    (congrArg CommRingCat.Hom.hom
      (coordinateOpenCechIntersection_baseScalarHom (R := R) a))
  change (coordinateOpenCechIntersectionAwayIso (R := R) a).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE le_top).op).hom
          ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
    algebraMap R
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun k => (a k).down)))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) at hscalar
  rw [hscalar, coordinateProductAwayRingEquiv_algebraMap,
    laurentMonomialRingEquiv_algebraMap_coeff]
  rfl

/-- A base scalar is the constant Laurent monomial after transporting coefficients to the affine
base's global-section ring. -/
@[simp]
theorem coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
        (((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE le_top).op).hom
            ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
      algebraMap
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (laurentExponentSubmonoid
            (coordinateTailExponent (fun k => (a k).down)))) r := by
  change AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
        (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE le_top).op).hom
              ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r))) = _
  rw [coordinateOpenCechIntersectionLaurentRingEquiv_baseScalar,
    AddMonoidAlgebra.mapRingEquiv_single]
  change AddMonoidAlgebra.single 0
      ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
        ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv r)) =
    AddMonoidAlgebra.single 0 r
  rw [(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm_apply_apply]

private noncomputable def coordinateOpenCechIntersectionBaseCechFactorAddEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃+
      Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) :=
  AddEquiv.refl _

private theorem coordinateOpenCechIntersectionBaseCechFactorAddEquiv_smul {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (x : Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a) :
    coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a (r • x) =
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (show coordinateOpenCechIntersection (R := R) a ≤ ⊤ from
          le_top)).op).hom
          ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r) *
        coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a x := by
  rfl

/-- A standard projective Cech intersection factor is the free module on its allowed Laurent
monomials over the affine base's global-section ring. -/
noncomputable def coordinateOpenCechIntersectionBaseLaurentLinearEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun k => (a k).down))) :=
  { (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a).trans
      (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a).toAddEquiv with
    map_smul' := by
      intro r x
      change coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
          (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a (r • x)) =
        r • coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
          (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a x)
      rw [coordinateOpenCechIntersectionBaseCechFactorAddEquiv_smul]
      rw [map_mul,
        coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar]
      rw [Algebra.smul_def] }

/-- A standard projective Cech intersection factor, reindexed by global homogeneous Laurent
weights of total degree `d` allowed on its coordinate tuple. -/
noncomputable def coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (d : ℤ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a k).down)} :=
  (coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a).trans
    (AddMonoidAlgebra.mapDomainLinearEquiv
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateLaurentExponentEquiv (fun k => (a k).down) d))

/-- The homogeneous-weight factor equivalence sends a local Laurent basis vector to the same
monomial indexed by its global weight. -/
@[simp]
theorem coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_apply
    {n : ℕ} (a : Fin (n + 1) → ULift.{u} σ) (d : ℤ)
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun k => (a k).down)))
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a d
        ((coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a).symm
          (AddMonoidAlgebra.single e r)) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentEquiv (fun k => (a k).down) d e) r := by
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    AddMonoidAlgebra.mapDomainLinearEquiv_single]

/-- Deleting a Cech coordinate can only shrink the tuple, so every weight allowed on the deleted
tuple is allowed on the full tuple. -/
def coordinateLaurentExponentDeleteEmbedding [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ) :
    {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => ((a.delete k).1 l).down)} ↪
      {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => (a.1 l).down)} where
  toFun e := ⟨e.1, by
    intro i hi
    obtain ⟨l, hl⟩ := e.2 hi
    refine ⟨k.succAbove l, ?_⟩
    change (a.1 (k.succAbove l)).down = i at hl
    exact hl⟩
  inj' e f h := by
    apply Subtype.ext
    exact congrArg
      (fun x : {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => (a.1 l).down)} => x.1) h

/-- The weight-coordinate form of a Cech coface: include the weights allowed on the deleted tuple
among those allowed on the full tuple. -/
noncomputable def coordinateHomogeneousLaurentDeleteLinearMap [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ) :
    AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun l => ((a.delete k).1 l).down)} →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun l => (a.1 l).down)} :=
  AddMonoidAlgebra.mapDomainLinearMap
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (coordinateLaurentExponentDeleteEmbedding a k d)

/-- A Cech deletion map preserves the underlying global homogeneous weight. -/
@[simp]
theorem coordinateHomogeneousLaurentDeleteLinearMap_single [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ)
    (e : {e : HomogeneousLaurentExponent σ d //
      e.IsAllowedOn (fun l => ((a.delete k).1 l).down)})
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d
        (AddMonoidAlgebra.single e r) =
      AddMonoidAlgebra.single (coordinateLaurentExponentDeleteEmbedding a k d e) r := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single
    (R := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (S := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (coordinateLaurentExponentDeleteEmbedding a k d) r e

/-- For a noninitial deletion, a local Laurent exponent remains the same exponent and only gains
the enlarged support permission from the full tuple. -/
noncomputable def coordinateLaurentExponentDeleteAddMonoidHom [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    laurentExponentSubmonoid
        (coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down)) →+
      laurentExponentSubmonoid
        (coordinateTailExponent (fun l => (a.1 l).down)) where
  toFun e := ⟨e.1, by
    intro i hi
    apply (coordinateTailExponent_ne_zero_iff
      (fun l => (a.1 l).down) i).2
    obtain ⟨l, hl⟩ := (coordinateTailExponent_ne_zero_iff
      (fun l => ((a.delete k.succ).1 l).down) i).1 (e.2 i hi)
    exact ⟨k.succ.succAbove l, hl⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The local exponent inclusion commutes with the natural-exponent maps into the two Laurent
localizations. -/
theorem coordinateLaurentExponentDeleteAddMonoidHom_awayMap [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (e : {j : σ // j ≠ (a.1 0).down} →₀ ℕ) :
    coordinateLaurentExponentDeleteAddMonoidHom a k
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete k.succ).1 l).down)) e) =
      laurentExponentAwayMap
        (coordinateTailExponent (fun l => (a.1 l).down)) e := by
  apply Subtype.ext
  ext i
  rfl

/-- Reindexing local exponents by homogeneous weights identifies the noninitial local inclusion
with the global deleted-tuple inclusion. -/
theorem coordinateLaurentExponentEquiv_delete_succ [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down))) :
    coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d
        (coordinateLaurentExponentDeleteAddMonoidHom a k e) =
      coordinateLaurentExponentDeleteEmbedding a k.succ d
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete k.succ).1 l).down) d e) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d
      (coordinateLaurentExponentDeleteAddMonoidHom a k e)).1.1 i =
    (coordinateLaurentExponentEquiv
      (fun l => ((a.delete k.succ).1 l).down) d e).1.1 i
  have hanchor : ((a.delete k.succ).1 0).down = (a.1 0).down := rfl
  by_cases hi : i = (a.1 0).down
  · subst i
    rw [coordinateLaurentExponentEquiv_apply_anchor]
    change d - Finsupp.degree e.1 =
      (coordinateLaurentExponentEquiv
        (fun l => ((a.delete k.succ).1 l).down) d e).1.1
          ((a.delete k.succ).1 0).down
    exact (coordinateLaurentExponentEquiv_apply_anchor
      (fun l => ((a.delete k.succ).1 l).down) d e).symm
  · have hi' : i ≠ ((a.delete k.succ).1 0).down := by
      simpa [hanchor] using hi
    rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi,
      coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi']
    rfl

section

local instance : DecidableEq σ := Classical.decEq σ

private theorem coordinateLaurentExponentDeleteRingHom_comp [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    (AddMonoidAlgebra.mapDomainRingHom R
      (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
        (AddMonoidAlgebra.mapDomainRingHom R
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom) =
      AddMonoidAlgebra.mapDomainRingHom R
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom := by
  rw [← AddMonoidAlgebra.mapDomainRingHom_comp]
  congr 1

/-- For a noninitial deletion, Laurent coordinates identify restriction to the full ordered Cech
intersection with the inclusion that preserves the underlying Laurent exponent. -/
theorem coordinateProductAwayLaurentRingEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))).toRingHom.comp
        ((coordinateProductAwayRingEquiv (R := R)
          (fun l => (a.1 l).down)).toRingHom.comp
          (HomogeneousLocalization.awayMap
            (homogeneousSubmodule σ R)
            (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
            (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ))) =
      (AddMonoidAlgebra.mapDomainRingHom R
        (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
        ((laurentMonomialRingEquiv R
          (coordinateTailExponent
            (fun l => ((a.delete k.succ).1 l).down))).toRingHom.comp
          (coordinateProductAwayRingEquiv (R := R)
            (fun l => ((a.delete k.succ).1 l).down)).toRingHom) := by
  letI := (HomogeneousLocalization.awayMap
    (f := X (a.1 0).down)
    (g := coordinateTailPolynomial (R := R)
      (fun l => ((a.delete k.succ).1 l).down))
    (x := coordinateProductPolynomial (R := R)
      (fun l => ((a.delete k.succ).1 l).down))
    (homogeneousSubmodule σ R)
    (coordinateTailPolynomial_mem (R := R)
      (fun l => ((a.delete k.succ).1 l).down)) rfl).toAlgebra
  let t : HomogeneousLocalization.Away (homogeneousSubmodule σ R)
      (X (a.1 0).down) :=
    HomogeneousLocalization.Away.isLocalizationElem
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
  letI : IsLocalization.Away t
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down))) :=
    HomogeneousLocalization.Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) rfl one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply DFunLike.ext _ _
  intro q
  simp only [RingHom.comp_apply]
  rw [show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X (a.1 0).down))
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down))) q =
    HomogeneousLocalization.awayMap
      (f := X (a.1 0).down)
      (g := coordinateTailPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (x := coordinateProductPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (homogeneousSubmodule σ R)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) rfl q from rfl]
  let p := chartRingEquiv R (a.1 0).down q
  calc
    _ = laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (HomogeneousLocalization.awayMap
            (f := X (a.1 0).down)
            (g := coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
            (x := coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))
            (homogeneousSubmodule σ R)
            (coordinateTailPolynomial_mem (R := R)
              (fun l => (a.1 l).down)) rfl q)) := congrArg
              (fun x => laurentMonomialRingEquiv R
                (coordinateTailExponent (fun l => (a.1 l).down))
                (coordinateProductAwayRingEquiv (R := R)
                  (fun l => (a.1 l).down) x))
              (coordinateTailAwayMap_comp_delete_succ (R := R) a k q)
    _ = AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom p :=
      coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (σ := σ) (n := n + 1) (fun l => (a.1 l).down) q
    _ = AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (AddMonoidAlgebra.mapDomain
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom p) := by
      change (AddMonoidAlgebra.mapDomainRingHom R
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom) p =
        ((AddMonoidAlgebra.mapDomainRingHom R
          (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
          (AddMonoidAlgebra.mapDomainRingHom R
            (laurentExponentAwayMap
              (coordinateTailExponent
                (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom)) p
      exact congrArg (fun f => f p)
        (coordinateLaurentExponentDeleteRingHom_comp (R := R) a k).symm
    _ = _ := congrArg
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k))
      (coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (σ := σ) (n := n)
        (fun l => ((a.delete k.succ).1 l).down) q).symm

/-- The inclusion of a full ordered Cech intersection into the intersection obtained by deleting
one entry. -/
abbrev coordinateOpenCechDelete [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateOpenCechIntersection (R := R) a.1 ⟶
      coordinateOpenCechIntersection (R := R) (a.delete k).1 :=
  (((FormalCoproduct.mk _ (coordinateOpenCover (R := R) (σ := σ))).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ a.1)

/-- Restriction from a deleted Cech intersection to the full intersection is the homogeneous
localization map at the removed coordinate. -/
theorem coordinateOpenCechIntersectionAwayIso_naturality_delete [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 k).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a k)) ≫
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom =
    (coordinateOpenCechIntersectionAwayIso (R := R) (a.delete k).1).hom ≫
      (Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a k).op := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_hom,
    Functor.mapIso_hom, Proj.basicOpenIsoAway, asIso_hom]
  rw [← Category.assoc, Proj.awayMap_awayToSection]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Laurent coordinates carry noninitial restriction between standard Cech intersections to the
inclusion that preserves the underlying local exponent. -/
theorem coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (x : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenCechIntersection (R := R) (a.delete k.succ).1)) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (coordinateOpenCechIntersectionLaurentRingEquiv
          (R := R) (a.delete k.succ).1 x) := by
  let q := (coordinateOpenCechIntersectionAwayIso
    (R := R) (a.delete k.succ).1).inv.hom x
  have hNat := coordinateOpenCechIntersectionAwayIso_naturality_delete
    (R := R) a k.succ
  have hNatq := ConcreteCategory.congr_hom hNat q
  change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
      (HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q) =
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (coordinateOpenCechDelete (R := R) a k.succ).op).hom
      ((coordinateOpenCechIntersectionAwayIso
        (R := R) (a.delete k.succ).1).hom.hom q) at hNatq
  have hq : (coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a k.succ).op).hom x) =
    HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
      (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q := by
    apply (coordinateOpenCechIntersectionAwayIso
      (R := R) a.1).commRingCatIsoToRingEquiv.injective
    change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a k.succ).op).hom x)) =
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q)
    rw [Iso.inv_hom_id_apply]
    rw [show (coordinateOpenCechIntersectionAwayIso
      (R := R) (a.delete k.succ).1).hom.hom q = x by
        simpa only [q] using
          (Iso.inv_hom_id_apply
            (coordinateOpenCechIntersectionAwayIso
              (R := R) (a.delete k.succ).1) x)] at hNatq
    exact hNatq.symm
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a k.succ).op).hom x))) = _
  rw [hq]
  exact DFunLike.congr_fun
    (coordinateProductAwayLaurentRingEquiv_naturality_delete_succ
      (R := R) a k) q

/-- After transporting coefficients to the affine base, noninitial restriction still preserves the
underlying local Laurent exponent. -/
theorem coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (x : Scheme.Modules.baseCechFactor
      (homogeneousProjπ (R := R) (σ := σ))
      (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1) :
    coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (coordinateOpenCechIntersectionBaseLaurentLinearEquiv
          (R := R) (a.delete k.succ).1 x) := by
  let e := (Scheme.ΓSpecIso
    (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
  let y := coordinateOpenCechIntersectionLaurentRingEquiv
    (R := R) (a.delete k.succ).1 x
  change AddMonoidAlgebra.mapRingEquiv _ e
      (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a k.succ).op x)) =
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteAddMonoidHom a k)
      (AddMonoidAlgebra.mapRingEquiv _ e y)
  rw [coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_succ
    (R := R) a k x]
  exact DFunLike.congr_fun
    (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom e.toRingHom
      (coordinateLaurentExponentDeleteAddMonoidHom a k)) y

/-- In global homogeneous-weight coordinates, a noninitial restriction is the existing deleted-
tuple inclusion. -/
theorem
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (x : Scheme.Modules.baseCechFactor
      (homogeneousProjπ (R := R) (σ := σ))
      (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) a.1 d
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k.succ d
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) (a.delete k.succ).1 d x) := by
  let S := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
  let y := coordinateOpenCechIntersectionBaseLaurentLinearEquiv
    (R := R) (a.delete k.succ).1 x
  change AddMonoidAlgebra.mapDomainLinearEquiv S S
      (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d)
      (coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x)) =
    AddMonoidAlgebra.mapDomainLinearMap S S
      (coordinateLaurentExponentDeleteEmbedding a k.succ d)
      (AddMonoidAlgebra.mapDomainLinearEquiv S S
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete k.succ).1 l).down) d) y)
  rw [coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k x]
  change AddMonoidAlgebra.mapDomainLinearEquiv S S
      (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d)
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k) y) = _
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [AddMonoidAlgebra.mapDomain_add, map_add, hx, hy]
  | single e r =>
      simp only [AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.mapDomainLinearEquiv_single,
        AddMonoidAlgebra.mapDomainLinearMap_single]
      rw [coordinateLaurentExponentEquiv_delete_succ a k d e]

/-- A noninitial Cech restriction sends each homogeneous Laurent basis vector to the same global
weight in the full tuple. -/
theorem
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down)))
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) a.1 d
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op
          ((coordinateOpenCechIntersectionBaseLaurentLinearEquiv
            (R := R) (a.delete k.succ).1).symm
            (AddMonoidAlgebra.single e r))) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentDeleteEmbedding a k.succ d
          (coordinateLaurentExponentEquiv
            (fun l => ((a.delete k.succ).1 l).down) d e)) r := by
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k d]
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_apply]
  exact coordinateHomogeneousLaurentDeleteLinearMap_single
    (R := R) a k.succ d _ r

end

/-- The standard frame of `O(d)` restricted to an ordered Cech intersection. -/
noncomputable def coordinateHyperplaneTwistCechTrivialization {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (j : σ) (d : ℤ) :
    (coordinateHyperplaneTwist (R := R) j d).restrict
        (coordinateOpenCechIntersection (R := R) a).ι ≅
      Scheme.Modules.unitObj
        (coordinateOpenCechIntersection (R := R) a).toScheme :=
  Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenCechIntersection_le (R := R) a 0)
    (coordinateHyperplaneTwistTrivialization (R := R) (a 0).down j d)

private noncomputable def baseModulePresheafObjIsoUnitOfOverIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Scheme.Modules.baseModulePresheaf π M).obj (op U) ≅
      (Scheme.Modules.baseModulePresheaf π (Scheme.Modules.unitObj X)).obj (op U) := by
  let eVal := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e
  let eTop := (PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
    (.op (Over.mk (𝟙 U)))).mapIso eVal
  let f : Γ(S, (⊤ : S.Opens)) →+* Γ(X, U) :=
    (X.presheaf.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U))).hom.comp
        π.appTop.hom
  exact (ModuleCat.restrictScalars f).mapIso eTop

private theorem baseModulePresheafObjIsoUnitOfOverIso_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Scheme.Modules.baseModulePresheaf π M).map (homOfLE hVU).op ≫
        (baseModulePresheafObjIsoUnitOfOverIso π M V
          (ModularCurves.SheafOfModules.restrictOverTrivialization
            X.ringCatSheaf M U e (Over.mk (homOfLE hVU)))).hom =
      (baseModulePresheafObjIsoUnitOfOverIso π M U e).hom ≫
        (Scheme.Modules.baseModulePresheaf π
          (Scheme.Modules.unitObj X)).map (homOfLE hVU).op := by
  ext x
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      (M.presheaf.map (homOfLE hVU).op x) =
    X.presheaf.map (homOfLE hVU).op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) x)
  let k : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U) :=
    Over.mkIdTerminal.from (Over.mk (homOfLE hVU))
  have hnat := PresheafOfModules.naturality_apply e.hom.val k.op x
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      ((M.over U).val.map k.op x) =
    (X.ringCatSheaf.over U).obj.map k.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) x) at hnat
  dsimp only [k] at hnat
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      (M.presheaf.map
        (Over.mkIdTerminal.from (Over.mk (homOfLE hVU))).left.op x) =
    X.presheaf.map
      (Over.mkIdTerminal.from (Over.mk (homOfLE hVU))).left.op
        (e.hom.val.app (.op (Over.mk (𝟙 U))) x) at hnat
  rw [Over.mkIdTerminal_from_left] at hnat
  exact hnat

private noncomputable def baseModulePresheafObjUnitScalar
    {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    (Scheme.Modules.baseModulePresheaf π (Scheme.Modules.unitObj X)).obj (op U) ⟶
      (Scheme.Modules.baseModulePresheaf π (Scheme.Modules.unitObj X)).obj (op U) := by
  let q := ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s
  let qVal := (SheafOfModules.forget (X.ringCatSheaf.over U)).map q
  let qTop := (PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
    (.op (Over.mk (𝟙 U)))).map qVal
  let f : Γ(S, (⊤ : S.Opens)) →+* Γ(X, U) :=
    (X.presheaf.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U))).hom.comp
        π.appTop.hom
  exact (ModuleCat.restrictScalars f).map qTop

private theorem baseModulePresheafObjIsoUnitOfOverIso_comp_scalar
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : e.hom = g.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) :
    (baseModulePresheafObjIsoUnitOfOverIso π M U e).hom =
      (baseModulePresheafObjIsoUnitOfOverIso π M U g).hom ≫
        baseModulePresheafObjUnitScalar π U s := by
  ext x
  change e.hom.val.app (.op (Over.mk (𝟙 U))) x =
    (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s).val.app
      (.op (Over.mk (𝟙 U))) (g.hom.val.app (.op (Over.mk (𝟙 U))) x)
  have happ := congrArg (fun q => q.val.app (.op (Over.mk (𝟙 U)))) h
  exact ConcreteCategory.congr_hom happ x

private lemma coordinateOpenTransitionTopUnit_zpow_coe_aux
    (i k : σ) (d : ℤ) :
    ((coordinateOpenTransitionTopUnit (R := R) i k ^ d :
        Γ((coordinateOpenOverlap (R := R) i k).toScheme,
          (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
      Γ((coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))) =
      Scheme.Modules.openTopSection (coordinateOpenOverlap (R := R) i k)
        ((coordinateOpenTransitionUnit (R := R) i k ^ d :
            Γ(Proj (homogeneousSubmodule σ R),
              coordinateOpenOverlap (R := R) i k)ˣ) :
          Γ(Proj (homogeneousSubmodule σ R),
            coordinateOpenOverlap (R := R) i k)) := by
  let f : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenOverlap (R := R) i k) →+*
      Γ((coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens)) :=
    ((coordinateOpenOverlap (R := R) i k).ι.appIso ⊤).hom.hom.comp
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (eqToHom (coordinateOpenOverlap (R := R) i k).ι_image_top).op).hom
  change (((Units.map f.toMonoidHom
      (coordinateOpenTransitionUnit (R := R) i k)) ^ d :
        Γ((coordinateOpenOverlap (R := R) i k).toScheme,
          (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
      Γ((coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))) =
    f ((coordinateOpenTransitionUnit (R := R) i k ^ d :
      Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenOverlap (R := R) i k)ˣ) :
      Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenOverlap (R := R) i k))
  rw [← (Units.map f.toMonoidHom).map_zpow]
  rfl

private theorem restrictOpenTrivialization_hom_eq_comp_scalar_aux
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e g : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection U r)) :
    (Scheme.Modules.restrictOpenTrivialization hVU e).hom =
      (Scheme.Modules.restrictOpenTrivialization hVU g).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection V
            (X.presheaf.map (homOfLE hVU).op r)) := by
  let eOver := Scheme.Modules.overTrivializationOfRestrictIso M U e
  let gOver := Scheme.Modules.overTrivializationOfRestrictIso M U g
  have hOver : eOver.hom = gOver.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r :=
    ModularCurves.overTrivializationOfRestrictIso_hom_eq_comp_scalar
      M U e g r h
  let eRes := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U eOver (Over.mk (homOfLE hVU))
  let gRes := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U gOver (Over.mk (homOfLE hVU))
  have hRes : eRes.hom = gRes.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
        (X.presheaf.map (homOfLE hVU).op r) :=
    ModularCurves.restrictOverTrivialization_hom_eq_comp_scalar
      M hVU gOver eOver r hOver
  have hOpen := ModularCurves.restrictTrivializationOfOverIso_hom_eq_comp_scalar
    M V eRes gRes (X.presheaf.map (homOfLE hVU).op r) hRes
  have heOver := Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
    hVU e
  have hgOver := Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
    hVU g
  have heOpen := congrArg
    (ModularCurves.restrictTrivializationOfOverIso M V) heOver
  have hgOpen := congrArg
    (ModularCurves.restrictTrivializationOfOverIso M V) hgOver
  rw [ModularCurves.restrictTrivializationOfOverTrivializationOfRestrictIso]
    at heOpen hgOpen
  rw [← heOpen, ← hgOpen] at hOpen
  exact hOpen

/-- A twist Cech factor is the corresponding structure-sheaf section module. -/
noncomputable def coordinateHyperplaneTwistBaseCechFactorIsoUnit {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (j : σ) (d : ℤ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n a ≅
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a :=
  baseModulePresheafObjIsoUnitOfOverIso
    (homogeneousProjπ (R := R) (σ := σ))
    (coordinateHyperplaneTwist (R := R) j d)
    (coordinateOpenCechIntersection (R := R) a)
    (Scheme.Modules.overTrivializationOfRestrictIso
      (coordinateHyperplaneTwist (R := R) j d)
      (coordinateOpenCechIntersection (R := R) a)
      (coordinateHyperplaneTwistCechTrivialization (R := R) a j d))

/-- The order relation underlying `coordinateOpenCechDelete`. -/
theorem coordinateOpenCechDelete_le [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateOpenCechIntersection (R := R) a.1 ≤
      coordinateOpenCechIntersection (R := R) (a.delete k).1 :=
  leOfHom (coordinateOpenCechDelete (R := R) a k)

/-- A full ordered Cech intersection lies in the overlap of its first two
standard charts. -/
theorem coordinateOpenCechIntersection_le_firstOverlap [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateOpenCechIntersection (R := R) a.1 ≤
      coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down := by
  rw [coordinateOpenOverlap_eq]
  exact le_inf
    (coordinateOpenCechIntersection_le (R := R) a.1 0)
    (coordinateOpenCechIntersection_le (R := R) a.1 1)

private noncomputable def coordinateOpenCechFirstTransitionRingHom
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down) →+*
      Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
        (⊤ : (coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens)) :=
  (((coordinateOpenCechIntersection (R := R) a.1).ι.appIso ⊤).hom.hom.comp
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (eqToHom (coordinateOpenCechIntersection (R := R) a.1).ι_image_top).op).hom).comp
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
        (R := R) a)).op).hom

/-- The first-chart transition unit, restricted to a full ordered Cech
intersection and transported to its top ring. -/
noncomputable def coordinateOpenCechFirstTransitionTopUnit
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
      (⊤ : (coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))ˣ :=
  Units.map (coordinateOpenCechFirstTransitionRingHom (R := R) a).toMonoidHom
    (coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down)

private lemma coordinateOpenCechFirstTransitionTopUnit_zpow_coe
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    ((coordinateOpenCechFirstTransitionTopUnit (R := R) a ^ d :
        Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
          (⊤ : (coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))ˣ) :
      Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
        (⊤ : (coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))) =
      Scheme.Modules.openTopSection (coordinateOpenCechIntersection (R := R) a.1)
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
            (R := R) a)).op
          ((coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down ^ d :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
            Γ(Proj (homogeneousSubmodule σ R),
              coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))) := by
  let f := coordinateOpenCechFirstTransitionRingHom (R := R) a
  change (((Units.map f.toMonoidHom
      (coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down)) ^ d :
        Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
          (⊤ : (coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))ˣ) :
      Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
        (⊤ : (coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))) =
    f ((coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down ^ d :
      Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
      Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))
  rw [← (Units.map f.toMonoidHom).map_zpow]
  rfl

/-- Multiplication by the first-chart transition unit on the structure-sheaf
factor of a full ordered Cech intersection. -/
noncomputable def coordinateOpenCechFirstTransitionFactorEnd
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) (n + 1) a.1 ⟶
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) (n + 1) a.1 :=
  baseModulePresheafObjUnitScalar
    (homogeneousProjπ (R := R) (σ := σ))
    (coordinateOpenCechIntersection (R := R) a.1)
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
        (R := R) a)).op
      ((coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down ^ d :
          Γ(Proj (homogeneousSubmodule σ R),
            coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
        Γ(Proj (homogeneousSubmodule σ R),
          coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)))

/-- Deleting a noninitial entry preserves the anchor frame on the smaller
standard intersection. -/
theorem coordinateHyperplaneTwistCechTrivialization_restrict_delete_of_ne_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ 0) (j : σ) (d : ℤ) :
    Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenCechDelete_le (R := R) a k)
        (coordinateHyperplaneTwistCechTrivialization
          (R := R) (a.delete k).1 j d) =
      coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d := by
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
  rw [coordinateHyperplaneTwistCechTrivialization,
    Scheme.Modules.restrictOpenTrivialization_comp]
  rfl

/-- Deleting the first Cech entry changes the anchor frame by the restricted
integer power of the standard-chart transition unit. -/
theorem coordinateHyperplaneTwistCechTrivialization_restrict_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : σ) (d : ℤ) :
    (coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d).hom =
      (Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenCechDelete_le (R := R) a 0)
          (coordinateHyperplaneTwistCechTrivialization
            (R := R) (a.delete 0).1 j d)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((coordinateOpenCechFirstTransitionTopUnit (R := R) a ^ d :
              Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
                (⊤ : (coordinateOpenCechIntersection
                  (R := R) a.1).toScheme.Opens))ˣ) :
            Γ((coordinateOpenCechIntersection (R := R) a.1).toScheme,
              (⊤ : (coordinateOpenCechIntersection
                (R := R) a.1).toScheme.Opens))) := by
  let i := (a.1 0).down
  let k := (a.1 1).down
  let U := coordinateOpenOverlap (R := R) i k
  let V := coordinateOpenCechIntersection (R := R) a.1
  let hVU := coordinateOpenCechIntersection_le_firstOverlap (R := R) a
  let eI := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_left (R := R) i k)
    (coordinateHyperplaneTwistTrivialization (R := R) i j d)
  let eK := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_right (R := R) i k)
    (coordinateHyperplaneTwistTrivialization (R := R) k j d)
  let r : Γ(Proj (homogeneousSubmodule σ R), U) :=
    ((coordinateOpenTransitionUnit (R := R) i k ^ d :
      Γ(Proj (homogeneousSubmodule σ R), U)ˣ) :
      Γ(Proj (homogeneousSubmodule σ R), U))
  have hOverlap : eI.hom = eK.hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection U r) := by
    rw [← coordinateOpenTransitionTopUnit_zpow_coe_aux]
    exact coordinateHyperplaneTwistTrivialization_restrict_transition
      (R := R) i k j d
  have hV := restrictOpenTrivialization_hom_eq_comp_scalar_aux
    (coordinateHyperplaneTwist (R := R) j d) hVU eI eK r hOverlap
  have hIFrame :
      coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d =
        Scheme.Modules.restrictOpenTrivialization hVU eI := by
    rw [coordinateHyperplaneTwistCechTrivialization]
    dsimp only [eI]
    rw [Scheme.Modules.restrictOpenTrivialization_comp]
  have hKFrame :
      Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenCechDelete_le (R := R) a 0)
          (coordinateHyperplaneTwistCechTrivialization
            (R := R) (a.delete 0).1 j d) =
        Scheme.Modules.restrictOpenTrivialization hVU eK := by
    rw [coordinateHyperplaneTwistCechTrivialization]
    dsimp only [eK]
    rw [Scheme.Modules.restrictOpenTrivialization_comp,
      Scheme.Modules.restrictOpenTrivialization_comp]
    dsimp only [k]
    change Scheme.Modules.restrictOpenTrivialization _
        (coordinateHyperplaneTwistTrivialization
          (R := R) (a.1 1).down j d) =
      Scheme.Modules.restrictOpenTrivialization _
        (coordinateHyperplaneTwistTrivialization
          (R := R) (a.1 1).down j d)
    rfl
  rw [hIFrame, hKFrame,
    coordinateOpenCechFirstTransitionTopUnit_zpow_coe]
  exact hV

/-- Every noninitial Cech face is ordinary restriction in the chosen twist
coordinates. -/
theorem coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_of_ne_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ 0) (j : σ) (d : ℤ) :
    (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)).map
          (coordinateOpenCechDelete (R := R) a k).op ≫
      (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom =
    (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) (a.delete k).1 j d).hom ≫
      (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (coordinateOpenCechDelete (R := R) a k).op := by
  let M := coordinateHyperplaneTwist (R := R) j d
  let U := coordinateOpenCechIntersection (R := R) (a.delete k).1
  let V := coordinateOpenCechIntersection (R := R) a.1
  let hVU := coordinateOpenCechDelete_le (R := R) a k
  let eU := Scheme.Modules.overTrivializationOfRestrictIso M U
    (coordinateHyperplaneTwistCechTrivialization (R := R) (a.delete k).1 j d)
  have hframe :=
    coordinateHyperplaneTwistCechTrivialization_restrict_delete_of_ne_zero
      (R := R) a k hk j d
  have hover :
      Scheme.Modules.overTrivializationOfRestrictIso M V
          (coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d) =
        ModularCurves.SheafOfModules.restrictOverTrivialization
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf M U eU
            (Over.mk (homOfLE hVU)) := by
    rw [← hframe]
    exact Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hVU _
  change (Scheme.Modules.baseModulePresheaf
      (homogeneousProjπ (R := R) (σ := σ)) M).map (homOfLE hVU).op ≫
    (baseModulePresheafObjIsoUnitOfOverIso
      (homogeneousProjπ (R := R) (σ := σ)) M V _).hom =
    (baseModulePresheafObjIsoUnitOfOverIso
      (homogeneousProjπ (R := R) (σ := σ)) M U eU).hom ≫
      (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (homOfLE hVU).op
  rw [hover]
  exact baseModulePresheafObjIsoUnitOfOverIso_naturality
    (homogeneousProjπ (R := R) (σ := σ)) M hVU eU

/-- The first Cech face is ordinary restriction followed by multiplication
by the restricted integer-twist transition unit. -/
theorem coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : σ) (d : ℤ) :
    (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)).map
          (coordinateOpenCechDelete (R := R) a 0).op ≫
      (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom =
    (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) (a.delete 0).1 j d).hom ≫
      (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (coordinateOpenCechDelete (R := R) a 0).op ≫
      coordinateOpenCechFirstTransitionFactorEnd (R := R) a d := by
  let X := Proj (homogeneousSubmodule σ R)
  let π := homogeneousProjπ (R := R) (σ := σ)
  let M := coordinateHyperplaneTwist (R := R) j d
  let U := coordinateOpenCechIntersection (R := R) (a.delete 0).1
  let V := coordinateOpenCechIntersection (R := R) a.1
  let hVU := coordinateOpenCechDelete_le (R := R) a 0
  let eU := Scheme.Modules.overTrivializationOfRestrictIso M U
    (coordinateHyperplaneTwistCechTrivialization (R := R) (a.delete 0).1 j d)
  let eV := Scheme.Modules.overTrivializationOfRestrictIso M V
    (coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d)
  let eRes := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U eU (Over.mk (homOfLE hVU))
  let s : Γ(X, V) :=
    X.presheaf.map
      (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
        (R := R) a)).op
      ((coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down ^ d :
        Γ(X, coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
        Γ(X, coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))
  have hframe := coordinateHyperplaneTwistCechTrivialization_restrict_delete_zero
    (R := R) a j d
  have hframe' :
      (coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d).hom =
        (Scheme.Modules.restrictOpenTrivialization hVU
          (coordinateHyperplaneTwistCechTrivialization
            (R := R) (a.delete 0).1 j d)).hom ≫
          ModularCurves.unitEndomorphismOfTopSection
            (Scheme.Modules.openTopSection V s) := by
    rw [← coordinateOpenCechFirstTransitionTopUnit_zpow_coe]
    exact hframe
  have hOver := ModularCurves.overTrivializationOfRestrictIso_hom_eq_comp_scalar
    M V
      (coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d)
      (Scheme.Modules.restrictOpenTrivialization hVU
        (coordinateHyperplaneTwistCechTrivialization
          (R := R) (a.delete 0).1 j d)) s hframe'
  have heRes : Scheme.Modules.overTrivializationOfRestrictIso M V
      (Scheme.Modules.restrictOpenTrivialization hVU
        (coordinateHyperplaneTwistCechTrivialization
          (R := R) (a.delete 0).1 j d)) = eRes :=
    Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hVU _
  rw [heRes] at hOver
  have hScalar := baseModulePresheafObjIsoUnitOfOverIso_comp_scalar
    π M V eV eRes s hOver
  have hNat := baseModulePresheafObjIsoUnitOfOverIso_naturality
    π M hVU eU
  change (Scheme.Modules.baseModulePresheaf π M).map (homOfLE hVU).op ≫
    (baseModulePresheafObjIsoUnitOfOverIso π M V eV).hom =
    (baseModulePresheafObjIsoUnitOfOverIso π M U eU).hom ≫
      (Scheme.Modules.baseModulePresheaf π (Scheme.Modules.unitObj X)).map
        (homOfLE hVU).op ≫ baseModulePresheafObjUnitScalar π V s
  rw [hScalar, ← Category.assoc, hNat, Category.assoc]

/-- The degree-`n` ordered Cech object of `O(d)` is factorwise identified with
the ordered Cech object of the structure sheaf. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n ≅
      Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n :=
  Pi.mapIso (fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.1 j d)

/-- The degreewise twist-to-unit Cech comparison is the landed factor
comparison on every ordered tuple. -/
@[reassoc]
theorem coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit_hom_comp_π
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Scheme.Modules.baseCechFactor
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (coordinateOpenCover (R := R) (σ := σ)) n b.1) a =
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) a ≫
      (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom := by
  exact Pi.mapIso_hom_π
    (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) b.1 j d) a

/-- Every noninitial ordered Cech coface becomes ordinary structure-sheaf
restriction in the standard twist frames. -/
theorem coordinateHyperplaneTwistOrderedBaseCechCoface_of_ne_zero
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (k : Fin (n + 2)) (hk : k ≠ 0) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      Scheme.Modules.orderedBaseCechCoface
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n k =
    Scheme.Modules.orderedBaseCechCoface
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n k ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  unfold coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
  unfold Scheme.Modules.orderedBaseCechCoface
  unfold Scheme.Modules.orderedBaseCechObject
  unfold FormalCoproduct.evalOp
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_π, Pi.mapIso_hom_π_assoc,
    Category.assoc, Pi.mapIso_hom_π]
  conv_rhs => erw [← Category.assoc, Pi.lift_π]
  let a' : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) := a
  change Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete k) ≫
      ((coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) (a'.delete k).1 j d).hom ≫
        (Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a' k).op) =
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete k) ≫
      ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (coordinateHyperplaneTwist (R := R) j d)).map
            (coordinateOpenCechDelete (R := R) a' k).op ≫
        (coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) a'.1 j d).hom)
  have hNat :=
    coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_of_ne_zero
    (R := R) a' k hk j d
  exact congrArg
    (fun q =>
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Scheme.Modules.baseCechFactor
          (homogeneousProjπ (R := R) (σ := σ))
          (coordinateHyperplaneTwist (R := R) j d)
          (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete k) ≫ q)
    hNat.symm

/-- The first coface in standard twist coordinates: ordinary restriction
followed by multiplication by the first-chart transition factor. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechFirstCoface
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n ⟶
      Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) (n + 1) :=
  Pi.lift fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a.delete 0) ≫
      (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (coordinateOpenCechDelete (R := R) a 0).op ≫
      coordinateOpenCechFirstTransitionFactorEnd (R := R) a d

/-- The first coordinate coface has the advertised restriction-and-transition
formula on every ordered tuple. -/
@[reassoc]
theorem coordinateHyperplaneTwistOrderedBaseCechFirstCoface_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateHyperplaneTwistOrderedBaseCechFirstCoface
        (R := R) d n ≫
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
        Scheme.Modules.baseCechFactor
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (coordinateOpenCover (R := R) (σ := σ)) (n + 1) b.1) a =
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a.delete 0) ≫
      (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (coordinateOpenCechDelete (R := R) a 0).op ≫
      coordinateOpenCechFirstTransitionFactorEnd (R := R) a d := by
  exact Pi.lift_π _ a

/-- The exceptional first twist coface becomes the coordinate coface carrying
the first-chart transition factor. -/
theorem coordinateHyperplaneTwistOrderedBaseCechCoface_zero
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      coordinateHyperplaneTwistOrderedBaseCechFirstCoface
        (R := R) d n =
    Scheme.Modules.orderedBaseCechCoface
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n 0 ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  unfold coordinateHyperplaneTwistOrderedBaseCechFirstCoface
  unfold coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
  unfold Scheme.Modules.orderedBaseCechCoface
  unfold Scheme.Modules.orderedBaseCechObject
  unfold FormalCoproduct.evalOp
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_π, Pi.mapIso_hom_π_assoc,
    Category.assoc, Pi.mapIso_hom_π]
  conv_rhs => erw [← Category.assoc, Pi.lift_π]
  let a' : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) := a
  change Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete 0) ≫
      ((coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) (a'.delete 0).1 j d).hom ≫
        (Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a' 0).op ≫
        coordinateOpenCechFirstTransitionFactorEnd (R := R) a' d) =
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete 0) ≫
      ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (coordinateHyperplaneTwist (R := R) j d)).map
            (coordinateOpenCechDelete (R := R) a' 0).op ≫
        (coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) a'.1 j d).hom)
  have hNat :=
    coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_zero
      (R := R) a' j d
  exact congrArg
    (fun q =>
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Scheme.Modules.baseCechFactor
          (homogeneousProjπ (R := R) (σ := σ))
          (coordinateHyperplaneTwist (R := R) j d)
          (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete 0) ≫ q)
    hNat.symm

/-- The ordered Cech coface in standard twist coordinates. Only the first
face carries a transition factor. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechCoface
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n ⟶
      Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) (n + 1) :=
  if k = 0 then
    coordinateHyperplaneTwistOrderedBaseCechFirstCoface (R := R) d n
  else
    Scheme.Modules.orderedBaseCechCoface
      (homogeneousProjπ (R := R) (σ := σ))
      (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) n k

/-- The degreewise twist comparison intertwines every twist coface with its
explicit coordinate coface. -/
theorem coordinateHyperplaneTwistOrderedBaseCechCoface_naturality
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      coordinateHyperplaneTwistOrderedBaseCechCoface
        (R := R) d n k =
    Scheme.Modules.orderedBaseCechCoface
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n k ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  by_cases hk : k = 0
  · subst k
    exact coordinateHyperplaneTwistOrderedBaseCechCoface_zero
      (R := R) j d n
  · rw [coordinateHyperplaneTwistOrderedBaseCechCoface, if_neg hk]
    exact coordinateHyperplaneTwistOrderedBaseCechCoface_of_ne_zero
      (R := R) j d n k hk

/-- The alternating ordered Cech differential in standard twist coordinates. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechDifferential
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n ⟶
      Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    coordinateHyperplaneTwistOrderedBaseCechCoface (R := R) d n k

/-- The degreewise standard-frame comparison conjugates the twist Cech
differential to the explicit coordinate differential. -/
theorem coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) d n =
    Scheme.Modules.orderedBaseCechDifferential
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  rw [coordinateHyperplaneTwistOrderedBaseCechDifferential,
    Scheme.Modules.orderedBaseCechDifferential,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    coordinateHyperplaneTwistOrderedBaseCechCoface_naturality]

/-- Consecutive coordinate differentials compose to zero. -/
theorem coordinateHyperplaneTwistOrderedBaseCechDifferential_comp
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n ≫
      coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d (n + 1) = 0 := by
  apply (cancel_epi
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
      (R := R) j d n).hom).1
  rw [Limits.comp_zero, ← Category.assoc,
    coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality,
    Category.assoc,
    coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality,
    ← Category.assoc,
    Scheme.Modules.orderedBaseCechDifferential_comp,
    Limits.zero_comp]

/-- The explicit standard-coordinate ordered Cech complex for `O(d)`. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechComplex
    [LinearOrder σ] (j : σ) (d : ℤ) :
    CochainComplex
      (ModuleCat.{u} Γ(Spec (CommRingCat.of R),
        (⊤ : (Spec (CommRingCat.of R)).Opens))) ℕ :=
  CochainComplex.of
    (fun n => Scheme.Modules.orderedBaseCechObject
      (homogeneousProjπ (R := R) (σ := σ))
      (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) n)
    (coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) d)
    (coordinateHyperplaneTwistOrderedBaseCechDifferential_comp
      (R := R) j d)

@[simp]
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_X
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).X n =
      Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n := rfl

@[simp]
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_d
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).d n (n + 1) =
      coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n := by
  simp [coordinateHyperplaneTwistOrderedBaseCechComplex]

/-- The ordered Cech complex of `O(d)` is the explicit standard-coordinate
complex under the chosen chart frames. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechComplexIso
    [LinearOrder σ] (j : σ) (d : ℤ) :
    Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) ≅
      coordinateHyperplaneTwistOrderedBaseCechComplex
        (R := R) j d :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
      (R := R) j d n) (by
        intro n m hnm
        simp only [ComplexShape.up_Rel] at hnm
        subst m
        rw [Scheme.Modules.orderedBaseCechComplex_d,
          coordinateHyperplaneTwistOrderedBaseCechComplex_d]
        exact coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality
          (R := R) j d n)

@[simp]
theorem coordinateHyperplaneTwistOrderedBaseCechComplexIso_hom_f
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplexIso
      (R := R) j d).hom.f n =
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom := rfl

end

end MvPolynomial
