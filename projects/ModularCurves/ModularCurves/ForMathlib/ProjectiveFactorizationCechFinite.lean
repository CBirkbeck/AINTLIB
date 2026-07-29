/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.ProjectiveFactorization
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFinite
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechFinite

/-!
# Cech finiteness from a projective factorization

A projective factorization supplies a standard coordinate cover on which every ordered
base-Cech homology module of a finite-type quasicoherent module is finite.
-/

open CategoryTheory

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsProjectiveFactorization

private def coordinateCollapse (d : ℕ) : Fin (d + 2) → Fin (d + 1) :=
  Fin.predAbove 0

private lemma coordinateCollapse_surjective (d : ℕ) :
    Function.Surjective (coordinateCollapse d) :=
  Fin.predAbove_surjective 0

private lemma homogeneousCoordinateCollapse_surjective
    (R : Type u) [CommRing R] (d : ℕ) :
    Function.Surjective
      (MvPolynomial.homogeneousRenameGradedHom R (coordinateCollapse d)) := by
  exact MvPolynomial.rename_surjective (coordinateCollapse d)
    (coordinateCollapse_surjective d)

private lemma homogeneousCoordinateCollapse_irrelevant_le
    (R : Type u) [CommRing R] (d : ℕ) :
    HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (d + 2)) R)).map
          (MvPolynomial.homogeneousRenameGradedHom R (coordinateCollapse d)) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective _
    (homogeneousCoordinateCollapse_surjective R d)

private def homogeneousProjSuccι (R : Type u) [CommRing R] (d : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 2)) R) :=
  Proj.map
    (MvPolynomial.homogeneousRenameGradedHom R (coordinateCollapse d))
    (homogeneousCoordinateCollapse_irrelevant_le R d)

private lemma homogeneousProjSuccι_isClosedImmersion
    (R : Type u) [CommRing R] (d : ℕ) :
    IsClosedImmersion (homogeneousProjSuccι R d) :=
  HomogeneousIdeal.isClosedImmersion_projMap_of_surjective _
    (homogeneousCoordinateCollapse_irrelevant_le R d)
    (homogeneousCoordinateCollapse_surjective R d)

private lemma homogeneousCoordinateCollapse_zero_algebraMap
    (R : Type u) [CommRing R] (d : ℕ) (r : R) :
    ModularCurves.gradedRingHomZero
          (MvPolynomial.homogeneousRenameGradedHom R (coordinateCollapse d))
          (algebraMap R
            (MvPolynomial.homogeneousSubmodule (Fin (d + 2)) R 0) r) =
      algebraMap R
        (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R 0) r := by
  apply Subtype.ext
  exact (MvPolynomial.rename (coordinateCollapse d)).commutes r

private lemma homogeneousCoordinateCollapse_zero_comp_algebraMap
    (R : Type u) [CommRing R] (d : ℕ) :
    CommRingCat.ofHom
          (algebraMap R
            (MvPolynomial.homogeneousSubmodule (Fin (d + 2)) R 0)) ≫
        CommRingCat.ofHom
          (ModularCurves.gradedRingHomZero
            (MvPolynomial.homogeneousRenameGradedHom R (coordinateCollapse d))) =
      CommRingCat.ofHom
        (algebraMap R
          (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R 0)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact homogeneousCoordinateCollapse_zero_algebraMap R d r

private lemma homogeneousProjSuccι_comp_homogeneousProjπ
    (R : Type u) [CommRing R] (d : ℕ) :
    homogeneousProjSuccι R d ≫
        MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 2)) =
      MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)) := by
  unfold homogeneousProjSuccι MvPolynomial.homogeneousProjπ
  rw [← Category.assoc, ModularCurves.map_comp_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp,
    homogeneousCoordinateCollapse_zero_comp_algebraMap]

variable {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {f : X ⟶ Spec (.of R)}

/-- A projective factorization supplies a standard coordinate cover with finite ordered
base-Cech homology in every degree. -/
theorem exists_orderedBaseCechHomologyFinite
    (hf : AlgebraicGeometry.IsProjectiveFactorization f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (d : ℕ)
      (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)),
      IsClosedImmersion i ∧
        i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)) = f ∧
        Scheme.Modules.OrderedBaseCechHomologyFinite f
          (fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
            (R := R) (σ := Fin (d + 1)) j) M := by
  obtain ⟨d, i, hi, hif⟩ := hf
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion (homogeneousProjSuccι R d) :=
    homogeneousProjSuccι_isClosedImmersion R d
  let j := i ≫ homogeneousProjSuccι R d
  have hjf :
      j ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 2)) = f := by
    dsimp only [j]
    rw [Category.assoc, homogeneousProjSuccι_comp_homogeneousProjπ, hif]
  refine ⟨d + 1, j, inferInstance, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hjf
  · intro q
    rw [← hjf]
    exact MvPolynomial.closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite
      j M q

end AlgebraicGeometry.IsProjectiveFactorization
