/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistFixedPresentation
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistShiftIso
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistTensorEquivalence

/-!
# Shifted presentations by projective twists

Tensoring a fixed-coordinate negative-twist presentation by a sufficiently
large positive twist produces a presentation by nonnegative twists.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
  MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance shiftedPresentationMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Tensoring a finite coproduct of fixed-coordinate negative twists by a
sufficiently large positive twist produces nonnegative twists. -/
noncomputable def fixedCoordinateNegativeTwistCoproductTensorIso
    (j : σ) {r : ℕ} (d : Fin r → ℕ) (N : ℕ)
    (hN : ∀ i, d i ≤ N) :
    (∐ fun i : Fin r ↦
        coordinateHyperplaneIdealModulePower (R := R) j (d i)) ⊗
        coordinateHyperplanePoleSheafPower (R := R) j N ≅
      ∐ fun i : Fin r ↦
        coordinateHyperplanePoleSheafPower (R := R) j (N - d i) := by
  let E := coordinateHyperplanePoleSheafPowerTensorEquivalence
    (R := R) j N
  let L : Fin r → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    coordinateHyperplaneIdealModulePower (R := R) j (d i)
  let P : Fin r → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    coordinateHyperplanePoleSheafPower (R := R) j (N - d i)
  let e₀ : E.functor.obj (∐ L) ≅ ∐ fun i ↦ E.functor.obj (L i) :=
    PreservesCoproduct.iso E.functor L
  let e₁ : (∐ fun i ↦ E.functor.obj (L i)) ≅ ∐ P :=
    Sigma.mapIso fun i =>
      coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE
        (R := R) j (d i) N (hN i)
  exact e₀ ≪≫ e₁

/-- After one fixed positive twist, a finite-type quasicoherent module is a
quotient of finitely many nonnegative powers of the same coordinate twist. -/
theorem exists_fin_coordinateNonnegativeTwist_quotient [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (N : ℕ)
        (f : (∐ fun i : Fin r ↦
          coordinateHyperplanePoleSheafPower (R := R) j (N - d i)) ⟶
            M ⊗ coordinateHyperplanePoleSheafPower (R := R) j N),
      Epi f := by
  classical
  obtain ⟨r, d, f, hf⟩ :=
    exists_fin_fixedCoordinateNegativeTwist_quotient M j
  letI : Epi f := hf
  let N := Finset.univ.sup d
  have hN (i : Fin r) : d i ≤ N :=
    Finset.le_sup (Finset.mem_univ i)
  let E := coordinateHyperplanePoleSheafPowerTensorEquivalence
    (R := R) j N
  letI : E.functor.PreservesEpimorphisms := inferInstance
  let e := fixedCoordinateNegativeTwistCoproductTensorIso
    (R := R) j d N hN
  let g : (∐ fun i : Fin r ↦
      coordinateHyperplanePoleSheafPower (R := R) j (N - d i)) ⟶
        M ⊗ coordinateHyperplanePoleSheafPower (R := R) j N :=
    e.inv ≫ E.functor.map f
  refine ⟨r, d, N, g, ?_⟩
  change Epi (e.inv ≫ E.functor.map f)
  exact @epi_comp _ _ _ _ _ e.inv (by infer_instance)
    (E.functor.map f) (E.functor.map_epi f)

end

end MvPolynomial
