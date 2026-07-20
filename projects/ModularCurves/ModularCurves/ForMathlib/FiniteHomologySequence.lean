/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.BaseChangeKerCoker

/-!
# Finiteness in long homology sequences

Over a Noetherian ring, each exact pair in the long homology sequence of a short exact
sequence of complexes transfers finite generation from the two surrounding terms to the
middle term.
-/

open CategoryTheory

universe u v w

namespace ModularCurves.CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {ι : Type w} {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)}

/-- In a short exact sequence of complexes, finite homology of the third complex in one
degree and of the second complex in the following degree imply finite homology of the first
complex in the following degree. -/
theorem finite_homology_X1 (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    [Module.Finite R (S.X₃.homology i)] [Module.Finite R (S.X₂.homology j)] :
    Module.Finite R (S.X₁.homology j) :=
  Module.Finite.of_exact_of_finite _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ i j hij))

/-- In a short exact sequence of complexes, finite homology of the first and third
complexes in one degree implies finite homology of the second complex in that degree. -/
theorem finite_homology_X2 (hS : S.ShortExact) (i : ι)
    [Module.Finite R (S.X₁.homology i)] [Module.Finite R (S.X₃.homology i)] :
    Module.Finite R (S.X₂.homology i) :=
  Module.Finite.of_exact_of_finite _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ i))

/-- In a short exact sequence of complexes, finite homology of the second complex in one
degree and of the first complex in the following degree imply finite homology of the third
complex in the first degree. -/
theorem finite_homology_X3 (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    [Module.Finite R (S.X₂.homology i)] [Module.Finite R (S.X₁.homology j)] :
    Module.Finite R (S.X₃.homology i) :=
  Module.Finite.of_exact_of_finite _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ i j hij))

end ModularCurves.CategoryTheory.ShortComplex.ShortExact
