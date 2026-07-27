/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TranslationAction
import ModularCurves.ForMathlib.HopfGaloisTheorem
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The translation co-action on a stable affine chart

Construction support for `[CHARTER-HOPF]` Wave C (`.mathlib-quality/decomposition-hopf-crux.md`,
appendix "Wave C scoping"; `T-G3d-infra` obligation 1 = 3a-ii): on a `G`-stable affine chart
`U = Spec B` of `E` (over an affine base patch `Spec R` with `G` restricted to `Spec A`,
`A` a finite free `R`-Hopf algebra), the structure-sheaf dual of `translationAction`
is a co-action `ρ : B →ₐ[R] B ⊗[R] A` in the sense of `IsCoaction`, and the freeness of
translation makes its Galois precursor surjective. Feeding
`isHopfGalois_of_surjective_galoisPrecursor` (the M5 theorem) then produces
`IsHopfGalois ρ` per chart, whence `isColimit_of_isHopfGalois` gives the affine quotient.

This file sets up the chart-level data. The geometric inputs (existence of stable
charts, the closed-immersion property of `actPair`) are Wave-C leaves `[HG-C3]`/`[HG-C2]`.

## The chart datum

`StableAffineChartData` packages what the per-chart argument consumes:
* rings `R`, `A`, `B` with `A` a finite free commutative `R`-Hopf algebra,
* the co-action candidate `ρ : B →ₐ[R] B ⊗[R] A` (the `Γ`-dual of the restricted action,
  transported along `pullbackSpecIso`),
* the two axioms making it an `IsCoaction` (counit and coassociativity, the `Γ`-duals of
  the action-unit and action-associativity diagrams), and
* the surjectivity of the Galois precursor (the `Γ`-dual of `actPair` being a closed
  immersion on the chart).

The bridge lemmas identifying these fields with `Γ`-images of the scheme-level data are
the content of `[HG-C1]`/`[HG-C2]`; the assembly consuming this structure is `[HG-C4]`.
-/

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace ModularCurves

/-- The per-chart algebraic datum extracted from a `G`-stable affine chart of `E`.
All Wave-C geometry funnels into producing terms of this structure; the M5 theorem
consumes them. -/
structure StableAffineChartData (R A B : Type u) [CommRing R] [CommRing A]
    [HopfAlgebra R A] [Module.Free R A] [Module.Finite R A]
    [CommRing B] [Algebra R B] where
  /-- The translation co-action on the chart. -/
  coaction : B →ₐ[R] B ⊗[R] A
  /-- The co-action axioms (counit + coassociativity). -/
  isCoaction : IsCoaction coaction
  /-- Freeness of translation: the Galois precursor is surjective on the chart. -/
  precursorSurjective : Function.Surjective (galoisPrecursor R A coaction)

namespace StableAffineChartData

variable {R A B : Type u} [CommRing R] [CommRing A]
  [HopfAlgebra R A] [Module.Free R A] [Module.Finite R A]
  [CommRing B] [Algebra R B]

/-- **Per-chart Hopf–Galois property** — the M5 theorem applied to a chart datum. -/
theorem isHopfGalois (D : StableAffineChartData R A B) : IsHopfGalois D.coaction :=
  isHopfGalois_of_surjective_galoisPrecursor R A D.coaction D.isCoaction
    D.precursorSurjective

end StableAffineChartData

end ModularCurves
