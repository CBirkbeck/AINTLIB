/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Connectedness from closed points, and along surjections (Gap B, the cheap bridge)

The two scheme-theoretic halves of the connectedness argument for
`yRho_geometricallyIrreducible`. Neither needs GAGA, an analytification functor, or any
coherent-sheaf comparison:

* `preconnectedSpace_of_closedPoints` — for `X` locally of finite type over a field, the
  closed points are **dense** (`X` is a Jacobson space), so if they are connected in the
  subspace topology then `X` is connected. Over an algebraically closed field the closed
  points are exactly the `K`-points (`AlgebraicGeometry.pointEquivClosedPoint`), so this is
  the bridge "the `K`-points are connected ⟹ the scheme is connected". Combined with "the
  analytic topology refines the Zariski topology" it replaces the GAGA leaf of the original
  plan, which asked for an *iff* where only this direction is used.

* `connectedSpace_of_surjective` — connectedness transfers along a surjective morphism of
  schemes. Applied to `Y ⊗ ℂ → Y ⊗ ℚ̄` it gives the "insensitive to `ℚ̄ ↪ ℂ`" step.

Reviewed by gpt-5.6-sol; the mathlib lemmas used were verified present before being cited.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ModularCurves

/-- A scheme locally of finite type over a field has a Jacobson underlying space (the base
`Spec K` is a single point, hence Jacobson). -/
theorem jacobsonSpace_of_locallyOfFiniteType_over_field {X : Scheme.{u}} {K : Type u}
    [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    JacobsonSpace ↥X := by
  haveI : JacobsonSpace ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (JacobsonSpace (PrimeSpectrum K))
  exact LocallyOfFiniteType.jacobsonSpace f

/-- **(Gap B bridge, part 1)** If the closed points of a scheme locally of finite type over a
field are connected in the subspace topology, the scheme is connected. -/
theorem preconnectedSpace_of_closedPoints {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [PreconnectedSpace (closedPoints ↥X)] : PreconnectedSpace ↥X := by
  haveI := jacobsonSpace_of_locallyOfFiniteType_over_field f
  refine DenseRange.preconnectedSpace (f := ((↑) : closedPoints ↥X → ↥X)) ?_
    continuous_subtype_val
  rw [DenseRange, Subtype.range_coe_subtype]
  exact dense_iff_closure_eq.mpr (closure_closedPoints (X := ↥X))

/-- **(Gap B bridge, part 2)** Connectedness transfers along a surjective morphism of
schemes: applied to `Y ⊗ ℂ → Y ⊗ ℚ̄` this is the insensitivity of geometric connectedness
to the extension of algebraically closed fields. -/
theorem connectedSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [ConnectedSpace ↥X] : ConnectedSpace ↥Y :=
  Function.Surjective.connectedSpace (Scheme.Hom.surjective f) f.continuous

end ModularCurves
