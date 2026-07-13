/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.ForMathlib.EtaleFieldCount
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Point count of a finite étale scheme over a separably closed field

The scheme-level companion to `natCard_primeSpectrum_eq_finrank`: a finite étale scheme over a
separably closed field `k` has exactly `finrank`-many topological points. This is the reduced-fibre
point count (KM 3.7.1) at the scheme level, used for the Y(N) `[YF-⊆]` distinctness argument.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Scheme-level point count.** For `A` an essentially-finite-type formally-étale algebra over a
separably closed field `k`, the affine scheme `Spec A` has exactly `finrank k A` topological
points. -/
theorem natCard_spec_carrier_eq_finrank (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.EssFiniteType k A] [Algebra.FormallyEtale k A] [IsSepClosed k] :
    Nat.card ↥(Spec (CommRingCat.of A)) = Module.finrank k A :=
  Algebra.FormallyEtale.natCard_primeSpectrum_eq_finrank k A

/-- The source of a finite morphism to an affine scheme is affine (the affineness step of the
finite-étale point count for the Y(N) torsion fibre). -/
theorem isAffine_source_of_isFinite {k : Type u} [Field k] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (CommRingCat.of k)) [IsFinite f] : IsAffine Z :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (f := f)).mp inferInstance

end AlgebraicGeometry
