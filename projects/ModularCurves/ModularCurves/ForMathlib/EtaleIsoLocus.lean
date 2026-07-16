/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import ModularCurves.ForMathlib.FinrankComp

/-!
# Rank loci of finite flat morphisms are clopen; the rank-one locus is an iso-locus

For a finite flat locally finitely presented `f : X ⟶ Y`:

* `isClopen_finrank_eq` — each rank locus `{y | f.finrank y = n}` is clopen
  (the rank function is locally constant, mathlib `isLocallyConstant_finrank`);
* `isIso_morphismRestrict_of_finrank_eq_one` — over an open where the rank is `1`, the
  restriction of `f` is an isomorphism (`isIso_iff_finrank_eq` + `finrank_morphismRestrict`).

This is the [GHA3 β3] core (KM 1.6.7): the locus where a morphism of finite étale `T`-schemes
is an isomorphism — e.g. where a tuple of torsion sections is a *full set* of sections — is
clopen, with the restriction an iso. Étale enters only through `LocallyOfFinitePresentation`
and flatness; no group structure is needed.
-/

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- **(β3-core, rank loci are clopen)** Each rank locus of a finite flat locally finitely
presented morphism is clopen: the rank function is locally constant. -/
theorem isClopen_finrank_eq (f : X ⟶ Y) [Flat f] [IsFinite f] [LocallyOfFinitePresentation f]
    (n : ℕ) : IsClopen {y : Y | f.finrank y = n} := by
  have h := f.isLocallyConstant_finrank
  exact ⟨IsLocallyConstant.isClosed_fiber h n, IsLocallyConstant.isOpen_fiber h n⟩

/-- **(β3-core, the rank-one locus is an iso-locus)** Over an open on which the fibre rank of a
finite flat locally finitely presented morphism is `1`, its restriction is an isomorphism. -/
theorem isIso_morphismRestrict_of_finrank_eq_one (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f] (U : Y.Opens) (hU : ∀ y : U, f.finrank y.1 = 1) :
    IsIso (f ∣_ U) := by
  haveI : Flat (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹Flat f› U
  haveI : IsFinite (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsFinite f› U
  haveI : LocallyOfFinitePresentation (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict ‹LocallyOfFinitePresentation f› U
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext y
  rw [Scheme.Hom.finrank_morphismRestrict f U y, hU y]
  rfl

end AlgebraicGeometry
