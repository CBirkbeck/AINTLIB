/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.NaiveGammaOneLevel
import ModularCurves.Moduli.LevelLocusNatural

/-!
# `[Γ₁(N)]` is relatively representable, affine and étale over `(Ell)` (WP-D1c-coarse)

The naive `Γ₁(N)` locus of `GroupScheme/NaiveGammaOneLocus.lean` relatively represents
`gammaOneNaiveProblem`, and does so by a finite étale morphism.

Two things make this short. First, `(X.pullbackAlong g).curve` is *definitionally*
`X.curve.baseChange g` (`Moduli/EllCategory.lean:99`), so the classifying equivalence
`naiveGammaOneLocusPointsEquiv` already has the target the `AffineOverEll` predicate wants —
no transport is needed. Second, the naturality square reduces, via `section_ext_comp_fst`,
to the carrier-level identity `naiveGammaOneLocusPointsEquiv_natural`, exactly as
`Moduli/LevelLocusNatural.lean` does it for the full-level case.

This is the last piece before `Y(N) ⟶ Y₁(N)` can be shown finite étale on *representing
objects*, which transports `Y₁(N)`'s known smoothness (`gammaOneNaive_representable`) to
`Y(N)` and closes `YFull.exists_representing_smooth_affine`.

Throughout the *naive* locus is used, never `levelSpaceΓ₁` — the latter is built from the
Drinfeld `exists_exactOrderLocus` and would re-introduce the still-open register box T-D6,
whereas `gammaOneNaiveProblem` is stated with `IsNaiveGammaOne` and needs none of it.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

-- As in `Moduli/LevelLocusNatural.lean:27`: `(X.pullbackAlong g).curve` and
-- `X.curve.baseChange g` are definitionally equal but not syntactically, and `rw` needs to
-- see through the coercion. (A transparency option, not a heartbeat bump.)
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

namespace EllObj

variable {R : CommRingCat.{u}}

/-- **(WP-D1c-coarse)** The `Γ₁`-analogue of `fullLevelLocusPointsEquiv_pullSection_fst`:
the locus dictionary commutes with the base-change comparison. -/
theorem naiveGammaOneLocusPointsEquiv_pullSection (X : EllObj R) (N : ℕ) [NeZero N]
    (h : NIsInvertible X.base N) {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (w : { h' : T ⟶ X.curve.naiveGammaOneLocus N h //
      h' ≫ X.curve.naiveGammaOneLocusπ N h = g }) :
    ((X.curve.naiveGammaOneLocusPointsEquiv N h (k ≫ g)
        ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩).1 :
          (X.pullbackAlong (k ≫ g)).curve.Section) =
      EllHom.pullSection R (X.pullbackAlongMap g k)
        ((X.curve.naiveGammaOneLocusPointsEquiv N h g w).1 :
          (X.pullbackAlong g).curve.Section) := by
  refine section_ext_comp_fst X ?_
  rw [pullSection_pullbackAlongMap_comp_fst X g k]
  exact X.curve.naiveGammaOneLocusPointsEquiv_natural N h g k w

end EllObj

variable (R : CommRingCat.{u})

/-- **(WP-D1c-coarse)** `N` invertible in the base ring is `N` invertible on the base
scheme of any `Ell/R`-object. -/
theorem nIsInvertible_base (N : ℕ) (hinv : IsUnit (N : R)) (X : EllObj R) :
    NIsInvertible X.base N := by
  have h0 : NIsInvertible (Spec R) N := by
    rw [NIsInvertible]
    have hh := hinv.map (Scheme.ΓSpecIso R).inv.hom
    rwa [map_natCast] at hh
  exact h0.of_hom X.structMap

/-- **(WP-D1c-coarse)** The naive `Γ₁(N)` problem is affine over `(Ell)`, relatively
represented by the naive `Γ₁(N)` locus — which is finite étale over the base, so in
particular the structure morphism is affine.

The `Γ₁`-analogue of `gammaFullNaive_affineOverEll`, built on the *naive* locus rather than
the Drinfeld one, so that register box T-D6 stays out of the dependency graph. -/
theorem gammaOneNaive_affineOverEll (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).AffineOverEll := by
  intro X
  have h : NIsInvertible X.base N := nIsInvertible_base R N hinv X
  haveI : IsFinite (X.curve.naiveGammaOneLocusπ N h) :=
    X.curve.naiveGammaOneLocusπ_isFinite N h
  refine ⟨X.curve.naiveGammaOneLocus N h, X.curve.naiveGammaOneLocusπ N h, inferInstance,
    fun {T} g => X.curve.naiveGammaOneLocusPointsEquiv N h g, ?_⟩
  intro T T' g k w
  exact Subtype.ext (X.naiveGammaOneLocusPointsEquiv_pullSection N h g k w)

/-- **(WP-D1c-coarse)** …hence relatively representable. -/
theorem gammaOneNaive_relativelyRepresentable (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).RelativelyRepresentable :=
  (gammaOneNaive_affineOverEll R N hinv).relativelyRepresentable

end ModularCurves
