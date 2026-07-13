/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaH
import ModularCurves.LevelStructure.Incidence

/-!
# Relative representability of the Drinfeld `Γ₁(N)` problem (KM 3.6.0, Γ₁ half)

The Drinfeld `Γ₁(N)` moduli problem `gammaOneDrinfeldProblem` is **affine over `Ell`**
(hence relatively representable), assembled — per KM 1.6.2 (`ℤ/N`-Str, no rank hypothesis,
so **no `c4`**) — from two pieces that already exist sorry-free in the library:

* **c2 (the Hom-scheme ambient, KM 1.6.1)** — `EllipticCurve.torsionPointsEquiv`: `T`-points
  of `E[N] = E.torsion N` over `t` are the `N`-torsion of `E.Point t`
  (`Hom_{S-gp}(ℤ/N, E) = E[N]`).
* **c1 (the A-Str closed subscheme, KM 1.6.2 via 1.3.7)** — `ModularCurves.exists_exactOrderLocus`:
  a closed subscheme `Z ⊆ E[N]` through which an `N`-torsion `T`-point factors **iff** it has
  Drinfeld exact order `N`.

The representing `S`-scheme is `Z.subscheme` (finite over `S`, as a closed subscheme of the
finite `E[N]`), and the functor-of-points bijection is `torsionPointsEquiv` cut down to `Z`.

`Representable` itself then follows from `ModuliProblem.representable_iff` (KM SCHOLIE 4.7.0)
together with rigidity — the same shared engine endgame the naive problems consume.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-- The exact-order locus is a closed subscheme of the finite `E[N]`, so its structure
morphism to `S` is affine (`c1`/`c2` affineness ingredient for KM SCHOLIE 4.7.0). -/
theorem exactOrderLocus_isAffineHom {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    [NeZero N] (Z : (E.torsion N).IdealSheafData) :
    IsAffineHom (Z.subschemeι ≫ E.torsionπ N) := by
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  exact inferInstance

/-- **(KM 1.6.2, `ℤ/N`-Str — no rank hypothesis, hence no `c4`)** The Drinfeld `Γ₁(N)`
moduli problem is affine over `Ell`: for each `E/S` the functor of Drinfeld exact-order-`N`
points is represented by the exact-order locus `Z ⊆ E[N]`, finite (hence affine) over `S`.
Assembled from `torsionPointsEquiv` (c2, KM 1.6.1) + `exists_exactOrderLocus` (c1). -/
theorem gammaOneDrinfeld_affineOverEll (N : ℕ) [NeZero N] :
    (gammaOneDrinfeldProblem R N).AffineOverEll := by
  intro X
  obtain ⟨Z, hZ⟩ := exists_exactOrderLocus X.curve N
  refine ⟨Z.subscheme, Z.subschemeι ≫ X.curve.torsionπ N,
    exactOrderLocus_isAffineHom X.curve N Z, ?_⟩
  sorry

end ModularCurves
