/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.OrdPipeline
import ModularCurves.WeilPairing.SelfUniversal
import ModularCurves.Moduli.KeystoneGeometricPoint

/-!
# The field leaf of `e_N(x,x) = 1` (U5-AC)

Over an algebraically closed field `K` with `(N : K) ≠ 0`, the diagonal pairing value
is `1`: transport to the projective Weierstrass model along the pointed record iso of
`exists_projModelIso_of_field` (U1, `weilPairingEval_mapIso`), instantiate the
Katz–Mazur dataset through the κ-dictionary + G2′ chart machinery, and read the value
through `weilPairingEval_eq_torsionSplittingEval` (U5-L4) +
`torsionSplittingEval_self_eq_one` (U5-L5).

Stage plan (each stage replaces the trailing `sorry`):
1. model transport (DONE here);
2. the model-side instances (IsIntegral, Dedekind, Flat/IsFinite/LOFP for `[N]`);
3. the dataset (KAPPA-DICT + officiality + G2′);
4. the H-side splittings (D4-pipe) + the dictionaries (p, hxp, hT, zQm-data);
5. the L4-pin + L5-close.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ModularCurves

namespace EllipticCurve

/-- **(U5-AC, the algebraically closed field leaf)** `e_N(x, x) = 1` over an
algebraically closed field in which `N` is invertible. -/
theorem weilPairingEval_self_of_isAlgClosed {K : Type u} [Field K] [DecidableEq K]
    [IsAlgClosed K]
    (E : EllipticCurve (Spec (CommRingCat.of K))) {N : ℕ} [NeZero N]
    (hNK : (N : K) ≠ 0)
    (x : E.Point (𝟙 (Spec (CommRingCat.of K))))
    (hx : x.1 ≫ E.mulByHom N = 𝟙 _ ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(Spec (CommRingCat.of K), ⊤)) = 1 := by
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := by
    haveI : IsNoetherianRing K := inferInstance
    infer_instance
  -- stage 1: the model transport
  obtain ⟨W, hell, ψ, hψπ, hψz⟩ := exists_projModelIso_of_field E
  haveI := hell
  have hΦw : ψ.hom ≫ (modelEllipticCurve W).asOver.hom = E.asOver.hom := hψπ
  set Φ : E.asOver ≅ (modelEllipticCurve W).asOver := Over.isoMk ψ hΦw with hΦ
  have hΦη : (η[E.asOver] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.asOver) ≫ Φ.hom =
      η[(modelEllipticCurve W).asOver] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, E.one_eq_zero, (modelEllipticCurve W).one_eq_zero]
    exact (Category.assoc _ _ _).trans
      (congrArg _ (show E.zero ≫ ψ.hom = (modelEllipticCurve W).zero from hψz))
  haveI hmon : IsMonHom Φ.hom := isMonHom_of_pointed Φ.hom hΦη
  have hx' : (Point.mapIso Φ x).1 ≫ (modelEllipticCurve W).mulByHom N =
      𝟙 _ ≫ (modelEllipticCurve W).zero :=
    Point.mapIso_killedBy Φ hx
  rw [← weilPairingEval_mapIso Φ x x hx hx hx' hx']
  -- stage 2: the model-side instances
  haveI hIntP : AlgebraicGeometry.IsIntegral (projModel W) := isIntegral_projModel_u W
  haveI hFlat : Flat ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_flat N
  haveI hFin : IsFinite ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_isFinite N
  haveI hLofp : LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_locallyOfFinitePresentation N
  haveI hbcEll : ((W.baseChange K).toAffine).IsElliptic := by
    rw [EllipticCurve.baseChange_self_eq W]
    infer_instance
  haveI hDed : IsDedekindDomain
      (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve K).CoordinateRing := inferInstance
  -- stages 3–5 at the model
  sorry

end EllipticCurve

end ModularCurves
