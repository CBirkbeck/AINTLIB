/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FibrePointDict
import ModularCurves.WeilPairing.GaloisFieldPairing
import ModularCurves.Moduli.ChartPointsGalois

/-!
# Galois equivariance at a geometric fibre (DS4 M1c, nodes D–E)

Node D assembles the two chart naturality statements of `Moduli/ChartPointsGalois.lean`
into naturality of `chartAffinePointEquiv`, and node E transports
`fieldWeilPairing_galois` along it, giving `σ`-equivariance of `fibreWeilPairing` — the
pairing on *scheme* points that the étale-descent engine consumes.

As throughout this stream, hypotheses are stated on **underlying morphisms**: the
scheme-level Galois action is `P ↦ Spec σ ≫ P`, and `Spec σ ≫ t = t` only
propositionally, so carrying it in a dependent type is what makes these arguments
expensive.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits WeierstrassCurve

namespace ModularCurves

/-! ## Node D — `chartAffinePointEquiv` -/

section ChartAffine

open LocalPresentation

variable {S : Scheme.{u}} {E : EllipticCurve S} {V : S.affineOpens}
  (Pr : LocalPresentation E.toEllipticCurveGeom V)
  (K : Type u) [Field K] [DecidableEq K] [Algebra Γ(S, V.1) K]

/-- **(D ★)** The geometric-fibre point dictionary carries the scheme-level Galois action
`P ↦ Spec σ ≫ P` to mathlib's coordinatewise `Affine.Point.map σ`. -/
theorem chartAffinePointEquiv_of_coe_eq (σ : K ≃ₐ[Γ(S, V.1)] K)
    (P Q : letI := Pr.elliptic
      E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V))
    (hQ : (Q.1 : Spec (CommRingCat.of K) ⟶ E.E) =
      Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫ (P.1 : Spec (CommRingCat.of K) ⟶ E.E)) :
    letI := Pr.elliptic
    chartAffinePointEquiv Pr K Q =
      WeierstrassCurve.Affine.Point.map (W' := Pr.W) (F := K) (K := K)
        (σ : K →ₐ[Γ(S, V.1)] K) (chartAffinePointEquiv Pr K P) := by
  letI := Pr.elliptic
  -- `Spec σ` fixes the geometric point
  have hσt : Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun c => σ.commutes c)
  -- the same point, read over the moved base
  refine modelPointAddEquiv_of_coe_eq Pr.W σ (chartPointsEquiv Pr _ P)
    (chartPointsEquiv Pr _ Q) ?_
  refine Eq.trans (chartPointsEquiv_congr_base Pr hσt.symm Q
    (⟨Q.1, by rw [hσt]; exact Q.2⟩ :
      E.Point ((Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K))) ≫ chartρ V)) rfl) ?_
  exact chartPointsEquiv_restrict_coe Pr _ _ P ⟨Q.1, by rw [hσt]; exact Q.2⟩ hQ

end ChartAffine

end ModularCurves
