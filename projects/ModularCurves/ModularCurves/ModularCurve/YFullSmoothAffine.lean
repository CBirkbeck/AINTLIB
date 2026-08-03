/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.YFullFromYOne
import ModularCurves.Moduli.GammaOneNaiveRelRep
import ModularCurves.Moduli.Bootstrap
import ModularCurves.Moduli.LevelThreeSmooth
import ModularCurves.Moduli.GammaHClosure

/-!
# `Y(N)` is smooth and affine (WP-D2c-5 / -6)

`YFull.exists_representing_smooth_affine` (`ModularCurve/YFullRoute.lean`) asks, for
`3 ≤ N` invertible in `R`, for **some** object representing the naive full level-`N`
problem whose structure morphism is smooth and affine. Since
`YFull.smooth_affine_of_representableBy` is generic in the moduli problem, one such object
settles it for every representing object.

Two arms, because the two available inputs have different ranges.

* **`4 ≤ N` (WP-D2c-5).** `gammaOneNaive_representable` gives `Y₁(N)` with a *smooth affine*
  structure morphism (Loeffler Thm 3.4.4, via the explicit Tate-point model `yOneEllObj`),
  and `yFullCandidate_representableBy` (`ModularCurve/YFullFromYOne.lean`) exhibits
  `Y₁(N)`'s universal curve, pulled back to the completion locus of the universal
  `Γ₁`-section, as a representing object of the full-level problem. Its structure morphism
  is finite étale over `Y₁(N)`'s, hence still smooth and affine.

* **`N = 3` (WP-D2c-6).** The `Γ₁`-route cannot reach `N = 3`: `Γ₁(3)` is not rigid — the
  curve `y² + y = x³` over `ℤ[1/3, ζ₃]` has the automorphism `(x, y) ↦ (ζ₃ x, y)` fixing
  both the origin and the flex `P = (0,0)`, which has exact order `3`. No explicit model is
  needed instead: the level-3 rigidifier `universalE3Obj R` *is* a representing object of
  `gammaFullNaiveProblem R 3` (`naiveLevelThree_representable_by_affine`), its base is
  `Spec (E3ModuliRing R)`, and `E3ModuliRing R` is standard smooth of relative dimension one
  over `R` (`e3ModuliRing_isStandardSmoothOfRelativeDimension`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

variable (R : CommRingCat.{u})

/-- **(WP-D2c-5)** For `4 ≤ N` invertible in `R`, the naive full level-`N` problem is
represented by an object with smooth affine structure morphism: the universal curve over
`Y₁(N)`, pulled back to the completion locus of the universal `Γ₁(N)`-section. -/
theorem exists_representing_smooth_affine_of_four_le (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    ∃ X₀ : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X₀) ∧
      Smooth X₀.structMap ∧ IsAffineHom X₀.structMap := by
  obtain ⟨⟨rOne⟩, hsm, ha⟩ := yOne_representable_smooth_affine R N hN hinv
  set X₁ := yOneEllObj R N with hX₁
  have h : NIsInvertible X₁.base N := nIsInvertible_base R N hinv X₁
  exact exists_representing_smooth_affine_of_candidate N X₁ h _ hsm ha
    (yFullCandidate_representableBy N X₁ h _ rOne rfl hinv)

/-- **(WP-D2c-6)** For `N = 3` invertible in `R`, the level-3 rigidifier `universalE3Obj R`
represents the naive full level-3 problem, and its structure morphism — `Spec` of
`R ⟶ E3ModuliRing R` — is smooth (standard smooth of relative dimension one) and affine. -/
theorem exists_representing_smooth_affine_three (hR : IsUnit (3 : R)) :
    ∃ X₀ : EllObj R, Nonempty ((gammaFullNaiveProblem R 3).RepresentableBy X₀) ∧
      Smooth X₀.structMap ∧ IsAffineHom X₀.structMap := by
  have hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R) :=
    ⟨⟨by exact_mod_cast three_zsmul_universalE3P_of_isUnit R hR,
        by exact_mod_cast three_zsmul_universalE3Q_of_isUnit R hR⟩,
      fun k _ _ t x hx => universalE3_generation R hR k t x hx⟩
  have hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 3), IsE3Datum X L := fun X L =>
    isE3Datum_of_bridges X hR L
      (fun V Pr hM => bridgeP_holds X hR L V Pr hM)
      (fun V Pr ha₂ ha₄ ha₆ hMP p q hMQ =>
        bridgeQ_holds X hR L V Pr ha₂ ha₄ ha₆ hMP p q hMQ)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (E3ModuliRing R) :=
    e3ModuliRing_isStandardSmoothOfRelativeDimension R hR
  haveI : Algebra.IsStandardSmooth R (E3ModuliRing R) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1)
  refine ⟨universalE3Obj R, ⟨naiveLevelThreeRepresentableBy R hR hL hArb⟩, ?_, ?_⟩
  · show Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (E3ModuliRing R))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact (RingHom.smooth_algebraMap (R := R) (S := E3ModuliRing R)).mpr inferInstance
  · show IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (E3ModuliRing R))))
    infer_instance

namespace YFull

/-- **([YF-GEOM] = KM Cor 4.7.1's geometric computation; WP-D2c-7)** SOME representing
object of `[Γ(N)]` has smooth affine base over `Spec R`. KM 4.7.1 (verbatim, p. 116): *"Any
relatively representable moduli problem 𝒫 which is affine and etale over (Ell), and rigid,
is representable by a smooth affine curve over Z."*

Relocated here from `ModularCurve/YFullRoute.lean` (see the note at the end of that file's
`YFull` section) and split by range: `4 ≤ N` goes through `Y₁(N)`, `N = 3` through the
level-3 rigidifier. `Γ₁(3)` is not rigid — `y² + y = x³` has `(x, y) ↦ (ζ₃x, y)` fixing the
flex `(0,0)` of exact order 3 — so the two arms are genuinely needed. -/
theorem exists_representing_smooth_affine (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ∃ X₀ : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X₀) ∧
      Smooth X₀.structMap ∧ IsAffineHom X₀.structMap := by
  rcases eq_or_lt_of_le hN with hN3 | hN4
  · subst hN3
    exact exists_representing_smooth_affine_three R (by exact_mod_cast hinv)
  · exact exists_representing_smooth_affine_of_four_le R N hN4 hinv

/-- **(T-E9 ASSEMBLY = KM Cor 4.7.2; the bridge into
`ModularCurves.gammaFullNaive_representable`)** For `N ≥ 3` invertible in `R`: `[Γ(N)]` is
rigid and representable, and every representing object has smooth affine base over
`Spec R`. Statement shape is VERBATIM that of the held
`Moduli/Representability.lean:gammaFullNaive_representable`.

The rigid-and-representable half is `gammaFullNaive_rigid_and_representable`
(`Moduli/GammaHClosure.lean`, axiom-verified), not the older `gammaFullNaive_rigid` /
`gammaFullNaive_representable_of_engine` pair — those two still carry the engine's `sorry`s
and are exactly what kept this assembly from being axiom-verified. -/
theorem gammaFullNaive_representable_assembly (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ((gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable) ∧
      ∀ X : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by
  refine ⟨gammaFullNaive_rigid_and_representable R N (by exact_mod_cast hN) hinv,
    fun X hX => ?_⟩
  obtain ⟨X₀, ⟨r₀⟩, hs, ha⟩ := exists_representing_smooth_affine R N hN hinv
  exact smooth_affine_of_representableBy R r₀ hs ha X hX

end YFull

end ModularCurves
