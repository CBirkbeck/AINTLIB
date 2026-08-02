/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.NaiveGammaOneLocus
import ModularCurves.ModularCurve.YFullToYOne
import ModularCurves.Moduli.QuotientProblem

/-!
# The candidate `Y(N)` built over `Y₁(N)` (WP-D2c)

`YFull.exists_representing_smooth_affine` asks for **some** object representing the naive
full level-`N` problem whose structure morphism is smooth and affine. Since
`YFull.smooth_affine_of_representableBy` is generic in the moduli problem, exhibiting one
such object settles it for all of them.

The object to exhibit is the universal curve over `Y₁(N)` pulled back to the full-level
locus:

  `X₀ := X₁.pullbackAlong (X₁.curve.fullLevelLocusπ N h)`,

where `X₁` represents `gammaOneNaiveProblem` and is already known smooth and affine
(`gammaOneNaive_representable`, axiom-verified).

This file proves the **free half** (WP-D2c-2): `X₀.structMap` is smooth and affine, because
it factors as a finite étale morphism followed by a smooth affine one. Nothing here needs
new mathematics — `Etale ⟹ Smooth` is an instance, and `Smooth`, `IsAffineHom` and
`IsFinite` all compose.

What remains (WP-D2c-3) is that `X₀` *represents* the full-level problem; the functorial
half of that is `yFullToYOneFibreEquiv` (WP-D2b) and the relative half is
`fullLevelLocusPointsEquiv`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-- **(WP-D2c-1)** The candidate representing object for the naive full level-`N` problem:
the universal curve over a `Γ₁(N)`-object, pulled back to its full-level locus. -/
noncomputable def yFullCandidate (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) : EllObj R :=
  X₁.pullbackAlong (X₁.curve.fullLevelLocusπ N h)

@[simp] theorem yFullCandidate_base (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) :
    (yFullCandidate N X₁ h).base = X₁.curve.fullLevelLocus N h := rfl

@[simp] theorem yFullCandidate_structMap (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) :
    (yFullCandidate N X₁ h).structMap =
      X₁.curve.fullLevelLocusπ N h ≫ X₁.structMap := rfl

/-- **(WP-D2c-2)** The candidate's structure morphism is smooth: it is a finite étale
morphism followed by a smooth one. -/
theorem yFullCandidate_structMap_smooth (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (hsm : Smooth X₁.structMap) :
    Smooth (yFullCandidate N X₁ h).structMap := by
  haveI : Etale (X₁.curve.fullLevelLocusπ N h) := X₁.curve.fullLevelLocusπ_etale N h
  haveI : Smooth (X₁.curve.fullLevelLocusπ N h) := inferInstance
  haveI := hsm
  rw [yFullCandidate_structMap]
  exact MorphismProperty.comp_mem _ _ _ inferInstance hsm

/-- **(WP-D2c-2)** The candidate's structure morphism is affine: it is a finite morphism
followed by an affine one. -/
theorem yFullCandidate_structMap_isAffineHom (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) [IsAffineHom X₁.structMap] :
    IsAffineHom (yFullCandidate N X₁ h).structMap := by
  haveI : IsFinite (X₁.curve.fullLevelLocusπ N h) := X₁.curve.fullLevelLocusπ_isFinite N h
  haveI hfa : IsAffineHom (X₁.curve.fullLevelLocusπ N h) := inferInstance
  rw [yFullCandidate_structMap]
  -- the composition instance does not fire through the `abbrev`, so inline its proof
  refine ⟨fun U hU => ?_⟩
  haveI := hfa
  exact (hU.preimage X₁.structMap).preimage (X₁.curve.fullLevelLocusπ N h)

/-- **(WP-D2c-2)** Both at once — the shape `smooth_affine_of_representableBy` consumes. -/
theorem yFullCandidate_smooth_affine (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (hsm : Smooth X₁.structMap)
    (ha : IsAffineHom X₁.structMap) :
    Smooth (yFullCandidate N X₁ h).structMap ∧
      IsAffineHom (yFullCandidate N X₁ h).structMap :=
  haveI := ha
  ⟨yFullCandidate_structMap_smooth N X₁ h hsm,
    yFullCandidate_structMap_isAffineHom N X₁ h⟩

/-! ### `yFullCandidate` represents the full-level problem (WP-D2c-3)

The single remaining step of the D-chain. Stated here so the interface is fixed and
type-checked; the proof is the one piece still open.

**Proof plan.** Write `B := X₁.curve.fullLevelLocus N h` and `π_B := fullLevelLocusπ`.

*Forward.* Given `u : T ⟶ yFullCandidate N X₁ h`, its base map is `u.baseHom : T.base ⟶ B`,
and `u ≫ X₁.pullbackAlongπ π_B : T ⟶ X₁` has base map `u.baseHom ≫ π_B`. Feeding
`⟨u.baseHom, _⟩` to `fullLevelLocusPointsEquiv` yields a naive full level structure on
`X₁.curve.baseChange (u.baseHom ≫ π_B) = (X₁.pullbackAlong (u.baseHom ≫ π_B)).curve`;
transport it to `T.curve` along the isomorphism `toPullbackAlong` supplies
(`Moduli/QuotientProblem.lean:73`, with `toPullbackAlong_pullbackAlongπ` as its defining
property).

*Backward.* Given a full level structure `(P, Q)` on `T`, its first member is a naive
`Γ₁(N)`-structure by `isNaiveGammaOne_of_isNaiveFullLevel` (WP-D1a), so
`v := rOne.homEquiv.symm ⟨P, _⟩ : T ⟶ X₁` classifies it. Transporting `(P, Q)` along
`toPullbackAlong v` and applying `fullLevelLocusPointsEquiv.symm` gives a lift
`T.base ⟶ B` over `v.baseHom`; combining with `toPullbackAlong v` produces
`T ⟶ yFullCandidate N X₁ h`.

*Round trips* are the two `Equiv` laws of `fullLevelLocusPointsEquiv` together with
`toPullbackAlong_pullbackAlongπ`; *naturality* is
`fullLevelLocusPointsEquiv`'s naturality (`Moduli/LevelLocusNatural.lean`) plus
functoriality of `toPullbackAlong`.

Note `rOne` is a hypothesis: the candidate is built from a `Γ₁(N)`-representing object, and
the backward direction is exactly where that representability is consumed. -/
theorem yFullCandidate_representableBy (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N)
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy X₁)
    (hinv : ∀ (X : EllObj R) (k : Type u) [Field k] [IsAlgClosed k],
      (Spec (CommRingCat.of k) ⟶ X.base) → (N : k) ≠ 0) :
    Nonempty ((gammaFullNaiveProblem R N).RepresentableBy (yFullCandidate N X₁ h)) := by
  sorry

/-- **(WP-D2c-4)** Given WP-D2c-3, every object representing the naive full level-`N`
problem has smooth affine structure morphism — which is exactly
`YFull.exists_representing_smooth_affine`. -/
theorem exists_representing_smooth_affine_of_candidate (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N)
    (hsm : Smooth X₁.structMap) (ha : IsAffineHom X₁.structMap)
    (hrep : Nonempty ((gammaFullNaiveProblem R N).RepresentableBy (yFullCandidate N X₁ h))) :
    ∃ X₀ : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X₀) ∧
      Smooth X₀.structMap ∧ IsAffineHom X₀.structMap :=
  haveI := ha
  ⟨yFullCandidate N X₁ h, hrep, yFullCandidate_structMap_smooth N X₁ h hsm,
    yFullCandidate_structMap_isAffineHom N X₁ h⟩

end ModularCurves
