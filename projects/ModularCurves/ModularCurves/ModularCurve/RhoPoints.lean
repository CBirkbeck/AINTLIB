/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.RhoSmooth

/-!
# `T`-points of the representing curve as pairs `(E, α)`

**[T-YR-7a/7b]** For a representing object `X` of `rhoProblem D`, a `T`-point of
`X.base` over `ℚ` gives an elliptic curve over `T` (the pullback of the universal
curve) together with a ρ-level structure, and conversely. These are the two maps
underlying the `Quot`-points clause of `RepresentsYRho`; well-definedness on
`Quot`-classes (T-YR-7c) and the roundtrips (T-YR-7d) are separate.
-/

noncomputable section

namespace ModularCurves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

variable {N : ℕ} [NeZero N]

open scoped FintypeCatDiscrete in
/-- **[T-YR-7a]** A `T`-point of the representing curve, over `ℚ`, yields a pair
`(E, α)`: the pullback of the universal curve with its ρ-level structure. -/
def pointToPair (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (h : { h : T ⟶ X.base // h ≫ X.structMap = sT }) :
    Σ E : EllipticCurve T, RhoLevelStructure D sT E :=
  ⟨(X.pullbackAlong h.1).curve,
    cast (congrArg (fun t => RhoLevelStructure D t (X.pullbackAlong h.1).curve) h.2)
      (r.homEquiv (X.pullbackAlongπ h.1) :
        RhoLevelStructure D (h.1 ≫ X.structMap) (X.pullbackAlong h.1).curve)⟩

open scoped FintypeCatDiscrete in
/-- **[T-YR-7b]** A pair `(E, α)` over `T` yields a `T`-point of the representing
curve over `ℚ`: the base component of its classifying morphism. -/
def pairToPoint (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (a : Σ E : EllipticCurve T, RhoLevelStructure D sT E) :
    { h : T ⟶ X.base // h ≫ X.structMap = sT } :=
  ⟨(r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, a.1⟩) from a.2)).baseHom,
    (r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, a.1⟩) from a.2)).base_w⟩

open scoped FintypeCatDiscrete in
/-- **[T-YR-7d, first roundtrip]** Classifying the pair attached to a point returns
the point. -/
theorem pairToPoint_pointToPair (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (h : { h : T ⟶ X.base // h ≫ X.structMap = sT }) :
    pairToPoint D r sT (pointToPair D r sT h) = h := by
  obtain ⟨h, rfl⟩ := h
  apply Subtype.ext
  show (r.homEquiv.symm (r.homEquiv (X.pullbackAlongπ h))).baseHom = h
  rw [Equiv.symm_apply_apply]
  rfl

open scoped FintypeCatDiscrete in
/-- **[T-YR-7d, second roundtrip, structure part]** The universal structure pulled
back along the classifying morphism of `(E, α)` is `α` itself: the canonical
comparison `E ≅ (X.pullbackAlong h).curve` (where `h` is the classifying point)
carries the point's structure to `α`. This is the `Quot`-relation witness for the
reverse roundtrip. -/
theorem pull_homEquiv_pullbackAlongπ (D : GaloisRepData N)
    {X : EllObj (CommRingCat.of ℚ)} (r : (rhoProblem D).RepresentableBy X)
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (E : EllipticCurve T) (α : RhoLevelStructure D sT E) :
    RhoLevelStructure.pull D
        (EllObj.toPullbackAlong
          (r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, E⟩) from α)))
        (r.homEquiv (X.pullbackAlongπ
          (r.homEquiv.symm
            (show (rhoProblem D).obj (op ⟨T, sT, E⟩) from α)).baseHom)) = α := by
  set u := r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, E⟩) from α) with hu
  have h := r.homEquiv_comp (EllObj.toPullbackAlong u) (X.pullbackAlongπ u.baseHom)
  rw [EllObj.toPullbackAlong_pullbackAlongπ u, hu, Equiv.apply_symm_apply] at h
  exact h.symm

end ModularCurves

end
