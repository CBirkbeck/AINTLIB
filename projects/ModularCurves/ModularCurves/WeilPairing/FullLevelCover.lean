/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LevelThreeTorsor

/-!
# The full-level space as an fppf cover (WP-COVER)

The Weil-pairing descent `weilPairingCharZero` (`WeilPairing/CharZeroDescent.lean`) consumes
an fppf cover of the base trivialising `E[N]`. The natural such cover is the **full-level
space** `Y_{Γ(N)} = YFull.fullLevelSpace X N`: over it the tautological naive full level-`N`
structure trivialises `E[N]` to `(ℤ/N)²`.

This file supplies the three properties the descent needs of that cover, at **general `N`**:
finite (`YFull.isFinite_fullLevelSpaceStruct`), étale (`levelSpaceΓπ_etale`) — both already
proved — and **surjective**, which existed only as `private` `N = 3` and `N = 4` replays.
The general-`N` proof is the same argument: over a point of the base take the anchored
geometric point, produce a naive full level-`N` structure on the fibre
(`exists_isNaiveFullLevel_of_isAlgClosed`, general `N`), classify it through the
points-equivalence family (`YFull.exists_pointsEquiv_family`), and read off its image.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {R : CommRingCat.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-COVER)** The full-level structure map is surjective at general `N`, when `N` is
invertible on the base. The `N = 3` and `N = 4` cases were `private` replays in
`Moduli/LevelThreeTorsor.lean` / `Moduli/LevelFourTorsor.lean`; this is the shared
argument. -/
theorem fullLevelSpaceStruct_surjective (N : ℕ) [NeZero N]
    (hinv : IsUnit ((N : ℕ) : R)) (X : EllObj R) :
    AlgebraicGeometry.Surjective (YFull.fullLevelSpaceStruct X N) := by
  constructor
  intro y
  set t : Spec (CommRingCat.of (AlgebraicClosure (X.base.residueField y))) ⟶ X.base :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.base.residueField y)
      (AlgebraicClosure (X.base.residueField y)))) ≫ X.base.fromSpecResidueField y with ht
  have hk : ((N : ℕ) : AlgebraicClosure (X.base.residueField y)) ≠ 0 := by
    have h := hinv.map (Spec.preimage (t ≫ X.structMap)).hom
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨P, Q, hPQ⟩ := exists_isNaiveFullLevel_of_isAlgClosed
    (AlgebraicClosure (X.base.residueField y)) ((X.pullbackAlong t).curve) N hk
  obtain ⟨z, hz⟩ := (((YFull.exists_pointsEquiv_family R X N hinv).choose) t).symm
    ⟨(P, Q), hPQ⟩
  obtain ⟨pt⟩ : Nonempty
      ↥(Spec (CommRingCat.of (AlgebraicClosure (X.base.residueField y)))) := inferInstance
  refine ⟨z.base pt, ?_⟩
  have h1 : (YFull.fullLevelSpaceStruct X N).base (z.base pt) = t.base pt := by
    have h0 : (z ≫ YFull.fullLevelSpaceStruct X N).base pt = t.base pt :=
      congrArg (fun m => m.base pt) hz
    rwa [Scheme.Hom.comp_apply] at h0
  rw [h1, ht, Scheme.Hom.comp_apply]
  exact X.base.fromSpecResidueField_apply y _

end ModularCurves
