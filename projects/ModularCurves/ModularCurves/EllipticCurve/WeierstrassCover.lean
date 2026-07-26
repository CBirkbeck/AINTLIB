/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.GroupLaw

/-!
# The Weierstrass cover of the base (Gap A, (LOCAL-SQUARE) step 1)

`LocallyWeierstrass` is phrased pointwise: *every* point of the base has an affine
neighbourhood carrying a Weierstrass model. The descent argument for the relative theorem of
the square needs it packaged as an **indexed cover** `U : ι → S.Opens` with `iSup U = ⊤`,
because that is the shape `ModularCurves.nonempty_unitObj_iso_of_normalized_glue` consumes.

`LocallyWeierstrass.exists_cover` does the repackaging (indexing by the points of `S`, via
choice). Downstream, the theorem-of-the-square identity is proved on each `U i` using the
Weierstrass model there, and glued by rigidified descent.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace ModularCurves

/-- **The Weierstrass cover.** The affine opens supplied by `LocallyWeierstrass`, indexed by
the points of the base, form an open cover carrying Weierstrass models. -/
theorem LocallyWeierstrass.exists_cover {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E}
    {hz : z ≫ π = 𝟙 S} (h : LocallyWeierstrass π z hz) :
    ∃ U : S → S.Opens, iSup U = ⊤ ∧
      ∀ s : S, s ∈ U s ∧ IsAffineOpen (U s) ∧
        ∃ W : WeierstrassCurve Γ(S, U s), W.IsElliptic ∧
          Nonempty (pullback π (U s).ι ≅ projModel W) := by
  classical
  choose U hsU W hell e _ _ using h
  refine ⟨fun s => (U s).1, ?_, fun s => ⟨hsU s, (U s).2, W s, hell s, ⟨e s⟩⟩⟩
  rw [eq_top_iff]
  intro s _
  exact Opens.mem_iSup.mpr ⟨s, hsU s⟩

/-- The Weierstrass cover of the base of a base-changed elliptic curve: every elliptic curve
is locally Weierstrass, and that survives base change, so the base of `E ×_S T ⟶ T` is
covered by opens carrying Weierstrass models. This is the cover the descent runs on. -/
theorem EllipticCurve.exists_weierstrass_cover_baseChange {S : Scheme.{u}}
    (E : EllipticCurve S) {T : Scheme.{u}} (t : T ⟶ S) :
    ∃ U : T → T.Opens, iSup U = ⊤ ∧
      ∀ x : T, x ∈ U x ∧ IsAffineOpen (U x) ∧
        ∃ W : WeierstrassCurve Γ(T, U x), W.IsElliptic ∧
          Nonempty (pullback (pullback.snd E.π t) (U x).ι ≅ projModel W) :=
  (E.localModel.baseChange t).exists_cover

end ModularCurves
