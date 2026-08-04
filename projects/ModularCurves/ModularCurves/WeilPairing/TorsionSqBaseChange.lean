/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.CharZeroDescent

/-!
# The torsion square commutes with base change (route β, the descent's plumbing)

`WeilPairingLocalData` asks for a pairing on `pullback (E.torsionSqπ N) p` — the base change of the
Weil-pairing source along the trivialising cover. `fullLevelPairing`
(`WeilPairing/FullLevelPairing.lean`) instead produces a pairing on
`pullback ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N)` — the Weil-pairing source of
the base-changed curve. The two are canonically identified, and this file supplies that:

`isPullback_torsionSq_baseChange` says the comparison map `pullback.map` of the two torsion
projections makes the torsion square cartesian over `p`, whence `torsionSqBaseChangeIso`.

The proof is pure pullback pasting on top of `torsion_baseChange_isPullback`
(`EllipticCurve/TorsionFibre.lean`), in two steps:

* pasting the (flipped) standard square of `(E ×_S S')[N] ×_{S'} (E ×_S S')[N]` horizontally with
  the torsion base-change square exhibits the torsion square of the base change as
  `(E ×_S S')[N] ×_S E[N]`;
* `IsPullback.of_right` against the (flipped) standard square of `E[N] ×_S E[N]` turns that into
  the *first-projection* square, which pastes **vertically** with the torsion base-change square to
  give the statement about `torsionSqπ`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) {S' : Scheme.{u}} (p : S' ⟶ S)

/-- The comparison map from the torsion square of the base-changed curve to the torsion square of
the original: `torsionBaseChangeHom` on both factors. -/
noncomputable def torsionSqBaseChangeHom :
    pullback ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ⟶
      pullback (E.torsionπ N) (E.torsionπ N) :=
  pullback.map _ _ _ _ (E.torsionBaseChangeHom N p) (E.torsionBaseChangeHom N p) p
    (E.torsion_baseChange_isPullback N p).w.symm (E.torsion_baseChange_isPullback N p).w.symm

@[reassoc (attr := simp)]
theorem torsionSqBaseChangeHom_fst :
    E.torsionSqBaseChangeHom N p ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) =
      pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ≫
        E.torsionBaseChangeHom N p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem torsionSqBaseChangeHom_snd :
    E.torsionSqBaseChangeHom N p ≫ pullback.snd (E.torsionπ N) (E.torsionπ N) =
      pullback.snd ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ≫
        E.torsionBaseChangeHom N p :=
  pullback.lift_snd _ _ _

/-- **(route β plumbing, the intermediate square)** The torsion square of the base change, read
against the *first* projections: the comparison map is cartesian over `torsionBaseChangeHom`.

Geometrically this is `(E_{S'}[N] ×_{S'} E_{S'}[N]) = E_{S'}[N] ×_{E[N]} (E[N] ×_S E[N])`. -/
theorem isPullback_torsionSq_baseChange_fst :
    IsPullback (E.torsionSqBaseChangeHom N p)
      (pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N))
      (pullback.fst (E.torsionπ N) (E.torsionπ N)) (E.torsionBaseChangeHom N p) := by
  have hbc := E.torsion_baseChange_isPullback N p
  have hbig :
      IsPullback (pullback.snd ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ≫
          E.torsionBaseChangeHom N p)
        (pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N))
        (E.torsionπ N) ((E.baseChange p).torsionπ N ≫ p) :=
    (IsPullback.of_hasPullback ((E.baseChange p).torsionπ N)
      ((E.baseChange p).torsionπ N)).flip.paste_horiz hbc
  have hs : IsPullback
      (E.torsionSqBaseChangeHom N p ≫ pullback.snd (E.torsionπ N) (E.torsionπ N))
      (pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N))
      (E.torsionπ N) (E.torsionBaseChangeHom N p ≫ E.torsionπ N) := by
    rw [E.torsionSqBaseChangeHom_snd N p, hbc.w]
    exact hbig
  exact IsPullback.of_right hs (E.torsionSqBaseChangeHom_fst N p)
    ((IsPullback.of_hasPullback (E.torsionπ N) (E.torsionπ N)).flip)

/-- **(route β plumbing, THE RESULT)** The torsion square commutes with base change: the
comparison map makes the square cartesian over the cover, *for the structure morphisms
`torsionSqπ`*.

This is `isPullback_torsionSq_baseChange_fst` pasted vertically with the torsion base-change
square, since `torsionSqπ = pullback.fst ≫ torsionπ` on both sides. -/
theorem isPullback_torsionSq_baseChange :
    IsPullback (E.torsionSqBaseChangeHom N p) ((E.baseChange p).torsionSqπ N)
      (E.torsionSqπ N) p :=
  (E.isPullback_torsionSq_baseChange_fst N p).paste_vert
    (E.torsion_baseChange_isPullback N p)

/-- …hence the base change of the Weil-pairing source along the cover *is* the Weil-pairing source
of the base-changed curve. This is the identification along which `fullLevelPairing` on the cover
becomes the `pairing` field of a `WeilPairingLocalData`. -/
noncomputable def torsionSqBaseChangeIso :
    pullback (E.torsionSqπ N) p ≅
      pullback ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) :=
  (E.isPullback_torsionSq_baseChange N p).isoPullback.symm

/-! ### Torsion points and base change (route β, item (A) step 1)

The revised item (A) needs the base-change compatibility of `fullLevelPairing`, whose heart is this:
the torsion point of the base-changed curve determined by a *pulled-back* section maps, under
`torsionBaseChangeHom`, to the torsion point of the original curve determined by that section. -/

/-- **(route β, item (A) step 1, the core)** `torsionBaseChangeHom` carries the torsion point of the
base-changed curve cut out by `Point.asSection σ x` to the torsion point of `E` cut out by `x`.

`pullback.hom_ext` splits this into the two legs of `E.torsion N = pullback (E.mulByHom N) E.zero`:
the `torsionι` leg is `torsionBaseChangeHom_torsionι` then `pointToTorsion_torsionι` then
**`Point.asSection_val_fst`** (the tree's own computation rule — `pullback.lift_fst` does *not* match
here, because `Point.asSection`'s lift and `torsionBaseChangeHom_torsionι`'s `pullback.fst E.π σ`
arrive by different instance paths), and the `torsionπ` leg is the same with `_torsionπ`.

Note also that `← Category.assoc` fails on these goals with a *type-correctness under implicit
transparency* note; `(Category.assoc _ _ _).symm.trans` is the working substitute. -/
theorem pointToTorsion_asSection_torsionBaseChangeHom {T' : Scheme.{u}} (σ : T' ⟶ S)
    (x : E.Point σ) (hx : (x : T' ⟶ E.E) ≫ E.mulByHom N = σ ≫ E.zero)
    (hy : ((EllipticCurve.Point.asSection E σ x : (E.baseChange σ).Point (𝟙 T')) :
        T' ⟶ (E.baseChange σ).E) ≫ (E.baseChange σ).mulByHom N =
      (𝟙 T') ≫ (E.baseChange σ).zero) :
    (E.baseChange σ).pointToTorsion (EllipticCurve.Point.asSection E σ x) hy ≫
        E.torsionBaseChangeHom N σ =
      E.pointToTorsion x hx := by
  refine pullback.hom_ext ?_ ?_
  · show _ ≫ E.torsionι N = _ ≫ E.torsionι N
    simp only [Category.assoc, E.torsionBaseChangeHom_torsionι N σ]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [(E.baseChange σ).pointToTorsion_torsionι (EllipticCurve.Point.asSection E σ x) hy,
      EllipticCurve.Point.asSection_val_fst, E.pointToTorsion_torsionι x hx]
  · show _ ≫ E.torsionπ N = _ ≫ E.torsionπ N
    simp only [Category.assoc, E.torsionBaseChangeHom_torsionπ N σ]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [(E.baseChange σ).pointToTorsion_torsionπ (EllipticCurve.Point.asSection E σ x) hy,
      Category.id_comp]
    exact (E.pointToTorsion_torsionπ x hx).symm

end EllipticCurve

end ModularCurves
