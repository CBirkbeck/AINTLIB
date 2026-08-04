/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.DetCocycle
import ModularCurves.GroupScheme.ConstSchemeSquare
import ModularCurves.GroupScheme.GLSchemeAction

/-!
# The Weil pairing over a base with a full level structure (route β, step 1)

`nonempty_weilPairing_of_root_of_trivialised` (`WeilPairing/DetCocycle.lean`) produces the pairing
over any base on which `E[N] ×_S E[N]` is trivialised, from nothing but an `N`-th root of unity —
the determinant law plays no part, because at `p = 𝟙 S` the kernel pair is degenerate.

This file supplies that trivialisation from a **full level structure**: `fullLevelIso`
(`GroupScheme/GLSchemeAction.lean`) trivialises `E[N]` for `N` invertible, and `constSchemeSqIso`
(`GroupScheme/ConstSchemeSquare.lean`) identifies the fibre square of constant schemes. The result
is the route-β entry point:

> an elliptic curve over a base carrying a full level-`N` structure, with `N` invertible and an
> `N`-th root of unity on the base, has a Weil pairing.

The determinant law re-enters only one step later, when descending from such a base to a general
one; there it is the `GL₂(ℤ/N)`-equivariance of this pairing, whose stabiliser case is
`fieldWeilPairing_det_of_galois` (`WeilPairing/PairingTransport.lean`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ} [NeZero N]

/-- **(route β, step 1)** A full level structure trivialises the *square* `E[N] ×_S E[N]`: the
two legs are trivialised by `fullLevelIso` and the resulting fibre square of constant schemes is
`constSchemeSqIso`. -/
noncomputable def fullLevelSqIso (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    pullback (E.torsionπ N) (E.torsionπ N) ≅
      constScheme S ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) :=
  have hinvπ : (E.fullLevelIso hinv L).inv ≫ constSchemeπ S (Fin 2 → ZMod N) =
      E.torsionπ N := by
    rw [Iso.inv_comp_eq]
    exact (E.fullLevelHom_torsionπ L).symm
  have hsq : IsPullback
      (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ (E.fullLevelIso hinv L).symm.hom)
      (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ (E.fullLevelIso hinv L).symm.hom)
      (constSchemeπ S (Fin 2 → ZMod N)) (constSchemeπ S (Fin 2 → ZMod N)) :=
    (IsPullback.of_hasPullback (E.torsionπ N) (E.torsionπ N)).of_iso (Iso.refl _)
      (E.fullLevelIso hinv L).symm (E.fullLevelIso hinv L).symm (Iso.refl S)
      (by simp) (by simp) (by simpa using hinvπ.symm) (by simpa using hinvπ.symm)
  hsq.isoPullback.trans
    (constSchemeSqIso S (Fin 2 → ZMod N) (Fin 2 → ZMod N))

/-- …and the trivialisation of the square is a morphism over `S`, in exactly the form
`nonempty_weilPairing_of_root_of_trivialised` consumes. -/
theorem fullLevelSqIso_hom_π (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    (E.fullLevelSqIso hinv L).hom ≫
        constSchemeπ S ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      E.torsionSqπ N := by
  rw [fullLevelSqIso, Iso.trans_hom, Category.assoc, constSchemeSqIso_hom_π,
    IsPullback.isoPullback_hom_snd_assoc, Category.assoc, Iso.symm_hom,
    (E.fullLevelIso hinv L).inv_comp_eq.mpr (E.fullLevelHom_torsionπ L).symm,
    torsionSqπ]
  exact pullback.condition.symm

/-- **(route β, step 1, THE ENTRY POINT)** An elliptic curve over a base carrying a **full
level-`N` structure**, with `N` invertible and an `N`-th root of unity on the base, admits a Weil
pairing — the DS4 register's `weilPairing` together with its `weilPairing_over` specification.

No determinant law, no descent, no cover: over such a base the pairing *is* the determinant
formula `(v, w) ↦ ζ ^ det (v, w)` read through the level structure. -/
theorem nonempty_weilPairing_of_fullLevel (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    (ζ : { a : Γ(S, (⊤ : S.Opens)) // a ^ N = 1 }) :
    ∃ e : pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N,
      e ≫ muNπ S N = E.torsionSqπ N :=
  nonempty_weilPairing_of_root_of_trivialised E N ζ (E.fullLevelSqIso hinv L)
    (E.fullLevelSqIso_hom_π hinv L)

end EllipticCurve

end ModularCurves
