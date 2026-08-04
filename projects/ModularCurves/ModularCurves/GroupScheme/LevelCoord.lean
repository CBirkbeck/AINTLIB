/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.GLSchemeAction

/-!
# Coordinates of a torsion point in a full level basis (route β, the transition)

The last unwritten input of route β is the **transition** between two full level structures on the
kernel pair of a trivialising cover: `hdet`'s two readings `vw.1`, `vw.2` are the labels of one and
the same pair of torsion points in two different level bases, and to compare their determinants one
needs the matrix relating the bases.

That matrix is read off coordinate by coordinate, and this file supplies the coordinate map: a
torsion point over `T`, transported through `fullLevelIso`, becomes a `T`-point of the constant
scheme, i.e. a locally constant `(ℤ/N)²`-valued function — its coordinate vector in the basis.

`levelCoord_sigmaι` is the computation rule that makes the map usable: the coordinate vector of the
basis combination labelled `v` is the constant function `v`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ} [NeZero N]

/-- `fullLevelIso.inv` followed by the structure map of the constant scheme is the structure map of
the torsion — the inverse form of `fullLevelHom_torsionπ`. -/
@[reassoc]
theorem fullLevelIso_inv_constSchemeπ (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    (E.fullLevelIso hinv L).inv ≫ constSchemeπ S (Fin 2 → ZMod N) = E.torsionπ N := by
  rw [Iso.inv_comp_eq]
  exact (E.fullLevelHom_torsionπ L).symm

/-- **(route β, the transition's ingredient)** The coordinate vector of a `T`-point of `E[N]` in a
full level basis: transport the point through `fullLevelIso` into the constant scheme and read the
resulting locally constant `(ℤ/N)²`-valued label. -/
noncomputable def levelCoord (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    {T : Scheme.{u}} {g : T ⟶ S} (t : T ⟶ E.torsion N) (ht : t ≫ E.torsionπ N = g) :
    LocallyConstant T (Fin 2 → ZMod N) :=
  constSchemePointsEquiv S (Fin 2 → ZMod N) g
    ⟨t ≫ (E.fullLevelIso hinv L).inv, by
      rw [Category.assoc, E.fullLevelIso_inv_constSchemeπ hinv L, ht]⟩

/-- **(the computation rule)** The coordinate vector of the basis combination labelled `v` is the
constant function `v`: `fullLevelHom` sends the `v`-th copy of `S` to `v₀ P + v₁ Q`, and
`fullLevelIso` inverts it, leaving the coproduct inclusion, whose reading is `const v`
(`constSchemePointsEquiv_sigmaι`). -/
theorem levelCoord_sigmaι (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    (v : Fin 2 → ZMod N) :
    E.levelCoord hinv L (g := 𝟙 S)
        (Sigma.ι (fun _ : Fin 2 → ZMod N => S) v ≫ E.fullLevelHom L)
        (by rw [Category.assoc, E.fullLevelHom_torsionπ L]; simp [constSchemeπ]) =
      LocallyConstant.const S v := by
  rw [← constSchemePointsEquiv_sigmaι (S := S) (A := Fin 2 → ZMod N) v]
  refine congrArg _ (Subtype.ext ?_)
  show (Sigma.ι (fun _ : Fin 2 → ZMod N => S) v ≫ E.fullLevelHom L) ≫
      (E.fullLevelIso hinv L).inv = Sigma.ι (fun _ : Fin 2 → ZMod N => S) v
  have hhom : E.fullLevelHom L = (E.fullLevelIso hinv L).hom := rfl
  rw [hhom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The coordinate vector determines the point: `levelCoord` is injective, because
`fullLevelIso.inv` is an isomorphism and `constSchemePointsEquiv` is an equivalence. -/
theorem levelCoord_injective (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    {T : Scheme.{u}} {g : T ⟶ S} (t t' : T ⟶ E.torsion N)
    (ht : t ≫ E.torsionπ N = g) (ht' : t' ≫ E.torsionπ N = g)
    (h : E.levelCoord hinv L t ht = E.levelCoord hinv L t' ht') : t = t' := by
  have h' : t ≫ (E.fullLevelIso hinv L).inv = t' ≫ (E.fullLevelIso hinv L).inv :=
    congrArg Subtype.val ((constSchemePointsEquiv S (Fin 2 → ZMod N) g).injective h)
  exact (Iso.cancel_iso_inv_right _ _ _).mp h'

/-! ### The transition between two level bases -/

/-- The `j`-th basis point of a full level structure, as a section of the torsion: the image of the
`j`-th standard basis vector under `fullLevelHom`. No `pointToTorsion` plumbing is needed —
`fullLevelHom` already sends the `j`-th standard vector to the `j`-th basis point. -/
noncomputable def levelBasisPt (L : E.FullLevelPt N) (j : Fin 2) : S ⟶ E.torsion N :=
  Sigma.ι (fun _ : Fin 2 → ZMod N => S) (Pi.single j 1) ≫ E.fullLevelHom L

theorem levelBasisPt_torsionπ (L : E.FullLevelPt N) (j : Fin 2) :
    E.levelBasisPt L j ≫ E.torsionπ N = 𝟙 S := by
  rw [levelBasisPt, Category.assoc, E.fullLevelHom_torsionπ L]
  simp [constSchemeπ]

/-- **(route β, THE TRANSITION)** The transition between two full level bases, as the locally
constant *pair of columns*: the coordinate vectors of `L'`'s two basis points in the basis `L`.

Local constancy is free — each column is a `levelCoord`, i.e. the reading of a map into a constant
scheme — and the pair form is the one `detFun` consumes directly. -/
noncomputable def levelTransitionCols (hinv : NIsInvertible S N) (L L' : E.FullLevelPt N) :
    LocallyConstant S ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) where
  toFun t :=
    (E.levelCoord hinv L (E.levelBasisPt L' 0) (E.levelBasisPt_torsionπ L' 0) t,
      E.levelCoord hinv L (E.levelBasisPt L' 1) (E.levelBasisPt_torsionπ L' 1) t)
  isLocallyConstant :=
    IsLocallyConstant.prodMk
      (E.levelCoord hinv L (E.levelBasisPt L' 0) (E.levelBasisPt_torsionπ L' 0)).isLocallyConstant
      (E.levelCoord hinv L (E.levelBasisPt L' 1) (E.levelBasisPt_torsionπ L' 1)).isLocallyConstant

/-- The transition of a basis with itself is the identity pair: `levelCoord` of the `j`-th basis
point in its own basis is the `j`-th standard vector (`levelCoord_sigmaι`). -/
theorem levelTransitionCols_self (hinv : NIsInvertible S N) (L : E.FullLevelPt N) (t : S) :
    E.levelTransitionCols hinv L L t = (Pi.single 0 1, Pi.single 1 1) := by
  have h : ∀ j : Fin 2,
      E.levelCoord hinv L (E.levelBasisPt L j) (E.levelBasisPt_torsionπ L j) t =
        Pi.single j 1 := fun j => by
    have := E.levelCoord_sigmaι hinv L (Pi.single j 1)
    exact congrArg (fun f => LocallyConstant.toFun f t) this
  exact Prod.ext (h 0) (h 1)

/-- **(the bridge to the trivialisation level)** Where a column of the transition is the *constant*
vector `c`, the corresponding basis point of `L'` **is** the `L`-basis combination labelled `c` —
i.e. the transition's columns really do express `L'` in terms of `L`.

`levelCoord_injective` plus `levelCoord_sigmaι`: both points have the same coordinate vector. -/
theorem levelBasisPt_eq_sigmaι (hinv : NIsInvertible S N) (L L' : E.FullLevelPt N) (j : Fin 2)
    (c : Fin 2 → ZMod N)
    (hc : E.levelCoord hinv L (E.levelBasisPt L' j) (E.levelBasisPt_torsionπ L' j) =
      LocallyConstant.const S c) :
    E.levelBasisPt L' j =
      Sigma.ι (fun _ : Fin 2 → ZMod N => S) c ≫ E.fullLevelHom L := by
  refine E.levelCoord_injective hinv L _ _ (E.levelBasisPt_torsionπ L' j)
    (by rw [Category.assoc, E.fullLevelHom_torsionπ L]; simp [constSchemeπ]) ?_
  rw [hc, E.levelCoord_sigmaι hinv L c]

end EllipticCurve

end ModularCurves
