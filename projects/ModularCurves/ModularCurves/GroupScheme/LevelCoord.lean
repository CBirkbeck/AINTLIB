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

/-- **(the forward direction)** The `j`-th basis point of `g • L` is the `L`-basis combination
labelled by the `j`-th **column** of `g`.

No `ZMod.val` arithmetic is needed here: `constGL_hom_fullLevelHom` already contains it, and
`Matrix.mulVec_single` reads `g · e_j` as the `j`-th column. -/
theorem levelBasisPt_glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (L : E.FullLevelPt N) (j : Fin 2) :
    E.levelBasisPt (E.glSmul g L) j =
      Sigma.ι (fun _ : Fin 2 → ZMod N => S)
        (fun i => (g : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) ≫ E.fullLevelHom L := by
  rw [levelBasisPt, ← E.constGL_hom_fullLevelHom g L, ← Category.assoc]
  congr 1
  show Sigma.ι (fun _ : Fin 2 → ZMod N => S) (Pi.single j 1) ≫
      Sigma.desc (fun a => Sigma.ι (fun _ : Fin 2 → ZMod N => S) (glEquiv g a)) = _
  rw [Sigma.ι_desc]
  congr 1
  show (g : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec (Pi.single j 1) = _
  rw [Matrix.mulVec_single_one]
  rfl

/-- `levelCoord` depends on the point only through the morphism — the section-condition proof is a
`Prop`, so it may be replaced freely. -/
theorem levelCoord_congr (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    {T : Scheme.{u}} {g : T ⟶ S} {t t' : T ⟶ E.torsion N}
    (ht : t ≫ E.torsionπ N = g) (ht' : t' ≫ E.torsionπ N = g) (h : t = t') :
    E.levelCoord hinv L t ht = E.levelCoord hinv L t' ht' := by
  subst h; rfl

/-- …hence the transition columns of `g • L` against `L` are exactly the columns of `g`. This is the
forward half of "the transition matrix expresses `L'` in terms of `L`". -/
theorem levelCoord_levelBasisPt_glSmul (hinv : NIsInvertible S N)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) (j : Fin 2) :
    E.levelCoord hinv L (E.levelBasisPt (E.glSmul g L) j)
        (E.levelBasisPt_torsionπ (E.glSmul g L) j) =
      LocallyConstant.const S (fun i => (g : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) := by
  rw [E.levelCoord_congr hinv L (E.levelBasisPt_torsionπ (E.glSmul g L) j)
    (by rw [Category.assoc, E.fullLevelHom_torsionπ L]; simp [constSchemeπ])
    (E.levelBasisPt_glSmul g L j)]
  exact E.levelCoord_sigmaι hinv L _

/-! ### The converse: equal basis points force equal level structures

This is the one step whose `ZMod.val` bookkeeping cannot be borrowed from
`constGL_hom_fullLevelHom`: it is the same computation run in reverse. -/

/-- Equal basis points give equal basis *combinations* as sections: `pointToTorsion` is injective
(compose with `torsionι`). -/
theorem basisComb_eq_of_levelBasisPt_eq (L L' : E.FullLevelPt N) (j : Fin 2)
    (h : E.levelBasisPt L j = E.levelBasisPt L' j) :
    (((Pi.single j 1 : Fin 2 → ZMod N) 0).val : ℤ) • L.1.1 +
        (((Pi.single j 1 : Fin 2 → ZMod N) 1).val : ℤ) • L.1.2 =
      (((Pi.single j 1 : Fin 2 → ZMod N) 0).val : ℤ) • L'.1.1 +
        (((Pi.single j 1 : Fin 2 → ZMod N) 1).val : ℤ) • L'.1.2 := by
  have h' := congrArg (fun m => m ≫ E.torsionι N) h
  simp only [levelBasisPt, fullLevelHom, Category.assoc, Sigma.ι_desc,
    E.pointToTorsion_torsionι] at h'
  exact Subtype.ext h'

/-- `(1 : ZMod N).val • R = R` for an `N`-torsion section: the valuation of `1` is congruent to `1`
mod `N`, and `zsmul_eq_of_intCast_eq` turns that into equality of the scalar actions. -/
theorem one_val_zsmul {R : E.Section} (hR : (N : ℤ) • R = 0) :
    (((1 : ZMod N)).val : ℤ) • R = R := by
  rw [zsmul_eq_of_intCast_eq R hR (b := 1) (by simp), one_smul]

/-- …and `(0 : ZMod N).val • R = 0`. -/
theorem zero_val_zsmul (R : E.Section) :
    (((0 : ZMod N)).val : ℤ) • R = 0 := by
  simp

/-- **(the converse, THE RESULT)** A full level structure is determined by its two basis points: if
two level structures have the same basis points they are equal.

Together with `levelBasisPt_eq_sigmaι` and `levelBasisPt_glSmul` this closes the transition
statement: two level structures whose transition columns are the constant columns of `g` satisfy
`L' = g • L`, so `fullLevelPairing_glSmul` applies. -/
theorem FullLevelPt.ext_of_levelBasisPt (L L' : E.FullLevelPt N)
    (h : ∀ j : Fin 2, E.levelBasisPt L j = E.levelBasisPt L' j) : L = L' := by
  have e00 : (Pi.single (0 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 0 = 1 := by simp
  have e01 : (Pi.single (0 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 1 = 0 := by simp
  have e10 : (Pi.single (1 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 0 = 0 := by simp
  have e11 : (Pi.single (1 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 1 = 1 := by simp
  have h0 := E.basisComb_eq_of_levelBasisPt_eq L L' 0 (h 0)
  have h1 := E.basisComb_eq_of_levelBasisPt_eq L L' 1 (h 1)
  rw [e00, e01, E.one_val_zsmul L.2.1.1, E.one_val_zsmul L'.2.1.1, E.zero_val_zsmul,
    E.zero_val_zsmul, add_zero, add_zero] at h0
  rw [e10, e11, E.one_val_zsmul L.2.1.2, E.one_val_zsmul L'.2.1.2, E.zero_val_zsmul,
    E.zero_val_zsmul, zero_add, zero_add] at h1
  exact Subtype.ext (Prod.ext h0 h1)

/-- **(route β, THE TRANSITION STATEMENT)** If the transition columns of `L'` against `L` are the
*constant* columns of a matrix `g ∈ GL₂(ℤ/N)`, then `L' = g • L`.

This is what `fullLevelPairing_glSmul` consumes on each clopen piece of `levelTransitionCols`. -/
theorem eq_glSmul_of_levelCoord (hinv : NIsInvertible S N) (L L' : E.FullLevelPt N)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hc : ∀ j : Fin 2,
      E.levelCoord hinv L (E.levelBasisPt L' j) (E.levelBasisPt_torsionπ L' j) =
        LocallyConstant.const S (fun i => (g : Matrix (Fin 2) (Fin 2) (ZMod N)) i j)) :
    L' = E.glSmul g L :=
  FullLevelPt.ext_of_levelBasisPt E L' (E.glSmul g L) fun j => by
    rw [E.levelBasisPt_eq_sigmaι hinv L L' j _ (hc j), E.levelBasisPt_glSmul g L j]

/-! ### The section identities behind the transition

`constSchemeMap` lives in `WeilPairing/CharZeroDescent.lean`, so the *trivialisation-level* linearity
(`fullLevelHom_eq_constSchemeMap_comp`) is proved in `WeilPairing/FullLevelPairing.lean`; what belongs
here are the **section identities** it consumes. -/

/-- The section identity behind `fullLevelHom_eq_constSchemeMap_comp`'s hypotheses: if the `j`-th
basis point of `L'` is the `L`-combination labelled `c`, then the corresponding basis *section* of
`L'` is that combination. -/
theorem basis_eq_of_levelBasisPt_eq_sigmaι (L L' : E.FullLevelPt N) (j : Fin 2)
    (c : Fin 2 → ZMod N)
    (h : E.levelBasisPt L' j =
      Sigma.ι (fun _ : Fin 2 → ZMod N => S) c ≫ E.fullLevelHom L) :
    (((Pi.single j 1 : Fin 2 → ZMod N) 0).val : ℤ) • L'.1.1 +
        (((Pi.single j 1 : Fin 2 → ZMod N) 1).val : ℤ) • L'.1.2 =
      (((c 0).val : ℤ) • L.1.1 + ((c 1).val : ℤ) • L.1.2) := by
  have h' := congrArg (fun m => m ≫ E.torsionι N) h
  simp only [levelBasisPt, fullLevelHom, Category.assoc, Sigma.ι_desc,
    E.pointToTorsion_torsionι] at h'
  exact Subtype.ext h'

/-- …read at `j = 0`: the first basis section of `L'` is the combination labelled by the first
column. -/
theorem basis_fst_eq_of_levelBasisPt_eq_sigmaι (L L' : E.FullLevelPt N) (c : Fin 2 → ZMod N)
    (h : E.levelBasisPt L' 0 =
      Sigma.ι (fun _ : Fin 2 → ZMod N => S) c ≫ E.fullLevelHom L) :
    L'.1.1 = ((c 0).val : ℤ) • L.1.1 + ((c 1).val : ℤ) • L.1.2 := by
  have e00 : (Pi.single (0 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 0 = 1 := by simp
  have e01 : (Pi.single (0 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 1 = 0 := by simp
  have h0 := E.basis_eq_of_levelBasisPt_eq_sigmaι L L' 0 c h
  rwa [e00, e01, E.one_val_zsmul L'.2.1.1, E.zero_val_zsmul, add_zero] at h0

/-- …and at `j = 1`. -/
theorem basis_snd_eq_of_levelBasisPt_eq_sigmaι (L L' : E.FullLevelPt N) (c : Fin 2 → ZMod N)
    (h : E.levelBasisPt L' 1 =
      Sigma.ι (fun _ : Fin 2 → ZMod N => S) c ≫ E.fullLevelHom L) :
    L'.1.2 = ((c 0).val : ℤ) • L.1.1 + ((c 1).val : ℤ) • L.1.2 := by
  have e10 : (Pi.single (1 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 0 = 0 := by simp
  have e11 : (Pi.single (1 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N) 1 = 1 := by simp
  have h1 := E.basis_eq_of_levelBasisPt_eq_sigmaι L L' 1 c h
  rwa [e10, e11, E.one_val_zsmul L'.2.1.2, E.zero_val_zsmul, zero_add] at h1

end EllipticCurve

end ModularCurves
