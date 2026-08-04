/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.DetCocycle
import ModularCurves.WeilPairing.TorsionSqBaseChange
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

/-- **(route β, step 1)** The torsion square, transported along the level trivialisation, is the
fibre square of two copies of the constant scheme. Named separately from `fullLevelSqIso` so that
`IsPullback.isoPullback_inv_fst`/`_snd` are available for the computation rules below. -/
theorem isPullback_constSchemeπ_of_fullLevel (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    IsPullback (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ (E.fullLevelIso hinv L).inv)
      (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ (E.fullLevelIso hinv L).inv)
      (constSchemeπ S (Fin 2 → ZMod N)) (constSchemeπ S (Fin 2 → ZMod N)) := by
  have hinvπ : (E.fullLevelIso hinv L).inv ≫ constSchemeπ S (Fin 2 → ZMod N) =
      E.torsionπ N := by
    rw [Iso.inv_comp_eq]
    exact (E.fullLevelHom_torsionπ L).symm
  exact (IsPullback.of_hasPullback (E.torsionπ N) (E.torsionπ N)).of_iso (Iso.refl _)
    (E.fullLevelIso hinv L).symm (E.fullLevelIso hinv L).symm (Iso.refl S)
    (by simp) (by simp) (by simpa using hinvπ.symm) (by simpa using hinvπ.symm)

/-- **(route β, step 1)** A full level structure trivialises the *square* `E[N] ×_S E[N]`: the
two legs are trivialised by `fullLevelIso` and the resulting fibre square of constant schemes is
`constSchemeSqIso`. -/
noncomputable def fullLevelSqIso (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    pullback (E.torsionπ N) (E.torsionπ N) ≅
      constScheme S ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) :=
  (E.isPullback_constSchemeπ_of_fullLevel hinv L).isoPullback.trans
    (constSchemeSqIso S (Fin 2 → ZMod N) (Fin 2 → ZMod N))

/-- …and the trivialisation of the square is a morphism over `S`, in exactly the form
`nonempty_weilPairing_of_root_of_trivialised` consumes. -/
theorem fullLevelSqIso_hom_π (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    (E.fullLevelSqIso hinv L).hom ≫
        constSchemeπ S ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      E.torsionSqπ N := by
  rw [fullLevelSqIso, Iso.trans_hom, Category.assoc, constSchemeSqIso_hom_π,
    IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
    (E.fullLevelIso hinv L).inv_comp_eq.mpr (E.fullLevelHom_torsionπ L).symm, torsionSqπ]
  exact pullback.condition.symm

/-- The computation rule for `fullLevelSqIso`: the `(v, w)`-th copy of `S` is the pair of torsion
sections labelled `v` and `w` by the level structure. -/
theorem fullLevelSqIso_inv_ι (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    (v w : Fin 2 → ZMod N) :
    Sigma.ι (fun _ : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) => S) (v, w) ≫
        (E.fullLevelSqIso hinv L).inv =
      pullback.lift
        (Sigma.ι (fun _ : Fin 2 → ZMod N => S) v ≫ (E.fullLevelIso hinv L).hom)
        (Sigma.ι (fun _ : Fin 2 → ZMod N => S) w ≫ (E.fullLevelIso hinv L).hom)
        (by
          have h : (E.fullLevelIso hinv L).hom ≫ E.torsionπ N =
              constSchemeπ S (Fin 2 → ZMod N) := E.fullLevelHom_torsionπ L
          rw [Category.assoc, Category.assoc, h]
          simp [constSchemeπ]) := by
  have hfst : (E.isPullback_constSchemeπ_of_fullLevel hinv L).isoPullback.inv ≫
      pullback.fst (E.torsionπ N) (E.torsionπ N) =
        pullback.fst (constSchemeπ S (Fin 2 → ZMod N)) (constSchemeπ S (Fin 2 → ZMod N)) ≫
          (E.fullLevelIso hinv L).hom := by
    rw [← (E.isPullback_constSchemeπ_of_fullLevel hinv L).isoPullback_inv_fst]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsnd : (E.isPullback_constSchemeπ_of_fullLevel hinv L).isoPullback.inv ≫
      pullback.snd (E.torsionπ N) (E.torsionπ N) =
        pullback.snd (constSchemeπ S (Fin 2 → ZMod N)) (constSchemeπ S (Fin 2 → ZMod N)) ≫
          (E.fullLevelIso hinv L).hom := by
    rw [← (E.isPullback_constSchemeπ_of_fullLevel hinv L).isoPullback_inv_snd]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [fullLevelSqIso, Iso.trans_inv, ← Category.assoc, constSchemeSqIso_inv_ι]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hfst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, hsnd, pullback.lift_snd_assoc, pullback.lift_snd]

/-- **(route β, step 2, the equivariance)** Re-marking the level structure by `g ∈ GL₂(ℤ/N)`
composes the trivialisation of the square with the diagonal action of `g`:

`(fullLevelSqIso L).inv = constSchemeMap (gl2Both N g) ≫ (fullLevelSqIso (g • L)).inv`… read in
the direction the pairing consumes, `(fullLevelSqIso L).hom = (fullLevelSqIso (g • L)).hom ≫
constSchemeMap (gl2Both N g)`.

`fullLevelIso_glSmul` is the one-leg statement; the square version follows by checking on the
coproduct inclusions with `fullLevelSqIso_inv_ι`. -/
theorem fullLevelSqIso_glSmul_inv (hinv : NIsInvertible S N)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    (E.fullLevelSqIso hinv (E.glSmul g L)).inv =
      constSchemeMap (S := S) (gl2Both N (g : Matrix (Fin 2) (Fin 2) (ZMod N))) ≫
        (E.fullLevelSqIso hinv L).inv := by
  refine Sigma.hom_ext _ _ fun vw => ?_
  obtain ⟨v, w⟩ := vw
  rw [← Category.assoc, constSchemeMap_ι]
  have hgl : gl2Both N (g : Matrix (Fin 2) (Fin 2) (ZMod N)) (v, w) =
      ((g : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v,
        (g : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec w) := rfl
  rw [hgl, E.fullLevelSqIso_inv_ι hinv (E.glSmul g L) v w, E.fullLevelSqIso_inv_ι hinv L _ _]
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [pullback.lift_fst, pullback.lift_snd, E.fullLevelIso_glSmul hinv g L,
      Iso.trans_hom, constGL, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc] <;> rfl

/-- …hence, at the level of the `hom`s, the direction the pairing consumes. -/
theorem fullLevelSqIso_glSmul_hom (hinv : NIsInvertible S N)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    (E.fullLevelSqIso hinv L).hom =
      (E.fullLevelSqIso hinv (E.glSmul g L)).hom ≫
        constSchemeMap (S := S) (gl2Both N (g : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
  have h := E.fullLevelSqIso_glSmul_inv hinv g L
  calc (E.fullLevelSqIso hinv L).hom
      = (E.fullLevelSqIso hinv (E.glSmul g L)).hom ≫
          (E.fullLevelSqIso hinv (E.glSmul g L)).inv ≫ (E.fullLevelSqIso hinv L).hom := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = _ := by simp [h]

/-! ### The pairing itself, named

Per the architectural correction on the board, the register entry must be a *definition*, not a
`choose` from an existence statement: only then are the computational specs reachable. Over a
full-level base the definition is the determinant formula read through the level structure. -/

/-- **(route β, step 1, the pairing)** The Weil pairing over a base with a full level structure:
read the pair of torsion sections in the level basis, take the determinant, and raise `ζ` to it. -/
noncomputable def fullLevelPairing (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    (ζ : { a : Γ(S, (⊤ : S.Opens)) // a ^ N = 1 }) :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N :=
  (E.fullLevelSqIso hinv L).hom ≫ detConstMor N ≫ rootSplitting N ζ

/-- The pairing is a morphism over `S` — the DS4 `weilPairing_over` specification. -/
theorem fullLevelPairing_over (hinv : NIsInvertible S N) (L : E.FullLevelPt N)
    (ζ : { a : Γ(S, (⊤ : S.Opens)) // a ^ N = 1 }) :
    E.fullLevelPairing hinv L ζ ≫ muNπ S N = E.torsionSqπ N := by
  simp only [fullLevelPairing, Category.assoc]
  rw [rootSplitting_π, detConstMor, constSchemeMap_π, E.fullLevelSqIso_hom_π hinv L]

/-- **(route β, step 2, THE DETERMINANT LAW OF THE PAIRING)** The pairing is unchanged by
re-marking the level structure by `g` *provided the root is simultaneously raised to `det g`*:

`e_{g • L, ζ ^ det g} = e_{L, ζ}`.

This is exactly the cocycle condition the descent from the frame bundle consumes, and it is a
*theorem*, not an assumption: `fullLevelSqIso_glSmul_hom` moves the re-marking onto the constant
scheme, where WP-A4 (`constSchemeMap_gl2Both_comp_detConstMor_rootSplitting`) converts the diagonal
`GL₂`-action into the `det g`-th power of the root.

Read contrapositively, this is the precise sense in which the root **must** transform by `det`: the
`L`-pairing and the `g • L`-pairing agree for the *same* `ζ` only when `det g = 1`. -/
theorem fullLevelPairing_glSmul (hinv : NIsInvertible S N)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N)
    (ζ : { a : Γ(S, (⊤ : S.Opens)) // a ^ N = 1 }) :
    E.fullLevelPairing hinv (E.glSmul g L)
        ⟨(ζ : Γ(S, (⊤ : S.Opens))) ^ (g : Matrix (Fin 2) (Fin 2) (ZMod N)).det.val, by
          rw [← pow_mul, mul_comm, pow_mul, ζ.2, one_pow]⟩ =
      E.fullLevelPairing hinv L ζ := by
  rw [fullLevelPairing, fullLevelPairing, E.fullLevelSqIso_glSmul_hom hinv g L, Category.assoc,
    constSchemeMap_gl2Both_comp_detConstMor_rootSplitting]

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

/-! ### The pairing on a trivialising cover, and the descent

`WeilPairingLocalData` wants a pairing out of `pullback (E.torsionSqπ N) p`; `fullLevelPairing`
produces one out of the base-changed curve's torsion square. `torsionSqBaseChangeIso`
(`WeilPairing/TorsionSqBaseChange.lean`) identifies the two, and `muNMapAlong` brings the values
back over `S`. Everything then goes through except the cocycle, which is the one remaining
arithmetic input. -/

variable {S' : Scheme.{u}}

/-- **(route β, step 3)** The pairing on the base change of the Weil-pairing source along a cover
carrying a full level structure: `fullLevelPairing` of the base-changed curve, read through
`torsionSqBaseChangeIso` and pushed back over `S` by `muNMapAlong`. -/
noncomputable def coverPairing (p : S' ⟶ S) (hinv : NIsInvertible S' N)
    (L : (E.baseChange p).FullLevelPt N) (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) :
    pullback (E.torsionSqπ N) p ⟶ muN S N :=
  (E.torsionSqBaseChangeIso N p).hom ≫
    (E.baseChange p).fullLevelPairing hinv L ζ ≫ muNMapAlong p N

/-- The cover pairing is a morphism over `S` — the `overBase` field of a
`WeilPairingLocalData`. -/
theorem coverPairing_over (p : S' ⟶ S) (hinv : NIsInvertible S' N)
    (L : (E.baseChange p).FullLevelPt N) (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) :
    E.coverPairing p hinv L ζ ≫ muNπ S N =
      pullback.fst (E.torsionSqπ N) p ≫ E.torsionSqπ N := by
  have hsnd : (E.torsionSqBaseChangeIso N p).hom ≫ (E.baseChange p).torsionSqπ N =
      pullback.snd (E.torsionSqπ N) p := by
    rw [torsionSqBaseChangeIso, Iso.symm_hom, Iso.inv_comp_eq]
    exact (E.isPullback_torsionSq_baseChange N p).isoPullback_hom_snd.symm
  simp only [coverPairing, Category.assoc]
  rw [muNMapAlong_π, ← Category.assoc ((E.baseChange p).fullLevelPairing hinv L ζ),
    (E.baseChange p).fullLevelPairing_over hinv L ζ, ← Category.assoc, hsnd]
  exact pullback.condition.symm

/-- The trivialisation of the base change of the Weil-pairing source that the cover pairing is
built from: the base-change identification followed by the level trivialisation of the square. -/
noncomputable def coverTriv (p : S' ⟶ S) (hinv : NIsInvertible S' N)
    (L : (E.baseChange p).FullLevelPt N) :
    pullback (E.torsionSqπ N) p ≅
      constScheme S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) :=
  (E.torsionSqBaseChangeIso N p).trans ((E.baseChange p).fullLevelSqIso hinv L)

theorem coverTriv_htriv (p : S' ⟶ S) (hinv : NIsInvertible S' N)
    (L : (E.baseChange p).FullLevelPt N) :
    (E.coverTriv p hinv L).hom ≫
        constSchemeπ S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      pullback.snd (E.torsionSqπ N) p := by
  rw [coverTriv, Iso.trans_hom, Category.assoc,
    (E.baseChange p).fullLevelSqIso_hom_π hinv L, torsionSqBaseChangeIso, Iso.symm_hom,
    Iso.inv_comp_eq]
  exact (E.isPullback_torsionSq_baseChange N p).isoPullback_hom_snd.symm

/-- **(route β, the two lines converge)** The cover pairing *is* the local determinant pairing of
`WeilPairing/RootSplitting.lean` for the trivialisation `coverTriv`.

Consequently the whole clopen-decomposition machinery of `WeilPairing/DetCocycle.lean`
(`comp_localDetPairing_restrict`, `comp_localDetPairing_eq_of_pieces`,
`nonempty_weilPairing_of_root_of_det`) applies to it verbatim — and `fullLevelPairing_glSmul` is the
tool that discharges the surviving `hdet`. -/
theorem coverPairing_eq_localDetPairing (p : S' ⟶ S) (hinv : NIsInvertible S' N)
    (L : (E.baseChange p).FullLevelPt N)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) :
    E.coverPairing p hinv L ζ = localDetPairing E N p ζ (E.coverTriv p hinv L) := by
  simp only [coverPairing, localDetPairing, coverTriv, fullLevelPairing, Iso.trans_hom,
    Category.assoc]

/-- **(route β, step 3, THE DESCENT)** An elliptic curve admits a Weil pairing as soon as it admits
a trivialising fppf cover carrying a **full level structure** and an `N`-th root of unity, *and* the
resulting cover pairing satisfies the cocycle condition on the kernel pair.

Every field of `WeilPairingLocalData` except `cocycle` is discharged here. The cocycle is the one
remaining arithmetic input, and `fullLevelPairing_glSmul` is what turns it into a statement about
`ζ` alone: on the kernel pair the two level structures differ by the transition matrix `g`, so the
two pairings agree exactly when `g^*ζ = ζ ^ det g`. -/
theorem nonempty_weilPairing_of_cover_of_cocycle (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hinv : NIsInvertible S' N) (L : (E.baseChange p).FullLevelPt N)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 })
    (hcoc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫
        E.coverPairing p hinv L ζ =
      pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫
        E.coverPairing p hinv L ζ) :
    ∃ e : pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N,
      e ≫ muNπ S N = E.torsionSqπ N :=
  nonempty_weilPairing_of_localData
    { cover := S'
      p := p
      flat := ‹Flat p›
      lfp := ‹LocallyOfFinitePresentation p›
      surj := ‹Surjective p›
      pairing := E.coverPairing p hinv L ζ
      cocycle := hcoc
      overBase := E.coverPairing_over p hinv L ζ }

end EllipticCurve

end ModularCurves
