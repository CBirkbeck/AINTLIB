/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.RootSplitting
import ModularCurves.WeilPairing.CharZeroAssembly

/-!
# Reading the local determinant pairing on a clopen piece (WP-B5b)

`WeilPairingLocalData`'s only missing field is the cocycle
`pr₁ ≫ localDetPairing = pr₂ ≫ localDetPairing` on the kernel pair of the trivialising
cover. Two things make that awkward as stated: the two projections lie over **different**
`S'`-points, so the comparison of the pulled-back trivialisations is a locally constant
`GL₂(ℤ/N)`-valued function rather than a single matrix, and the root relation therefore
carries a locally constant exponent — which WP-A4
(`constSchemeMap_gl2Both_comp_detConstMor_rootSplitting`, stated for a constant `g`) cannot
absorb.

Both dissolve on the clopen pieces where the trivialisation reading is constant, and
`GroupScheme/MuN.lean` already exports the vocabulary for that: `constSchemePointsEquiv`
turns a map into a constant scheme into a `LocallyConstant`, `locConstPiece` names its clopen
fibres, `constMap_factor_of_le` says the map factors through the corresponding summand there,
and `locConst_hom_ext` glues.

This file supplies the *reading* half: on such a piece the local pairing is literally
`ζ ^ det v`. The cocycle then becomes the pointwise comparison of two such readings, which is
the content-bearing statement (the root transforms by `det`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(WP-B5b)** On the clopen piece where the trivialisation reads the constant value `v`,
the local determinant pairing is the constant `ζ ^ det v`.

The three rewrites are `constMap_factor_of_le` (the map into the constant scheme factors
through the `v`-summand), `constSchemeMap_ι` (the determinant model sends the `v`-summand to
the `det v`-summand) and `rootSplitting_ι` (the splitting sends the `k`-summand to `ζ ^ k`). -/
theorem comp_localDetPairing_restrict (N : ℕ) [NeZero N] {S' : Scheme.{u}} (p : S' ⟶ S)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 })
    (triv : pullback (E.torsionSqπ N) p ≅
      constScheme S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)))
    (htriv : triv.hom ≫ constSchemeπ S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      pullback.snd (E.torsionSqπ N) p)
    {W : Scheme.{u}} (a : W ⟶ pullback (E.torsionSqπ N) p)
    (v : (Fin 2 → ZMod N) × (Fin 2 → ZMod N)) {U : W.Opens}
    (hU : U ≤ locConstPiece
      (constSchemePointsEquiv S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N))
        (a ≫ pullback.snd (E.torsionSqπ N) p)
        ⟨a ≫ triv.hom, by rw [Category.assoc, htriv]⟩) v) :
    U.ι ≫ a ≫ localDetPairing E N p ζ triv =
      (U.ι ≫ a ≫ pullback.snd (E.torsionSqπ N) p) ≫
        rootPower N ζ (detFun N v) ≫ muNMapAlong p N := by
  have hfac := constMap_factor_of_le (S := S')
    (A := (Fin 2 → ZMod N) × (Fin 2 → ZMod N))
    (g := a ≫ pullback.snd (E.torsionSqπ N) p) (a ≫ triv.hom)
    (by rw [Category.assoc, htriv]) v hU
  rw [localDetPairing, reassoc_of% hfac, ← Category.assoc
      (Sigma.ι (fun _ : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) => S') v) (detConstMor N),
    detConstMor, constSchemeMap_ι]
  simp only [← Category.assoc, rootSplitting_ι]

/-- The joint clopen decomposition of `W` by the two trivialisation readings of `a` and `b`:
the locally constant function recording both at once. -/
noncomputable def jointReading (N : ℕ) [NeZero N] {S' : Scheme.{u}} (p : S' ⟶ S)
    (triv : pullback (E.torsionSqπ N) p ≅
      constScheme S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)))
    (htriv : triv.hom ≫ constSchemeπ S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      pullback.snd (E.torsionSqπ N) p)
    {W : Scheme.{u}} (a b : W ⟶ pullback (E.torsionSqπ N) p) :
    LocallyConstant W
      (((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) × ((Fin 2 → ZMod N) × (Fin 2 → ZMod N))) :=
  { toFun := fun t =>
      (constSchemePointsEquiv S' _ (a ≫ pullback.snd (E.torsionSqπ N) p)
          ⟨a ≫ triv.hom, by rw [Category.assoc, htriv]⟩ t,
        constSchemePointsEquiv S' _ (b ≫ pullback.snd (E.torsionSqπ N) p)
          ⟨b ≫ triv.hom, by rw [Category.assoc, htriv]⟩ t)
    isLocallyConstant :=
      IsLocallyConstant.prodMk
        (constSchemePointsEquiv S' _ (a ≫ pullback.snd (E.torsionSqπ N) p)
          ⟨a ≫ triv.hom, by rw [Category.assoc, htriv]⟩).isLocallyConstant
        (constSchemePointsEquiv S' _ (b ≫ pullback.snd (E.torsionSqπ N) p)
          ⟨b ≫ triv.hom, by rw [Category.assoc, htriv]⟩).isLocallyConstant }

/-- **(WP-B5b, the glue)** Two morphisms into the trivialising cover induce the same local
determinant pairing as soon as, on each piece of the joint clopen decomposition, the two
constant readings `ζ ^ det v` and `ζ ^ det w` agree.

This is where the locally-constant comparison matrix stops being an obstacle: on each piece
both readings are *constant*, so WP-A4's determinant twist applies verbatim, and
`locConst_hom_ext` glues the pieces back together. What is left as the hypothesis is exactly
the content-bearing statement — that the root transforms by `det`. -/
theorem comp_localDetPairing_eq_of_pieces (N : ℕ) [NeZero N] {S' : Scheme.{u}} (p : S' ⟶ S)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 })
    (triv : pullback (E.torsionSqπ N) p ≅
      constScheme S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)))
    (htriv : triv.hom ≫ constSchemeπ S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      pullback.snd (E.torsionSqπ N) p)
    {W : Scheme.{u}} (a b : W ⟶ pullback (E.torsionSqπ N) p)
    (h : ∀ vw, (locConstPiece (jointReading E N p triv htriv a b) vw).ι ≫
        (a ≫ pullback.snd (E.torsionSqπ N) p) ≫
          rootPower N ζ (detFun N vw.1) ≫ muNMapAlong p N =
      (locConstPiece (jointReading E N p triv htriv a b) vw).ι ≫
        (b ≫ pullback.snd (E.torsionSqπ N) p) ≫
          rootPower N ζ (detFun N vw.2) ≫ muNMapAlong p N) :
    a ≫ localDetPairing E N p ζ triv = b ≫ localDetPairing E N p ζ triv := by
  refine locConst_hom_ext (jointReading E N p triv htriv a b) fun vw => ?_
  have ha : (locConstPiece (jointReading E N p triv htriv a b) vw : W.Opens) ≤
      locConstPiece (constSchemePointsEquiv S' _ (a ≫ pullback.snd (E.torsionSqπ N) p)
        ⟨a ≫ triv.hom, by rw [Category.assoc, htriv]⟩) vw.1 := fun t ht =>
    congrArg Prod.fst (mem_locConstPiece.mp ht)
  have hb : (locConstPiece (jointReading E N p triv htriv a b) vw : W.Opens) ≤
      locConstPiece (constSchemePointsEquiv S' _ (b ≫ pullback.snd (E.torsionSqπ N) p)
        ⟨b ≫ triv.hom, by rw [Category.assoc, htriv]⟩) vw.2 := fun t ht =>
    congrArg Prod.snd (mem_locConstPiece.mp ht)
  rw [comp_localDetPairing_restrict E N p ζ triv htriv a vw.1 ha,
    comp_localDetPairing_restrict E N p ζ triv htriv b vw.2 hb,
    Category.assoc, Category.assoc]
  simpa only [Category.assoc] using h vw

/-! ### DS4 reduced to the root's determinant law -/

/-- **(WP-B5b, THE REDUCTION)** An elliptic curve admits a Weil pairing — the DS4 register's
`weilPairing` together with its `weilPairing_over` specification — as soon as it admits a
trivialising fppf cover, a root of unity on it, and the **determinant law** relating the two
readings on the kernel pair.

Everything else in route A is discharged here: `localDetPairing` is the pairing,
`localDetPairing_over` is the over-`S` field, `comp_localDetPairing_eq_of_pieces` is the
cocycle field, and `nonempty_weilPairing_of_localData` (`WeilPairing/CharZeroAssembly.lean`)
turns the record into the register entries.

The surviving hypothesis `hdet` is exactly *"the root transforms by `det`"*, read on the
clopen pieces of the joint trivialisation reading, where the exponent is constant. -/
theorem nonempty_weilPairing_of_root_of_det (N : ℕ) [NeZero N] {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 })
    (triv : pullback (E.torsionSqπ N) p ≅
      constScheme S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)))
    (htriv : triv.hom ≫ constSchemeπ S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      pullback.snd (E.torsionSqπ N) p)
    (hdet : ∀ vw,
      (locConstPiece (jointReading E N p triv htriv
          (pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p))
          (pullback.snd (pullback.fst (E.torsionSqπ N) p)
            (pullback.fst (E.torsionSqπ N) p))) vw).ι ≫
        (pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫
            pullback.snd (E.torsionSqπ N) p) ≫
          rootPower N ζ (detFun N vw.1) ≫ muNMapAlong p N =
      (locConstPiece (jointReading E N p triv htriv
          (pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p))
          (pullback.snd (pullback.fst (E.torsionSqπ N) p)
            (pullback.fst (E.torsionSqπ N) p))) vw).ι ≫
        (pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫
            pullback.snd (E.torsionSqπ N) p) ≫
          rootPower N ζ (detFun N vw.2) ≫ muNMapAlong p N) :
    ∃ e : pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N,
      e ≫ muNπ S N = E.torsionSqπ N :=
  EllipticCurve.nonempty_weilPairing_of_localData
    { cover := S'
      p := p
      flat := ‹Flat p›
      lfp := ‹LocallyOfFinitePresentation p›
      surj := ‹Surjective p›
      pairing := localDetPairing E N p ζ triv
      cocycle := comp_localDetPairing_eq_of_pieces E N p ζ triv htriv _ _ hdet
      overBase := localDetPairing_over E N p ζ triv htriv }

end ModularCurves
