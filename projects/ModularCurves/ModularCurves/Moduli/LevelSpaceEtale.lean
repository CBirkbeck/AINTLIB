/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LevelSpaces
import ModularCurves.GroupScheme.TorsionEtaleTriv
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# [GHA3] Towards étaleness of the full-level space (KM 3.7.1, route β)

The KM 1.6.7 fallback route to `levelSpaceΓπ_etale` (`U_{Γ(N)} → S` is étale for `N`
invertible), avoiding the Weil pairing:

* **β1** — `E[N]` is trivialized by a surjective étale cover `p : T ⟶ S`
  (`torsion_etaleLocal_triv`, PROVEN in `GroupScheme/TorsionEtaleTriv.lean`).
* **β2** — the level space commutes with base change: `U_{Γ(N)}(E) ×_S T ≅ U_{Γ(N)}(E_T)`
  compatibly over the torsion ambient. Mechanism: closed subschemes are determined by their
  factorization predicate (`exists_iso_of_factor_iff` below), and both sides classify Drinfeld
  full-level pairs (`levelSpaceΓ_spec` on either curve, matched through the fibrewise-generation
  form `fullLevel_divisor_iff_naive_gen` whose geometric-point condition composes across base
  changes).
* **β3** — over the trivialized curve the incidence locus is a clopen of the constant scheme
  `((ℤ/N)² × (ℤ/N)²)_T`, hence étale over `T`.
* **β4** — étaleness descends along the surjective flat locally-finitely-presented `p`
  (mathlib `DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` + the fpqc→fppf
  upgrade): `levelSpaceΓπ_etale_of_cover` below.

This file provides the two reusable mechanisms (the mono factorization-predicate uniqueness and
the descent shell); β2/β3 land against them.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

section FactorIff

variable {C : Type*} [Category C]

/-- **Subobjects are determined by their factorization predicate**: two monomorphisms into a
common target through which exactly the same morphisms factor differ by an isomorphism over the
target. (Applied to closed immersions: a closed subscheme is determined by which `V`-points of
the ambient it absorbs.) -/
theorem exists_iso_of_factor_iff {A L L' : C} (i : L ⟶ A) (i' : L' ⟶ A) [Mono i] [Mono i']
    (h : ∀ (V : C) (v : V ⟶ A), (∃ w : V ⟶ L, w ≫ i = v) ↔ ∃ w' : V ⟶ L', w' ≫ i' = v) :
    ∃ e : L ≅ L', e.hom ≫ i' = i := by
  obtain ⟨w, hw⟩ := (h L i).mp ⟨𝟙 L, Category.id_comp i⟩
  obtain ⟨w', hw'⟩ := (h L' i').mpr ⟨𝟙 L', Category.id_comp i'⟩
  refine ⟨⟨w, w', ?_, ?_⟩, hw⟩
  · rw [← cancel_mono i, Category.assoc, hw', hw, Category.id_comp]
  · rw [← cancel_mono i', Category.assoc, hw, hw', Category.id_comp]

end FactorIff

variable {S : Scheme.{u}}

/-- **(β4, the descent shell)** Étaleness descends along any surjective flat
locally-finitely-presented cover of the base: if `X ×_S T → T` is étale then `X → S` is étale.
Instance chain: mathlib's `DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` (fpqc
descent of étaleness, `LocalFlatDescent`) upgraded to the fppf form (`FlatDescent`), which needs
no quasi-compactness of the cover — exactly right for the sigma-assembled trivializing cover of
β1. Applied to `levelSpaceΓπ` this is the final leg of [GHA3]. -/
theorem etale_of_etale_pullback_snd_of_cover {X T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    [Surjective p] [Flat p] [LocallyOfFinitePresentation p]
    (hpb : Etale (pullback.snd f p)) : Etale f :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨‹Surjective p›, ‹Flat p›⟩, ‹LocallyOfFinitePresentation p›⟩ hpb

section PairBaseChange

variable (E : EllipticCurve S) {T : Scheme.{u}} (p : T ⟶ S) (N : ℕ) [NeZero N]

/-- **(β2, ambient comparison)** The comparison map on torsion self-products
`E_T[N] ×_T E_T[N] ⟶ E[N] ×_S E[N]` induced by the single-factor comparison
`torsionBaseChangeHom` on each leg. -/
noncomputable def torsionPairBaseChangeHom :
    pullback ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ⟶
      pullback (E.torsionπ N) (E.torsionπ N) :=
  pullback.map _ _ _ _ (E.torsionBaseChangeHom N p) (E.torsionBaseChangeHom N p) p
    (E.torsion_baseChange_isPullback N p).w.symm (E.torsion_baseChange_isPullback N p).w.symm

/-- **(β2, ambient square)** The torsion self-product commutes with base change: the square
`E_T[N] ×_T E_T[N] → E[N] ×_S E[N]`, `→ T`, `E[N] ×_S E[N] → S`, `T → S` is cartesian
(both structure maps through the first projection). Proved by hand from the universal
properties, threading each leg through the single-factor square
`torsion_baseChange_isPullback`. -/
theorem torsionPair_baseChange_isPullback :
    IsPullback (torsionPairBaseChangeHom E p N)
      (pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ≫
        (E.baseChange p).torsionπ N)
      (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) p := by
  have hsq := E.torsion_baseChange_isPullback N p
  have hw : torsionPairBaseChangeHom E p N ≫
        pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N
      = (pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ≫
          (E.baseChange p).torsionπ N) ≫ p := by
    rw [torsionPairBaseChangeHom, ← Category.assoc, pullback.lift_fst, Category.assoc,
      hsq.w, ← Category.assoc, Category.assoc]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift
      (hsq.lift (s.fst ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) s.snd
        (by rw [Category.assoc, s.condition]))
      (hsq.lift (s.fst ≫ pullback.snd (E.torsionπ N) (E.torsionπ N)) s.snd
        (by rw [Category.assoc, ← pullback.condition, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd]))
    (fun s => ?_) (fun s => ?_) (fun s m hm1 hm2 => ?_))
  · -- fac (first projection of the cone = the comparison map)
    apply pullback.hom_ext
    · rw [Category.assoc, torsionPairBaseChangeHom, pullback.lift_fst,
        ← Category.assoc, pullback.lift_fst, IsPullback.lift_fst]
    · rw [Category.assoc, torsionPairBaseChangeHom, pullback.lift_snd,
        ← Category.assoc, pullback.lift_snd, IsPullback.lift_fst]
  · -- fac (second projection = the T-structure)
    rw [← Category.assoc, pullback.lift_fst, IsPullback.lift_snd]
  · -- uniqueness
    apply pullback.hom_ext
    · apply hsq.hom_ext
      · have h1 := congrArg (· ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) hm1
        simp only [Category.assoc, torsionPairBaseChangeHom, pullback.lift_fst] at h1
        simpa only [Category.assoc, pullback.lift_fst_assoc, IsPullback.lift_fst] using h1
      · simpa only [Category.assoc, pullback.lift_fst_assoc, IsPullback.lift_snd] using hm2
    · apply hsq.hom_ext
      · have h1 := congrArg (· ≫ pullback.snd (E.torsionπ N) (E.torsionπ N)) hm1
        simp only [Category.assoc, torsionPairBaseChangeHom, pullback.lift_snd] at h1
        simpa only [Category.assoc, pullback.lift_snd_assoc, IsPullback.lift_fst] using h1
      · have hm2' : m ≫ pullback.snd ((E.baseChange p).torsionπ N)
            ((E.baseChange p).torsionπ N) ≫ (E.baseChange p).torsionπ N = s.snd := by
          rw [← pullback.condition, ← Category.assoc]
          exact hm2
        simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
          IsPullback.lift_fst, IsPullback.lift_snd, ← pullback.condition] using hm2'

/-- **(β2-L)** The base change of the level space along `p : T ⟶ S` is the pullback of its
closed immersion along the ambient comparison map:
`U_{Γ(N)} ×_S T ≅ U_{Γ(N)} ×_{E[N] ×_S E[N]} (E_T[N] ×_T E_T[N])`. Composite of the
pasting cancellation `pullbackRightPullbackFstIso` with the leg-transport along
`torsionPair_baseChange_isPullback.isoPullback`. -/
noncomputable def levelSpacePullbackIso :
    pullback (levelSpaceΓι E N ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) p
      ≅ pullback (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N) :=
  (pullbackRightPullbackFstIso
      (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) p (levelSpaceΓι E N)).symm
    ≪≫ asIso (pullback.map _ _ _ _ (𝟙 _)
        (torsionPair_baseChange_isPullback E p N).isoPullback.inv (𝟙 _)
        (by simp)
        (by
          rw [Category.comp_id]
          exact ((torsionPair_baseChange_isPullback E p N).isoPullback_inv_fst).symm))

/-- The `L`-projection triangle of `levelSpacePullbackIso`. -/
@[reassoc]
theorem levelSpacePullbackIso_hom_fst :
    (levelSpacePullbackIso E p N).hom ≫
        pullback.fst (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N)
      = pullback.fst
          (levelSpaceΓι E N ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) p := by
  rw [levelSpacePullbackIso]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_inv_fst]

/-- The `T`-structure triangle of `levelSpacePullbackIso`: the second projection of the
pulled-back subscheme, followed by the primed ambient structure map, is the base-changed
structure map. -/
@[reassoc]
theorem levelSpacePullbackIso_hom_snd_struct :
    (levelSpacePullbackIso E p N).hom ≫
        pullback.snd (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N) ≫
        pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N) ≫
        (E.baseChange p).torsionπ N
      = pullback.snd
          (levelSpaceΓι E N ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) p := by
  rw [levelSpacePullbackIso]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), pullback.lift_snd]
  rw [Category.assoc, (torsionPair_baseChange_isPullback E p N).isoPullback_inv_snd]
  rw [Iso.inv_comp_eq]
  exact (pullbackRightPullbackFstIso_hom_snd
    (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) p (levelSpaceΓι E N)).symm

end PairBaseChange

end ModularCurves
