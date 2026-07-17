/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LevelSpaces
import ModularCurves.LevelStructure.FullLevelDictionary
import ModularCurves.Moduli.DrinfeldRepresentability
import ModularCurves.GroupScheme.TorsionEtaleTriv
import ModularCurves.GroupScheme.TorsionCombination
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

section BridgeCompat

variable (E : EllipticCurve S)

/-- Transport of points along an equality of base morphisms (the `assoc`-alignment glue for
double base changes). -/
noncomputable def _root_.ModularCurves.EllipticCurve.Point.congrBase {T : Scheme.{u}}
    {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) : E.Point g₁ ≃+ E.Point g₂ :=
  h ▸ AddEquiv.refl (E.Point g₁)

@[simp]
lemma _root_.ModularCurves.EllipticCurve.Point.congrBase_apply_coe {T : Scheme.{u}}
    {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) (x : E.Point g₁) :
    ((EllipticCurve.Point.congrBase E h) x).1 = x.1 := by
  subst h
  rfl

/-- The pull of a point along a further morphism: `⟨u ≫ P.1, _⟩`. The general-`g` form of
`Point.pull` (which is the `g = 𝟙 S` case). -/
noncomputable def _root_.ModularCurves.EllipticCurve.Point.pullAlong {T T' : Scheme.{u}}
    {g : T ⟶ S} (u : T' ⟶ T) (P : E.Point g) : E.Point (u ≫ g) :=
  ⟨u ≫ P.1, by rw [Category.assoc, P.2]⟩

/-- **(β2-heart compat)** The base-change point dictionary carries the pull of the tautological
section back to the pull of the underlying point: for `P : E.Point σ` and `t̄ : T' ⟶ T`,
`baseChangeEquiv (pull t̄ (asSection P)) = pullAlong t̄ P`. Pure coe-chase. -/
lemma baseChangeEquiv_pull_asSection {T T' : Scheme.{u}} (σ : T ⟶ S) (u : T' ⟶ T)
    (P : E.Point σ) :
    (EllipticCurve.Point.baseChangeEquiv E σ u)
        (EllipticCurve.Point.pull (E.baseChange σ) u (EllipticCurve.Point.asSection E σ P))
      = EllipticCurve.Point.pullAlong E u P := by
  refine Subtype.ext ?_
  show (u ≫ (EllipticCurve.Point.asSection E σ P).1) ≫ pullback.fst E.π σ = u ≫ P.1
  rw [Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

/-- Kill-transport across `asSection`: `n • asSection g P = 0 ↔ n • P = 0`
(`asSection` is an injective additive map). -/
lemma zsmul_asSection_eq_zero_iff {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) (P : E.Point g) :
    n • EllipticCurve.Point.asSection E g P = 0 ↔ n • P = 0 := by
  rw [← EllipticCurve.Point.asSection_zsmul]
  constructor
  · intro h
    exact asSection_injective E g (h.trans (asSection_zero E g).symm)
  · intro h
    rw [h, asSection_zero]

end BridgeCompat

section BridgeU2

open EllipticCurve

variable (E : EllipticCurve S) {T V : Scheme.{u}} (p : T ⟶ S) (t' : V ⟶ T)

/-- The geometric-point transport chain of the bridge: points of the doubly base-changed curve
over `tb` are points of the once base-changed curve at the composite, matched to the
composite-base-changed curve through associativity. -/
noncomputable def bridgeEquiv {W : Scheme.{u}} (tb : W ⟶ V) :
    ((E.baseChange p).baseChange t').Point tb ≃+ (E.baseChange (t' ≫ p)).Point tb :=
  ((Point.baseChangeEquiv (E.baseChange p) t' tb).trans
    ((Point.baseChangeEquiv E p (tb ≫ t')).trans
      (Point.congrBase E (Category.assoc tb t' p)))).trans
    (Point.baseChangeEquiv E (t' ≫ p) tb).symm

/-- **(β2-heart U2, generator transport)** The bridge equivalence carries the pulled tautological
section of the double base change to the pulled tautological section of the composite base
change. Pure coe-chase through `baseChangeEquiv_pull_asSection` on both levels. -/
lemma bridgeEquiv_pull_asSection {W : Scheme.{u}} (tb : W ⟶ V)
    (R : (E.baseChange p).Point t') :
    bridgeEquiv E p t' tb
        (Point.pull ((E.baseChange p).baseChange t') tb (Point.asSection (E.baseChange p) t' R))
      = Point.pull (E.baseChange (t' ≫ p)) tb
          (Point.asSection E (t' ≫ p) ((Point.baseChangeEquiv E p t') R)) := by
  rw [bridgeEquiv]
  simp only [AddEquiv.trans_apply]
  rw [baseChangeEquiv_pull_asSection]
  rw [AddEquiv.symm_apply_eq]
  rw [baseChangeEquiv_pull_asSection]
  refine Subtype.ext ?_
  rw [EllipticCurve.Point.congrBase_apply_coe]
  show ((Point.baseChangeEquiv E p (tb ≫ t')) (Point.pullAlong (E.baseChange p) tb R)).1
      = (Point.pullAlong E tb ((Point.baseChangeEquiv E p t') R)).1
  show (tb ≫ R.1) ≫ pullback.fst E.π p = tb ≫ (R.1 ≫ pullback.fst E.π p)
  rw [Category.assoc]

/-- **(β2-heart U2, THE BRIDGE)** Drinfeld full-levelness transports across double base change:
the pair `(P', Q')` of points of `E_T` over `t' : V ⟶ T` gives a full level structure on
`(E_T)_V` iff its composite-transport gives one on `E_V` (base change along `t' ≫ p`). Route:
`isFullLevel_iff_naive` on both sides (T-D8), then the naive form — killing plus
geometric-fibre generation — transports along the additive dictionaries: killing via
`zsmul_asSection_eq_zero_iff` + `map_zsmul`, generation per geometric point via `bridgeEquiv`
(whose action on the generators is `bridgeEquiv_pull_asSection`) and `map_closure`. -/
theorem isFullLevel_baseChange_comp_iff (N : ℕ) [NeZero N] (hNV : NIsInvertible V N)
    (P' Q' : (E.baseChange p).Point t') :
    (E.baseChange (t' ≫ p)).IsFullLevel N
        (Point.asSection E (t' ≫ p) ((Point.baseChangeEquiv E p t') P'))
        (Point.asSection E (t' ≫ p) ((Point.baseChangeEquiv E p t') Q'))
      ↔ ((E.baseChange p).baseChange t').IsFullLevel N
          (Point.asSection (E.baseChange p) t' P')
          (Point.asSection (E.baseChange p) t' Q') := by
  have hzkill : ∀ R : (E.baseChange p).Point t',
      ((N : ℤ) • (Point.baseChangeEquiv E p t') R = 0 ↔ (N : ℤ) • R = 0) := by
    intro R
    constructor
    · intro h0
      have h1 : (Point.baseChangeEquiv E p t') ((N : ℤ) • R) = 0 :=
        ((Point.baseChangeEquiv E p t').toAddMonoidHom.map_zsmul ((N : ℤ)) R).trans h0
      exact (Point.baseChangeEquiv E p t').injective
        (h1.trans ((Point.baseChangeEquiv E p t').toAddMonoidHom.map_zero).symm)
    · intro h0
      calc (N : ℤ) • (Point.baseChangeEquiv E p t') R
          = (Point.baseChangeEquiv E p t') ((N : ℤ) • R) :=
            ((Point.baseChangeEquiv E p t').toAddMonoidHom.map_zsmul ((N : ℤ)) R).symm
        _ = 0 := by rw [h0]; exact (Point.baseChangeEquiv E p t').toAddMonoidHom.map_zero
  rw [isFullLevel_iff_naive' _ N hNV, isFullLevel_iff_naive' _ N hNV]
  unfold EllipticCurve.IsNaiveFullLevel
  refine and_congr (and_congr ?_ ?_) ?_
  · rw [zsmul_asSection_eq_zero_iff, zsmul_asSection_eq_zero_iff]
    exact hzkill P'
  · rw [zsmul_asSection_eq_zero_iff, zsmul_asSection_eq_zero_iff]
    exact hzkill Q'
  · constructor
    · intro h k _ _ tb x' hx'
      have hkill : (N : ℤ) • ((bridgeEquiv E p t' tb) x') = 0 := by
        calc (N : ℤ) • (bridgeEquiv E p t' tb) x'
            = (bridgeEquiv E p t' tb) ((N : ℤ) • x') :=
              ((bridgeEquiv E p t' tb).toAddMonoidHom.map_zsmul ((N : ℤ)) x').symm
          _ = 0 := by rw [hx']; exact (bridgeEquiv E p t' tb).toAddMonoidHom.map_zero
      have hx := h k tb ((bridgeEquiv E p t' tb) x') hkill
      have hset : ({Point.pull (E.baseChange (t' ≫ p)) tb
            (Point.asSection E (t' ≫ p) ((Point.baseChangeEquiv E p t') P')),
          Point.pull (E.baseChange (t' ≫ p)) tb
            (Point.asSection E (t' ≫ p) ((Point.baseChangeEquiv E p t') Q'))} :
            Set ((E.baseChange (t' ≫ p)).Point tb))
          = ⇑(bridgeEquiv E p t' tb).toAddMonoidHom ''
              {Point.pull ((E.baseChange p).baseChange t') tb
                  (Point.asSection (E.baseChange p) t' P'),
                Point.pull ((E.baseChange p).baseChange t') tb
                  (Point.asSection (E.baseChange p) t' Q')} := by
        rw [Set.image_insert_eq, Set.image_singleton]
        show _ = ({(bridgeEquiv E p t' tb) _, (bridgeEquiv E p t' tb) _} : Set _)
        rw [bridgeEquiv_pull_asSection, bridgeEquiv_pull_asSection]
      rw [hset, ← AddMonoidHom.map_closure] at hx
      have hmem := (AddSubgroup.mem_map_equiv (f := bridgeEquiv E p t' tb)).mp hx
      rwa [AddEquiv.symm_apply_apply] at hmem
    · intro h k _ _ tb x hx
      have hkill : (N : ℤ) • ((bridgeEquiv E p t' tb).symm x) = 0 := by
        calc (N : ℤ) • (bridgeEquiv E p t' tb).symm x
            = (bridgeEquiv E p t' tb).symm ((N : ℤ) • x) :=
              ((bridgeEquiv E p t' tb).symm.toAddMonoidHom.map_zsmul ((N : ℤ)) x).symm
          _ = 0 := by rw [hx]; exact (bridgeEquiv E p t' tb).symm.toAddMonoidHom.map_zero
      have hx' := h k tb ((bridgeEquiv E p t' tb).symm x) hkill
      have hset : ({Point.pull ((E.baseChange p).baseChange t') tb
            (Point.asSection (E.baseChange p) t' P'),
          Point.pull ((E.baseChange p).baseChange t') tb
            (Point.asSection (E.baseChange p) t' Q')} :
            Set (((E.baseChange p).baseChange t').Point tb))
          = ⇑(bridgeEquiv E p t' tb).symm.toAddMonoidHom ''
              {Point.pull (E.baseChange (t' ≫ p)) tb
                  (Point.asSection E (t' ≫ p) ((Point.baseChangeEquiv E p t') P')),
                Point.pull (E.baseChange (t' ≫ p)) tb
                  (Point.asSection E (t' ≫ p) ((Point.baseChangeEquiv E p t') Q'))} := by
        rw [Set.image_insert_eq, Set.image_singleton]
        show _ = ({(bridgeEquiv E p t' tb).symm _, (bridgeEquiv E p t' tb).symm _} : Set _)
        rw [← bridgeEquiv_pull_asSection, ← bridgeEquiv_pull_asSection,
          AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      rw [hset, ← AddMonoidHom.map_closure] at hx'
      have hmem := (AddSubgroup.mem_map_equiv (f := (bridgeEquiv E p t' tb).symm)).mp hx'
      rwa [AddEquiv.symm_symm, AddEquiv.apply_symm_apply] at hmem

end BridgeU2

section FactorAssembly

open EllipticCurve

variable (E : EllipticCurve S) {T : Scheme.{u}} (p : T ⟶ S) (N : ℕ) [NeZero N]

/-- **(β2-heart U3, the factor-iff)** A `V`-point of the primed torsion ambient
`E_T[N] ×_T E_T[N]` factors through the pulled-back level space iff it factors through the
level space of the base-changed curve: both factorizations classify the same Drinfeld
full-level condition, matched by `levelSpaceΓ_spec` on either curve and the U2 bridge
`isFullLevel_baseChange_comp_iff`. This is the hypothesis of `exists_iso_of_factor_iff`. -/
theorem factor_pulled_iff_factor_levelSpace (hinv : NIsInvertible S N) {V : Scheme.{u}}
    (v : V ⟶ pullback ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N)) :
    (∃ w : V ⟶ pullback (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N),
        w ≫ pullback.snd (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N) = v)
      ↔ ∃ w' : V ⟶ levelSpaceΓ (E.baseChange p) N,
          w' ≫ levelSpaceΓι (E.baseChange p) N = v := by
  set v1 := v ≫ pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N)
    with hv1
  set v2 := v ≫ pullback.snd ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N)
    with hv2
  set tV : V ⟶ T := v1 ≫ (E.baseChange p).torsionπ N with htV
  have hv2π : v2 ≫ (E.baseChange p).torsionπ N = tV := by
    rw [hv2, htV, hv1, Category.assoc, Category.assoc, ← pullback.condition]
  -- the two tautological points of `E_T` over `tV`
  have hP'over : (v1 ≫ (E.baseChange p).torsionι N) ≫ (E.baseChange p).π = tV := by
    rw [Category.assoc, (E.baseChange p).torsionι_π N]
  have hQ'over : (v2 ≫ (E.baseChange p).torsionι N) ≫ (E.baseChange p).π = tV := by
    rw [Category.assoc, (E.baseChange p).torsionι_π N, hv2π]
  set P' : (E.baseChange p).Point tV := ⟨v1 ≫ (E.baseChange p).torsionι N, hP'over⟩
    with hP'def
  set Q' : (E.baseChange p).Point tV := ⟨v2 ≫ (E.baseChange p).torsionι N, hQ'over⟩
    with hQ'def
  have hcondT : (E.baseChange p).torsionι N ≫ (E.baseChange p).mulByHom N
      = (E.baseChange p).torsionπ N ≫ (E.baseChange p).zero := pullback.condition
  have hP' : P'.1 ≫ (E.baseChange p).mulByHom N = tV ≫ (E.baseChange p).zero := by
    show (v1 ≫ (E.baseChange p).torsionι N) ≫ _ = _
    rw [Category.assoc, hcondT, ← Category.assoc]
  have hQ' : Q'.1 ≫ (E.baseChange p).mulByHom N = tV ≫ (E.baseChange p).zero := by
    show (v2 ≫ (E.baseChange p).torsionι N) ≫ _ = _
    rw [Category.assoc, hcondT, ← Category.assoc, hv2π]
  -- the corresponding points of `E` over `tV ≫ p`
  have hPE : ((Point.baseChangeEquiv E p tV) P').1 ≫ E.mulByHom N = (tV ≫ p) ≫ E.zero := by
    refine (E.smul_eq_zero_iff_comp_mulByHom (tV ≫ p) N _).mp ?_
    have hkP' : (N : ℤ) • P' = 0 :=
      ((E.baseChange p).smul_eq_zero_iff_comp_mulByHom tV N P').mpr hP'
    calc (N : ℤ) • (Point.baseChangeEquiv E p tV) P'
        = (Point.baseChangeEquiv E p tV) ((N : ℤ) • P') :=
          ((Point.baseChangeEquiv E p tV).toAddMonoidHom.map_zsmul ((N : ℤ)) P').symm
      _ = 0 := by rw [hkP']; exact (Point.baseChangeEquiv E p tV).toAddMonoidHom.map_zero
  have hQE : ((Point.baseChangeEquiv E p tV) Q').1 ≫ E.mulByHom N = (tV ≫ p) ≫ E.zero := by
    refine (E.smul_eq_zero_iff_comp_mulByHom (tV ≫ p) N _).mp ?_
    have hkQ' : (N : ℤ) • Q' = 0 :=
      ((E.baseChange p).smul_eq_zero_iff_comp_mulByHom tV N Q').mpr hQ'
    calc (N : ℤ) • (Point.baseChangeEquiv E p tV) Q'
        = (Point.baseChangeEquiv E p tV) ((N : ℤ) • Q') :=
          ((Point.baseChangeEquiv E p tV).toAddMonoidHom.map_zsmul ((N : ℤ)) Q').symm
      _ = 0 := by rw [hkQ']; exact (Point.baseChangeEquiv E p tV).toAddMonoidHom.map_zero
  -- reconstruction on the primed side: the classifying lift of `(P', Q')` IS `v`
  have hptt1 : (E.baseChange p).pointToTorsion P' hP' = v1 := by
    apply pullback.hom_ext
    · show (E.baseChange p).pointToTorsion P' hP' ≫ (E.baseChange p).torsionι N
        = v1 ≫ (E.baseChange p).torsionι N
      rw [(E.baseChange p).pointToTorsion_torsionι P' hP']
    · show (E.baseChange p).pointToTorsion P' hP' ≫ (E.baseChange p).torsionπ N
        = v1 ≫ (E.baseChange p).torsionπ N
      rw [(E.baseChange p).pointToTorsion_torsionπ P' hP', htV]
  have hptt2 : (E.baseChange p).pointToTorsion Q' hQ' = v2 := by
    apply pullback.hom_ext
    · show (E.baseChange p).pointToTorsion Q' hQ' ≫ (E.baseChange p).torsionι N
        = v2 ≫ (E.baseChange p).torsionι N
      rw [(E.baseChange p).pointToTorsion_torsionι Q' hQ']
    · show (E.baseChange p).pointToTorsion Q' hQ' ≫ (E.baseChange p).torsionπ N
        = v2 ≫ (E.baseChange p).torsionπ N
      rw [(E.baseChange p).pointToTorsion_torsionπ Q' hQ', hv2π]
  have hrecT : pullback.lift ((E.baseChange p).pointToTorsion P' hP')
      ((E.baseChange p).pointToTorsion Q' hQ') (by simp) = v := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hptt1]
    · rw [pullback.lift_snd, hptt2]
  -- reconstruction on the base side: the classifying lift of the transported pair is
  -- `v ≫ torsionPairBaseChangeHom`
  have hκι : E.torsionBaseChangeHom N p ≫ E.torsionι N
      = (E.baseChange p).torsionι N ≫ pullback.fst E.π p := E.torsionBaseChangeHom_torsionι N p
  have hκπ : E.torsionBaseChangeHom N p ≫ E.torsionπ N
      = (E.baseChange p).torsionπ N ≫ p := E.torsionBaseChangeHom_torsionπ N p
  have hpttE1 : E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE
      = v1 ≫ E.torsionBaseChangeHom N p := by
    apply pullback.hom_ext
    · show E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE ≫ E.torsionι N
        = (v1 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionι N
      calc E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE ≫ E.torsionι N
          = ((Point.baseChangeEquiv E p tV) P').1 := E.pointToTorsion_torsionι _ hPE
        _ = (v1 ≫ (E.baseChange p).torsionι N) ≫ pullback.fst E.π p := rfl
        _ = v1 ≫ ((E.baseChange p).torsionι N ≫ pullback.fst E.π p) := Category.assoc _ _ _
        _ = v1 ≫ (E.torsionBaseChangeHom N p ≫ E.torsionι N) := by rw [hκι]
        _ = (v1 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionι N := (Category.assoc _ _ _).symm
    · show E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE ≫ E.torsionπ N
        = (v1 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionπ N
      calc E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE ≫ E.torsionπ N
          = tV ≫ p := E.pointToTorsion_torsionπ _ hPE
        _ = (v1 ≫ (E.baseChange p).torsionπ N) ≫ p := by rw [htV]
        _ = v1 ≫ ((E.baseChange p).torsionπ N ≫ p) := Category.assoc _ _ _
        _ = v1 ≫ (E.torsionBaseChangeHom N p ≫ E.torsionπ N) := by rw [hκπ]
        _ = (v1 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionπ N := (Category.assoc _ _ _).symm
  have hpttE2 : E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE
      = v2 ≫ E.torsionBaseChangeHom N p := by
    apply pullback.hom_ext
    · show E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE ≫ E.torsionι N
        = (v2 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionι N
      calc E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE ≫ E.torsionι N
          = ((Point.baseChangeEquiv E p tV) Q').1 := E.pointToTorsion_torsionι _ hQE
        _ = (v2 ≫ (E.baseChange p).torsionι N) ≫ pullback.fst E.π p := rfl
        _ = v2 ≫ ((E.baseChange p).torsionι N ≫ pullback.fst E.π p) := Category.assoc _ _ _
        _ = v2 ≫ (E.torsionBaseChangeHom N p ≫ E.torsionι N) := by rw [hκι]
        _ = (v2 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionι N := (Category.assoc _ _ _).symm
    · show E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE ≫ E.torsionπ N
        = (v2 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionπ N
      calc E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE ≫ E.torsionπ N
          = tV ≫ p := E.pointToTorsion_torsionπ _ hQE
        _ = (v2 ≫ (E.baseChange p).torsionπ N) ≫ p := by rw [← hv2π]
        _ = v2 ≫ ((E.baseChange p).torsionπ N ≫ p) := Category.assoc _ _ _
        _ = v2 ≫ (E.torsionBaseChangeHom N p ≫ E.torsionπ N) := by rw [hκπ]
        _ = (v2 ≫ E.torsionBaseChangeHom N p) ≫ E.torsionπ N := (Category.assoc _ _ _).symm
  have hrecE : pullback.lift (E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE)
      (E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE) (by simp)
      = v ≫ torsionPairBaseChangeHom E p N := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      calc E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE
          = v1 ≫ E.torsionBaseChangeHom N p := hpttE1
        _ = (v ≫ pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N))
              ≫ E.torsionBaseChangeHom N p := by rw [hv1]
        _ = v ≫ (pullback.fst ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N)
              ≫ E.torsionBaseChangeHom N p) := Category.assoc _ _ _
        _ = v ≫ (torsionPairBaseChangeHom E p N
              ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) := by
            rw [torsionPairBaseChangeHom, pullback.lift_fst]
        _ = (v ≫ torsionPairBaseChangeHom E p N)
              ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) := (Category.assoc _ _ _).symm
    · rw [pullback.lift_snd]
      calc E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE
          = v2 ≫ E.torsionBaseChangeHom N p := hpttE2
        _ = (v ≫ pullback.snd ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N))
              ≫ E.torsionBaseChangeHom N p := by rw [hv2]
        _ = v ≫ (pullback.snd ((E.baseChange p).torsionπ N) ((E.baseChange p).torsionπ N)
              ≫ E.torsionBaseChangeHom N p) := Category.assoc _ _ _
        _ = v ≫ (torsionPairBaseChangeHom E p N
              ≫ pullback.snd (E.torsionπ N) (E.torsionπ N)) := by
            rw [torsionPairBaseChangeHom, pullback.lift_snd]
        _ = (v ≫ torsionPairBaseChangeHom E p N)
              ≫ pullback.snd (E.torsionπ N) (E.torsionπ N) := (Category.assoc _ _ _).symm
  -- assemble the chain
  have hNV : NIsInvertible V N := NIsInvertible.of_hom (tV ≫ p) hinv
  constructor
  · rintro ⟨w, hw⟩
    -- factor through the pulled-back subscheme ⟹ the composite factors through `U_Γ(E)`
    have hu : ∃ u : V ⟶ levelSpaceΓ E N,
        u ≫ levelSpaceΓι E N = v ≫ torsionPairBaseChangeHom E p N := by
      refine ⟨w ≫ pullback.fst (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N), ?_⟩
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    rw [← hrecE] at hu
    have hfullE := (levelSpaceΓ_spec E N (tV ≫ p) ((Point.baseChangeEquiv E p tV) P')
      ((Point.baseChangeEquiv E p tV) Q') hPE hQE).mp hu
    have hfullT := (isFullLevel_baseChange_comp_iff E p tV N hNV P' Q').mp hfullE
    have := (levelSpaceΓ_spec (E.baseChange p) N tV P' Q' hP' hQ').mpr hfullT
    rwa [hrecT] at this
  · rintro ⟨w', hw'⟩
    have hv' : ∃ h : V ⟶ levelSpaceΓ (E.baseChange p) N,
        h ≫ levelSpaceΓι (E.baseChange p) N = pullback.lift
          ((E.baseChange p).pointToTorsion P' hP')
          ((E.baseChange p).pointToTorsion Q' hQ') (by simp) := by
      refine ⟨w', ?_⟩
      rw [hrecT, hw']
    have hfullT := (levelSpaceΓ_spec (E.baseChange p) N tV P' Q' hP' hQ').mp hv'
    have hfullE := (isFullLevel_baseChange_comp_iff E p tV N hNV P' Q').mpr hfullT
    have hu := (levelSpaceΓ_spec E N (tV ≫ p) ((Point.baseChangeEquiv E p tV) P')
      ((Point.baseChangeEquiv E p tV) Q') hPE hQE).mpr hfullE
    rw [hrecE] at hu
    obtain ⟨u, hu⟩ := hu
    exact ⟨pullback.lift u v hu, pullback.lift_snd _ _ _⟩

/-- **(β2 COMPLETE — the base-change identification of the level space)** The pulled-back level
space is the level space of the base-changed curve, as closed subschemes of the primed torsion
ambient: `exists_iso_of_factor_iff` applied to `factor_pulled_iff_factor_levelSpace`. -/
theorem exists_levelSpace_baseChange_iso (hinv : NIsInvertible S N) :
    ∃ e : pullback (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N)
        ≅ levelSpaceΓ (E.baseChange p) N,
      e.hom ≫ levelSpaceΓι (E.baseChange p) N
        = pullback.snd (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N) := by
  haveI h1 : IsClosedImmersion (levelSpaceΓι E N) :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.subschemeι _))
  haveI h2 : IsClosedImmersion (levelSpaceΓι (E.baseChange p) N) :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.subschemeι _))
  haveI h3 : IsClosedImmersion
      (pullback.snd (levelSpaceΓι E N) (torsionPairBaseChangeHom E p N)) :=
    MorphismProperty.pullback_snd _ _ h1
  exact exists_iso_of_factor_iff _ _
    (fun V v => factor_pulled_iff_factor_levelSpace E p N hinv v)

end FactorAssembly

section CombinationLocus

open EllipticCurve

variable (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- The first tautological `N`-torsion point of `E` over the torsion self-product
`E[N] ×_S E[N]`. -/
noncomputable def tautFst :
    E.Point (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) :=
  ⟨pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N, by
    rw [Category.assoc, E.torsionι_π N]⟩

/-- The second tautological `N`-torsion point (over the same structure map, via the
pullback condition of the self-product). -/
noncomputable def tautSnd :
    E.Point (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) :=
  ⟨pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N, by
    rw [Category.assoc, E.torsionι_π N, ← pullback.condition]⟩

/-- The torsion-kernel condition, spelled at the `torsionι`/`torsionπ` names. -/
lemma torsion_kernel_condition :
    E.torsionι N ≫ E.mulByHom N = E.torsionπ N ≫ E.zero := pullback.condition

lemma tautFst_killed : (N : ℤ) • tautFst E N = 0 := by
  rw [E.smul_eq_zero_iff_comp_mulByHom]
  show (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N) ≫ E.mulByHom N = _
  rw [Category.assoc, torsion_kernel_condition, ← Category.assoc]

lemma tautSnd_killed : (N : ℤ) • tautSnd E N = 0 := by
  rw [E.smul_eq_zero_iff_comp_mulByHom]
  show (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N) ≫ E.mulByHom N = _
  rw [Category.assoc, torsion_kernel_condition, ← Category.assoc, ← pullback.condition]

/-- The `(a, b)` combination point `a•P + b•Q` of the tautological pair. -/
noncomputable def combo (a b : ℤ) :
    E.Point (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) :=
  a • tautFst E N + b • tautSnd E N

lemma combo_killed (a b : ℤ) : (N : ℤ) • combo E N a b = 0 := by
  rw [combo, smul_add, smul_comm (N : ℤ) a, smul_comm (N : ℤ) b,
    tautFst_killed, tautSnd_killed, smul_zero, smul_zero, add_zero]

/-- The classifying map of the `(a, b)` combination to the torsion scheme. -/
noncomputable def comboMap (a b : ℤ) :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ E.torsion N :=
  E.pointToTorsion (combo E N a b)
    ((E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (combo_killed E N a b))

/-- The zero section of the torsion scheme. -/
noncomputable def torsionZero : S ⟶ E.torsion N :=
  pullback.lift E.zero (𝟙 S) (by
    have h0 : ((0 : E.Point (𝟙 S)) : S ⟶ E.E) ≫ E.mulByHom (N : ℤ) = 𝟙 S ≫ E.zero :=
      (E.smul_eq_zero_iff_comp_mulByHom (𝟙 S) N 0).mp (smul_zero _)
    rw [E.point_zero_val, Category.id_comp] at h0
    rw [Category.id_comp]
    exact h0)

@[simp]
lemma torsionZero_torsionπ : torsionZero E N ≫ E.torsionπ N = 𝟙 S :=
  pullback.lift_snd _ _ _

/-- **(β3, the zero locus is clopen)** For `N` invertible the range of the zero section of
`E[N]` is clopen: the section is a closed immersion (cancellation against the separated
`torsionπ`) and étale (cancellation of the identity against the étale `torsionπ`), so its
range is closed and open. -/
lemma isClopen_range_torsionZero (hinv : NIsInvertible S N) :
    IsClopen (Set.range (torsionZero E N).base) := by
  haveI hfin : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI het : Etale (E.torsionπ N) := E.torsionπ_etale N hinv
  haveI : IsClosedImmersion (torsionZero E N) := by
    have h1 : IsClosedImmersion (torsionZero E N ≫ E.torsionπ N) := by
      rw [torsionZero_torsionπ]
      infer_instance
    exact IsClosedImmersion.of_comp (f := torsionZero E N) (g := E.torsionπ N)
  haveI : Etale (torsionZero E N) := by
    have h1 : Etale (torsionZero E N ≫ E.torsionπ N) := by
      rw [torsionZero_torsionπ]
      infer_instance
    exact Etale.of_comp (torsionZero E N) (E.torsionπ N)
  constructor
  · exact (torsionZero E N).isClosedMap.isClosed_range
  · exact (torsionZero E N).isOpenMap.isOpen_range

/-- **(β3, the good locus)** The set of points of `E[N] ×_S E[N]` where every nonzero
`(ℤ/N)²`-combination of the tautological pair avoids the zero section. -/
def fullLevelLocusSet : Set ↥(pullback (E.torsionπ N) (E.torsionπ N)) :=
  ⋂ (ab : {ab : ZMod N × ZMod N // ab ≠ 0}),
    (comboMap E N (ab.1.1.val : ℤ) (ab.1.2.val : ℤ)).base ⁻¹'
      (Set.range (torsionZero E N).base)ᶜ

/-- **(β3, the good locus is clopen)** A finite intersection of preimages of the clopen
complement of the zero locus. -/
lemma isClopen_fullLevelLocusSet (hinv : NIsInvertible S N) :
    IsClopen (fullLevelLocusSet E N) := by
  haveI : Finite {ab : ZMod N × ZMod N // ab ≠ 0} := by
    haveI : NeZero N := ‹_›
    infer_instance
  refine isClopen_iInter_of_finite fun ab => ?_
  exact ((isClopen_range_torsionZero E N hinv).compl.preimage
    (Scheme.Hom.continuous _))

end CombinationLocus

section PairGeneration

variable {G : Type*} [AddCommGroup G] (N : ℕ) [NeZero N]

/-- Representative independence of `ℤ`-scalars on `N`-killed elements: the `val` of the
mod-`N` reduction acts like the integer itself. -/
private lemma zsmul_val_cast_eq {P : G} (hP : (N : ℤ) • P = 0) (k : ℤ) :
    (((k : ZMod N).val : ℤ)) • P = k • P := by
  obtain ⟨m, hm⟩ : (N : ℤ) ∣ (((k : ZMod N).val : ℤ) - k) := by
    have h0 : ((((k : ZMod N).val : ℤ) - k : ℤ) : ZMod N) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h0
  have hdiff : (((k : ZMod N).val : ℤ)) • P - k • P = 0 := by
    rw [← sub_smul, hm, mul_smul, smul_comm, hP, smul_zero]
  rw [sub_eq_zero] at hdiff
  exact hdiff

/-- **(β3, the generation criterion — KM 1.6.7 / AX2-e at general `N`)** In an `N`-killed
abelian group of order `N²`, a pair generates iff every nonzero `(ℤ/N)²`-combination of it is
nonzero: the combination map `(ℤ/N)² → G` is injective iff it misses zero away from zero, and
between finite sets of equal cardinality injective = surjective = bijective. -/
theorem pair_generates_iff_combos_ne_zero
    (hcard : Nat.card G = N ^ 2) (hkill : ∀ g : G, (N : ℤ) • g = 0) (P Q : G) :
    (∀ ab : ZMod N × ZMod N, ab ≠ 0 →
        ((ab.1.val : ℤ)) • P + ((ab.2.val : ℤ)) • Q ≠ 0)
      ↔ ∀ x : G, x ∈ AddSubgroup.closure ({P, Q} : Set G) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (pow_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 2).ne')
  set φ : ZMod N × ZMod N → G :=
    fun ab => ((ab.1.val : ℤ)) • P + ((ab.2.val : ℤ)) • Q with hφ
  have hcards : Nat.card (ZMod N × ZMod N) = Nat.card G := by
    rw [Nat.card_prod, Nat.card_zmod, hcard, sq]
  constructor
  · intro hcombo x
    have hinj : Function.Injective φ := by
      intro ab cd h
      by_contra hne
      have hd : ((ab.1 - cd.1, ab.2 - cd.2) : ZMod N × ZMod N) ≠ 0 := by
        intro hzero
        apply hne
        have h1 : ab.1 - cd.1 = 0 := congrArg Prod.fst hzero
        have h2 : ab.2 - cd.2 = 0 := congrArg Prod.snd hzero
        exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
      refine hcombo _ hd ?_
      have e1 : (((ab.1 - cd.1).val : ℤ)) • P
          = ((ab.1.val : ℤ) - (cd.1.val : ℤ)) • P := by
        have hz := zsmul_val_cast_eq N (hkill P) ((ab.1.val : ℤ) - (cd.1.val : ℤ))
        have hcast : (((((ab.1.val : ℤ) - (cd.1.val : ℤ)) : ℤ) : ZMod N))
            = ab.1 - cd.1 := by
          push_cast
          rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
        rw [hcast] at hz
        exact hz
      have e2 : (((ab.2 - cd.2).val : ℤ)) • Q
          = ((ab.2.val : ℤ) - (cd.2.val : ℤ)) • Q := by
        have hz := zsmul_val_cast_eq N (hkill Q) ((ab.2.val : ℤ) - (cd.2.val : ℤ))
        have hcast : (((((ab.2.val : ℤ) - (cd.2.val : ℤ)) : ℤ) : ZMod N))
            = ab.2 - cd.2 := by
          push_cast
          rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
        rw [hcast] at hz
        exact hz
      show (((ab.1 - cd.1).val : ℤ)) • P + (((ab.2 - cd.2).val : ℤ)) • Q = 0
      have h' : ((ab.1.val : ℤ)) • P + ((ab.2.val : ℤ)) • Q
          = ((cd.1.val : ℤ)) • P + ((cd.2.val : ℤ)) • Q := h
      rw [e1, e2, sub_smul, sub_smul, sub_add_sub_comm, h', sub_self]
    have hbij : Function.Bijective φ :=
      (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcards⟩
    obtain ⟨ab, rfl⟩ := hbij.2 x
    exact AddSubgroup.mem_closure_pair.mpr ⟨_, _, rfl⟩
  · intro hgen ab hab habs
    have hsurj : Function.Surjective φ := by
      intro x
      obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp (hgen x)
      refine ⟨((m : ZMod N), (n : ZMod N)), ?_⟩
      show (((m : ZMod N).val : ℤ)) • P + (((n : ZMod N).val : ℤ)) • Q = x
      rw [zsmul_val_cast_eq N (hkill P) m, zsmul_val_cast_eq N (hkill Q) n]
      exact hmn
    have hbij : Function.Bijective φ :=
      (Nat.bijective_iff_surjective_and_card φ).mpr ⟨hsurj, hcards⟩
    have h0 : φ 0 = 0 := by
      show (((0 : ZMod N).val : ℤ)) • P + (((0 : ZMod N).val : ℤ)) • Q = 0
      simp [ZMod.val_zero]
    exact hab (hbij.1 (habs.trans h0.symm))

end PairGeneration

section LevelSpaceIdentification

open EllipticCurve

variable (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- **([DEDUP-CC] bridge)** This file's zero section agrees with the carrier-of-record's
(`GroupScheme/TorsionCombination.lean`): both are the lift of the zero point. -/
theorem torsionZero_eq : torsionZero E N = E.torsionZero N := by
  apply pullback.hom_ext
  · show torsionZero E N ≫ E.torsionι N = E.torsionZero N ≫ E.torsionι N
    rw [E.torsionZero_torsionι, E.point_zero_val, Category.id_comp]
    exact pullback.lift_fst _ _ _
  · show torsionZero E N ≫ E.torsionπ N = E.torsionZero N ≫ E.torsionπ N
    rw [E.torsionZero_torsionπ]
    exact torsionZero_torsionπ E N

/-- **([DEDUP-CC] bridge)** This file's combination maps agree with the carrier-of-record's. -/
theorem comboMap_eq (ab : ZMod N × ZMod N) :
    comboMap E N (ab.1.val : ℤ) (ab.2.val : ℤ) = E.combinationHom N ab := by
  apply pullback.hom_ext
  · show comboMap E N _ _ ≫ E.torsionι N = E.combinationHom N ab ≫ E.torsionι N
    rw [E.combinationHom_torsionι]
    exact E.pointToTorsion_torsionι _ _
  · show comboMap E N _ _ ≫ E.torsionπ N = E.combinationHom N ab ≫ E.torsionπ N
    rw [E.combinationHom_torsionπ]
    exact E.pointToTorsion_torsionπ _ _

/-- **([DEDUP-CC] bridge — the dispatched lemma)** This file's full-level locus set is the
carrier-of-record's `fullLevelSet`. -/
theorem fullLevelLocusSet_eq_fullLevelSet :
    fullLevelLocusSet E N = E.fullLevelSet N := by
  ext x
  simp only [fullLevelLocusSet, EllipticCurve.fullLevelSet, Set.mem_iInter,
    Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff]
  constructor
  · intro h v hv
    have h' := h ⟨v, hv⟩
    rwa [comboMap_eq, torsionZero_eq] at h'
  · intro h ab
    have h' := h ab.1 ab.2
    rwa [← comboMap_eq, ← torsionZero_eq] at h'

omit [NeZero N] in
/-- The tautological pair pulled along a `V`-point of the pair scheme is killed
(morphism-level form). -/
lemma pullAlong_taut_killed {V : Scheme.{u}} (v : V ⟶ E.torsionPair N)
    (P : E.Point (E.torsionPairπ N)) (hP : (N : ℤ) • P = 0) :
    ((EllipticCurve.Point.pullAlong E v P : E.Point (v ≫ E.torsionPairπ N)) :
        V ⟶ E.E) ≫ E.mulByHom N = (v ≫ E.torsionPairπ N) ≫ E.zero := by
  have h0 := (E.smul_eq_zero_iff_comp_mulByHom _ N P).mp hP
  show (v ≫ (P : _ ⟶ E.E)) ≫ E.mulByHom N = _
  rw [Category.assoc, h0, ← Category.assoc]

/-- **(the `E`-side classification)** A `V`-point of the pair scheme factors through the level
space iff its tautological pair is a Drinfeld full level structure (`levelSpaceΓ_spec` plus the
reconstruction of `v` from its two torsion legs). -/
theorem factor_levelSpace_iff_isFullLevel {V : Scheme.{u}} (v : V ⟶ E.torsionPair N) :
    (∃ w : V ⟶ levelSpaceΓ E N, w ≫ levelSpaceΓι E N = v)
      ↔ (E.baseChange (v ≫ E.torsionPairπ N)).IsFullLevel N
          (EllipticCurve.Point.asSection E _
            (EllipticCurve.Point.pullAlong E v (E.torsionPairFst N)))
          (EllipticCurve.Point.asSection E _
            (EllipticCurve.Point.pullAlong E v (E.torsionPairSnd N))) := by
  have hP := pullAlong_taut_killed E N v (E.torsionPairFst N) (E.torsionPairFst_killed N)
  have hQ := pullAlong_taut_killed E N v (E.torsionPairSnd N) (E.torsionPairSnd_killed N)
  have hspec := levelSpaceΓ_spec E N (v ≫ E.torsionPairπ N)
    (EllipticCurve.Point.pullAlong E v (E.torsionPairFst N))
    (EllipticCurve.Point.pullAlong E v (E.torsionPairSnd N)) hP hQ
  rw [← hspec]
  -- the classifying lift of the pulled pair IS `v`
  have hrec : pullback.lift
      (E.pointToTorsion (EllipticCurve.Point.pullAlong E v (E.torsionPairFst N)) hP)
      (E.pointToTorsion (EllipticCurve.Point.pullAlong E v (E.torsionPairSnd N)) hQ)
      (by simp) = v := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply pullback.hom_ext
      · show E.pointToTorsion _ hP ≫ E.torsionι N
          = (v ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionι N
        rw [E.pointToTorsion_torsionι]
        show v ≫ (E.torsionPairFst N : _ ⟶ E.E) = _
        rw [Category.assoc]
        rfl
      · show E.pointToTorsion _ hP ≫ E.torsionπ N
          = (v ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionπ N
        rw [E.pointToTorsion_torsionπ]
        rfl
    · rw [pullback.lift_snd]
      apply pullback.hom_ext
      · show E.pointToTorsion _ hQ ≫ E.torsionι N
          = (v ≫ pullback.snd (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionι N
        rw [E.pointToTorsion_torsionι]
        show v ≫ (E.torsionPairSnd N : _ ⟶ E.E) = _
        rw [Category.assoc]
        rfl
      · show E.pointToTorsion _ hQ ≫ E.torsionπ N
          = (v ≫ pullback.snd (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionπ N
        rw [E.pointToTorsion_torsionπ]
        show v ≫ E.torsionPairπ N = v ≫ pullback.snd _ _ ≫ E.torsionπ N
        rw [show pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N
          = E.torsionPairπ N from pullback.condition.symm]
  rw [hrec]

/-- **(the endgame identification, master-iff-gated)** Given the pointwise master
identification (the fibrewise generation dictionary — the [DEDUP-CC] seam to the
combination-locus classification), the level space IS the full-level locus, compatibly with
the inclusions into the pair scheme. -/
theorem exists_levelSpaceΓ_iso_fullLevelLocus (h : NIsInvertible S N)
    (hmaster : ∀ {V : Scheme.{u}} (v : V ⟶ E.torsionPair N),
      (E.baseChange (v ≫ E.torsionPairπ N)).IsFullLevel N
          (EllipticCurve.Point.asSection E _
            (EllipticCurve.Point.pullAlong E v (E.torsionPairFst N)))
          (EllipticCurve.Point.asSection E _
            (EllipticCurve.Point.pullAlong E v (E.torsionPairSnd N)))
        ↔ ∀ t : V, v.base t ∈ E.fullLevelSet N) :
    ∃ e : levelSpaceΓ E N ≅ E.fullLevelLocus N h,
      e.hom ≫ E.fullLevelLocusι N h = levelSpaceΓι E N := by
  haveI : IsClosedImmersion (levelSpaceΓι E N) :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.subschemeι _))
  haveI : IsOpenImmersion (E.fullLevelLocusι N h) :=
    inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))
  refine exists_iso_of_factor_iff _ _ (fun V v => ?_)
  rw [factor_levelSpace_iff_isFullLevel E N v, hmaster v]
  constructor
  · intro hall
    refine ⟨IsOpenImmersion.lift (E.fullLevelLocusι N h) v ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rw [Scheme.Opens.range_ι]
    rintro x ⟨t, rfl⟩
    exact hall t
  · rintro ⟨w, rfl⟩ t
    have : (E.fullLevelLocusι N h).base (w.base t) ∈
        Set.range (E.fullLevelLocusι N h).base := Set.mem_range_self _
    rw [Scheme.Opens.range_ι] at this
    exact this

/-- **(:3497-shaped)** Given the master identification, the level-space structure morphism is
étale: the identification composes it through the étale `fullLevelLocusπ`. -/
theorem levelSpaceΓ_structure_etale_of_master (h : NIsInvertible S N)
    (hmaster : ∀ {V : Scheme.{u}} (v : V ⟶ E.torsionPair N),
      (E.baseChange (v ≫ E.torsionPairπ N)).IsFullLevel N
          (EllipticCurve.Point.asSection E _
            (EllipticCurve.Point.pullAlong E v (E.torsionPairFst N)))
          (EllipticCurve.Point.asSection E _
            (EllipticCurve.Point.pullAlong E v (E.torsionPairSnd N)))
        ↔ ∀ t : V, v.base t ∈ E.fullLevelSet N) :
    Etale (levelSpaceΓι E N ≫
      pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) := by
  obtain ⟨e, he⟩ := exists_levelSpaceΓ_iso_fullLevelLocus E N h hmaster
  have hcomp : levelSpaceΓι E N ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N
      = e.hom ≫ E.fullLevelLocusπ N h := by
    rw [← he, Category.assoc]
  rw [hcomp]
  haveI := E.fullLevelLocusπ_etale N h
  infer_instance

end LevelSpaceIdentification

end ModularCurves
