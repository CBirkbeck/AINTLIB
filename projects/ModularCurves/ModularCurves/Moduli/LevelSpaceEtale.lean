/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LevelSpaces
import ModularCurves.Moduli.DrinfeldRepresentability
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
  rw [isFullLevel_iff_naive _ N hNV, isFullLevel_iff_naive _ N hNV]
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
  have hzfst : (E.baseChange p).zero ≫ pullback.fst E.π p = p ≫ E.zero :=
    pullback.lift_fst _ _ _
  have hPE : ((Point.baseChangeEquiv E p tV) P').1 ≫ E.mulByHom N = (tV ≫ p) ≫ E.zero := by
    have h0 := congrArg (· ≫ pullback.fst E.π p) hP'
    simp only [Category.assoc] at h0
    rw [mulByHom_baseChange_fst, hzfst] at h0
    show (P'.1 ≫ pullback.fst E.π p) ≫ E.mulByHom N = _
    rw [Category.assoc, h0, ← Category.assoc]
  have hQE : ((Point.baseChangeEquiv E p tV) Q').1 ≫ E.mulByHom N = (tV ≫ p) ≫ E.zero := by
    have h0 := congrArg (· ≫ pullback.fst E.π p) hQ'
    simp only [Category.assoc] at h0
    rw [mulByHom_baseChange_fst, hzfst] at h0
    show (Q'.1 ≫ pullback.fst E.π p) ≫ E.mulByHom N = _
    rw [Category.assoc, h0, ← Category.assoc]
  -- reconstruction on the primed side: the classifying lift of `(P', Q')` IS `v`
  have hptt1 : (E.baseChange p).pointToTorsion P' hP' = v1 := by
    apply pullback.hom_ext
    · rw [(E.baseChange p).pointToTorsion_torsionι P' hP']
    · rw [(E.baseChange p).pointToTorsion_torsionπ P' hP']
  have hptt2 : (E.baseChange p).pointToTorsion Q' hQ' = v2 := by
    apply pullback.hom_ext
    · rw [(E.baseChange p).pointToTorsion_torsionι Q' hQ']
    · rw [(E.baseChange p).pointToTorsion_torsionπ Q' hQ', hv2π]
  have hrecT : pullback.lift ((E.baseChange p).pointToTorsion P' hP')
      ((E.baseChange p).pointToTorsion Q' hQ') (by simp) = v := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hptt1]
    · rw [pullback.lift_snd, hptt2]
  -- reconstruction on the base side: the classifying lift of the transported pair is
  -- `v ≫ torsionPairBaseChangeHom`
  have hpttE1 : E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE
      = v1 ≫ E.torsionBaseChangeHom N p := by
    apply pullback.hom_ext
    · rw [E.pointToTorsion_torsionι _ hPE, Category.assoc, E.torsionBaseChangeHom_torsionι,
        ← Category.assoc]
      rfl
    · rw [E.pointToTorsion_torsionπ _ hPE, Category.assoc, E.torsionBaseChangeHom_torsionπ,
        ← Category.assoc]
  have hpttE2 : E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE
      = v2 ≫ E.torsionBaseChangeHom N p := by
    apply pullback.hom_ext
    · rw [E.pointToTorsion_torsionι _ hQE, Category.assoc, E.torsionBaseChangeHom_torsionι,
        ← Category.assoc]
      rfl
    · rw [E.pointToTorsion_torsionπ _ hQE, Category.assoc, E.torsionBaseChangeHom_torsionπ,
        ← Category.assoc, hv2π]
  have hrecE : pullback.lift (E.pointToTorsion ((Point.baseChangeEquiv E p tV) P') hPE)
      (E.pointToTorsion ((Point.baseChangeEquiv E p tV) Q') hQE) (by simp)
      = v ≫ torsionPairBaseChangeHom E p N := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hpttE1, hv1]
      rw [torsionPairBaseChangeHom, pullback.lift_fst, ← Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, hpttE2, hv2]
      rw [torsionPairBaseChangeHom, pullback.lift_snd, ← Category.assoc]
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

end FactorAssembly

end ModularCurves
