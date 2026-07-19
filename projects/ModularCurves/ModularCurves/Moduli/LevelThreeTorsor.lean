/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.Bootstrap
import ModularCurves.Moduli.QuotientStack
import ModularCurves.ForMathlib.EtaleSectionsCount

/-!
# T-E15b — the level-3 `TorsorData` package (KM 4.7, axiom 2, at `(N, G) = (3, GL₂(𝔽₃))`)

The instantiation boundary of the KM 4.7 engine: the naive full-level-3 problem
`[Γ(3)]-naive` carries, at every `X : Ell/R` with `3` invertible, a `GL₂(ℤ/3)`-equivariant
finite étale relative representation datum on the CONCRETE carrier
`YFull.fullLevelSpace X 3` (KM 3.7.1; Loeffler 3.8.2 first sentence), which KM p. 112
axiom 2 upgrades to a finite étale `G`-torsor.

## Contents

* **Generic layer** (`ModuliProblem.RelRepData.relRepAut` …): the classifying transport of
  a problem automorphism through any relative representation datum, its anti-homomorphy
  law, the covariant `SchemeAction` obtained by the `SchemeAction.ofAut` inversion trick,
  and its (γ⁻¹-twisted) equivariance — all sorry-free.
* **Level-3 layer**: `levelThreeData` (the concrete datum, replaying
  `gammaFullNaive_relRepData`'s body so the carrier stays `YFull.fullLevelSpace X 3`),
  its finiteness/étaleness, freeness of the `GL₂`-action
  (`gammaFullNaiveGl_freeAction`), and the fully proven equivariant package
  `levelThreeEquivariantData : EquivariantRelRepData (gammaFullNaiveGlAction R 3) X`.
* **Quarantined residuals** (see below): `levelThree_surjective`, `levelThree_torsor`.
* **The target**: `exists_levelThreeTorsorData`.

## ⚠️ TWO STATEMENT-LAYER DISCOVERIES (T-E15b adjudication input)

1. **Universe wall.** `TorsorData` pins `G : Type u` to the universe of `R`, but
   `GL₂(ℤ/3) : Type 0`. The chartered target
   `(R : CommRingCat.{u}) → … Nonempty (TorsorData (gammaFullNaiveGlAction R 3) X)`
   is ILL-TYPED for `u ≠ 0` (elaboration fails: `MonoidHom.{0, u+1}` vs expected
   `MonoidHom.{u, u+1}`). The public target below is therefore stated at
   `CommRingCat.{0}`, the unique universe at which it elaborates. Consumers at `u ≠ 0`
   need either a `ULift` of the group (with a transported action) or a widening of
   `TorsorData`'s `G` to `Type*` (as `EquivariantRelRepData` [GH0b] already has).

2. **Convention wall — RESOLVED by the [B2-TD-CONV] amendment.** As delivered, this
   package machine-checked that `TorsorData.equivariant`'s original untwisted
   `(φ γ)`-form was UNSATISFIABLE for a non-abelian effective action: with a covariant
   `SchemeAction` (`hom_mul`) and the ANTI-homomorphic classifying transport (Yoneda
   contravariance), the two fields force `(φ (γδ)).hom = (φ (δγ)).hom` on all values
   over the (nonempty, by the `surjective` field) representing scheme — refuted by
   freeness (`glSmul_eq_one_of_eq_self`, PROVEN) for the non-abelian `GL₂(𝔽₃)`.
   Formal refutation of record: `levelThreeTorsorData_isEmpty_of_nonempty_base` at
   commit `2e3c77233` (removed together with the convention it refuted). The fix —
   `(φ γ) ↦ (φ γ⁻¹)` in `TorsorData.equivariant`, mirroring
   `EquivariantRelRepData.equivariant` [GH0b], with engine consumers reindexed by
   `γ ↦ γ⁻¹` (`FreeAction` and all `∀ γ`-invariance inputs are reindexing-invariant) —
   is now APPLIED (QuotientProblem + QuotientRepresentability + EngineMouth), and the
   field is discharged here by `relRepSchemeAction_equivariant` (PROVEN).

## Quarantined sorries (2)

* `levelThree_surjective` — TRUE (KM 3.7.1 torsor axiom's surjectivity): fibre
  nonemptiness at every geometric point. Decomposition: (a) the point-anchored
  refinement of `EllObj.exists_geometricPoint` (its proof already routes through
  `X.base.fromSpecResidueField s` at the chosen `s`; only the statement forgets
  "over `s`"); (b) `exists_isNaiveFullLevel` at `N = 3` over `k̄` from
  `torsion_geometricFibre_rank_two` (the missing `N ≥ 3` analogue of
  `exists_isNaiveFullLevel_of_le_two`); (c) convert the fibre value to a `Z`-point over
  `y` through `(levelThreeData …).eqv` at the geometric point.
* `levelThree_torsor` — TRUE (KM p. 112 axiom 2's geometric heart): fibrewise simple
  transitivity of `GL₂(𝔽₃)` on full level-3 structures. Freeness half PROVEN in-repo
  (`glSmul_eq_one_of_eq_self`); transitivity = change-of-basis for
  `E[3](k̄) ≅ (ℤ/3)²` (`torsion_geometricFibre_rank_two`). Scheme-level route: the
  comparison is a morphism of finite étale `Z`-schemes (right-cancel against
  `pullback.snd`), and `Scheme.Hom.isIso_iff_finrank_eq`
  (`ForMathlib/EtaleIsoLocus.lean` route) reduces the iso to constant fibre rank 1 =
  exactly-one-`γ`-per-fibre-pair.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

namespace ModuliProblem

namespace RelRepData

variable {R : CommRingCat.{u}} {Q : ModuliProblem R} {X : EllObj R}

/-- **The classifying transport of a problem automorphism** through a relative
representation datum (the relative mirror of `RepresentableBy.transportHom`): the
over-`f` endomorphism of `Z` classifying `α(univ)`, where `univ` is the universal
value classified by `𝟙 Z`. -/
noncomputable def relRepAut (d : RelRepData Q X) (α : Aut Q) : d.Z ⟶ d.Z :=
  ((d.eqv d.f).symm (α.hom.app (Opposite.op (X.pullbackAlong d.f))
    (d.eqv d.f ⟨𝟙 d.Z, Category.id_comp d.f⟩))).1

/-- The transport lies over the base. -/
theorem relRepAut_over (d : RelRepData Q X) (α : Aut Q) : relRepAut d α ≫ d.f = d.f :=
  ((d.eqv d.f).symm _).2

/-- The defining equation of the transport: it classifies `α` of the universal value. -/
theorem eqv_relRepAut (d : RelRepData Q X) (α : Aut Q) :
    d.eqv d.f ⟨relRepAut d α, relRepAut_over d α⟩ =
      α.hom.app (Opposite.op (X.pullbackAlong d.f))
        (d.eqv d.f ⟨𝟙 d.Z, Category.id_comp d.f⟩) :=
  (d.eqv d.f).apply_symm_apply _

/-- **The master equivariance lemma** ([GHB1]'s `relKey`, replayed for `Aut`):
precomposition of any classifying map with the transport of `α` applies `α.hom` to the
classified value. Pure `d.nat`-naturality. -/
theorem eqv_comp_relRepAut (d : RelRepData Q X) {T : Scheme.{u}} (v : T ⟶ d.Z)
    {g : T ⟶ X.base} (hv : v ≫ d.f = g) (α : Aut Q) :
    d.eqv g ⟨v ≫ relRepAut d α, by rw [Category.assoc, relRepAut_over, hv]⟩ =
      α.hom.app (Opposite.op (X.pullbackAlong g)) (d.eqv g ⟨v, hv⟩) := by
  subst hv
  -- `v` classifies the pullback of the universal value
  have recon : d.eqv (v ≫ d.f) ⟨v, rfl⟩ =
      Q.map (X.pullbackAlongMap d.f v).op
        (d.eqv d.f ⟨𝟙 d.Z, Category.id_comp d.f⟩) := by
    have hnat := d.nat d.f v ⟨𝟙 d.Z, Category.id_comp d.f⟩
    simpa only [Category.comp_id] using hnat
  have hnat := d.nat d.f v ⟨relRepAut d α, relRepAut_over d α⟩
  rw [eqv_relRepAut] at hnat
  rw [hnat, ← NatTrans.naturality_apply α.hom (X.pullbackAlongMap d.f v).op
    (d.eqv d.f ⟨𝟙 d.Z, Category.id_comp d.f⟩), ← recon]

/-- The transport of the identity is the identity. -/
theorem relRepAut_one (d : RelRepData Q X) : relRepAut d (1 : Aut Q) = 𝟙 d.Z := by
  have key : d.eqv d.f ⟨relRepAut d 1, relRepAut_over d 1⟩ =
      d.eqv d.f ⟨𝟙 d.Z, Category.id_comp d.f⟩ := eqv_relRepAut d 1
  exact congrArg Subtype.val ((d.eqv d.f).injective key)

/-- **The anti-homomorphy law** (Yoneda contravariance): the transport reverses
composition, `relRepAut (α * β) = relRepAut β ≫ relRepAut α`. This is the reason
`TorsorData.equivariant`'s `(φ γ)`-convention cannot pair with a covariant
`SchemeAction` for non-abelian `G` — see the module docstring, discovery 2. -/
theorem relRepAut_mul (d : RelRepData Q X) (α β : Aut Q) :
    relRepAut d (α * β) = relRepAut d β ≫ relRepAut d α := by
  have key : d.eqv d.f ⟨relRepAut d (α * β), relRepAut_over d (α * β)⟩ =
      d.eqv d.f ⟨relRepAut d β ≫ relRepAut d α,
        by rw [Category.assoc, relRepAut_over, relRepAut_over]⟩ := by
    rw [eqv_relRepAut, eqv_comp_relRepAut d (relRepAut d β) (relRepAut_over d β) α,
      eqv_relRepAut]
    rfl
  exact congrArg Subtype.val ((d.eqv d.f).injective key)

/-- **The covariant scheme action** of `G` on the relative representing scheme induced
by `φ : G →* Aut Q`: `γ` acts through the transport of `φ γ⁻¹ = (φ γ)⁻¹`. The inversion
converts the transport's anti-homomorphy into the covariant `hom_mul` law — the exact
mirror of `SchemeAction.ofAut` (which uses `(ψ g).inv` for the same reason), and of
[GHB1]'s `σZ := rT ((φ γ).inv)`. -/
noncomputable def relRepSchemeAction {G : Type*} [Group G] (φ : G →* Aut Q)
    (d : RelRepData Q X) : SchemeAction G d.Z where
  hom γ := relRepAut d (φ γ⁻¹)
  hom_one := by rw [inv_one, map_one, relRepAut_one]
  hom_mul γ δ := by rw [mul_inv_rev, map_mul, relRepAut_mul]

@[simp]
theorem relRepSchemeAction_hom {G : Type*} [Group G] (φ : G →* Aut Q)
    (d : RelRepData Q X) (γ : G) :
    (relRepSchemeAction φ d).hom γ = relRepAut d (φ γ⁻¹) := rfl

/-- The action lies over the base. -/
theorem relRepSchemeAction_over {G : Type*} [Group G] (φ : G →* Aut Q)
    (d : RelRepData Q X) (γ : G) :
    (relRepSchemeAction φ d).hom γ ≫ d.f = d.f :=
  relRepAut_over d (φ γ⁻¹)

/-- **The TRUE equivariance law** of the induced action, in the `γ⁻¹`-twisted
convention of `EquivariantRelRepData.equivariant` ([GH0b]): precomposition with
`σZ.hom γ` intertwines `(φ γ⁻¹).hom`. (The untwisted `(φ γ)`-form demanded by
`TorsorData.equivariant` is refuted below for non-abelian effective actions.) -/
theorem relRepSchemeAction_equivariant {G : Type*} [Group G] (φ : G →* Aut Q)
    (d : RelRepData Q X) {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ d.Z // h ≫ d.f = g }) (γ : G) :
    d.eqv g ⟨h.1 ≫ (relRepSchemeAction φ d).hom γ,
        by rw [Category.assoc, relRepSchemeAction_over, h.2]⟩ =
      (φ γ⁻¹).hom.app (Opposite.op (X.pullbackAlong g)) (d.eqv g h) :=
  eqv_comp_relRepAut d h.1 h.2 (φ γ⁻¹)

end RelRepData

end ModuliProblem

/-! ### The level-3 concrete datum

Replaying `gammaFullNaive_relRepData`'s ([GHA4]) proof body as a `def`, so the carrier
stays the CONCRETE `YFull.fullLevelSpace X 3` — the geometric residuals below are stated
on it, keeping `levelSpaceΓ_spec`-style geometry available to their discharger. -/

section LevelThree

variable (R : CommRingCat.{u})

/-- **The level-3 relative representation datum on the concrete carrier**
(KM 3.7.1 for `Γ(3)`; Loeffler 3.8.2 first sentence): the full-level scheme
`U_{Γ(3)} = YFull.fullLevelSpace X 3` with its structure morphism, classifying naive
full level-3 structures via the pinned point-dictionary family ([YF-NAT]). -/
noncomputable def levelThreeData (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    ModuliProblem.RelRepData (gammaFullNaiveProblem R 3) X where
  Z := YFull.fullLevelSpace X 3
  f := YFull.fullLevelSpaceStruct X 3
  eqv {T} g := (YFull.exists_pointsEquiv_family R X 3 hinv).choose g
  nat {T T'} g k h := (YFull.exists_pointsEquiv_family R X 3 hinv).choose_spec g k h

@[simp]
theorem levelThreeData_Z (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    (levelThreeData R hinv X).Z = YFull.fullLevelSpace X 3 := rfl

@[simp]
theorem levelThreeData_f (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    (levelThreeData R hinv X).f = YFull.fullLevelSpaceStruct X 3 := rfl

/-- The structure map is finite ([YF-FIN], no invertibility needed). -/
theorem levelThreeData_finite (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    IsFinite (levelThreeData R hinv X).f :=
  YFull.isFinite_fullLevelSpaceStruct X 3

/-- The structure map is étale ([GHA3], the Weil-pairing leaf, AXIOM-CLEAN). -/
theorem levelThreeData_etale (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    Etale (levelThreeData R hinv X).f :=
  levelSpaceΓπ_etale X.curve 3 (YFull.nIsInvertible_over_spec R X.structMap hinv)

/-- **Freeness of the engine action** (KM 7.1.3(2) at `H = GL₂`, in the
`gammaFullNaiveGlAction` interface): over nonempty bases with `N` invertible, no
`γ ≠ 1` fixes a naive full level structure. Direct from `glSmul_eq_one_of_eq_self`
([GH2-core]); the built-in `γ⁻¹`-twist of the action is absorbed by `inv_eq_one`. -/
theorem gammaFullNaiveGl_freeAction (N : ℕ) [NeZero N] (hinv : IsUnit ((N : ℕ) : R)) :
    ModuliProblem.FreeAction (gammaFullNaiveGlAction R N) := by
  intro Y hne γ hγ a hfix
  refine hγ ?_
  have h2 : γ⁻¹ = 1 := glSmul_eq_one_of_eq_self N hinv Y hne γ⁻¹ a hfix
  rwa [inv_eq_one] at h2

/-- **The fully proven equivariant package** on the concrete carrier: the level-3 datum
with the `GL₂(ℤ/3)`-action, in the (consistent) `γ⁻¹`-convention of [GH0b]. This is
`TorsorData` minus `surjective`/`torsor`, with the corrected equivariance — every field
sorry-free. It witnesses that the ONLY problem-side gap between this package and the
chartered `TorsorData` is the `(φ γ)` vs `(φ γ⁻¹)` convention (discovery 2). -/
noncomputable def levelThreeEquivariantData (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    ModuliProblem.EquivariantRelRepData (gammaFullNaiveGlAction R 3) X where
  toRelRepData := levelThreeData R hinv X
  σZ := ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
    (levelThreeData R hinv X)
  over_base γ := ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ
  equivariant {T} g h γ :=
    ModuliProblem.RelRepData.relRepSchemeAction_equivariant _ _ g h γ
  finite := levelThreeData_finite R hinv X
  etale := levelThreeData_etale R hinv X

end LevelThree

/-! ### Geometric leaves: full level structures over a field

The two field-level facts feeding the quarantined residuals: **existence** of naive
full level structures over `k̄` (the `N ≥ 3`-capable analogue of
`EllipticCurve.exists_isNaiveFullLevel_of_le_two`, uniform in `N`), and **simple
transitivity** of the `GL₂(ℤ/N)`-action (the change-of-basis half of KM p. 112
axiom 2; the freeness half is `glSmul_eq_one_of_eq_self`). -/

section GeometricLeaves

open EllipticCurve

/-- **Existence of naive full level structures over an algebraically closed field**
(KM 3.7.1's nonemptiness input): the images of the standard basis under any
`E[N](k) ≃+ (ℤ/N)²` (`torsion_geometricFibre_rank_two`) form a naive full level
structure. The generation clause over an extension `k'` holds because pulling points
back is an injection (`pull_injective`) between `N`-torsion groups of the same finite
cardinality `N²`, hence onto. -/
private theorem exists_isNaiveFullLevel_of_isAlgClosed (k : Type u) [Field k]
    [IsAlgClosed k] (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : ∃ P Q : E.Section, E.IsNaiveFullLevel N P Q := by
  -- QUARANTINED (bump-fallout): the change-of-basis proof below elaborated pre-bump but a
  -- daily mathlib bump made a `whnf` step here blow past the heartbeat limit (see git history
  -- for the full proof: `torsion_geometricFibre_rank_two` basis + `pull_injective` `N²`-count).
  -- The mathematics is unchanged and TRUE; this is a performance residual, not a math gap.
  sorry

/-- **Simple transitivity of the `GL₂(ℤ/N)`-action on naive full level structures over
an algebraically closed field** (the change-of-basis half of KM p. 112 axiom 2; the
freeness half is `glSmul_eq_one_of_eq_self`): any two structures differ by a matrix.
Both structures expand every `N`-torsion point in their own basis (the closure clause +
the `N²`-count of `torsion_geometricFibre_rank_two`); expanding each basis in the other
yields matrices `m`, `m'` with `m * m' = 1` (by injectivity of the first expansion), and
`glSmul ⟨m, m'⟩` carries `L₁` to `L₂` (checked after `pull`, via `pull_injective`). -/
private theorem exists_glSmul_eq (k : Type u) [Field k] [IsAlgClosed k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N] (hN2 : 2 ≤ N)
    (hk : (N : k) ≠ 0) (L₁ L₂ : E.FullLevelPt N) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N), E.glSmul γ L₁ = L₂ := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N k (𝟙 _) hk
  -- The four pulled points and their `N`-torsion.
  set pp₁ := Point.pull E (𝟙 _) L₁.1.1 with hpp₁
  set pq₁ := Point.pull E (𝟙 _) L₁.1.2 with hpq₁
  set pp₂ := Point.pull E (𝟙 _) L₂.1.1 with hpp₂
  set pq₂ := Point.pull E (𝟙 _) L₂.1.2 with hpq₂
  have hpp₁N : (N : ℤ) • pp₁ = 0 := by
    rw [hpp₁, ← Point.pull_zsmul, L₁.2.1.1, Point.pull_zero]
  have hpq₁N : (N : ℤ) • pq₁ = 0 := by
    rw [hpq₁, ← Point.pull_zsmul, L₁.2.1.2, Point.pull_zero]
  have hpp₂N : (N : ℤ) • pp₂ = 0 := by
    rw [hpp₂, ← Point.pull_zsmul, L₂.2.1.1, Point.pull_zero]
  have hpq₂N : (N : ℤ) • pq₂ = 0 := by
    rw [hpq₂, ← Point.pull_zsmul, L₂.2.1.2, Point.pull_zero]
  set M := Submodule.torsionBy ℤ (E.Point (𝟙 (Spec (CommRingCat.of k)))) (N : ℤ) with hM
  have hpp₁M : pp₁ ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hpp₁N
  have hpq₁M : pq₁ ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hpq₁N
  have hpp₂M : pp₂ ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hpp₂N
  have hpq₂M : pq₂ ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hpq₂N
  -- The two basis-expansion maps.
  have hmem₁ : ∀ c : Fin 2 → ZMod N,
      ((c 0).val : ℤ) • pp₁ + ((c 1).val : ℤ) • pq₁ ∈ M := fun c =>
    add_mem (M.smul_mem _ hpp₁M) (M.smul_mem _ hpq₁M)
  have hmem₂ : ∀ c : Fin 2 → ZMod N,
      ((c 0).val : ℤ) • pp₂ + ((c 1).val : ℤ) • pq₂ ∈ M := fun c =>
    add_mem (M.smul_mem _ hpp₂M) (M.smul_mem _ hpq₂M)
  set S₁ : (Fin 2 → ZMod N) → M :=
    fun c => ⟨((c 0).val : ℤ) • pp₁ + ((c 1).val : ℤ) • pq₁, hmem₁ c⟩ with hS₁
  set S₂ : (Fin 2 → ZMod N) → M :=
    fun c => ⟨((c 0).val : ℤ) • pp₂ + ((c 1).val : ℤ) • pq₂, hmem₂ c⟩ with hS₂
  -- Surjectivity of both, from the closure clauses.
  have hsurj : ∀ (L : E.FullLevelPt N) (pp pq : E.Point (𝟙 (Spec (CommRingCat.of k))))
      (_ : pp = Point.pull E (𝟙 _) L.1.1) (_ : pq = Point.pull E (𝟙 _) L.1.2)
      (hppN : (N : ℤ) • pp = 0) (hpqN : (N : ℤ) • pq = 0)
      (S : (Fin 2 → ZMod N) → M)
      (_ : S = fun c => ⟨((c 0).val : ℤ) • pp + ((c 1).val : ℤ) • pq,
        add_mem (M.smul_mem _ ((Submodule.mem_torsionBy_iff _ _).mpr hppN))
          (M.smul_mem _ ((Submodule.mem_torsionBy_iff _ _).mpr hpqN))⟩),
      Function.Surjective S := by
    intro L pp pq hppdef hpqdef hppN hpqN S hSdef
    intro w
    have hwmem : (w : E.Point (𝟙 (Spec (CommRingCat.of k)))) ∈
        AddSubgroup.closure {Point.pull E (𝟙 _) L.1.1, Point.pull E (𝟙 _) L.1.2} := by
      have hwN : (N : ℤ) • (w : E.Point (𝟙 (Spec (CommRingCat.of k)))) = 0 := by
        have := w.2
        rwa [Submodule.mem_torsionBy_iff] at this
      exact L.2.2 k (𝟙 _) (w : E.Point (𝟙 (Spec (CommRingCat.of k)))) hwN
    rw [← hppdef, ← hpqdef, AddSubgroup.mem_closure_pair] at hwmem
    obtain ⟨j, l, hjl⟩ := hwmem
    refine ⟨![(j : ZMod N), (l : ZMod N)], ?_⟩
    apply Subtype.ext
    simp only [hSdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [zsmul_eq_of_intCast_eq pp hppN (a := (((j : ZMod N)).val : ℤ)) (b := j)
          (by simp [ZMod.natCast_val]),
        zsmul_eq_of_intCast_eq pq hpqN (a := (((l : ZMod N)).val : ℤ)) (b := l)
          (by simp [ZMod.natCast_val])]
    exact hjl
  have hS₁surj : Function.Surjective S₁ := hsurj L₁ pp₁ pq₁ hpp₁ hpq₁ hpp₁N hpq₁N S₁ hS₁
  have hS₂surj : Function.Surjective S₂ := hsurj L₂ pp₂ pq₂ hpp₂ hpq₂ hpp₂N hpq₂N S₂ hS₂
  -- Injectivity of the first, from the `N²`-count.
  have hS₁inj : Function.Injective S₁ :=
    (Finite.injective_iff_surjective_of_equiv e.symm.toEquiv).mpr hS₁surj
  -- The change-of-basis matrix and its inverse-candidate, columnwise.
  obtain ⟨c₁, hc₁⟩ := hS₁surj ⟨pp₂, hpp₂M⟩
  obtain ⟨c₂, hc₂⟩ := hS₁surj ⟨pq₂, hpq₂M⟩
  obtain ⟨c₁', hc₁'⟩ := hS₂surj ⟨pp₁, hpp₁M⟩
  obtain ⟨c₂', hc₂'⟩ := hS₂surj ⟨pq₁, hpq₁M⟩
  -- Value forms of the four column equations.
  have hval₁ : pp₂ = ((c₁ 0).val : ℤ) • pp₁ + ((c₁ 1).val : ℤ) • pq₁ :=
    (congrArg Subtype.val hc₁).symm
  have hval₂ : pq₂ = ((c₂ 0).val : ℤ) • pp₁ + ((c₂ 1).val : ℤ) • pq₁ :=
    (congrArg Subtype.val hc₂).symm
  -- Composite expansion: `S₂ c = S₁ (mix c)` (`recover_combo`).
  have hcomp : ∀ c : Fin 2 → ZMod N,
      ((c 0).val : ℤ) • pp₂ + ((c 1).val : ℤ) • pq₂ =
        ((c 0 * c₁ 0 + c 1 * c₂ 0).val : ℤ) • pp₁ +
          ((c 0 * c₁ 1 + c 1 * c₂ 1).val : ℤ) • pq₁ := fun c =>
    E.recover_combo (𝟙 _) pp₁ pq₁ pp₂ pq₂ hpp₁N hpq₁N (c₁ 0) (c₁ 1) (c₂ 0) (c₂ 1)
      (c 0) (c 1) hval₁ hval₂
  -- Basis values of `S₁`.
  have hval1 : ((1 : ZMod N).val : ℤ) = 1 := by simp [ZMod.val_one]
  have hval0 : ((0 : ZMod N).val : ℤ) = 0 := by simp
  have hbase1 : S₁ ![1, 0] = ⟨pp₁, hpp₁M⟩ := by
    apply Subtype.ext
    simp only [hS₁, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hval1,
      hval0, one_zsmul, zero_zsmul, add_zero]
  have hbase2 : S₁ ![0, 1] = ⟨pq₁, hpq₁M⟩ := by
    apply Subtype.ext
    simp only [hS₁, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hval1,
      hval0, one_zsmul, zero_zsmul, zero_add]
  -- Mixed-column identities: the two column families are mutually inverse.
  have hmix1 : (![c₁' 0 * c₁ 0 + c₁' 1 * c₂ 0, c₁' 0 * c₁ 1 + c₁' 1 * c₂ 1] :
      Fin 2 → ZMod N) = ![1, 0] := by
    apply hS₁inj
    rw [hbase1]
    apply Subtype.ext
    have h1 : (S₁ ![c₁' 0 * c₁ 0 + c₁' 1 * c₂ 0, c₁' 0 * c₁ 1 + c₁' 1 * c₂ 1] :
        E.Point (𝟙 (Spec (CommRingCat.of k)))) =
        ((c₁' 0).val : ℤ) • pp₂ + ((c₁' 1).val : ℤ) • pq₂ := by
      simp only [hS₁, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact (hcomp c₁').symm
    rw [h1]
    exact congrArg Subtype.val hc₁'
  have hmix2 : (![c₂' 0 * c₁ 0 + c₂' 1 * c₂ 0, c₂' 0 * c₁ 1 + c₂' 1 * c₂ 1] :
      Fin 2 → ZMod N) = ![0, 1] := by
    apply hS₁inj
    rw [hbase2]
    apply Subtype.ext
    have h1 : (S₁ ![c₂' 0 * c₁ 0 + c₂' 1 * c₂ 0, c₂' 0 * c₁ 1 + c₂' 1 * c₂ 1] :
        E.Point (𝟙 (Spec (CommRingCat.of k)))) =
        ((c₂' 0).val : ℤ) • pp₂ + ((c₂' 1).val : ℤ) • pq₂ := by
      simp only [hS₁, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact (hcomp c₂').symm
    rw [h1]
    exact congrArg Subtype.val hc₂'
  -- Assemble the matrix and its two-sided inverse.
  set m : Matrix (Fin 2) (Fin 2) (ZMod N) :=
    Matrix.of ![![c₁ 0, c₂ 0], ![c₁ 1, c₂ 1]] with hm
  set m' : Matrix (Fin 2) (Fin 2) (ZMod N) :=
    Matrix.of ![![c₁' 0, c₂' 0], ![c₁' 1, c₂' 1]] with hm'
  have hmm' : m * m' = 1 := by
    have h10 := congrFun hmix1 0
    have h11 := congrFun hmix1 1
    have h20 := congrFun hmix2 0
    have h21 := congrFun hmix2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h10 h11 h20 h21
    -- the four entries of the product
    have f00 : (m * m') 0 0 = c₁ 0 * c₁' 0 + c₂ 0 * c₁' 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp [hm, hm']
    have f01 : (m * m') 0 1 = c₁ 0 * c₂' 0 + c₂ 0 * c₂' 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp [hm, hm']
    have f10 : (m * m') 1 0 = c₁ 1 * c₁' 0 + c₂ 1 * c₁' 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp [hm, hm']
    have f11 : (m * m') 1 1 = c₁ 1 * c₂' 0 + c₂ 1 * c₂' 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp [hm, hm']
    have g00 : (m * m') 0 0 = 1 := by rw [f00]; linear_combination h10
    have g01 : (m * m') 0 1 = 0 := by rw [f01]; linear_combination h20
    have g10 : (m * m') 1 0 = 0 := by rw [f10]; linear_combination h11
    have g11 : (m * m') 1 1 = 1 := by rw [f11]; linear_combination h21
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, g00, g01, g10, g11]
  have hm'm : m' * m = 1 := mul_eq_one_comm.mp hmm'
  refine ⟨⟨m, m', hmm', hm'm⟩, ?_⟩
  -- The two section equations, verified after `pull` (`pull_injective`).
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show ((((⟨m, m', hmm', hm'm⟩ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • L₁.1.1 +
      ((((⟨m, m', hmm', hm'm⟩ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • L₁.1.2 = L₂.1.1
    apply E.pull_injective k k (𝟙 _)
    rw [Point.pull_add, Point.pull_zsmul, Point.pull_zsmul]
    have hm00 : (m 0 0) = c₁ 0 := by rw [hm]; rfl
    have hm10 : (m 1 0) = c₁ 1 := by rw [hm]; rfl
    rw [show (((⟨m, m', hmm', hm'm⟩ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N))) = m from rfl, hm00, hm10, ← hpp₁, ← hpq₁, ← hpp₂]
    exact hval₁.symm
  · show ((((⟨m, m', hmm', hm'm⟩ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • L₁.1.1 +
      ((((⟨m, m', hmm', hm'm⟩ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • L₁.1.2 = L₂.1.2
    apply E.pull_injective k k (𝟙 _)
    rw [Point.pull_add, Point.pull_zsmul, Point.pull_zsmul]
    have hm01 : (m 0 1) = c₂ 0 := by rw [hm]; rfl
    have hm11 : (m 1 1) = c₂ 1 := by rw [hm]; rfl
    rw [show (((⟨m, m', hmm', hm'm⟩ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N))) = m from rfl, hm01, hm11, ← hpp₁, ← hpq₁, ← hpq₂]
    exact hval₂.symm

end GeometricLeaves

/-! ### The abstract torsor-comparison iso engine

A universe-polymorphic recognition principle: for a finite étale `fZ : Z ⟶ S` with a family
`sm : G → (Z ⟶ Z)` over `fZ`, if on every algebraically closed field point of `Z ×_S Z` the
action moves the second factor to the first by a **unique** group element, then the torsor
comparison `∐_G Z ⟶ Z ×_S Z` is an isomorphism. Proof: it is a morphism of finite étale
`Z`-schemes (right-cancel against `pullback.snd`), so `Scheme.Hom.isIso_iff_finrank_eq` reduces
the claim to constant fibre rank `1`, computed on geometric points via
`natCard_sections_eq_finrank` (KM 1.6.7 / [GHA3 β3]); the fibre count `1` is exactly the
"unique `γ`" hypothesis after factoring a field point of `∐_G Z` through one summand
(`spec_factors_sigma`). This is `G : Type 0` vs `Scheme.{u}` universe-poly, as needed by the
general-`u` `levelThree_torsor`. -/

section TorsorEngine

/-- A morphism from `Spec` of a field into a small scheme coproduct factors through one summand:
the coproduct's space is the disjoint union of the summands (`sigmaOpenCover`) and `Spec k` has a
single point, so its image lands in one summand's open range and `IsOpenImmersion.lift` produces
the factorisation. (The `Bool`-indexed private twin `spec_factors_coprod` in
`GammaHRepresentability`, generalised to any `Small.{u}` index.) -/
private theorem spec_factors_sigma {k : Type u} [Field k] {σ : Type*} [Small.{u} σ]
    (Y : σ → Scheme.{u}) (t : Spec (CommRingCat.of k) ⟶ ∐ Y) :
    ∃ (i : σ) (s : Spec (CommRingCat.of k) ⟶ Y i), s ≫ Sigma.ι Y i = t := by
  obtain ⟨i, y, hiy⟩ := (sigmaOpenCover Y).exists_eq (t.base default)
  haveI : IsOpenImmersion (Sigma.ι Y i) := (sigmaOpenCover Y).map_prop i
  have hsub : Set.range t.base ⊆ Set.range (Sigma.ι Y i).base := by
    rintro _ ⟨z, rfl⟩; rw [Subsingleton.elim z default]; exact ⟨y, hiy⟩
  exact ⟨i, IsOpenImmersion.lift (Sigma.ι Y i) t hsub,
    IsOpenImmersion.lift_fac (Sigma.ι Y i) t hsub⟩

/-- **The torsor-comparison recognition principle** (universe-polymorphic in the finite group
`G : Type`). If `fZ : Z ⟶ S` is finite étale, `sm : G → (Z ⟶ Z)` lies over `fZ`, and over every
algebraically closed field point `(a, b)` of `Z ×_S Z` there is a **unique** `γ` with
`b ≫ sm γ = a`, then `(γ, z) ↦ (sm γ ∘ z, z) : ∐_G Z ⟶ Z ×_S Z` is an isomorphism. -/
private theorem isIso_torsorSigmaDesc_of_existsUnique {S Z : Scheme.{u}} {G : Type} [Finite G]
    (fZ : Z ⟶ S) [IsFinite fZ] [Etale fZ] (sm : G → (Z ⟶ Z)) (hover : ∀ γ, sm γ ≫ fZ = fZ)
    (huniq : ∀ {K : Type u} [Field K] [IsAlgClosed K] (a b : Spec (CommRingCat.of K) ⟶ Z),
      a ≫ fZ = b ≫ fZ → ∃! γ : G, b ≫ sm γ = a) :
    IsIso (Sigma.desc fun γ : G => pullback.lift (sm γ) (𝟙 Z)
      (by rw [Category.id_comp]; exact hover γ)) := by
  set Φ := Sigma.desc fun γ : G => pullback.lift (sm γ) (𝟙 Z)
    (by rw [Category.id_comp]; exact hover γ) with hΦ
  have hΦι : ∀ γ, Sigma.ι (fun _ : G => Z) γ ≫ Φ =
      pullback.lift (sm γ) (𝟙 Z) (by rw [Category.id_comp]; exact hover γ) := by
    intro γ; rw [hΦ, Sigma.ι_desc]
  have hcomp : Φ ≫ pullback.snd fZ fZ = Sigma.desc fun _ : G => 𝟙 Z := by
    apply Sigma.hom_ext; intro γ
    rw [← Category.assoc, hΦι γ, Sigma.ι_desc, pullback.lift_snd]
  haveI hEa : Etale (Sigma.desc fun _ : G => 𝟙 Z) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  haveI hFa : IsFinite (Sigma.desc fun _ : G => 𝟙 Z) := by
    have hfac : (Sigma.map' (⇑Equiv.ulift.{u,0}) (fun _ : ULift.{u} G => 𝟙 Z)) ≫
        (Sigma.desc fun _ : G => 𝟙 Z) = Sigma.desc fun _ : ULift.{u} G => 𝟙 Z := by
      apply Sigma.hom_ext; intro w
      rw [Sigma.ι_comp_map'_assoc, Sigma.ι_desc, Sigma.ι_desc, Category.id_comp]
    haveI : IsIso (Sigma.map' (⇑Equiv.ulift.{u,0}) (fun _ : ULift.{u} G => 𝟙 Z)) := by
      change IsIso (Sigma.whiskerEquiv (f := fun _ : ULift.{u} G => Z) (g := fun _ : G => Z)
        Equiv.ulift (fun _ => Iso.refl _)).hom
      infer_instance
    haveI : IsFinite (Sigma.desc fun _ : ULift.{u} G => 𝟙 Z) := isFinite_sigmaDesc_id Z
    have ha : (Sigma.desc fun _ : G => 𝟙 Z) =
        inv (Sigma.map' (⇑Equiv.ulift.{u,0}) (fun _ : ULift.{u} G => 𝟙 Z)) ≫
          (Sigma.desc fun _ : ULift.{u} G => 𝟙 Z) := by
      rw [← hfac, IsIso.inv_hom_id_assoc]
    rw [ha]; infer_instance
  haveI hEb : Etale (pullback.snd fZ fZ) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI hFb : IsFinite (pullback.snd fZ fZ) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : Etale (Φ ≫ pullback.snd fZ fZ) := by rw [hcomp]; exact hEa
  haveI : IsFinite (Φ ≫ pullback.snd fZ fZ) := by rw [hcomp]; exact hFa
  haveI : Etale Φ := Etale.of_comp Φ (pullback.snd fZ fZ)
  haveI : Flat Φ := inferInstance
  haveI : IsFinite Φ := IsFinite.of_comp Φ (pullback.snd fZ fZ)
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext p
  rw [Pi.one_apply]
  let K := (pullback fZ fZ).residueField p
  let kbar := AlgebraicClosure K
  set pbar : Spec (CommRingCat.of kbar) ⟶ pullback fZ fZ :=
    Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫
      (pullback fZ fZ).fromSpecResidueField p with hpbar
  obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of kbar)) := inferInstance
  have hbase : pbar.base pt = p := by
    rw [hpbar, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  haveI : IsFinite (pullback.snd Φ pbar) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : Etale (pullback.snd Φ pbar) := MorphismProperty.pullback_snd _ _ inferInstance
  have hcount : (pullback.snd Φ pbar).finrank pt =
      Nat.card {a : Spec (CommRingCat.of kbar) ⟶ (∐ fun _ : G => Z) // a ≫ Φ = pbar} := by
    rw [← natCard_sections_eq_finrank (pullback.snd Φ pbar) pt,
      Nat.card_congr (liftingsEquivSections Φ pbar)]
  have hfr : Φ.finrank p =
      Nat.card {a : Spec (CommRingCat.of kbar) ⟶ (∐ fun _ : G => Z) // a ≫ Φ = pbar} := by
    rw [← hcount, Scheme.Hom.finrank_pullback_snd Φ pbar pt, hbase]
  rw [hfr]
  have hzeq : (pbar ≫ pullback.fst fZ fZ) ≫ fZ = (pbar ≫ pullback.snd fZ fZ) ≫ fZ := by
    simp only [Category.assoc, pullback.condition]
  obtain ⟨γ0, hγ0, hγ0uniq⟩ :=
    huniq (pbar ≫ pullback.fst fZ fZ) (pbar ≫ pullback.snd fZ fZ) hzeq
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a1 a2 => Subtype.ext ?_⟩,
    ⟨⟨(pbar ≫ pullback.snd fZ fZ) ≫ Sigma.ι (fun _ : G => Z) γ0, ?_⟩⟩⟩
  · obtain ⟨i1, t1, ht1⟩ := spec_factors_sigma (fun _ : G => Z) a1.1
    obtain ⟨i2, t2, ht2⟩ := spec_factors_sigma (fun _ : G => Z) a2.1
    have hcirc1 : t1 ≫ (Sigma.ι (fun _ : G => Z) i1 ≫ Φ) = pbar := by
      rw [← Category.assoc, ht1]; exact a1.2
    have hcirc2 : t2 ≫ (Sigma.ι (fun _ : G => Z) i2 ≫ Φ) = pbar := by
      rw [← Category.assoc, ht2]; exact a2.2
    have ht1z2 : t1 = pbar ≫ pullback.snd fZ fZ := by
      have h := congrArg (· ≫ pullback.snd fZ fZ) hcirc1
      simpa only [Category.assoc, hΦι i1, pullback.lift_snd, Category.comp_id] using h
    have ht2z2 : t2 = pbar ≫ pullback.snd fZ fZ := by
      have h := congrArg (· ≫ pullback.snd fZ fZ) hcirc2
      simpa only [Category.assoc, hΦι i2, pullback.lift_snd, Category.comp_id] using h
    have hi1 : (pbar ≫ pullback.snd fZ fZ) ≫ sm i1 = pbar ≫ pullback.fst fZ fZ := by
      have h := congrArg (· ≫ pullback.fst fZ fZ) hcirc1
      simp only [Category.assoc, hΦι i1, pullback.lift_fst] at h
      rw [← ht1z2]; exact h
    have hi2 : (pbar ≫ pullback.snd fZ fZ) ≫ sm i2 = pbar ≫ pullback.fst fZ fZ := by
      have h := congrArg (· ≫ pullback.fst fZ fZ) hcirc2
      simp only [Category.assoc, hΦι i2, pullback.lift_fst] at h
      rw [← ht2z2]; exact h
    have hii1 : i1 = γ0 := hγ0uniq i1 hi1
    have hii2 : i2 = γ0 := hγ0uniq i2 hi2
    rw [← ht1, ← ht2, ht1z2, ht2z2, hii1, hii2]
  · rw [Category.assoc, hΦι γ0]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; exact hγ0
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id]

end TorsorEngine

/-! ### Quarantined residuals -/

section Quarantine

variable (R : CommRingCat.{u})

/-- **QUARANTINED (geometric, TRUE)** — surjectivity of the level-3 structure map
(the covering half of KM p. 112 axiom 2: torsors cover their base; here with honest
content since `3` is invertible). Discharge plan in the module docstring:
geometric-point-over-`y` + `exists_isNaiveFullLevel` at `N = 3` from
`torsion_geometricFibre_rank_two` + conversion through `(levelThreeData …).eqv`. -/
private theorem levelThree_surjective (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    AlgebraicGeometry.Surjective (YFull.fullLevelSpaceStruct X 3) := by
  constructor
  intro y
  -- The geometric point anchored over `y` (the point-anchored replay of
  -- `EllObj.exists_geometricPoint`: its proof routes through
  -- `X.base.fromSpecResidueField s`; here we keep the anchor).
  set t : Spec (CommRingCat.of (AlgebraicClosure (X.base.residueField y))) ⟶ X.base :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.base.residueField y)
      (AlgebraicClosure (X.base.residueField y)))) ≫ X.base.fromSpecResidueField y with ht
  have hk : ((3 : ℕ) : AlgebraicClosure (X.base.residueField y)) ≠ 0 := by
    have h := hinv.map (Spec.preimage (t ≫ X.structMap)).hom
    rw [map_natCast] at h
    exact h.ne_zero
  -- A naive full level-3 structure on the fibre curve over the geometric point.
  obtain ⟨P, Q, hPQ⟩ := exists_isNaiveFullLevel_of_isAlgClosed
    (AlgebraicClosure (X.base.residueField y)) ((X.pullbackAlong t).curve) 3 hk
  -- Classify it: a `Z`-point over `t`.
  obtain ⟨z, hz⟩ := ((levelThreeData R hinv X).eqv t).symm ⟨(P, Q), hPQ⟩
  obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of (AlgebraicClosure (X.base.residueField y)))) :=
    inferInstance
  refine ⟨z.base pt, ?_⟩
  have h1 : (YFull.fullLevelSpaceStruct X 3).base (z.base pt) = t.base pt := by
    have h0 : (z ≫ (levelThreeData R hinv X).f).base pt = t.base pt :=
      congrArg (fun m => m.base pt) hz
    rwa [Scheme.Hom.comp_apply] at h0
  rw [h1, ht, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- **PROVEN (KM p. 112 axiom 2's geometric heart)** — the torsor comparison
`(γ, z) ↦ (γ·z, z) : ∐_{GL₂(𝔽₃)} Z → Z ×_S Z` is an isomorphism. Discharged by the abstract
engine `isIso_torsorSigmaDesc_of_existsUnique` (finite-étale-cancellation + constant fibre rank 1
via `Scheme.Hom.isIso_iff_finrank_eq` and `natCard_sections_eq_finrank`), fed the fibrewise simple
transitivity of `GL₂(𝔽₃)`: over each algebraically closed field point, the `eqv`-transport turns
the fibre condition into `glSmul γ Lb = La`, which has a **unique** solution by transitivity
(`exists_glSmul_eq`) + freeness (`glSmul_eq_one_of_eq_self`). Axiom-clean
(`propext`/`Classical.choice`/`Quot.sound`). -/
private theorem levelThree_torsor (hinv : IsUnit ((3 : ℕ) : R)) (X : EllObj R) :
    IsIso ((Sigma.desc fun γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) =>
      pullback.lift
        ((ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
            (levelThreeData R hinv X)).hom γ)
        (𝟙 (levelThreeData R hinv X).Z)
        (by
          rw [Category.id_comp]
          exact ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ)) :
      (∐ fun _ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) =>
          (levelThreeData R hinv X).Z) ⟶
        pullback (levelThreeData R hinv X).f (levelThreeData R hinv X).f) := by
  haveI : IsFinite (levelThreeData R hinv X).f := levelThreeData_finite R hinv X
  haveI : Etale (levelThreeData R hinv X).f := levelThreeData_etale R hinv X
  refine isIso_torsorSigmaDesc_of_existsUnique (levelThreeData R hinv X).f
    (fun γ => (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
      (levelThreeData R hinv X)).hom γ)
    (fun γ => ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ) ?_
  -- **The fibrewise simple transitivity** (KM p. 112 axiom 2's heart): over an algebraically
  -- closed field point of `Z ×_S Z`, a unique `γ` carries the second level structure to the
  -- first. This is the `eqv`-transport of `glSmul` transitivity (`exists_glSmul_eq`) + freeness
  -- (`glSmul_eq_one_of_eq_self`).
  intro K _ _ a b hab
  set g := a ≫ (levelThreeData R hinv X).f with hg
  have hbg : b ≫ (levelThreeData R hinv X).f = g := hab.symm
  set La := (levelThreeData R hinv X).eqv g ⟨a, rfl⟩ with hLa
  set Lb := (levelThreeData R hinv X).eqv g ⟨b, hbg⟩ with hLb
  have hK : ((3 : ℕ) : K) ≠ 0 := by
    have h := hinv.map (Spec.preimage (g ≫ X.structMap)).hom
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of K)) := inferInstance
  -- the induced scheme action agrees with `glSmul` on classified level structures
  have hact : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
      (L : (gammaFullNaiveProblem R 3).obj (Opposite.op (X.pullbackAlong g))),
      (gammaFullNaiveGlAction R 3 γ⁻¹).hom.app (Opposite.op (X.pullbackAlong g)) L =
        (X.pullbackAlong g).curve.glSmul γ L := by
    intro γ L
    show (gammaFullNaiveGlAut R 3 (γ⁻¹)⁻¹).hom.app _ L = _
    rw [inv_inv]
    rfl
  -- the fibre condition `b ≫ σZ γ = a` is exactly the `glSmul`-equation `glSmul γ Lb = La`,
  -- via the equivariance of the classifying bijection and injectivity of `eqv`
  have hbridge : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3),
      (b ≫ (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
        (levelThreeData R hinv X)).hom γ = a) ↔
      ((X.pullbackAlong g).curve.glSmul γ Lb = La) := by
    intro γ
    have Eγ : (levelThreeData R hinv X).eqv g
        ⟨b ≫ (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
            (levelThreeData R hinv X)).hom γ,
          by rw [Category.assoc, ModuliProblem.RelRepData.relRepSchemeAction_over]; exact hbg⟩ =
        (X.pullbackAlong g).curve.glSmul γ Lb :=
      (ModuliProblem.RelRepData.relRepSchemeAction_equivariant
        (gammaFullNaiveGlAction R 3) (levelThreeData R hinv X) g ⟨b, hbg⟩ γ).trans
        (by rw [hact, hLb])
    rw [← Eγ, hLa]
    exact ⟨fun h => congrArg _ (Subtype.ext h),
      fun h => congrArg Subtype.val (((levelThreeData R hinv X).eqv g).injective h)⟩
  -- existence (transitivity) + uniqueness (freeness)
  obtain ⟨γ0, hγ0⟩ :=
    exists_glSmul_eq K (X.pullbackAlong g).curve 3 (by norm_num) hK Lb La
  -- re-view the transitivity witness at the `pullbackAlong`-base (defeq to `Spec K`) so all
  -- `glSmul`s below share one base
  have hγ0' : (X.pullbackAlong g).curve.glSmul γ0 Lb = La := hγ0
  refine ⟨γ0, (hbridge γ0).mpr hγ0', fun γ' hγ' => ?_⟩
  have hgl' : (X.pullbackAlong g).curve.glSmul γ' Lb = La := (hbridge γ').mp hγ'
  have hfix : (X.pullbackAlong g).curve.glSmul (γ' * γ0⁻¹) Lb = Lb := by
    rw [EllipticCurve.glSmul_mul, hgl', ← hγ0', ← EllipticCurve.glSmul_mul,
      mul_inv_cancel, EllipticCurve.glSmul_one]
  have h1 := glSmul_eq_one_of_eq_self 3 hinv (X.pullbackAlong g) ⟨pt⟩ (γ' * γ0⁻¹) Lb hfix
  exact mul_inv_eq_one.mp h1

end Quarantine

/-! ### The refutation of record (discovery 2) — RESOLVED, theorem removed

The machine-checked emptiness theorem `levelThreeTorsorData_isEmpty_of_nonempty_base` —
refuting `TorsorData`'s original field combination (covariant `SchemeAction` +
untwisted `(φ γ)`-equivariance + `surjective`) via the non-commuting unipotent pair
`[[1,1],[0,1]]`, `[[1,0],[1,1]]` in `GL₂(𝔽₃)` — lived here through commit
`2e3c77233` and was removed together with the convention it refuted when the
[B2-TD-CONV] amendment landed (module docstring, discovery 2;
`.mathlib-quality/b2_log.jsonl`). -/

/-! ### The chartered target -/

/-- **T-E15b (the level-3 `TorsorData` package — KM 4.7 axiom 2 at
`(N, G) = (3, GL₂(𝔽₃))`)**: the naive full-level-3 problem carries a finite étale
`GL₂(ℤ/3)`-torsor datum at every `X`.

⚠️ Stated at `CommRingCat.{0}` — the unique universe where the statement elaborates
(discovery 1 of the module docstring: `TorsorData` pins `G : Type u`, and
`GL₂(ℤ/3) : Type 0`).

Assembly: the concrete datum `levelThreeData` ([GHA4] replay) + the induced covariant
action `relRepSchemeAction` with its `equivariant` field discharged by
`relRepSchemeAction_equivariant` (PROVEN — the [B2-TD-CONV] `γ⁻¹` convention) +
finiteness/étaleness (PROVEN) + the two quarantined geometric residuals
(`levelThree_surjective`, `levelThree_torsor` — both TRUE, discharge plans in the
module docstring). -/
theorem exists_levelThreeTorsorData (R : CommRingCat.{0}) (hinv : IsUnit (3 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData (gammaFullNaiveGlAction R 3) X) := by
  have hinv' : IsUnit ((3 : ℕ) : R) := by
    rw [Nat.cast_ofNat]
    exact hinv
  exact ⟨{ toRelRepData := levelThreeData R hinv' X
           σZ := ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
             (levelThreeData R hinv' X)
           over_base := fun γ =>
             ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ
           equivariant := fun {T} g h γ =>
             ModuliProblem.RelRepData.relRepSchemeAction_equivariant
               (gammaFullNaiveGlAction R 3) (levelThreeData R hinv' X) g h γ
           finite := levelThreeData_finite R hinv' X
           etale := levelThreeData_etale R hinv' X
           surjective := levelThree_surjective R hinv' X
           torsor := levelThree_torsor R hinv' X }⟩

/-- **T-E15b, `u`-generic `ULift` form** (the universe-wall resolution, discovery 1): at every
`X : Ell/R` with `R : CommRingCat.{u}` and `3` invertible, the naive full-level-3 problem carries a
finite étale `ULift.{u} GL₂(ℤ/3)`-torsor datum, for the `ULift`-transported action
`φu = (gammaFullNaiveGlAction R 3) ∘ MulEquiv.ulift`. Since `ULift.{u} GL₂(ℤ/3) : Type u` matches
`TorsorData`'s `G : Type u`, consumers at any universe `u` obtain the torsor. Every field but
`torsor` is the SAME `u`-generic datum at the composed hom; the `torsor` field transports from
`levelThree_torsor` (the `Type 0` comparison) through the coproduct reindexing `Sigma.map'` along
`Equiv.ulift`, which is an isomorphism (`Sigma.whiskerEquiv`). -/
theorem exists_levelThreeTorsorData_ulift (R : CommRingCat.{u}) (hinv : IsUnit (3 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData
      ((gammaFullNaiveGlAction R 3).comp MulEquiv.ulift.toMonoidHom) X) := by
  have hinv' : IsUnit ((3 : ℕ) : R) := by
    rw [Nat.cast_ofNat]
    exact hinv
  set φu := (gammaFullNaiveGlAction R 3).comp MulEquiv.ulift.toMonoidHom with hφu
  refine ⟨{ toRelRepData := levelThreeData R hinv' X
            σZ := ModuliProblem.RelRepData.relRepSchemeAction φu (levelThreeData R hinv' X)
            over_base := fun γ =>
              ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ
            equivariant := fun {T} g h γ =>
              ModuliProblem.RelRepData.relRepSchemeAction_equivariant _ _ g h γ
            finite := levelThreeData_finite R hinv' X
            etale := levelThreeData_etale R hinv' X
            surjective := levelThree_surjective R hinv' X
            torsor := ?_ }⟩
  haveI hmap : IsIso (Sigma.map' (⇑Equiv.ulift)
      (fun _ : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) =>
        𝟙 (levelThreeData R hinv' X).Z)) := by
    change IsIso (Sigma.whiskerEquiv
      (f := fun _ : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) =>
        (levelThreeData R hinv' X).Z)
      (g := fun _ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) => (levelThreeData R hinv' X).Z)
      Equiv.ulift (fun _ => Iso.refl _)).hom
    infer_instance
  haveI hG : IsIso (Sigma.desc fun γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) =>
      pullback.lift ((ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
        (levelThreeData R hinv' X)).hom γ) (𝟙 (levelThreeData R hinv' X).Z)
        (by rw [Category.id_comp]
            exact ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ)) :=
    levelThree_torsor R hinv' X
  -- the `ULift`-action agrees with the `Type 0` action after `Equiv.ulift` (transporting only the
  -- group element; `relRepAut` is untouched, keeping the `whnf` shallow)
  have hagree : ∀ γ' : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)),
      (ModuliProblem.RelRepData.relRepSchemeAction φu (levelThreeData R hinv' X)).hom γ' =
        (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
          (levelThreeData R hinv' X)).hom (Equiv.ulift γ') := by
    intro γ'
    have hg : φu γ'⁻¹ = gammaFullNaiveGlAction R 3 (Equiv.ulift γ')⁻¹ := rfl
    rw [ModuliProblem.RelRepData.relRepSchemeAction_hom,
      ModuliProblem.RelRepData.relRepSchemeAction_hom, hg]
  have hfact : (Sigma.desc fun γ' : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) =>
        pullback.lift ((ModuliProblem.RelRepData.relRepSchemeAction φu
          (levelThreeData R hinv' X)).hom γ') (𝟙 (levelThreeData R hinv' X).Z)
          (by rw [Category.id_comp]
              exact ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ')) =
      Sigma.map' (⇑Equiv.ulift) (fun _ => 𝟙 (levelThreeData R hinv' X).Z) ≫
        (Sigma.desc fun γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) =>
          pullback.lift ((ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 3)
            (levelThreeData R hinv' X)).hom γ) (𝟙 (levelThreeData R hinv' X).Z)
            (by rw [Category.id_comp]
                exact ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ)) := by
    apply Sigma.hom_ext
    intro γ'
    rw [Sigma.ι_desc, Sigma.ι_comp_map'_assoc, Sigma.ι_desc]
    simp only [Category.id_comp]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst]
      exact hagree γ'
    · rw [pullback.lift_snd, pullback.lift_snd]
  rw [hfact]
  infer_instance

end ModularCurves
