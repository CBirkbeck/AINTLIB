/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.Bootstrap

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
  sorry

/-- **QUARANTINED (geometric, TRUE)** — the torsor comparison
`(γ, z) ↦ (γ·z, z) : ∐_{GL₂(𝔽₃)} Z ≅ Z ×_S Z` is an isomorphism: fibrewise simple
transitivity of `GL₂(𝔽₃)` on full level-3 structures (KM p. 112 axiom 2's heart).
Freeness half in-repo (`glSmul_eq_one_of_eq_self`); route:
`Scheme.Hom.isIso_iff_finrank_eq` on the finite étale comparison (module docstring). -/
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
  sorry

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

end ModularCurves
