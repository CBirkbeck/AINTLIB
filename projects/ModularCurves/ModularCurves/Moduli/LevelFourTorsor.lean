/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.Bootstrap
import ModularCurves.Moduli.QuotientStack
import ModularCurves.ForMathlib.EtaleSectionsCount
import ModularCurves.Moduli.LevelThreeTorsor

/-!
# The level-4 `TorsorData` package (STREAM-E4, E4-B)

**(B2 resolution of record — board v10.342.)** KM 4.7.0's engine axiom 2 for
`δ = ` naive level 4: for every `E/S` with `2` invertible, the relative level-4 space is
a finite étale `GL₂(ℤ/4)`-torsor under the genuine global re-marking action
`gammaFullNaiveGlAction R 4`.

Per the LevelThreeTorsor generality audit (decomposition-e4.md §3): every mathematical
component is already general-`N` or general-group — `gammaFullNaive_relRepData`,
`isFinite_fullLevelSpaceStruct`, `levelSpaceΓπ_etale`, `gammaFullNaiveGl_freeAction`,
`exists_isNaiveFullLevel_of_isAlgClosed`, `exists_glSmul_eq` (needs `2 ≤ N`),
`glSmul_eq_one_of_eq_self`, and the abstract torsor-iso engine
`isIso_torsorSigmaDesc_of_existsUnique` (any finite group, any finite-étale morphism).
The rank-two torsion input `addEquiv_pi_fin_two_zmod_of_natCard` is pure group theory —
**no `ZMod 4`-vs-field obstruction exists**. This file's ticket (E4B) copies the ~10
`levelThree*` wrappers of `Moduli/LevelThreeTorsor.lean` at `N = 4`, keeping the
γ⁻¹-twisted equivariance convention ([B2-TD-CONV]) and the `ULift`/`MulEquiv.ulift`/
`Sigma.whiskerEquiv` universe transport for the `Type u` export.

## Reuse map (vs `Moduli/LevelThreeTorsor.lean`)

* **Imported as-is** (public there): the generic classifying-transport layer
  `ModuliProblem.RelRepData.relRepAut` / `relRepSchemeAction` /
  `relRepSchemeAction_over` / `relRepSchemeAction_equivariant`, and the general-`N`
  freeness lemma `gammaFullNaiveGl_freeAction`.
* **Replicated privately at general `N`** (their level-3 twins are `private`, hence
  inaccessible from here; bodies verbatim): `e4_exists_isNaiveFullLevel_of_isAlgClosed`,
  `e4_exists_glSmul_eq`, `e4_spec_factors_sigma`,
  `e4_isIso_torsorSigmaDesc_of_existsUnique`.
* **Instantiated at `N = 4`**: `levelFourData` (+ `_Z`/`_f`/`_finite`/`_etale`),
  `levelFourEquivariantData`, `levelFour_surjective`, `levelFour_torsor`, and the two
  exports `exists_levelFourTorsorData` / `exists_levelFourTorsorData_ulift`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

/-! ### The level-4 concrete datum

Replaying `gammaFullNaive_relRepData`'s ([GHA4]) proof body as a `def` at `N = 4`, so
the carrier stays the CONCRETE `YFull.fullLevelSpace X 4` — the geometric residuals
below are stated on it, keeping `levelSpaceΓ_spec`-style geometry available. -/

section LevelFour

variable (R : CommRingCat.{u})

/-- **The level-4 relative representation datum on the concrete carrier**
(KM 3.7.1 for `Γ(4)`; KM 4.6 first sentence): the full-level scheme
`U_{Γ(4)} = YFull.fullLevelSpace X 4` with its structure morphism, classifying naive
full level-4 structures via the pinned point-dictionary family ([YF-NAT]). Mirror of
`levelThreeData`. -/
noncomputable def levelFourData (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    ModuliProblem.RelRepData (gammaFullNaiveProblem R 4) X where
  Z := YFull.fullLevelSpace X 4
  f := YFull.fullLevelSpaceStruct X 4
  eqv {T} g := (YFull.exists_pointsEquiv_family R X 4 hinv).choose g
  nat {T T'} g k h := (YFull.exists_pointsEquiv_family R X 4 hinv).choose_spec g k h

@[simp]
theorem levelFourData_Z (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    (levelFourData R hinv X).Z = YFull.fullLevelSpace X 4 := rfl

@[simp]
theorem levelFourData_f (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    (levelFourData R hinv X).f = YFull.fullLevelSpaceStruct X 4 := rfl

/-- The structure map is finite ([YF-FIN], no invertibility needed). -/
theorem levelFourData_finite (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    IsFinite (levelFourData R hinv X).f :=
  YFull.isFinite_fullLevelSpaceStruct X 4

/-- The structure map is étale ([GHA3], the Weil-pairing leaf, AXIOM-CLEAN). -/
theorem levelFourData_etale (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    Etale (levelFourData R hinv X).f :=
  levelSpaceΓπ_etale X.curve 4 (YFull.nIsInvertible_over_spec R X.structMap hinv)

/-- **The fully proven equivariant package** on the concrete carrier: the level-4 datum
with the `GL₂(ℤ/4)`-action, in the (consistent) `γ⁻¹`-convention of [GH0b]. Mirror of
`levelThreeEquivariantData`; the action and its equivariance are the imported generic
layer `ModuliProblem.RelRepData.relRepSchemeAction` of `Moduli/LevelThreeTorsor.lean`. -/
noncomputable def levelFourEquivariantData (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    ModuliProblem.EquivariantRelRepData (gammaFullNaiveGlAction R 4) X where
  toRelRepData := levelFourData R hinv X
  σZ := ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
    (levelFourData R hinv X)
  over_base γ := ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ
  equivariant {T} g h γ :=
    ModuliProblem.RelRepData.relRepSchemeAction_equivariant _ _ g h γ
  finite := levelFourData_finite R hinv X
  etale := levelFourData_etale R hinv X

end LevelFour

/-! ### Geometric leaves: full level structures over a field

Verbatim replicas (general `N`) of the `private` level-3 leaves: **existence** of naive
full level structures over `k̄`, and **simple transitivity** of the `GL₂(ℤ/N)`-action
(the change-of-basis half of KM p. 112 axiom 2; the freeness half is
`glSmul_eq_one_of_eq_self`). -/

section GeometricLeaves

open EllipticCurve

/-- **Existence of naive full level structures over an algebraically closed field**
(KM 3.7.1's nonemptiness input): the images of the standard basis under any
`E[N](k) ≃+ (ℤ/N)²` (`torsion_geometricFibre_rank_two`) form a naive full level
structure. The generation clause over an extension `k'` holds because pulling points
back is an injection (`pull_injective`) between `N`-torsion groups of the same finite
cardinality `N²`, hence onto. Replica of the level-3 private leaf. -/
private theorem e4_exists_isNaiveFullLevel_of_isAlgClosed (k : Type u) [Field k]
    [IsAlgClosed k] (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : ∃ P Q : E.Section, E.IsNaiveFullLevel N P Q := by
  obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N k (𝟙 _) hk
  refine ⟨(e.symm ![1, 0]).1, (e.symm ![0, 1]).1,
    ⟨⟨(Submodule.mem_torsionBy_iff _ _).mp (e.symm ![1, 0]).2,
      (Submodule.mem_torsionBy_iff _ _).mp (e.symm ![0, 1]).2⟩, ?_⟩⟩
  intro k' _ _ t x hx
  -- `N` stays invertible over `k'`.
  have hk' : ((N : ℕ) : k') ≠ 0 := by
    have hu : IsUnit ((N : ℕ) : k) := isUnit_iff_ne_zero.mpr hk
    have hm := hu.map (Spec.preimage t).hom
    rw [map_natCast] at hm
    exact hm.ne_zero
  obtain ⟨e'⟩ := E.torsion_geometricFibre_rank_two N k' t hk'
  -- Pulling back is a map between the two `N`-torsion groups …
  have hpullmem : ∀ y : Submodule.torsionBy ℤ (E.Point (𝟙 (Spec (CommRingCat.of k)))) (N : ℤ),
      Point.pull E t y.1 ∈ Submodule.torsionBy ℤ (E.Point t) (N : ℤ) := by
    intro y
    refine (Submodule.mem_torsionBy_iff _ _).mpr ?_
    rw [← Point.pull_zsmul, (Submodule.mem_torsionBy_iff _ _).mp y.2, Point.pull_zero]
  set Φ : Submodule.torsionBy ℤ (E.Point (𝟙 (Spec (CommRingCat.of k)))) (N : ℤ) →
      Submodule.torsionBy ℤ (E.Point t) (N : ℤ) :=
    fun y => ⟨Point.pull E t y.1, hpullmem y⟩ with hΦ
  -- … which is injective, hence surjective by the `N²`-count on both sides.
  have hΦinj : Function.Injective Φ := fun y z h =>
    Subtype.ext (E.pull_injective k k' t (congrArg Subtype.val h))
  haveI : Finite (Submodule.torsionBy ℤ (E.Point (𝟙 (Spec (CommRingCat.of k)))) (N : ℤ)) :=
    Finite.of_equiv _ e.toEquiv.symm
  have hΦsurj : Function.Surjective Φ :=
    (Finite.injective_iff_surjective_of_equiv (e.toEquiv.trans e'.toEquiv.symm)).mp hΦinj
  obtain ⟨y, hy⟩ := hΦsurj ⟨x, (Submodule.mem_torsionBy_iff _ _).mpr hx⟩
  -- Expand `y` in the chosen basis and push through `pull`.
  have hc : e y = ((e y 0).val : ℤ) • ![1, 0] + ((e y 1).val : ℤ) • ![0, 1] := by
    funext i
    fin_cases i <;> simp [ZMod.natCast_val, ZMod.cast_id]
  have hy2 : y = ((e y 0).val : ℤ) • e.symm ![1, 0] + ((e y 1).val : ℤ) • e.symm ![0, 1] := by
    conv_lhs => rw [← e.symm_apply_apply y, hc]
    rw [map_add, map_zsmul, map_zsmul]
  have hy3 : (y : E.Point (𝟙 (Spec (CommRingCat.of k)))) =
      ((e y 0).val : ℤ) • ((e.symm ![1, 0]).1 : E.Point (𝟙 (Spec (CommRingCat.of k)))) +
        ((e y 1).val : ℤ) • (e.symm ![0, 1]).1 := by
    -- PERF: rewrite `y` on the LHS ONLY. A whole-goal `rw [hy2]` substitutes `y` into the
    -- RHS coefficients `e y`, forcing `whnf` to evaluate `e (e.symm …)` (an `AddEquiv`
    -- round-trip through the huge `torsionBy` structure) — the post-bump heartbeat blow-up.
    -- Restricting to `conv_lhs` leaves `e y` untouched; the rest is shallow coercion pushing.
    conv_lhs => rw [hy2]
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  have hx1 : Point.pull E t (y : E.Point (𝟙 (Spec (CommRingCat.of k)))) = x :=
    congrArg Subtype.val hy
  rw [← hx1, hy3, Point.pull_add, Point.pull_zsmul, Point.pull_zsmul]
  -- PERF: close via `mem_closure_pair` (a SYNTACTIC equality `rfl`) rather than a nested
  -- `add_mem (zsmul_mem (subset_closure (mem_insert …)) …) …` term — the latter forces the
  -- elaborator to `whnf` the large `Point.pull …`/`E.Point` terms across the unification chain
  -- (the post-bump heartbeat blow-up). Here the two sides are literally equal.
  rw [AddSubgroup.mem_closure_pair]
  exact ⟨((e y 0).val : ℤ), ((e y 1).val : ℤ), rfl⟩

/-- **Simple transitivity of the `GL₂(ℤ/N)`-action on naive full level structures over
an algebraically closed field** (the change-of-basis half of KM p. 112 axiom 2; the
freeness half is `glSmul_eq_one_of_eq_self`): any two structures differ by a matrix.
Both structures expand every `N`-torsion point in their own basis (the closure clause +
the `N²`-count of `torsion_geometricFibre_rank_two`); expanding each basis in the other
yields matrices `m`, `m'` with `m * m' = 1` (by injectivity of the first expansion), and
`glSmul ⟨m, m'⟩` carries `L₁` to `L₂` (checked after `pull`, via `pull_injective`).
Replica of the level-3 private leaf; no field hypothesis on `ZMod N` anywhere. -/
private theorem e4_exists_glSmul_eq (k : Type u) [Field k] [IsAlgClosed k]
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

/-! ### The abstract torsor-comparison iso engine (replica)

Verbatim replica of the level-3 private engine, universe-polymorphic in the finite group
`G : Type` and fully general in the finite étale morphism — see the extensive
documentation on the level-3 original. -/

section TorsorEngine

/-- A morphism from `Spec` of a field into a small scheme coproduct factors through one summand:
the coproduct's space is the disjoint union of the summands (`sigmaOpenCover`) and `Spec k` has a
single point, so its image lands in one summand's open range and `IsOpenImmersion.lift` produces
the factorisation. Replica of the level-3 private `spec_factors_sigma`. -/
private theorem e4_spec_factors_sigma {k : Type u} [Field k] {σ : Type*} [Small.{u} σ]
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
`b ≫ sm γ = a`, then `(γ, z) ↦ (sm γ ∘ z, z) : ∐_G Z ⟶ Z ×_S Z` is an isomorphism. Replica of
the level-3 private engine. -/
private theorem e4_isIso_torsorSigmaDesc_of_existsUnique {S Z : Scheme.{u}} {G : Type} [Finite G]
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
  · obtain ⟨i1, t1, ht1⟩ := e4_spec_factors_sigma (fun _ : G => Z) a1.1
    obtain ⟨i2, t2, ht2⟩ := e4_spec_factors_sigma (fun _ : G => Z) a2.1
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

/-! ### The geometric halves of the torsor axiom at `N = 4` -/

section Quarantine

variable (R : CommRingCat.{u})

/-- **Surjectivity of the level-4 structure map** (the covering half of KM p. 112
axiom 2: torsors cover their base; here with honest content since `4` is invertible).
Mirror of `levelThree_surjective`: geometric-point-over-`y` +
`e4_exists_isNaiveFullLevel_of_isAlgClosed` at `N = 4` + conversion through
`(levelFourData …).eqv`. -/
private theorem levelFour_surjective (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    AlgebraicGeometry.Surjective (YFull.fullLevelSpaceStruct X 4) := by
  constructor
  intro y
  -- The geometric point anchored over `y` (the point-anchored replay of
  -- `EllObj.exists_geometricPoint`: its proof routes through
  -- `X.base.fromSpecResidueField s`; here we keep the anchor).
  set t : Spec (CommRingCat.of (AlgebraicClosure (X.base.residueField y))) ⟶ X.base :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.base.residueField y)
      (AlgebraicClosure (X.base.residueField y)))) ≫ X.base.fromSpecResidueField y with ht
  have hk : ((4 : ℕ) : AlgebraicClosure (X.base.residueField y)) ≠ 0 := by
    have h := hinv.map (Spec.preimage (t ≫ X.structMap)).hom
    rw [map_natCast] at h
    exact h.ne_zero
  -- A naive full level-4 structure on the fibre curve over the geometric point.
  obtain ⟨P, Q, hPQ⟩ := e4_exists_isNaiveFullLevel_of_isAlgClosed
    (AlgebraicClosure (X.base.residueField y)) ((X.pullbackAlong t).curve) 4 hk
  -- Classify it: a `Z`-point over `t`.
  obtain ⟨z, hz⟩ := ((levelFourData R hinv X).eqv t).symm ⟨(P, Q), hPQ⟩
  obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of (AlgebraicClosure (X.base.residueField y)))) :=
    inferInstance
  refine ⟨z.base pt, ?_⟩
  have h1 : (YFull.fullLevelSpaceStruct X 4).base (z.base pt) = t.base pt := by
    have h0 : (z ≫ (levelFourData R hinv X).f).base pt = t.base pt :=
      congrArg (fun m => m.base pt) hz
    rwa [Scheme.Hom.comp_apply] at h0
  rw [h1, ht, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- **KM p. 112 axiom 2's geometric heart at `N = 4`** — the torsor comparison
`(γ, z) ↦ (γ·z, z) : ∐_{GL₂(ℤ/4)} Z → Z ×_S Z` is an isomorphism. Discharged by the
replica engine `e4_isIso_torsorSigmaDesc_of_existsUnique`, fed the fibrewise simple
transitivity of `GL₂(ℤ/4)`: over each algebraically closed field point, the
`eqv`-transport turns the fibre condition into `glSmul γ Lb = La`, which has a
**unique** solution by transitivity (`e4_exists_glSmul_eq`) + freeness
(`glSmul_eq_one_of_eq_self`). Mirror of `levelThree_torsor`. -/
private theorem levelFour_torsor (hinv : IsUnit ((4 : ℕ) : R)) (X : EllObj R) :
    IsIso ((Sigma.desc fun γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4) =>
      pullback.lift
        ((ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
            (levelFourData R hinv X)).hom γ)
        (𝟙 (levelFourData R hinv X).Z)
        (by
          rw [Category.id_comp]
          exact ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ)) :
      (∐ fun _ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4) =>
          (levelFourData R hinv X).Z) ⟶
        pullback (levelFourData R hinv X).f (levelFourData R hinv X).f) := by
  haveI : IsFinite (levelFourData R hinv X).f := levelFourData_finite R hinv X
  haveI : Etale (levelFourData R hinv X).f := levelFourData_etale R hinv X
  refine e4_isIso_torsorSigmaDesc_of_existsUnique (levelFourData R hinv X).f
    (fun γ => (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
      (levelFourData R hinv X)).hom γ)
    (fun γ => ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ) ?_
  -- **The fibrewise simple transitivity** (KM p. 112 axiom 2's heart): over an algebraically
  -- closed field point of `Z ×_S Z`, a unique `γ` carries the second level structure to the
  -- first. This is the `eqv`-transport of `glSmul` transitivity (`e4_exists_glSmul_eq`) +
  -- freeness (`glSmul_eq_one_of_eq_self`).
  intro K _ _ a b hab
  set g := a ≫ (levelFourData R hinv X).f with hg
  have hbg : b ≫ (levelFourData R hinv X).f = g := hab.symm
  set La := (levelFourData R hinv X).eqv g ⟨a, rfl⟩ with hLa
  set Lb := (levelFourData R hinv X).eqv g ⟨b, hbg⟩ with hLb
  have hK : ((4 : ℕ) : K) ≠ 0 := by
    have h := hinv.map (Spec.preimage (g ≫ X.structMap)).hom
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of K)) := inferInstance
  -- the induced scheme action agrees with `glSmul` on classified level structures
  have hact : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4))
      (L : (gammaFullNaiveProblem R 4).obj (Opposite.op (X.pullbackAlong g))),
      (gammaFullNaiveGlAction R 4 γ⁻¹).hom.app (Opposite.op (X.pullbackAlong g)) L =
        (X.pullbackAlong g).curve.glSmul γ L := by
    intro γ L
    show (gammaFullNaiveGlAut R 4 (γ⁻¹)⁻¹).hom.app _ L = _
    rw [inv_inv]
    rfl
  -- the fibre condition `b ≫ σZ γ = a` is exactly the `glSmul`-equation `glSmul γ Lb = La`,
  -- via the equivariance of the classifying bijection and injectivity of `eqv`
  have hbridge : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4),
      (b ≫ (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
        (levelFourData R hinv X)).hom γ = a) ↔
      ((X.pullbackAlong g).curve.glSmul γ Lb = La) := by
    intro γ
    have Eγ : (levelFourData R hinv X).eqv g
        ⟨b ≫ (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
            (levelFourData R hinv X)).hom γ,
          by rw [Category.assoc, ModuliProblem.RelRepData.relRepSchemeAction_over]; exact hbg⟩ =
        (X.pullbackAlong g).curve.glSmul γ Lb :=
      (ModuliProblem.RelRepData.relRepSchemeAction_equivariant
        (gammaFullNaiveGlAction R 4) (levelFourData R hinv X) g ⟨b, hbg⟩ γ).trans
        (by rw [hact, hLb])
    rw [← Eγ, hLa]
    exact ⟨fun h => congrArg _ (Subtype.ext h),
      fun h => congrArg Subtype.val (((levelFourData R hinv X).eqv g).injective h)⟩
  -- existence (transitivity) + uniqueness (freeness)
  obtain ⟨γ0, hγ0⟩ :=
    e4_exists_glSmul_eq K (X.pullbackAlong g).curve 4 (by norm_num) hK Lb La
  -- re-view the transitivity witness at the `pullbackAlong`-base (defeq to `Spec K`) so all
  -- `glSmul`s below share one base
  have hγ0' : (X.pullbackAlong g).curve.glSmul γ0 Lb = La := hγ0
  refine ⟨γ0, (hbridge γ0).mpr hγ0', fun γ' hγ' => ?_⟩
  have hgl' : (X.pullbackAlong g).curve.glSmul γ' Lb = La := (hbridge γ').mp hγ'
  have hfix : (X.pullbackAlong g).curve.glSmul (γ' * γ0⁻¹) Lb = Lb := by
    rw [EllipticCurve.glSmul_mul, hgl', ← hγ0', ← EllipticCurve.glSmul_mul,
      mul_inv_cancel, EllipticCurve.glSmul_one]
  have h1 := glSmul_eq_one_of_eq_self 4 hinv (X.pullbackAlong g) ⟨pt⟩ (γ' * γ0⁻¹) Lb hfix
  exact mul_inv_eq_one.mp h1

end Quarantine

/-! ### The chartered targets -/

/-- **(E4B, Type-0 export)** The level-4 `TorsorData` package at universe zero: the
naive level-4 problem's relative representing scheme is a finite étale
`GL₂(ℤ/4)`-torsor under the global re-marking action. Mirror of
`exists_levelThreeTorsorData`. -/
theorem exists_levelFourTorsorData (R : CommRingCat.{0}) (hinv : IsUnit (4 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData (gammaFullNaiveGlAction R 4) X) := by
  have hinv' : IsUnit ((4 : ℕ) : R) := by
    rw [Nat.cast_ofNat]
    exact hinv
  exact ⟨{ toRelRepData := levelFourData R hinv' X
           σZ := ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
             (levelFourData R hinv' X)
           over_base := fun γ =>
             ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ
           equivariant := fun {T} g h γ =>
             ModuliProblem.RelRepData.relRepSchemeAction_equivariant
               (gammaFullNaiveGlAction R 4) (levelFourData R hinv' X) g h γ
           finite := levelFourData_finite R hinv' X
           etale := levelFourData_etale R hinv' X
           surjective := levelFour_surjective R hinv' X
           torsor := levelFour_torsor R hinv' X }⟩

/-- **(E4B, the `Type u` export consumed by the engine's D(2) leg)** The level-4
`TorsorData` package with the group `ULift`ed to `Type u`. Mirror of
`exists_levelThreeTorsorData_ulift`. -/
theorem exists_levelFourTorsorData_ulift (R : CommRingCat.{u}) (hinv : IsUnit (4 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData
      ((gammaFullNaiveGlAction R 4).comp MulEquiv.ulift.toMonoidHom) X) := by
  have hinv' : IsUnit ((4 : ℕ) : R) := by
    rw [Nat.cast_ofNat]
    exact hinv
  set φu := (gammaFullNaiveGlAction R 4).comp MulEquiv.ulift.toMonoidHom with hφu
  refine ⟨{ toRelRepData := levelFourData R hinv' X
            σZ := ModuliProblem.RelRepData.relRepSchemeAction φu (levelFourData R hinv' X)
            over_base := fun γ =>
              ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ
            equivariant := fun {T} g h γ =>
              ModuliProblem.RelRepData.relRepSchemeAction_equivariant _ _ g h γ
            finite := levelFourData_finite R hinv' X
            etale := levelFourData_etale R hinv' X
            surjective := levelFour_surjective R hinv' X
            torsor := ?_ }⟩
  haveI hmap : IsIso (Sigma.map' (⇑Equiv.ulift)
      (fun _ : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 4)) =>
        𝟙 (levelFourData R hinv' X).Z)) := by
    change IsIso (Sigma.whiskerEquiv
      (f := fun _ : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 4)) =>
        (levelFourData R hinv' X).Z)
      (g := fun _ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4) => (levelFourData R hinv' X).Z)
      Equiv.ulift (fun _ => Iso.refl _)).hom
    infer_instance
  haveI hG : IsIso (Sigma.desc fun γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4) =>
      pullback.lift ((ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
        (levelFourData R hinv' X)).hom γ) (𝟙 (levelFourData R hinv' X).Z)
        (by rw [Category.id_comp]
            exact ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ)) :=
    levelFour_torsor R hinv' X
  -- the `ULift`-action agrees with the `Type 0` action after `Equiv.ulift` (transporting only the
  -- group element; `relRepAut` is untouched, keeping the `whnf` shallow)
  have hagree : ∀ γ' : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 4)),
      (ModuliProblem.RelRepData.relRepSchemeAction φu (levelFourData R hinv' X)).hom γ' =
        (ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
          (levelFourData R hinv' X)).hom (Equiv.ulift γ') := by
    intro γ'
    have hg : φu γ'⁻¹ = gammaFullNaiveGlAction R 4 (Equiv.ulift γ')⁻¹ := rfl
    rw [ModuliProblem.RelRepData.relRepSchemeAction_hom,
      ModuliProblem.RelRepData.relRepSchemeAction_hom, hg]
  have hfact : (Sigma.desc fun γ' : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 4)) =>
        pullback.lift ((ModuliProblem.RelRepData.relRepSchemeAction φu
          (levelFourData R hinv' X)).hom γ') (𝟙 (levelFourData R hinv' X).Z)
          (by rw [Category.id_comp]
              exact ModuliProblem.RelRepData.relRepSchemeAction_over _ _ γ')) =
      Sigma.map' (⇑Equiv.ulift) (fun _ => 𝟙 (levelFourData R hinv' X).Z) ≫
        (Sigma.desc fun γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4) =>
          pullback.lift ((ModuliProblem.RelRepData.relRepSchemeAction (gammaFullNaiveGlAction R 4)
            (levelFourData R hinv' X)).hom γ) (𝟙 (levelFourData R hinv' X).Z)
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
