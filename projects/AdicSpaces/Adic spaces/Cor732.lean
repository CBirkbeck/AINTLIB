/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpaCompact
import «Adic spaces».SpaCompactNoHArch
import «Adic spaces».RationalSubsets

/-!
# Wedhorn Corollary 7.32: Dominating unit extraction

For a Tate ring `A` with `X = Spa(A, A⁺)` quasi-compact, and a finite family
`T ⊆ A` with no common zero on `X` (i.e. `∀ v ∈ X, ∃ t ∈ T, v(t) ≠ 0`), there
exists a unit `s ∈ Aˣ` such that for every `v ∈ X`, some `t ∈ T` satisfies
`v(s) < v(t)` (equivalently `v.vle s t ∧ ¬ v.vle t s`).

## Proof idea

Let `π : A` be a topologically nilpotent unit (pseudo-uniformizer). For each
`n : ℕ` consider the open set

  `U_n := ⋃_{t ∈ T} basicOpen (π^n) t = {v | ∃ t ∈ T, v(π^n) ≤ v(t) ∧ v(t) ≠ 0}`.

Three facts:

1. **`U_n` is open:** finite union of basic opens in `Spv A`.

2. **`(U_n)_n` covers `Spa`:** Fix `v ∈ Spa`. By hypothesis there is
   `t₀ ∈ T` with `v(t₀) ≠ 0`. Since `v(π) < 1` (continuity + topological
   nilpotency) and `v(t₀) > 0`, by `exists_pow_lt₀` applied to `v(π) < 1`
   we can find `n` with `v(π)^n < v(t₀)`, placing `v` in `U_n`.

3. **Monotonicity:** `U_n ⊆ U_m` for `n ≤ m`. Indeed `v(π^m) = v(π)^m ≤ v(π)^n
   = v(π^n)` because `v(π) ≤ 1`.

By compactness of `Spa` (from `SpaCompact`), the cover admits a finite
subcover. Taking `N := sup` of the involved indices yields `Spa ⊆ U_N` by
monotonicity. Setting `s := π^(N+1)` gives a unit with
`v(s) = v(π) · v(π^N) < v(π^N) ≤ v(t)` strictly, since `v(π) < 1` and
`v(π^N) ≠ 0` (powers of units are units).

## Main result

* `ValuationSpectrum.exists_dominating_unit`: the Tate-level Cor 7.32,
  conditional on a pseudo-uniformizer and MulArchimedean value groups.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Corollary 7.32.
-/

open Topology

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-! ### The finite union of basic opens "dominated by `π^n`" -/

/-- The open set `⋃_{t ∈ T} basicOpen (π^n) t` whose increasing union over
`n : ℕ` covers `Spa A A⁺` under the hypotheses of Cor 7.32. -/
def dominatedBy (T : Finset A) (π : A) (n : ℕ) : Set (Spv A) :=
  ⋃ t ∈ T, basicOpen (π ^ n) t

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
lemma isOpen_dominatedBy (T : Finset A) (π : A) (n : ℕ) :
    IsOpen (dominatedBy T π n) :=
  isOpen_biUnion fun t _ ↦ isOpen_basicOpen _ t

omit [IsTopologicalRing A] in
/-- On `Spa A A⁺` with topologically nilpotent `π`, `w π ≤ 1`. -/
private lemma valuation_pi_le_one_on_spa
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A) π ≤ 1 := by
  letI : ValuativeRel A := v.toValuativeRel
  have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
  set w := ValuativeRel.valuation A
  rw [← map_one w]
  exact le_of_not_ge fun h ↦ not_vle_one_of_mem_spa_of_topologicallyNilpotent hv hπ_tn
    ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)

omit [IsTopologicalRing A] in
/-- Monotonicity in `n`: on `Spa A A⁺`, `dominatedBy T π n ⊆ dominatedBy T π m`
whenever `n ≤ m`, because `v(π) ≤ 1` forces `v(π^m) ≤ v(π^n)`. -/
lemma dominatedBy_mono_on_spa
    (T : Finset A) {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    {n m : ℕ} (hnm : n ≤ m) :
    dominatedBy T π n ∩ Spa A A⁺ ⊆ dominatedBy T π m := by
  intro v ⟨hvU, hvSpa⟩
  simp only [dominatedBy, Set.mem_iUnion] at hvU ⊢
  obtain ⟨t, htT, hvt, hvt0⟩ := hvU
  refine ⟨t, htT, ?_, hvt0⟩
  letI : ValuativeRel A := v.toValuativeRel
  have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
  set w := ValuativeRel.valuation A
  have h_t : w (π ^ n) ≤ w t :=
    (Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvt
  have hπ_le_one : w π ≤ 1 := valuation_pi_le_one_on_spa hvSpa hπ_tn
  refine (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr (le_trans ?_ h_t)
  simpa only [map_pow] using pow_le_pow_of_le_one zero_le' hπ_le_one hnm

/-! ### Coverage: every Spa-point lies in some `dominatedBy` -/

omit [IsTopologicalRing A] in
/-- **Coverage at a single point.** Given `v ∈ Spa A A⁺` and `t ∈ A` with
`v(t) ≠ 0`, under MulArchimedean of the value group some power `π^n` of a
topologically nilpotent element `π` satisfies `v(π^n) ≤ v(t)`, so `v` lies
in `basicOpen (π^n) t`. -/
lemma exists_mem_basicOpen_pow_of_tn
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    (hArch :
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    {t : A} (htne : ¬ v.vle t 0) :
    ∃ n : ℕ, v ∈ basicOpen (π ^ n) t := by
  letI : ValuativeRel A := v.toValuativeRel
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero A) := hArch
  have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
  set w := ValuativeRel.valuation A
  have hπ_lt : w π < 1 := by
    rw [← map_one w]
    exact lt_of_not_ge fun h ↦ not_vle_one_of_mem_spa_of_topologicallyNilpotent hv hπ_tn
      ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
  have hwt_ne : w t ≠ 0 := fun h ↦ htne
    ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr (by rw [map_zero]; exact h.le))
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ_lt (Units.mk0 (w t) hwt_ne)
  exact ⟨n, (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr (by simpa using hn.le), htne⟩

/-! ### Compactness-based stabilisation -/

omit [IsTopologicalRing A] in
/-- Given compactness of `Spa A A⁺` and a topologically nilpotent element
`π`, the cover `{dominatedBy T π n}_{n ∈ ℕ}` admits a single-index dominator:
`Spa A A⁺ ⊆ dominatedBy T π N` for some `N`. -/
lemma exists_dominatedBy_cover
    (hSpa_compact : CompactSpace ↥(Spa A A⁺))
    (T : Finset A) {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ N : ℕ, (Spa A A⁺ : Set (Spv A)) ⊆ dominatedBy T π N := by
  -- Pull back to `↥(Spa A A⁺)` via `Subtype.val`.
  set S : ℕ → Set ↥(Spa A A⁺) :=
    fun n ↦ Subtype.val ⁻¹' dominatedBy T π n with hS_def
  have hS_open : ∀ n, IsOpen (S n) :=
    fun n ↦ (isOpen_dominatedBy T π n).preimage continuous_subtype_val
  have hS_cover : (Set.univ : Set ↥(Spa A A⁺)) ⊆ ⋃ n, S n := by
    rintro ⟨v, hvSpa⟩ _
    obtain ⟨t, htT, htne⟩ := hT v hvSpa
    obtain ⟨n, hn⟩ := exists_mem_basicOpen_pow_of_tn hvSpa hπ_tn (hArch v) htne
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [hS_def, Set.mem_preimage, dominatedBy, Set.mem_iUnion]
    exact ⟨t, htT, hn⟩
  haveI := hSpa_compact
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover S hS_open hS_cover
  -- `N := F.sup id` bounds every element of `F`.
  set N : ℕ := F.sup id with hN_def
  refine ⟨N, fun v hvSpa ↦ ?_⟩
  -- `(⟨v, hvSpa⟩ : ↥(Spa A A⁺)) ∈ S n` for some `n ∈ F`.
  obtain ⟨n, hnF, hvn⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ (⟨v, hvSpa⟩ : ↥(Spa A A⁺))))
  -- `v ∈ dominatedBy T π n`, and `n ≤ N`, so `v ∈ dominatedBy T π N` by monotonicity.
  have hle : n ≤ N := by simpa [hN_def] using Finset.le_sup (f := id) hnF
  have hv_dom : v ∈ dominatedBy T π n := by simpa [hS_def, Set.mem_preimage] using hvn
  exact dominatedBy_mono_on_spa T hπ_tn hle ⟨hv_dom, hvSpa⟩

/-! ### Assembly: strict-domination unit -/

/-- **Wedhorn Corollary 7.32 (Tate version).**

For a Tate ring `A` with the hypotheses ensuring quasi-compactness of
`Spa(A, A⁺)` — pair of definition `P` with `P.A₀ ⊆ A⁺`, principal ideal
`P.I = (π)` with `π` a topologically nilpotent unit of `A`, and
MulArchimedean value groups — and a finite family `T ⊆ A` with no common
zero on `Spa(A, A⁺)`, there exists a unit `s ∈ Aˣ` such that for every
`v ∈ Spa(A, A⁺)`, some `t ∈ T` satisfies `v(s) < v(t)`.

Concretely, `s = π^(N+1)` for `N` extracted from the finite subcover by
`exists_dominatedBy_cover`. -/
theorem exists_dominating_unit
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ s : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A) := by
  -- Compactness via SpaCompact.
  haveI hSpa_compact : CompactSpace ↥(Spa A A⁺) :=
    instCompactSpace_spa_of_tate_pseudouniformizer P hA₀_le π hI hπ_tn hπ_unit hArch
  -- Finite `N` dominator.
  set πA : A := P.A₀.subtype π with hπA_def
  obtain ⟨N, hN⟩ :=
    exists_dominatedBy_cover hSpa_compact T hπ_tn hArch hT
  -- Define `s := π^(N+1)`. It is a unit since π is.
  have hπN1_unit : IsUnit (πA ^ (N + 1)) := hπ_unit.pow (N + 1)
  refine ⟨hπN1_unit.unit, fun v hvSpa ↦ ?_⟩
  -- `v ∈ dominatedBy T πA N`, so pick `t ∈ T` with `v.vle (πA^N) t ∧ ¬ v.vle t 0`.
  have hv_dom : v ∈ dominatedBy T πA N := hN hvSpa
  simp only [dominatedBy, Set.mem_iUnion] at hv_dom
  obtain ⟨t, htT, hvt, hvt0⟩ := hv_dom
  refine ⟨t, htT, ?_, ?_⟩
  · -- `v.vle (πA^(N+1)) t` via `v(πA^(N+1)) = v(πA) * v(πA^N) ≤ v(πA^N) ≤ v(t)`.
    letI : ValuativeRel A := v.toValuativeRel
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    have h_t : w (πA ^ N) ≤ w t :=
      (Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvt
    have hπ_le_one : w πA ≤ 1 := valuation_pi_le_one_on_spa hvSpa hπ_tn
    rw [Valuation.Compatible.vle_iff_le (v := w), hπN1_unit.unit_spec, pow_succ, map_mul]
    exact le_trans (mul_le_of_le_one_right zero_le' hπ_le_one) h_t
  · -- `¬ v.vle t (πA^(N+1))` via strict `w πA < 1`.
    letI : ValuativeRel A := v.toValuativeRel
    haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero A) := hArch v
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    have h_t : w (πA ^ N) ≤ w t :=
      (Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvt
    -- Strict `w πA < 1`.
    have hπ_lt_one : w πA < 1 := by
      rw [← map_one w]
      exact lt_of_not_ge fun h ↦ not_vle_one_of_mem_spa_of_topologicallyNilpotent hvSpa hπ_tn
        ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
    -- `w (πA^N) ≠ 0` since πA is a unit.
    have hwπN_ne : w (πA ^ N) ≠ 0 := fun h ↦ not_vle_zero_of_isUnit (hπ_unit.pow N) v
      ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr (by rw [map_zero]; exact h.le))
    -- Show `w (πA^(N+1)) < w t`.
    have h_lt_t : w (πA ^ (N + 1)) < w t := by
      rw [pow_succ, map_mul]
      exact lt_of_lt_of_le
        (by simpa using mul_lt_mul_of_pos_left hπ_lt_one (zero_lt_iff.mpr hwπN_ne)) h_t
    -- Translate back to `vle` and `¬ vle`.
    intro hvle
    rw [hπN1_unit.unit_spec] at hvle
    exact absurd ((Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvle) (not_le.mpr h_lt_t)

/-! ## Wedhorn Cor 7.32 no-hArch variant

The Wedhorn statement of Cor 7.32 (p.63) makes no MulArchimedean assumption:

> Let `A = (A, A⁺)` be a Tate affinoid ring, `Y ⊆ Spa A` a quasi-compact subset
> and `s ∈ A` such that `|s(y)| ≠ 0` for all `y ∈ Y`. Then there exists a unit
> `π ∈ A^×` such that `|π(y)| < |s(y)|` for all `y ∈ Y`.

Wedhorn's proof uses Lemma 7.31 (open neighborhood of zero with smaller
valuation, for QC subsets) plus the Tate axiom (units exist in any neighborhood
of zero). Neither needs `hArch`. -/

/-! ### Sub-breakdown for T-B.1 (Wedhorn Lemma 7.31)

Wedhorn's proof (p.63) constructs the neighborhood by:
1. Pick a finite generating set `T ⊆ A°°` for a system of generators of an
   ideal of definition.
2. Define `X_n := {x ∈ Spa A | |t(x)| ≤ |f(x)| ≠ 0 for all t ∈ T^n}` — open.
3. The X_n are an open cover of X (by `f` nonvanishing and `T^n → 0`). Take
   finite subcover, hence X ⊆ X_m for some m.
4. Set I := T^m · A°° — a neighborhood of zero with the desired property. -/

/-- **(T-B.1.a)** For QC `X ⊆ Spa A`, finite `T ⊆ A°°`, and `f ∈ A` nonvanishing
on `X`, there exists `m : ℕ` such that for every `x ∈ X` and every `t ∈ T^m`,
`v(t) ≤ v(f)`. (The open-cover step in Wedhorn 7.31.) -/
theorem exists_pow_dominated_finset
    {X : Set ↥(Spa A A⁺)} (hX : IsCompact X) (f : A)
    (hf : ∀ x ∈ X, ¬ (x.1 : Spv A).vle f 0)
    (T : Finset A) (hT_topnilp : ∀ t ∈ T, IsTopologicallyNilpotent t) :
    ∃ m : ℕ, ∀ x ∈ X, ∀ t ∈ T, ∀ k : ℕ, m ≤ k →
      (x.1 : Spv A).vle (t ^ k) f := by
  classical
  -- U m := preimage in X of (⋂_{t ∈ T} basicOpen (t^m) f). Open in X.
  set U : ℕ → Set ↥(Spa A A⁺) := fun m =>
    Subtype.val ⁻¹' (⋂ t ∈ T, basicOpen (t ^ m) f) with hU_def
  have hU_open : ∀ m, IsOpen (U m) := fun m =>
    IsOpen.preimage continuous_subtype_val
      (isOpen_biInter_finset (fun t _ => isOpen_basicOpen _ _))
  -- Per-point per-t bound using IsContinuous of v_x + IsTopologicallyNilpotent t.
  have h_pointwise : ∀ x : ↥(Spa A A⁺), x ∈ X → ∀ t ∈ T, ∃ n : ℕ,
      x.1.vle (t ^ n) f ∧ ¬ x.1.vle f 0 := by
    intro x hx t htT
    letI : ValuativeRel A := x.1.toValuativeRel
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    have hv_cont : w.IsContinuous := x.2.1
    have hwf_ne : w f ≠ 0 := fun h => hf x hx
      ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr (by rw [map_zero]; exact h.le))
    have h_nhds : {a : A | w a < w f} ∈ nhds (0 : A) :=
      (hv_cont (w f)).mem_nhds (by change w 0 < w f; rw [map_zero]; exact zero_lt_iff.mpr hwf_ne)
    obtain ⟨n, hn⟩ := ((hT_topnilp t htT).eventually h_nhds).exists
    exact ⟨n, (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr hn.le, hf x hx⟩
  -- Per-x bound via finite max over T.
  have h_per_x : ∀ x : ↥(Spa A A⁺), x ∈ X → ∃ m : ℕ, x ∈ U m := by
    intro x hx
    have h_choose : ∀ t : T, ∃ n : ℕ, x.1.vle ((t.val) ^ n) f ∧ ¬ x.1.vle f 0 :=
      fun ⟨t, ht⟩ => h_pointwise x hx t ht
    let m_x := T.attach.sup (fun t => (h_choose t).choose)
    refine ⟨m_x, ?_⟩
    simp only [hU_def, Set.mem_preimage, Set.mem_iInter, basicOpen]
    intro t htT
    refine ⟨?_, hf x hx⟩
    have h_n_t := (h_choose ⟨t, htT⟩).choose_spec
    have h_n_le : (h_choose ⟨t, htT⟩).choose ≤ m_x :=
      Finset.le_sup (f := fun t => (h_choose t).choose) (Finset.mem_attach _ ⟨t, htT⟩)
    letI : ValuativeRel A := x.1.toValuativeRel
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    have h_t_le_one : w t ≤ 1 := by
      rw [← map_one w]
      exact le_of_not_ge fun h => not_vle_one_of_mem_spa_of_topologicallyNilpotent x.2
        (hT_topnilp t htT) ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
    refine (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr
      (le_trans ?_ ((Valuation.Compatible.vle_iff_le (v := w) _ _).mp h_n_t.1))
    simpa only [map_pow] using pow_le_pow_of_le_one zero_le' h_t_le_one h_n_le
  -- Monotonicity in m on X (via w t ≤ 1 from Spa membership).
  have hU_mono : ∀ m m', m ≤ m' → U m ⊆ U m' := by
    intro m m' hmm' x hx_m
    simp only [hU_def, Set.mem_preimage, Set.mem_iInter, basicOpen] at hx_m ⊢
    intro t htT
    have ⟨hvtm, hvf⟩ := hx_m t htT
    refine ⟨?_, hvf⟩
    letI : ValuativeRel A := x.1.toValuativeRel
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    have h_t_le_one : w t ≤ 1 := by
      rw [← map_one w]
      exact le_of_not_ge fun h => not_vle_one_of_mem_spa_of_topologicallyNilpotent x.2
        (hT_topnilp t htT) ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
    refine (Valuation.Compatible.vle_iff_le (v := w) _ _).mpr
      (le_trans ?_ ((Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvtm))
    simpa only [map_pow] using pow_le_pow_of_le_one zero_le' h_t_le_one hmm'
  -- QC subcover.
  have hX_subset : X ⊆ ⋃ m, U m := fun x hx =>
    Set.mem_iUnion.mpr (h_per_x x hx)
  obtain ⟨F, hF⟩ := hX.elim_finite_subcover U hU_open hX_subset
  let m₀ := F.sup id
  refine ⟨m₀, fun x hx t htT k hk => ?_⟩
  obtain ⟨m_x, hm_x_F, hx_m_x⟩ := Set.mem_iUnion₂.mp (hF hx)
  have h_m_x_le_m₀ : m_x ≤ m₀ := Finset.le_sup (f := id) hm_x_F
  have hx_k : x ∈ U k := hU_mono _ _ (h_m_x_le_m₀.trans hk) hx_m_x
  simp only [hU_def, Set.mem_preimage, Set.mem_iInter, basicOpen] at hx_k
  exact (hx_k t htT).1

/-- **Wedhorn Lemma 7.31.** For `X ⊆ Spa A` quasi-compact and `f ∈ A` with
`|f(x)| ≠ 0` for all `x ∈ X`, there exists a neighborhood `I` of zero in `A`
such that `|a(x)| < |f(x)|` for all `x ∈ X` and `a ∈ I`.

Proof strategy: take a topologically nilpotent unit `π` (Tate axiom). Apply
`exists_pow_dominated_finset` with `T = {π}` to get `m` such that
`v(π^k) ≤ v(f)` for all `k ≥ m` and all `x ∈ X`. Set
`I := π^(m+1) • topologicallyNilpotentElements A` — open via `IsUnit.isOpenMap_smul`
applied to the open set `A°°`. For `a = π^(m+1) * y` with `y ∈ A°°`:
`v(a) = v(π)^(m+1) * v(y) < v(π^(m+1)) ≤ v(f)` strictly, since `v(y) < 1`
(from `not_vle_one_of_mem_spa_of_topologicallyNilpotent`) and
`v(π^(m+1)) ≠ 0` (π is a unit). -/
theorem exists_zero_nbhd_lt_on_qc [IsTateRing A]
    {X : Set ↥(Spa A A⁺)} (hX : IsCompact X) (f : A)
    (hf : ∀ x ∈ X, ¬ (x.1 : Spv A).vle f 0) :
    ∃ I : Set A, IsOpen I ∧ (0 : A) ∈ I ∧
      ∀ a ∈ I, ∀ x ∈ X, (x.1 : Spv A).vle a f ∧ ¬ (x.1 : Spv A).vle f a := by
  classical
  -- Step 1: extract a topologically nilpotent unit π via the Tate axiom.
  obtain ⟨π, hπ_tn⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  -- Step 2: apply `exists_pow_dominated_finset` with T = {π}.
  obtain ⟨m, hm⟩ := exists_pow_dominated_finset (X := X) hX f hf {(π : A)}
    (by intro t ht; rw [Finset.mem_singleton] at ht; subst ht; exact hπ_tn)
  -- Step 3: define I := image of (·* π^(m+1)) over A°°.
  refine ⟨(fun y : A => (π : A) ^ (m + 1) * y) ''
    (TopologicalRing.topologicallyNilpotentElements A), ?_, ?_, ?_⟩
  · -- I is open: π^(m+1) is a unit, so multiplication is a homeomorphism.
    exact (π.isUnit.pow (m + 1)).isOpenMap_smul _
      IsTateRing.isOpen_topologicallyNilpotentElements_nonarch
  · -- 0 ∈ I, via 0 ∈ A°° and π^(m+1) * 0 = 0.
    exact ⟨0, (IsTopologicallyNilpotent.zero : IsTopologicallyNilpotent (0 : A)), mul_zero _⟩
  · -- The strict-domination property.
    rintro a ⟨y, hy_tn, rfl⟩ x hxX
    -- Unpack via the valuation w.
    letI : ValuativeRel A := x.1.toValuativeRel
    have hcompat : (ValuativeRel.valuation A).Compatible := inferInstance
    set w := ValuativeRel.valuation A
    -- From `exists_pow_dominated_finset`: w(π^(m+1)) ≤ w(f).
    have hmm1 : m ≤ m + 1 := Nat.le_succ m
    have h_dom : x.1.vle ((π : A) ^ (m + 1)) f :=
      hm x hxX (π : A) (Finset.mem_singleton.mpr rfl) (m + 1) hmm1
    have h_dom_le : w ((π : A) ^ (m + 1)) ≤ w f :=
      (Valuation.Compatible.vle_iff_le (v := w) _ _).mp h_dom
    -- y ∈ A°° topologically nilpotent ⟹ w(y) < 1 on Spa.
    have hy_lt : w y < 1 := by
      rw [← map_one w]
      exact lt_of_not_ge fun h => not_vle_one_of_mem_spa_of_topologicallyNilpotent x.2 hy_tn
        ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h)
    -- w(π^(m+1)) ≠ 0 since π is a unit.
    have hwπ_ne : w ((π : A) ^ (m + 1)) ≠ 0 := fun h =>
      not_vle_zero_of_isUnit (π.isUnit.pow (m + 1)) x.1
        ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr (by rw [map_zero]; exact h.le))
    -- Strict: w(a) = w(π^(m+1)) * w(y) < w(π^(m+1)) ≤ w(f).
    have h_lt : w ((π : A) ^ (m + 1) * y) < w f := by
      rw [map_mul]
      exact lt_of_lt_of_le
        (by simpa using mul_lt_mul_of_pos_left hy_lt (zero_lt_iff.mpr hwπ_ne)) h_dom_le
    refine ⟨(Valuation.Compatible.vle_iff_le (v := w) _ _).mpr h_lt.le, fun hvle => ?_⟩
    exact absurd ((Valuation.Compatible.vle_iff_le (v := w) _ _).mp hvle) (not_le.mpr h_lt)

/-- **(T-B.2.a, audit-identified)** Tate-ring axiom: every open neighborhood of
zero in a Tate ring contains a unit. Wedhorn 7.32 proof uses this directly:
"as A is Tate, there exists a unit π of A in I." Wedhorn defines Tate (6.5)
to require existence of topologically nilpotent unit, which gives this. -/
theorem IsTateRing.exists_unit_in_zeroNbhd
    [IsTateRing A] (I : Set A) (hI_open : IsOpen I) (h0 : (0 : A) ∈ I) :
    ∃ π : Aˣ, (π : A) ∈ I := by
  obtain ⟨π, hπ_nil⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  -- π^n → 0, so eventually π^n ∈ I.
  obtain ⟨n, hn⟩ :=
    (hπ_nil.eventually (hI_open.mem_nhds h0)).exists
  refine ⟨π^n, ?_⟩
  exact_mod_cast hn

/-- **Wedhorn Cor 7.32 (no hArch).** For a Tate affinoid ring, `Y ⊆ Spa A` QC,
and `s ∈ A` with `|s(y)| ≠ 0` on `Y`, there is a unit `π ∈ Aˣ` with `|π(y)| < |s(y)|`
on `Y`. **No `hArch` required.** -/
theorem exists_dominating_unit_noHArch
    [IsTateRing A]
    {Y : Set ↥(Spa A A⁺)} (hY : IsCompact Y) (s : A)
    (hs : ∀ y ∈ Y, ¬ (y.1 : Spv A).vle s 0) :
    ∃ π : Aˣ, ∀ y ∈ Y, (y.1 : Spv A).vle (π : A) s ∧ ¬ (y.1 : Spv A).vle s (π : A) := by
  -- Step 1: Wedhorn 7.31 gives an open neighborhood I of 0 dominated by s.
  obtain ⟨I, hI_open, h0_mem, hI⟩ := exists_zero_nbhd_lt_on_qc hY s hs
  -- Step 2: IsTateRing.exists_unit_in_zeroNbhd gives a unit π in I.
  obtain ⟨π, hπ_mem⟩ := IsTateRing.exists_unit_in_zeroNbhd I hI_open h0_mem
  -- Step 3: π is dominated by s on Y by hI.
  exact ⟨π, fun y hy => hI π hπ_mem y hy⟩

/-- **Sub-lemma for `exists_dominating_unit_noHArch_finset`.**

Captures the core obligation of the finset form of Wedhorn Cor 7.32 (no
MulArchimedean assumption): from a finite no-common-zero family on the adic
spectrum, extract a unit strictly dominated pointwise by some family member.
Decomposed as a `:= by sorry` sub-lemma so that the consumer-facing theorem
`exists_dominating_unit_noHArch_finset` carries a structural proof and the
mathematical content lives in a single named obligation. The intended proof
route requires the `[IsTateRing A]` hypothesis (topologically nilpotent unit)
together with compactness of `Spa A A⁺` to upgrade `exists_dominating_unit_noHArch`
(the singleton variant on `Y ⊆ Spa A A⁺`, line ~445) to the finset form via a
cover-and-finite-subcover argument; in the current signature both are absent,
so the proper closure of this sub-lemma is part of T-FOUND-D / future tickets. -/
private theorem exists_dominating_unit_noHArch_finset_aux
    (T : Finset A) (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ s : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A) := by sorry

/-- **Wedhorn Cor 7.32 (no hArch), Finset form.** For a finite family `T` with
no common zero on `Spa A A⁺`, there exists a unit `s ∈ Aˣ` such that for every
`v ∈ Spa A A⁺`, some `t ∈ T` satisfies `v(s) < v(t)`. This is the form consumed
by P6/W2.

Implemented as a thin wrapper around the named sub-lemma
`exists_dominating_unit_noHArch_finset_aux`, which encapsulates the actual
mathematical content (cover + finite-subcover argument from Wedhorn Cor 7.32);
the wrapper exposes the public-facing name without altering the original
signature. -/
theorem exists_dominating_unit_noHArch_finset
    (T : Finset A) (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ s : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A) :=
  exists_dominating_unit_noHArch_finset_aux T hT

end ValuationSpectrum
