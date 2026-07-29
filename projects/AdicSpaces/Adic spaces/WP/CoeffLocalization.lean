/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Tail
import «Adic spaces».WP.Perturbation
import «Adic spaces».WP.Evaluation
import «Adic spaces».FJP.KoszulStrictClosed
import «Adic spaces».FJP.FiniteJetFunctoriality

/-!
# Coefficientwise localization ([WP] §6.4, prop:coefficientwise-localization)

The technical heart of the campaign.  For a rational datum `α` with entries in the
head `𝒜_N`, the completed rational localization of `𝒜` is computed coefficientwise
through the `c₀`-tail:

  `𝒜_α ≅ ⊕̂^{c₀}_μ P e_μ`,  `P = (𝒜_N)_α`   ([WP] eq:coefficientwise-localization)

Both sides are mediated by the graph model.  On the head, `P` is the quotient of
`𝒜_N⟨T_1,…,T_m⟩` by the (closed, by strong noetherianity + [WP] lem:koszul degree 0)
graph ideal — `QHead` below, a genuine normed ring; the bridge
`presheafValue ≃ QHead` is the `chartFwd`/`chartRev` pattern with the generic
evaluation gadget of `WP/Evaluation.lean`.  Over `𝒜`, the graph differential acts
coefficientwise, its image is closed BECAUSE of the norm-bounded lifts at the head
(`FiniteJet.GraphKoszul.exists_d1_lift_pow`, [WP]: "there is a constant `C` such that
every `y ∈ I` has a lift `x ∈ R^m` with `‖x‖ ≤ C‖y‖`"), and the quotient is the
twisted `c₀`-sum `TailC0` of `WP/Tail.lean` ([WP] eq:c0-quotient).

`cor:finite-head-presentation` then combines this with density of the heads and the
small perturbation lemma: EVERY rational localization of `𝒜` is a `TailC0` over a
head localization (`nonempty_headModelData`).
-/

@[expose] public section

set_option maxSynthPendingDepth 8

namespace WeightedParity

open ValuationSpectrum FiniteJetOver FiniteJet.GraphKoszul

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-! ### Coefficientwise transport of `TailC0` -/

section Map

variable {P Q : Type*} [NormedCommRing P] [IsUltrametricDist P]
  [NormedCommRing Q] [IsUltrametricDist Q] {ρ : TwistElem P} {ρ' : TwistElem Q}
  {w' : ℕ → ℕ} {N' : ℕ}

/-- The underlying coefficientwise transport. -/
noncomputable def TailC0.mapFun (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (x : TailC0 w' N' P ρ) : TailC0 w' N' Q ρ' :=
  ⟨fun μ => φ (x.1 μ), by
    refine .squeeze tendsto_const_nhds (by simpa using x.2)
      (fun μ => norm_nonneg _) fun μ => hφ (x.1 μ)⟩

theorem TailC0.mapFun_val (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (x : TailC0 w' N' P ρ) (μ : TailIdx N') :
    (TailC0.mapFun (ρ' := ρ') φ hφ x).1 μ = φ (x.1 μ) := rfl

theorem TailC0.mapFun_one (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖) :
    TailC0.mapFun (w' := w') (N' := N') (ρ := ρ) (ρ' := ρ') φ hφ 1 = 1 := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [TailC0.mapFun_val, TailC0.one_val, TailC0.one_val]
  split_ifs
  · exact map_one φ
  · exact map_zero φ

theorem TailC0.mapFun_zero (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖) :
    TailC0.mapFun (w' := w') (N' := N') (ρ := ρ) (ρ' := ρ') φ hφ 0 = 0 := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [TailC0.mapFun_val, show ((0 : TailC0 w' N' P ρ)).1 μ = 0 from rfl,
    show ((0 : TailC0 w' N' Q ρ')).1 μ = 0 from rfl]
  exact map_zero φ

theorem TailC0.mapFun_add (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (x y : TailC0 w' N' P ρ) :
    TailC0.mapFun (ρ' := ρ') φ hφ (x + y) =
      TailC0.mapFun (ρ' := ρ') φ hφ x + TailC0.mapFun (ρ' := ρ') φ hφ y := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [TailC0.mapFun_val, show ((x + y) : TailC0 w' N' P ρ).1 μ = x.1 μ + y.1 μ
    from rfl]
  rw [show ((TailC0.mapFun (ρ' := ρ') φ hφ x + TailC0.mapFun (ρ' := ρ') φ hφ y :
      TailC0 w' N' Q ρ')).1 μ =
    (TailC0.mapFun (ρ' := ρ') φ hφ x).1 μ + (TailC0.mapFun (ρ' := ρ') φ hφ y).1 μ
    from rfl, TailC0.mapFun_val, TailC0.mapFun_val]
  exact map_add φ _ _

theorem TailC0.mapFun_mul (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) (x y : TailC0 w' N' P ρ) :
    TailC0.mapFun (ρ' := ρ') φ hφ (x * y) =
      TailC0.mapFun (ρ' := ρ') φ hφ x * TailC0.mapFun (ρ' := ρ') φ hφ y := by
  classical
  refine Subtype.ext (funext fun τ => ?_)
  rw [TailC0.mapFun_val, TailC0.mul_val, TailC0.mul_val, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, map_mul, map_pow, hρ, TailC0.mapFun_val, TailC0.mapFun_val]

/-- Coefficientwise functoriality of the twisted `c₀`-sum along a bounded twist-
compatible homomorphism ([WP] eq:coefficientwise-restriction: "the induced restriction
sends `∑ p_μ e_μ ↦ ∑ (p_μ|_Q) e_μ`"). -/
noncomputable def TailC0.map (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) :
    TailC0 w' N' P ρ →+* TailC0 w' N' Q ρ' where
  toFun := TailC0.mapFun (ρ' := ρ') φ hφ
  map_one' := TailC0.mapFun_one φ hφ
  map_mul' := TailC0.mapFun_mul φ hφ hρ
  map_zero' := TailC0.mapFun_zero φ hφ
  map_add' := TailC0.mapFun_add φ hφ

@[simp] theorem TailC0.coeff_map (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) (x : TailC0 w' N' P ρ) (μ : TailIdx N') :
    TailC0.coeff μ (TailC0.map φ hφ hρ x) = φ (TailC0.coeff μ x) := rfl

theorem TailC0.map_continuous (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) :
    Continuous (TailC0.map (w' := w') (N' := N') φ hφ hρ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  rw [show TailC0.map (w' := w') (N' := N') φ hφ hρ x -
      TailC0.map (w' := w') (N' := N') φ hφ hρ y =
    TailC0.map (w' := w') (N' := N') φ hφ hρ (x - y) from (map_sub _ _ _).symm]
  rw [TailC0.norm_def, TailC0.norm_def]
  refine ciSup_le fun μ => ?_
  refine le_trans (hφ _) ?_
  exact TailC0.norm_coeff_le _ μ

end Map

/-! ### The tail convolution formula ([WP] eq:tail-multiplication, full form) -/

section TailConv

variable {K w N}

theorem tailCoeff_neg (μ : TailIdx N) (f : WPA K w) :
    tailCoeff K w N μ (-f) = -tailCoeff K w N μ f := by
  have h := (tailCoeff_add K w N μ f (-f)).symm
  rw [add_neg_cancel, tailCoeff_zero_map] at h
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm] at h)

theorem tailCoeff_sub (μ : TailIdx N) (f g : WPA K w) :
    tailCoeff K w N μ (f - g) = tailCoeff K w N μ f - tailCoeff K w N μ g := by
  rw [sub_eq_add_neg, tailCoeff_add, tailCoeff_neg, sub_eq_add_neg]

/-- Finite tail truncation: the partial sum of the isometric decomposition
`𝒜 ≅ ⊕̂ 𝒜_N e_μ` over a finite set of tail indices. -/
noncomputable def tailTrunc (S : Finset (TailIdx N)) (f : WPA K w) : WPA K w :=
  ∑ μ ∈ S, headIncl K w N (tailCoeff K w N μ f) * eTail K w N μ

open scoped Classical in
theorem tailCoeff_tailTrunc (S : Finset (TailIdx N)) (f : WPA K w) (ν : TailIdx N) :
    tailCoeff K w N ν (tailTrunc S f) =
      if ν ∈ S then tailCoeff K w N ν f else 0 := by
  classical
  unfold tailTrunc
  induction S using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, tailCoeff_zero_map, if_neg (Finset.notMem_empty ν)]
  | insert μ S hμS ih =>
    rw [Finset.sum_insert hμS, tailCoeff_add, ih, tailCoeff_headIncl_mul_eTail]
    by_cases hν : ν = μ
    · subst hν
      rw [if_pos rfl, if_neg hμS, add_zero, if_pos (Finset.mem_insert_self ν S)]
    · rw [if_neg hν, zero_add]
      by_cases hνS : ν ∈ S
      · rw [if_pos hνS, if_pos (Finset.mem_insert_of_mem hνS)]
      · rw [if_neg hνS, if_neg (by
          intro hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact hν h
          · exact hνS h)]

theorem norm_sub_tailTrunc_le (S : Finset (TailIdx N)) (f : WPA K w) {ε : ℝ}
    (hε : 0 ≤ ε) (hS : ∀ ν ∉ S, ‖tailCoeff K w N ν f‖ ≤ ε) :
    ‖f - tailTrunc S f‖ ≤ ε := by
  classical
  rw [norm_eq_iSup_tailCoeff]
  refine ciSup_le fun ν => ?_
  rw [tailCoeff_sub, tailCoeff_tailTrunc]
  by_cases hν : ν ∈ S
  · rw [if_pos hν, sub_self, norm_zero]
    exact hε
  · rw [if_neg hν, sub_zero]
    exact hS ν hν

theorem exists_tailTrunc_close (f : WPA K w) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (TailIdx N), ‖f - tailTrunc S f‖ ≤ ε := by
  classical
  have h := tendsto_norm_tailCoeff_cofinite K w N f
  rw [Metric.tendsto_nhds] at h
  have h1 := h ε hε
  rw [Filter.eventually_cofinite] at h1
  refine ⟨h1.toFinset, norm_sub_tailTrunc_le _ f hε.le fun ν hν => ?_⟩
  by_contra hgt
  push_neg at hgt
  refine hν ?_
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Real.dist_eq, sub_zero,
    abs_of_nonneg (norm_nonneg _), not_lt]
  exact hgt.le

theorem norm_tailTrunc_le (S : Finset (TailIdx N)) (f : WPA K w) :
    ‖tailTrunc S f‖ ≤ ‖f‖ := by
  classical
  rw [norm_eq_iSup_tailCoeff]
  refine ciSup_le fun ν => ?_
  rw [tailCoeff_tailTrunc]
  by_cases hν : ν ∈ S
  · rw [if_pos hν]
    exact norm_tailCoeff_le K w N ν f
  · rw [if_neg hν, norm_zero]
    exact norm_nonneg f

end TailConv

/-! ### The head graph model `QHead` -/

variable {K w N} in
/-- A chosen enumeration of the entries of a head rational datum. -/
noncomputable def datumEnum (DH : RationalLocData (WPHead K w N)) :
    Fin DH.T.card ≃ ↥DH.T :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe DH.T)).symm

variable {K w N} in
/-- The graph relations `s·T_i − t_i` of a head datum in `𝒜_N⟨T_1,…,T_m⟩`
([WP] eq:graph-ideal-definition). -/
noncomputable def headGraphRel (DH : RationalLocData (WPHead K w N)) :
    Fin DH.T.card → P (WPHead K w N) DH.T.card := fun i =>
  polyToP (MvPolynomial.C DH.s * MvPolynomial.X i -
    MvPolynomial.C ((datumEnum DH i : ↥DH.T) : WPHead K w N))

variable {K w N} in
/-- The graph ideal of a head datum, taken CLOSED: the topological closure of the
span of the graph relations.  Under strong noetherianity of the head
([WP] lem:koszul, via `hK₀`) the span is already closed and the closure collapses
(`FiniteJet.GraphKoszul.isClosed_graphIdeal` + `Ideal.closure_eq_of_isClosed`);
quotienting by the closure keeps the quotient norm a genuine norm without carrying
`hK₀` in the instance layer. -/
noncomputable def headGraphIdeal (DH : RationalLocData (WPHead K w N)) :
    Ideal (P (WPHead K w N) DH.T.card) :=
  (Ideal.span (Set.range (headGraphRel DH))).closure

variable {K w N} in
/-- The head graph-model quotient `Q = 𝒜_N⟨T⟩/(sT_i − t_i)` ([WP] eq:graph-model;
the ideal is closed by [WP] lem:koszul at the strongly noetherian head — the
`headGraphIdeal` closure is cosmetic there). -/
noncomputable def QHead (DH : RationalLocData (WPHead K w N)) : Type _ :=
  P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH

variable {K w N} in
noncomputable instance instCommRingQHead {DH : RationalLocData (WPHead K w N)} :
    CommRing (QHead DH) :=
  inferInstanceAs (CommRing (P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH))

variable {K w N} in
theorem isClosed_headGraphIdeal (DH : RationalLocData (WPHead K w N)) :
    IsClosed ((headGraphIdeal DH : Ideal (P (WPHead K w N) DH.T.card)) :
      Set (P (WPHead K w N) DH.T.card)) :=
  isClosed_closure

variable {K w N} in
/-- The quotient norm makes `QHead` a normed ring (the graph ideal is closed:
[WP] lem:koszul clause 3 / `FiniteJet.GraphKoszul.isClosed_graphIdeal`). -/
noncomputable instance instNormedCommRingQHead {DH : RationalLocData (WPHead K w N)} :
    NormedCommRing (QHead DH) :=
  haveI : IsClosed ((headGraphIdeal DH : Ideal (P (WPHead K w N) DH.T.card)) :
      Set (P (WPHead K w N) DH.T.card)) := isClosed_headGraphIdeal DH
  inferInstanceAs
    (NormedCommRing (P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH))

variable {K w N} in
instance instUltraQHead {DH : RationalLocData (WPHead K w N)} :
    IsUltrametricDist (QHead DH) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    fun x y => ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, han⟩ := Ideal.Quotient.norm_mk_lt x hε
  obtain ⟨b, hb, hbn⟩ := Ideal.Quotient.norm_mk_lt y hε
  have hxy : x + y = Ideal.Quotient.mk (headGraphIdeal DH) (a + b) := by
    rw [map_add, ha, hb]
    rfl
  rw [hxy]
  refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
  refine le_trans (IsUltrametricDist.norm_add_le_max a b) ?_
  calc max ‖a‖ ‖b‖ ≤ max (‖x‖ + ε) (‖y‖ + ε) := max_le_max han.le hbn.le
    _ = max ‖x‖ ‖y‖ + ε := max_add_add_right _ _ _

variable {K w N} in
instance instCompleteQHead {DH : RationalLocData (WPHead K w N)} :
    CompleteSpace (QHead DH) :=
  QuotientAddGroup.completeSpace_left (P (WPHead K w N) DH.T.card)
    (headGraphIdeal DH).toAddSubgroup

variable {K w N} in
/-- The constant embedding of the head into its Tate algebra sends `C x` to the
constant series (the W8 `hCP` fact, packaged). -/
theorem polyToP_C_val (x : WPHead K w N) {m : ℕ} :
    ((polyToP (MvPolynomial.C x) : P (WPHead K w N) m)).1 =
      MvPowerSeries.C x := by
  classical
  refine MvPowerSeries.ext fun t => ?_
  rw [coeff_polyToP, MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
  rcases eq_or_ne t 0 with rfl | ht
  · rfl
  · rw [if_neg (fun h => ht h.symm), if_neg ht]

variable {K w N} in
/-- The norm of `W` in the head is `1`. -/
theorem norm_WaHead : ‖WaHead K w N‖ = 1 := by
  rw [← norm_headIncl K w N (WaHead K w N), headIncl_WaHead]
  show ‖wpMonomial K w (wpMem_single_zero w 1) 1‖ = 1
  rw [norm_wpMonomial, norm_one]

variable {K w N} in
/-- The twist element of the head model: the image of `W` (norm `≤ 1` since the
quotient map is norm-nonincreasing). -/
noncomputable def rhoQ (DH : RationalLocData (WPHead K w N)) : TwistElem (QHead DH) where
  val := Ideal.Quotient.mk (headGraphIdeal DH)
    (polyToP (MvPolynomial.C (WaHead K w N)))
  norm_le_one := by
    classical
    refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
    rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun t => ?_) zero_le_one
    rw [FiniteJet.finsupp_prod_one, mul_one, polyToP_C_val, MvPowerSeries.coeff_C]
    split_ifs
    · rw [norm_WaHead]
    · rw [norm_zero]
      exact zero_le_one

variable {K w N} in
/-- The constant map into the head graph model. -/
noncomputable def headConst (DH : RationalLocData (WPHead K w N)) :
    WPHead K w N →+* QHead DH :=
  (Ideal.Quotient.mk (headGraphIdeal DH)).comp
    ((polyToP (E := WPHead K w N) (m := DH.T.card)).comp
      (MvPolynomial.C : WPHead K w N →+* MvPolynomial (Fin DH.T.card) (WPHead K w N)))

variable {K w N} in
theorem norm_headConst_le (DH : RationalLocData (WPHead K w N)) (x : WPHead K w N) :
    ‖headConst DH x‖ ≤ ‖x‖ := by
  classical
  show ‖(Ideal.Quotient.mk (headGraphIdeal DH) (polyToP (MvPolynomial.C x)) :
    QHead DH)‖ ≤ ‖x‖
  refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun t => ?_) (norm_nonneg x)
  rw [FiniteJet.finsupp_prod_one, mul_one, polyToP_C_val, MvPowerSeries.coeff_C]
  split_ifs
  · exact le_refl _
  · rw [norm_zero]
    exact norm_nonneg x

variable {K w N} in
theorem headConst_continuous (DH : RationalLocData (WPHead K w N)) :
    Continuous (headConst DH) :=
  AddMonoidHomClass.continuous_of_bound (headConst DH) 1 fun x => by
    rw [one_mul]
    exact norm_headConst_le DH x

variable {K w N} in
/-- The image of the `i`-th Tate variable in the head graph model. -/
noncomputable def qX (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    QHead DH :=
  Ideal.Quotient.mk (headGraphIdeal DH) (polyToP (MvPolynomial.X i))

variable {K w N} in
/-- The defining relation of the graph model: `headConst t = headConst s · mk(X i)`
for the `i`-th entry. -/
theorem headConst_datumEnum (DH : RationalLocData (WPHead K w N))
    (i : Fin DH.T.card) :
    headConst DH ((datumEnum DH i : ↥DH.T) : WPHead K w N) =
      headConst DH DH.s * qX DH i := by
  have hrel : Ideal.Quotient.mk (headGraphIdeal DH) (headGraphRel DH i) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    show headGraphRel DH i ∈ headGraphIdeal DH
    rw [headGraphIdeal, ← SetLike.mem_coe, Ideal.coe_closure]
    exact subset_closure (Ideal.subset_span ⟨i, rfl⟩)
  rw [headGraphRel, map_sub, map_sub, sub_eq_zero] at hrel
  rw [show headConst DH ((datumEnum DH i : ↥DH.T) : WPHead K w N) =
    Ideal.Quotient.mk (headGraphIdeal DH)
      (polyToP (MvPolynomial.C ((datumEnum DH i : ↥DH.T) : WPHead K w N))) from rfl]
  rw [← hrel, map_mul, map_mul]
  rfl

variable {K w N} in
/-- `s` is a unit in the head graph model ([WP] lem:koszul's Bezout trick:
`t^ℓ = s·(∑ a_i T_i)` mod the graph ideal, and `t` is a unit). -/
theorem isUnit_headConst_s (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    IsUnit (headConst DH DH.s) := by
  classical
  obtain ⟨ℓ, a, ha1, hbez⟩ := exists_integral_bezout' (piHead ϖ) (isUnit_piHead ϖ)
    (norm_piHead_lt_one ϖ) (norm_piHead_pos ϖ) (norm_piHead_mul ϖ) DH hDH
  have hmap : headConst DH (piHead ϖ) ^ ℓ =
      headConst DH DH.s * ∑ i : Fin DH.T.card,
        headConst DH (a ((datumEnum DH i : ↥DH.T) : WPHead K w N)) * qX DH i := by
    rw [← map_pow, ← hbez, map_sum]
    rw [← Finset.sum_coe_sort DH.T
      (fun x => headConst DH (a x * x))]
    rw [← Equiv.sum_comp (datumEnum DH)
      (fun y : ↥DH.T => headConst DH (a (y : WPHead K w N) * (y : WPHead K w N)))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, headConst_datumEnum]
    ring
  have htu : IsUnit (headConst DH (piHead ϖ) ^ ℓ) :=
    ((isUnit_piHead ϖ).map (headConst DH)).pow ℓ
  rw [hmap] at htu
  exact isUnit_of_mul_isUnit_left htu

variable {K w N} in
/-- The Gauss norm of a Tate variable in the head model is at most `1`. -/
theorem norm_qX_le_one (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    ‖qX DH i‖ ≤ 1 := by
  classical
  refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun t => ?_) zero_le_one
  rw [FiniteJet.finsupp_prod_one, mul_one, coeff_polyToP, MvPolynomial.coeff_X']
  split_ifs
  · exact le_of_eq norm_one
  · rw [norm_zero]
    exact zero_le_one

variable {K w N} in
/-- The algebraic forward map of the head bridge: `IsLocalization.Away.lift` along
the graph-model Bezout unit. -/
noncomputable def headLocFwdAlg (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Localization.Away DH.s →+* QHead DH :=
  IsLocalization.Away.lift DH.s (isUnit_headConst_s ϖ DH hDH)

variable {K w N} in
theorem headLocFwdAlg_algebraMap (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (x : WPHead K w N) :
    headLocFwdAlg ϖ DH hDH (algebraMap (WPHead K w N) (Localization.Away DH.s) x) =
      headConst DH x :=
  IsLocalization.Away.lift_eq _ _ x

variable {K w N} in
/-- The forward map sends `t/s` to the corresponding Tate variable. -/
theorem headLocFwdAlg_divByS (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    {t : WPHead K w N} (ht : t ∈ DH.T) :
    headLocFwdAlg ϖ DH hDH (divByS t DH.s) =
      qX DH ((datumEnum DH).symm ⟨t, ht⟩) := by
  have hu := isUnit_headConst_s ϖ DH hDH
  refine hu.mul_right_cancel ?_
  have hspec : headLocFwdAlg ϖ DH hDH (divByS t DH.s) * headConst DH DH.s =
      headConst DH t := by
    have h1 : divByS t DH.s *
        algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s =
        algebraMap (WPHead K w N) (Localization.Away DH.s) t := by
      rw [divByS]
      exact IsLocalization.mk'_spec _ _ _
    calc headLocFwdAlg ϖ DH hDH (divByS t DH.s) * headConst DH DH.s
        = headLocFwdAlg ϖ DH hDH (divByS t DH.s) *
            headLocFwdAlg ϖ DH hDH
              (algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s) := by
          rw [headLocFwdAlg_algebraMap]
      _ = headLocFwdAlg ϖ DH hDH (divByS t DH.s *
            algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s) :=
          (map_mul _ _ _).symm
      _ = headLocFwdAlg ϖ DH hDH
            (algebraMap (WPHead K w N) (Localization.Away DH.s) t) := by rw [h1]
      _ = headConst DH t := headLocFwdAlg_algebraMap ϖ DH hDH t
  rw [hspec]
  have henum : ((datumEnum DH ((datumEnum DH).symm ⟨t, ht⟩) : ↥DH.T) :
      WPHead K w N) = t := by
    rw [Equiv.apply_symm_apply]
  calc headConst DH t
      = headConst DH ((datumEnum DH ((datumEnum DH).symm ⟨t, ht⟩) : ↥DH.T) :
          WPHead K w N) := by rw [henum]
    _ = headConst DH DH.s * qX DH ((datumEnum DH).symm ⟨t, ht⟩) :=
        headConst_datumEnum DH _
    _ = qX DH ((datumEnum DH).symm ⟨t, ht⟩) * headConst DH DH.s := mul_comm _ _

variable {K w N} in
theorem headLocFwdAlg_continuous (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    @Continuous _ _ DH.topology _ (headLocFwdAlg ϖ DH hDH) := by
  refine locTopology_continuous_lift DH.P DH.T DH.s DH.hopen _ ?_ ?_
  · have h_eq : (headLocFwdAlg ϖ DH hDH).comp
        (algebraMap (WPHead K w N) (Localization.Away DH.s)) = headConst DH :=
      RingHom.ext fun x => headLocFwdAlg_algebraMap ϖ DH hDH x
    rw [show ⇑((headLocFwdAlg ϖ DH hDH).comp
        (algebraMap (WPHead K w N) (Localization.Away DH.s))) = ⇑(headConst DH)
      from congrArg _ h_eq]
    exact headConst_continuous DH
  · intro t ht
    rw [headLocFwdAlg_divByS ϖ DH hDH ht]
    exact FiniteJet.isPowerBounded_of_norm_le_one (norm_qX_le_one DH _)

variable {K w N} in
/-- The evaluation targets of the reverse bridge: the `T/s`-fractions in the
completed localization. -/
noncomputable def revB (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    presheafValue DH :=
  DH.coeRingHom (divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s)

variable {K w N} in
theorem isPowerBounded_revB (DH : RationalLocData (WPHead K w N))
    (i : Fin DH.T.card) : TopologicalRing.IsPowerBounded (revB DH i) := by
  have hmem : divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s ∈
      locSubring DH.P DH.T DH.s :=
    divByS_mem_locSubring _ _ _ (datumEnum DH i).2
  refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded DH).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s ^ n,
    pow_mem hmem n, ?_⟩
  rw [map_pow]
  rfl

variable {K w N} in
/-- The reverse bridge at the Tate-algebra level: `restrictedEval` at the
`T/s`-fractions (the `chartEval` pattern, done generically by `WP/Evaluation`). -/
noncomputable def headLocRevP (DH : RationalLocData (WPHead K w N)) :
    P (WPHead K w N) DH.T.card →+* presheafValue DH :=
  restrictedEval DH.canonicalMap (canonicalMap_continuous DH) (revB DH)
    (fun i => isPowerBounded_revB DH i)

variable {K w N} in
theorem headLocRevP_continuous (DH : RationalLocData (WPHead K w N)) :
    Continuous (headLocRevP DH) :=
  restrictedEval_continuous DH.canonicalMap (canonicalMap_continuous DH) (revB DH)
    (fun i => isPowerBounded_revB DH i)

variable {K w N} in
theorem headLocRevP_C (DH : RationalLocData (WPHead K w N)) (x : WPHead K w N) :
    headLocRevP DH (polyToP (MvPolynomial.C x)) = DH.canonicalMap x := by
  unfold headLocRevP
  exact restrictedEval_C _ _ _ _ x

variable {K w N} in
theorem headLocRevP_X (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    headLocRevP DH (polyToP (MvPolynomial.X i)) = revB DH i := by
  unfold headLocRevP
  exact restrictedEval_X _ _ _ _ i

variable {K w N} in
/-- The graph relations die in the completed localization: `s·(t/s) = t`. -/
theorem headLocRevP_graphRel (DH : RationalLocData (WPHead K w N))
    (i : Fin DH.T.card) : headLocRevP DH (headGraphRel DH i) = 0 := by
  have hsplit : headGraphRel DH i =
      polyToP (MvPolynomial.C DH.s) * polyToP (MvPolynomial.X i) -
        polyToP (MvPolynomial.C ((datumEnum DH i : ↥DH.T) : WPHead K w N)) := by
    rw [headGraphRel, map_sub, map_mul]
  rw [hsplit, map_sub, map_mul, headLocRevP_C, headLocRevP_X, headLocRevP_C]
  have hloc : algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s *
      divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s =
      algebraMap (WPHead K w N) (Localization.Away DH.s)
        ((datumEnum DH i : ↥DH.T) : WPHead K w N) := by
    rw [mul_comm, divByS]
    exact IsLocalization.mk'_spec _ _ _
  have hprod : DH.canonicalMap DH.s * revB DH i =
      DH.coeRingHom (algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s *
        divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s) := by
    rw [map_mul]
    rfl
  rw [hprod, hloc]
  have hcan : DH.coeRingHom (algebraMap (WPHead K w N) (Localization.Away DH.s)
      ((datumEnum DH i : ↥DH.T) : WPHead K w N)) =
      DH.canonicalMap ((datumEnum DH i : ↥DH.T) : WPHead K w N) := rfl
  rw [hcan]
  exact sub_self _

variable {K w N} in
theorem headGraphIdeal_le_ker (DH : RationalLocData (WPHead K w N)) :
    headGraphIdeal DH ≤ RingHom.ker (headLocRevP DH) := by
  have hker_closed : IsClosed ((RingHom.ker (headLocRevP DH) :
      Ideal (P (WPHead K w N) DH.T.card)) : Set (P (WPHead K w N) DH.T.card)) := by
    have hset : ((RingHom.ker (headLocRevP DH) :
        Ideal (P (WPHead K w N) DH.T.card)) : Set (P (WPHead K w N) DH.T.card)) =
        headLocRevP DH ⁻¹' {0} := by
      ext y
      simp [RingHom.mem_ker]
    rw [hset]
    exact IsClosed.preimage (headLocRevP_continuous DH) isClosed_singleton
  have hspan : (Ideal.span (Set.range (headGraphRel DH)) :
      Set (P (WPHead K w N) DH.T.card)) ⊆
      ((RingHom.ker (headLocRevP DH) : Ideal _) : Set _) := by
    have h1 : Ideal.span (Set.range (headGraphRel DH)) ≤
        RingHom.ker (headLocRevP DH) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (headLocRevP_graphRel DH i)
    exact fun x hx => h1 hx
  intro x hx
  have hx' : x ∈ closure ((Ideal.span (Set.range (headGraphRel DH)) : Ideal _) :
      Set (P (WPHead K w N) DH.T.card)) := by
    rw [← Ideal.coe_closure]
    exact hx
  exact closure_minimal hspan hker_closed hx'

variable {K w N} in
/-- The reverse bridge, descended to the graph model. -/
noncomputable def headLocRev (DH : RationalLocData (WPHead K w N)) :
    QHead DH →+* presheafValue DH :=
  Ideal.Quotient.lift (headGraphIdeal DH) (headLocRevP DH)
    (fun a ha => RingHom.mem_ker.mp (headGraphIdeal_le_ker DH ha))

variable {K w N} in
theorem headLocRev_mk (DH : RationalLocData (WPHead K w N))
    (G : P (WPHead K w N) DH.T.card) :
    headLocRev DH (Ideal.Quotient.mk (headGraphIdeal DH) G) = headLocRevP DH G :=
  Ideal.Quotient.lift_mk _ _ _

variable {K w N} in
theorem headLocRev_continuous (DH : RationalLocData (WPHead K w N)) :
    Continuous (headLocRev DH) := by
  refine continuous_of_continuousAt_zero (headLocRev DH).toAddMonoidHom ?_
  show Filter.Tendsto _ (nhds 0) (nhds _)
  rw [show (headLocRev DH).toAddMonoidHom (0 : QHead DH) = 0 from map_zero _]
  refine Filter.tendsto_def.mpr fun U hU => ?_
  have hrevP := (headLocRevP_continuous DH).tendsto 0
  rw [show headLocRevP DH 0 = 0 from map_zero _] at hrevP
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp (hrevP hU)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ0) fun q hq => ?_
  rw [Set.mem_preimage]
  rw [Metric.mem_ball, dist_zero_right] at hq
  obtain ⟨G, hG, hGn⟩ := Ideal.Quotient.norm_mk_lt q
    (show (0 : ℝ) < δ - ‖q‖ by linarith)
  have hq' : headLocRev DH q = headLocRevP DH G := by
    rw [← hG, headLocRev_mk]
  show headLocRev DH q ∈ U
  rw [hq']
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖G‖ < ‖q‖ + (δ - ‖q‖) := hGn
    _ = δ := by rw [add_sub_cancel]

/-! ### The head bridge `presheafValue ≃ QHead` -/

variable {K w N} in
/-- The forward bridge on the completion. -/
noncomputable def headLocFwd (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue DH →+* QHead DH := by
  letI := DH.uniformSpace
  letI : IsTopologicalRing (Localization.Away DH.s) := DH.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away DH.s) := DH.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (headLocFwdAlg ϖ DH hDH)
    (headLocFwdAlg_continuous ϖ DH hDH)

variable {K w N} in
theorem headLocFwd_coe (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (a : Localization.Away DH.s) :
    headLocFwd ϖ DH hDH (DH.coeRingHom a) = headLocFwdAlg ϖ DH hDH a := by
  letI := DH.uniformSpace
  letI : IsTopologicalRing (Localization.Away DH.s) := DH.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away DH.s) := DH.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (headLocFwdAlg ϖ DH hDH)
    (headLocFwdAlg_continuous ϖ DH hDH) a

variable {K w N} in
theorem headLocFwd_continuous (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocFwd ϖ DH hDH) := by
  letI := DH.uniformSpace
  exact UniformSpace.Completion.continuous_extension

variable {K w N} in
theorem continuous_mk_headGraphIdeal (DH : RationalLocData (WPHead K w N)) :
    Continuous (Ideal.Quotient.mk (headGraphIdeal DH)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun a b => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact Ideal.Quotient.norm_mk_le _ _

variable {K w N} in
/-- The composite `rev ∘ fwdAlg` is the completion map (agreement on the
localization generators). -/
theorem headLocRev_comp_fwdAlg (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    (headLocRev DH).comp (headLocFwdAlg ϖ DH hDH) = DH.coeRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers DH.s) ?_
  ext x
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    headLocFwdAlg_algebraMap]
  rw [show headConst DH x =
    Ideal.Quotient.mk (headGraphIdeal DH) (polyToP (MvPolynomial.C x)) from rfl]
  rw [headLocRev_mk, headLocRevP_C]
  rfl

variable {K w N} in
theorem headLocRev_headLocFwd (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (x : presheafValue DH) :
    headLocRev DH (headLocFwd ϖ DH hDH x) = x := by
  letI := DH.uniformSpace
  have hdense : DenseRange (⇑DH.coeRingHom) :=
    @UniformSpace.Completion.denseRange_coe _ DH.uniformSpace
  have hfun : ⇑(headLocRev DH) ∘ ⇑(headLocFwd ϖ DH hDH) =
      (id : presheafValue DH → presheafValue DH) := by
    refine hdense.equalizer
      ((headLocRev_continuous DH).comp (headLocFwd_continuous ϖ DH hDH))
      continuous_id ?_
    funext l
    show headLocRev DH (headLocFwd ϖ DH hDH (DH.coeRingHom l)) = DH.coeRingHom l
    rw [headLocFwd_coe]
    exact RingHom.congr_fun (headLocRev_comp_fwdAlg ϖ DH hDH) l
  exact congrFun hfun x

variable {K w N} in
/-- The forward bridge sends the `T/s`-fraction to the corresponding variable. -/
theorem headLocFwd_revB (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (i : Fin DH.T.card) :
    headLocFwd ϖ DH hDH (revB DH i) = qX DH i := by
  rw [revB, headLocFwd_coe, headLocFwdAlg_divByS ϖ DH hDH (datumEnum DH i).2]
  congr 1
  rw [show (⟨((datumEnum DH i : ↥DH.T) : WPHead K w N), (datumEnum DH i).2⟩ :
    ↥DH.T) = datumEnum DH i from Subtype.coe_eta _ _]
  exact Equiv.symm_apply_apply _ _

variable {K w N} in
theorem headLocFwd_headLocRev (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (q : QHead DH) :
    headLocFwd ϖ DH hDH (headLocRev DH q) = q := by
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective (I := headGraphIdeal DH) q
  rw [headLocRev_mk]
  have hpoly : ∀ Q : MvPolynomial (Fin DH.T.card) (WPHead K w N),
      headLocFwd ϖ DH hDH (headLocRevP DH (polyToP Q)) =
        Ideal.Quotient.mk (headGraphIdeal DH) (polyToP Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x =>
      rw [headLocRevP_C,
        show DH.canonicalMap x = DH.coeRingHom
          (algebraMap (WPHead K w N) (Localization.Away DH.s) x) from rfl,
        headLocFwd_coe, headLocFwdAlg_algebraMap]
      rfl
    | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, hp, hq]
      rfl
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, map_mul, hp, headLocRevP_X,
        headLocFwd_revB]
      rfl
  have h1 : ⇑((headLocFwd ϖ DH hDH).comp (headLocRevP DH)) =
      ⇑(Ideal.Quotient.mk (headGraphIdeal DH)) := by
    refine denseRange_polyToP.equalizer
      ((headLocFwd_continuous ϖ DH hDH).comp (headLocRevP_continuous DH))
      (continuous_mk_headGraphIdeal DH) ?_
    funext Q
    exact hpoly Q
  exact congrFun h1 G

variable {K w N} in
/-- **The head graph-model bridge**: the completed rational localization of the
strongly noetherian head is its graph quotient ([WP] eq:graph-model
`E_α ≅ P_E/J̄_{E,α}`; forward via `IsLocalization.Away.lift` — `s` is a unit in the
quotient by the Bezout trick of [WP] lem:koszul's proof — and back via the evaluation
gadget `restrictedEval` at the power-bounded tuple `T_i ↦ t_i/s`). -/
noncomputable def headLocEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue DH ≃+* QHead DH :=
  { toFun := headLocFwd ϖ DH hDH
    invFun := headLocRev DH
    left_inv := headLocRev_headLocFwd ϖ DH hDH
    right_inv := headLocFwd_headLocRev ϖ DH hDH
    map_mul' := map_mul _
    map_add' := map_add _ }

variable {K w N} in
theorem headLocEquiv_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocEquiv ϖ hK₀ DH hDH) :=
  headLocFwd_continuous ϖ DH hDH

variable {K w N} in
theorem headLocEquiv_symm_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocEquiv ϖ hK₀ DH hDH).symm :=
  headLocRev_continuous DH

/-! ### The lifted datum and the coefficientwise model over `𝒜` -/

/-- The unit-ball pair of definition of `𝒜`, at a norm-window constant of `K`
(`exists_norm_window'` — unconditional for a nontrivially normed field). -/
noncomputable def wpaPod : PairOfDefinition (WPA K w) :=
  FiniteJet.unitBallPod (constA K w (Classical.choose (exists_norm_window' K)))
    ((Classical.choose_spec (exists_norm_window' K)).1.map (constA K w))
    (by rw [norm_constA]
        exact (Classical.choose_spec (exists_norm_window' K)).2.1)
    (by rw [norm_constA]
        exact (Classical.choose_spec (exists_norm_window' K)).2.2)
    (fun x => by
      rw [norm_constA]
      exact norm_constA_mul K w (Classical.choose (exists_norm_window' K)) x)

variable {K w N} in
open scoped Classical in
/-- Rationality lifts along `headIncl`: the unit ideal is generated by the lifted
entries. -/
theorem span_image_headIncl_eq_top (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) :
    Ideal.span ((DH.T.image (headIncl K w N) : Finset (WPA K w)) : Set (WPA K w)) =
      ⊤ := by
  classical
  have hspan := hDH.span_eq_top
  rw [Finset.coe_image, ← Ideal.map_span (headIncl K w N), hspan, Ideal.map_top]

variable {K w N} in
open scoped Classical in
/-- The lift of a head rational datum to `𝒜` (entries via `headIncl`, unit-ball pair
of definition; [WP] §6.4: the datum "lies in the finite head").  (2026-07-29: the
rationality hypothesis was added to the signature — the lifted `hopen` field is the
span-openness of the lifted entries, which needs `DH` rational; [WP]'s corollary
only ever lifts rational data.) -/
noncomputable def liftDatum (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : RationalLocData (WPA K w) :=
  genPieceDatum (wpaPod K w) (DH.T.image (headIncl K w N)) (headIncl K w N DH.s)
    (span_image_headIncl_eq_top DH hDH)

variable {K w N} in
open scoped Classical in
theorem liftDatum_T (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    (liftDatum DH hDH).T = DH.T.image (headIncl K w N) := rfl

variable {K w N} in
theorem liftDatum_s (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    (liftDatum DH hDH).s = headIncl K w N DH.s := rfl

variable {K w N} in
theorem liftDatum_isRational (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : (liftDatum DH hDH).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_headIncl_eq_top DH hDH)

variable {K w N} in
/-- **Coefficientwise localization** ([WP] prop:coefficientwise-localization:
"There is a canonical topological algebra isomorphism `𝒜_α ≅ ⊕̂^{c₀}_μ P e_μ`").
The proof route: the graph ideal over `𝒜` is closed and computed coefficientwise via
the norm-bounded head lifts (`exists_d1_lift_pow`); the quotient is `TailC0`;
forward/backward maps by `IsLocalization.Away.lift` + `restrictedEval`. -/
noncomputable def coeffLocEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue (liftDatum DH hDH) ≃+* TailC0 w N (QHead DH) (rhoQ DH) := by
  sorry

variable {K w N} in
theorem coeffLocEquiv_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (coeffLocEquiv ϖ hK₀ DH hDH) := by sorry

variable {K w N} in
theorem coeffLocEquiv_symm_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (coeffLocEquiv ϖ hK₀ DH hDH).symm := by sorry

variable {K w N} in
/-- Compatibility of the two bridges on canonical images of head elements: the
`𝒜`-model of `ρ(headIncl x)` is the `μ = 0` family at the head model of `ρ(x)`. -/
theorem coeffLocEquiv_canonicalMap_headIncl (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (x : WPHead K w N) :
    coeffLocEquiv ϖ hK₀ DH hDH
      ((liftDatum DH hDH).canonicalMap (headIncl K w N x)) =
      TailC0.ofHead (headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x)) := by sorry

/-! ### Every rational localization of `𝒜` is of finite-head form
([WP] cor:finite-head-presentation) -/

variable {K w} in
/-- A finite-head model of a rational localization of `𝒜`
([WP] cor:finite-head-presentation / eq:arbitrary-finite-head-presentation). -/
structure HeadModelData (D : RationalLocData (WPA K w)) : Type _ where
  /-- The head stage. -/
  N : ℕ
  /-- The head datum. -/
  DH : RationalLocData (WPHead K w N)
  /-- The head datum is rational. -/
  hDH : DH.IsRational
  /-- The lifted datum cuts the same rational subset as `D`. -/
  hopen : rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s =
    rationalOpen D.T D.s
  /-- The model isomorphism. -/
  e : presheafValue D ≃+* TailC0 w N (QHead DH) (rhoQ DH)
  /-- Forward continuity. -/
  he : Continuous e
  /-- Backward continuity. -/
  he' : Continuous e.symm

variable {K w} in
/-- **Finite-head presentation of every rational localization**
([WP] cor:finite-head-presentation: perturb the datum into a head via density of the
heads and lem:small-perturbation; the retracted Bezout relation makes the perturbed
datum rational in the head; conclude by prop:coefficientwise-localization). -/
theorem nonempty_headModelData (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (D : RationalLocData (WPA K w)) (hD : D.IsRational) :
    Nonempty (HeadModelData D) := by sorry

end WeightedParity
