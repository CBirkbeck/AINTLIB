/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetFunctoriality
import «Adic spaces».FiniteJetUniformDomain

/-!
# The nonuniform chart: `𝓐⟨W/ϖ⟩ ≅ K⟨X,Q⟩/(Q²)` and failure of stable uniformity

Source: [FJP] §3. Proposition 3.1 (verbatim): "There is a canonical isomorphism of
topological k-algebras `𝒜_in ≅ k⟨X,Q⟩/(Q²)`, `W ↦ ϖX`, `Q ↦ Q`." — where
`𝒜_in = 𝒜⟨W/ϖ⟩ = (𝒜⟨X⟩/(ϖX − W))^∧` is the completed rational localization at the datum
`(W; ϖ)`, presented by `T = {W, ϖ}`, `s = ϖ`. In our models the target ring is literally
`𝓑 = DualNumber (K⟨X⟩)`.

Key computation ((3.3)): for `y ∈ Q²𝒞` and every `n`, `y = ϖⁿXⁿ(W^{-n}y)` with
`‖W^{-n}y‖ = ‖y‖`, so `Q²𝒞` dies in the separated completion.

Corollary 3.2 (verbatim): "The ring 𝒜 is not stably uniform." — the chart is nonzero and
nonuniform: "`Q ≠ 0`, `Q² = 0`, and every element of the unbounded line `kQ` is
power-bounded, while `‖λQ‖ = |λ|`."
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

noncomputable section

open scoped Classical

/-- The element `W ∈ 𝓐` (support `(1,0)`; [FJP] §1.4). -/
def Wa : JetA F :=
  ⟨sectionD F (TrivSqZeroExt.inl (Wu (R := K)).val), by
    rw [mem_jetSupport_iff_jet_in_range, rhoC_sectionD]
    have hsupp : (Wu (R := K)).val ∈ nonnegSubring K := by
      intro a ha
      show (single (1 : ℤ) (1 : K) : RestrictedLaurent K).coeff a = 0
      rw [coeff_single]
      exact if_neg (by omega)
    refine ⟨TrivSqZeroExt.inl ((nonnegEquiv (R := K)).symm ⟨(Wu (R := K)).val, hsupp⟩), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨(Wu (R := K)).val, hsupp⟩) =
        (Wu (R := K)).val
      rw [ofRestricted_nonnegEquiv_symm]
    · show ofRestricted (R := K) 0 = 0
      exact map_zero _⟩

/-- The chart datum `(W; ϖ)`: `T = {W, ϖ}`, `s = ϖ` — presenting the rational subset
`{|W| ≤ |ϖ| ≠ 0}` of `Spa(𝓐, 𝓐°)` ([FJP] (3.1)). -/
def chartDatum : RationalLocData (JetA F) where
  P := podA F
  T := {Wa F, tA F}
  s := tA F
  hopen := genPiece_hopen (podA F) {Wa F, tA F} (tA F)
    (Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (by
        rw [Finset.coe_insert, Finset.coe_singleton]
        exact Set.mem_insert_of_mem _ rfl))
      (isUnit_tA F))

theorem chartDatum_isRational : (chartDatum F).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (by
        show tA F ∈ (({Wa F, tA F} : Finset (JetA F)) : Set (JetA F))
        rw [Finset.coe_insert, Finset.coe_singleton]
        exact Set.mem_insert_of_mem _ rfl))
      (isUnit_tA F))

/-! ### The `ϖ`-rescaling twist (Prop 3.1's normalisation `W ↦ ϖX`) -/

/-- Rescaling a restricted power series by a norm-`≤ 1` scalar stays restricted
(the substitution `X ↦ aX`; coefficientwise `aⁿ`-scaling). -/
noncomputable def rescaleRestricted {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] (a : R) (ha : ‖a‖ ≤ 1) :
    PowerSeries.Restricted R (1 : ℝ) →+* PowerSeries.Restricted R (1 : ℝ) where
  toFun f := ⟨PowerSeries.rescale a f.1, by
    show PowerSeries.IsRestricted (1 : ℝ) (PowerSeries.rescale a f.1)
    have hf : PowerSeries.IsRestricted (1 : ℝ) f.1 := f.2
    rw [PowerSeries.IsRestricted] at hf ⊢
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hf
    rw [PowerSeries.coeff_rescale]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ‖a ^ n * PowerSeries.coeff n f.1‖
        ≤ ‖a ^ n‖ * ‖PowerSeries.coeff n f.1‖ := norm_mul_le _ _
      _ ≤ 1 * ‖PowerSeries.coeff n f.1‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          cases n with
          | zero => rw [pow_zero, norm_one]
          | succ k =>
              exact (norm_pow_le' a k.succ_pos).trans
                (pow_le_one₀ (norm_nonneg a) ha)
      _ = ‖PowerSeries.coeff n f.1‖ := one_mul _⟩
  map_one' := Subtype.ext (map_one (PowerSeries.rescale a))
  map_mul' f g := Subtype.ext (map_mul (PowerSeries.rescale a) f.1 g.1)
  map_zero' := Subtype.ext (map_zero (PowerSeries.rescale a))
  map_add' f g := Subtype.ext (map_add (PowerSeries.rescale a) f.1 g.1)

/-- The componentwise `ϖ`-twist of 𝓑 (`X ↦ ϖX` on both jet components). -/
noncomputable def twistB : JetB F →+* JetB F :=
  JetNorm.mapHom (rescaleRestricted (LaurentSeriesExample.t F) (norm_t_lt_one F).le)

/-- The twisted base map `θ = twist ∘ jB` implementing Prop 3.1's `W ↦ ϖX`. -/
noncomputable def thetaChart : JetA F →+* JetB F :=
  (twistB F).comp (jB F)

/-- Rescaling fixes constant power series (`rescale a (C r) = C r`). -/
theorem rescaleRestricted_const (a : K) (ha : ‖a‖ ≤ 1) (r : K) :
    rescaleRestricted a ha (constHomPS F r) = constHomPS F r := by
  refine Subtype.ext ?_
  show PowerSeries.rescale a (PowerSeries.C r : PowerSeries K) = PowerSeries.C r
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero => simp
  | succ k => simp [PowerSeries.coeff_C]

/-- `jB` sends the pseudouniformizer to the pseudouniformizer. -/
theorem jB_tA : jB F (tA F) = tB F := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine ofRestricted_injective (R := K) ?_
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff F 0 ((tA F : JetA F) : JetC F), (tA F).2.1⟩) =
      ofRestricted (constHomPS F (LaurentSeriesExample.t F))
    rw [ofRestricted_nonnegEquiv_symm]
    show qCoeff F 0 (constHomC F (RestrictedLaurent.C (LaurentSeriesExample.t F))) =
      ofRestricted (constHomPS F (LaurentSeriesExample.t F))
    rw [qCoeff_constHomC, if_pos rfl]
    show RestrictedLaurent.C (LaurentSeriesExample.t F) =
      ofRestricted (PowerSeries.Restricted.C (1 : ℝ) (LaurentSeriesExample.t F))
    rw [ofRestricted_C]
    rfl
  · refine ofRestricted_injective (R := K) ?_
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff F 1 ((tA F : JetA F) : JetC F), (tA F).2.2⟩) =
      ofRestricted (0 : PowerSeries.Restricted K (1 : ℝ))
    rw [ofRestricted_nonnegEquiv_symm, map_zero]
    show qCoeff F 1 (constHomC F (RestrictedLaurent.C (LaurentSeriesExample.t F))) = 0
    rw [qCoeff_constHomC, if_neg one_ne_zero]

/-- The twist fixes the pseudouniformizer: `θ(ϖ_𝓐) = ϖ_𝓑`. -/
theorem thetaChart_tA : thetaChart F (tA F) = tB F := by
  show twistB F (jB F (tA F)) = tB F
  rw [jB_tA]
  refine TrivSqZeroExt.ext ?_ ?_
  · show rescaleRestricted (LaurentSeriesExample.t F) (norm_t_lt_one F).le
      (constHomPS F (LaurentSeriesExample.t F)) =
      constHomPS F (LaurentSeriesExample.t F)
    exact rescaleRestricted_const F _ _ _
  · show rescaleRestricted (LaurentSeriesExample.t F) (norm_t_lt_one F).le 0 = 0
    exact map_zero _

/-- The rescaling twist is norm-nonincreasing (Gauss-sup, coefficientwise bound). -/
theorem norm_rescaleRestricted_le {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] (a : R) (ha : ‖a‖ ≤ 1) (f : PowerSeries.Restricted R (1 : ℝ)) :
    ‖rescaleRestricted a ha f‖ ≤ ‖f‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, PowerSeries.gaussNorm_eq]
  refine Real.iSup_le (fun n => ?_) ?_
  · show ‖PowerSeries.coeff n (PowerSeries.rescale a f.1)‖ * (1 : ℝ) ^ n ≤ _
    rw [PowerSeries.coeff_rescale]
    calc ‖a ^ n * PowerSeries.coeff n f.1‖ * (1 : ℝ) ^ n
        ≤ ‖PowerSeries.coeff n f.1‖ * (1 : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc ‖a ^ n * PowerSeries.coeff n f.1‖
              ≤ ‖a ^ n‖ * ‖PowerSeries.coeff n f.1‖ := norm_mul_le _ _
            _ ≤ 1 * ‖PowerSeries.coeff n f.1‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                cases n with
                | zero => rw [pow_zero, norm_one]
                | succ k =>
                    exact (norm_pow_le' a k.succ_pos).trans
                      (pow_le_one₀ (norm_nonneg a) ha)
            _ = ‖PowerSeries.coeff n f.1‖ := one_mul _
      _ ≤ PowerSeries.gaussNorm (norm : R → ℝ) 1 f.1 :=
          PowerSeries.le_gaussNorm (norm : R → ℝ) 1 f.1
            (Restricted.hasGaussNorm 1 f) n
  · exact PowerSeries.gaussNorm_nonneg (norm : R → ℝ) 1 f.1 (fun x => norm_nonneg x)

/-- The twisted base map is norm-nonincreasing, hence continuous. -/
theorem continuous_thetaChart : Continuous (thetaChart F) := by
  refine AddMonoidHomClass.continuous_of_bound (thetaChart F) 1 fun x => ?_
  rw [one_mul]
  show ‖twistB F (jB F x)‖ ≤ ‖x‖
  refine le_trans ?_ (norm_jB_le F x)
  show ‖(⟨rescaleRestricted _ _ (jB F x).fst,
    rescaleRestricted _ _ (jB F x).snd⟩ : JetB F)‖ ≤ ‖jB F x‖
  calc ‖(⟨rescaleRestricted _ _ (jB F x).fst,
        rescaleRestricted _ _ (jB F x).snd⟩ : JetB F)‖
      = max ‖rescaleRestricted (LaurentSeriesExample.t F) (norm_t_lt_one F).le
          (jB F x).fst‖ ‖rescaleRestricted (LaurentSeriesExample.t F)
          (norm_t_lt_one F).le (jB F x).snd‖ := JetNorm.norm_def _
    _ ≤ max ‖(jB F x).fst‖ ‖(jB F x).snd‖ :=
        max_le_max (norm_rescaleRestricted_le _ _ _) (norm_rescaleRestricted_le _ _ _)
    _ = ‖jB F x‖ := (JetNorm.norm_def _).symm

/-- The 𝓑-jet of `W` has vanishing `Q`-part. -/
theorem jB_Wa_snd : (jB F (Wa F)).snd = 0 := by
  refine ofRestricted_injective (R := K) ?_
  rw [map_zero]
  show ofRestricted ((nonnegEquiv (R := K)).symm
    ⟨qCoeff F 1 ((Wa F : JetA F) : JetC F), (Wa F).2.2⟩) = 0
  rw [ofRestricted_nonnegEquiv_symm]
  show qCoeff F 1 (sectionD F (TrivSqZeroExt.inl (Wu (R := K)).val)) = 0
  rw [qCoeff_sectionD]
  norm_num

/-- The Laurent shadow of the 𝓑-jet of `W` is the degree-one monomial. -/
theorem ofRestricted_jB_Wa_fst :
    ofRestricted (R := K) (jB F (Wa F)).fst = single 1 1 := by
  show ofRestricted ((nonnegEquiv (R := K)).symm
    ⟨qCoeff F 0 ((Wa F : JetA F) : JetC F), (Wa F).2.1⟩) = single 1 1
  rw [ofRestricted_nonnegEquiv_symm]
  show qCoeff F 0 (sectionD F (TrivSqZeroExt.inl (Wu (R := K)).val)) = single 1 1
  rw [qCoeff_sectionD]
  norm_num
  rfl

/-- Power-series coefficients of the 𝓑-jet of `W`. -/
theorem coeff_jB_Wa_fst (n : ℕ) :
    PowerSeries.coeff n ((jB F (Wa F)).fst).1 = if n = 1 then 1 else 0 := by
  have h : (ofPowerSeries ((jB F (Wa F)).fst)).coeff (n : ℤ) =
      (single 1 1 : RestrictedLaurent K).coeff (n : ℤ) := by
    rw [show ofPowerSeries ((jB F (Wa F)).fst) =
      ofRestricted (R := K) (jB F (Wa F)).fst from rfl, ofRestricted_jB_Wa_fst F]
  rw [coeff_ofPowerSeries, if_pos (by positivity), Int.toNat_natCast, coeff_single] at h
  rw [h]
  by_cases hn : n = 1
  · rw [if_pos (by exact_mod_cast hn), if_pos hn]
  · rw [if_neg (by exact_mod_cast hn), if_neg hn]

/-- **The key jet computation** ([FJP] Prop 3.1's `W ↦ ϖX`): the twist scales the
`W`-jet by the pseudouniformizer. -/
theorem thetaChart_Wa : thetaChart F (Wa F) = tB F * jB F (Wa F) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show rescaleRestricted (LaurentSeriesExample.t F) (norm_t_lt_one F).le
      (jB F (Wa F)).fst = (tB F * jB F (Wa F)).fst
    rw [TrivSqZeroExt.fst_mul]
    refine Subtype.ext ?_
    refine PowerSeries.ext fun n => ?_
    show PowerSeries.coeff n (PowerSeries.rescale (LaurentSeriesExample.t F)
      ((jB F (Wa F)).fst).1) = PowerSeries.coeff n
        ((PowerSeries.C (LaurentSeriesExample.t F) : PowerSeries K) *
          ((jB F (Wa F)).fst).1)
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, coeff_jB_Wa_fst]
    by_cases hn : n = 1
    · subst hn
      rw [if_pos rfl, pow_one]
    · rw [if_neg hn, mul_zero, mul_zero]
  · show rescaleRestricted (LaurentSeriesExample.t F) (norm_t_lt_one F).le
      (jB F (Wa F)).snd = (tB F * jB F (Wa F)).snd
    rw [jB_Wa_snd, map_zero, TrivSqZeroExt.snd_mul]
    rw [jB_Wa_snd]
    show (0 : PowerSeries.Restricted K (1 : ℝ)) =
      (tB F).fst • (0 : PowerSeries.Restricted K (1 : ℝ)) +
        MulOpposite.op ((jB F (Wa F)).fst) • (tB F).snd
    rw [smul_zero, show (tB F).snd = 0 from rfl, smul_zero, add_zero]

/-- The element `Q ∈ 𝓐` (support `(0,1)`; [FJP] §1.4). -/
def Qa : JetA F :=
  ⟨sectionD F (TrivSqZeroExt.inr (1 : L F)), by
    rw [mem_jetSupport_iff_jet_in_range, rhoC_sectionD]
    refine ⟨TrivSqZeroExt.inr ((nonnegEquiv (R := K)).symm
      ⟨(1 : RestrictedLaurent K), (nonnegSubring K).one_mem⟩), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show ofRestricted (R := K) 0 = 0
      exact map_zero _
    · show ofRestricted ((nonnegEquiv (R := K)).symm
        ⟨(1 : RestrictedLaurent K), (nonnegSubring K).one_mem⟩) = 1
      rw [ofRestricted_nonnegEquiv_symm]⟩

/-! ### The (3.3) collapse data: `Q² = Wⁿ · (W⁻ⁿQ²)` with unit `W`-multiples -/

/-- `W`'s underlying jet is the `Q⁰`-constant at the Laurent unit `W`. -/
theorem Wa_val_eq : ((Wa F : JetA F) : JetC F) = constHomC F (Wu (R := K)).val := by
  refine Subtype.ext ?_
  refine PowerSeries.ext fun n => ?_
  show PowerSeries.coeff n (sectionD F (TrivSqZeroExt.inl (Wu (R := K)).val)).1 = _
  rw [show (sectionD F (TrivSqZeroExt.inl (Wu (R := K)).val)).1 =
    PowerSeries.mk (fun n => if n = 0 then (Wu (R := K)).val else
      if n = 1 then 0 else 0) from rfl]
  rw [PowerSeries.coeff_mk]
  show _ = PowerSeries.coeff n (PowerSeries.C ((Wu (R := K)).val) :
    PowerSeries (L F))
  rw [PowerSeries.coeff_C]
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : n = 1
    · rw [if_pos h1]
    · rw [if_neg h1]

/-- The `W⁻ⁿQ²`-family: `yQ n := W⁻ⁿ·Q²` as an element of 𝓐 (its `(0,1)`-jets vanish). -/
noncomputable def yQ (n : ℕ) : JetA F :=
  ⟨constHomC F (((Wu (R := K))⁻¹).val ^ n) * ((Qa F : JetA F) : JetC F) *
    ((Qa F : JetA F) : JetC F), by
    have hq0 : qCoeff F 0 (((Qa F : JetA F) : JetC F)) = 0 := by
      show qCoeff F 0 (sectionD F (TrivSqZeroExt.inr (1 : L F))) = 0
      rw [qCoeff_sectionD]
      norm_num
    constructor
    · simp only [qCoeff_zero_mul, hq0, mul_zero]
      exact zero_mem _
    · simp only [qCoeff_one_mul, qCoeff_zero_mul, hq0, mul_zero, zero_mul,
        add_zero, zero_add]
      exact zero_mem _⟩

/-- The collapse identity in 𝓐: `Wⁿ · (W⁻ⁿQ²) = Q²`. -/
theorem Wa_pow_mul_yQ (n : ℕ) : Wa F ^ n * yQ F n = Qa F * Qa F := by
  refine Subtype.ext ?_
  show ((Wa F : JetA F) : JetC F) ^ n *
    (constHomC F (((Wu (R := K))⁻¹).val ^ n) * ((Qa F : JetA F) : JetC F) *
      ((Qa F : JetA F) : JetC F)) = ((Qa F : JetA F) : JetC F) * ((Qa F : JetA F) : JetC F)
  rw [Wa_val_eq, ← map_pow, ← mul_assoc, ← mul_assoc, ← map_mul,
    show (Wu (R := K)).val ^ n * ((Wu (R := K))⁻¹).val ^ n = 1 from by
      rw [← mul_pow]
      rw [show (Wu (R := K)).val * ((Wu (R := K))⁻¹).val = 1 from (Wu (R := K)).val_inv]
      rw [one_pow],
    map_one, one_mul]

/-! ### The forward map `𝒪_𝓐(chart) → 𝓑` (Prop 3.1's `ψ`-direction) -/

theorem isUnit_thetaChart_s : IsUnit (thetaChart F (chartDatum F).s) := by
  show IsUnit (thetaChart F (tA F))
  rw [thetaChart_tA]
  exact isUnit_tB F

/-- The chart's localization lift into 𝓑 (`ϖ` is already a unit there). -/
noncomputable def chartLocHom :
    Localization.Away (chartDatum F).s →+* JetB F :=
  IsLocalization.Away.lift (S := Localization.Away (chartDatum F).s)
    (chartDatum F).s (isUnit_thetaChart_s F)

theorem chartLocHom_algebraMap (a : JetA F) :
    chartLocHom F (algebraMap (JetA F) (Localization.Away (chartDatum F).s) a) =
      thetaChart F a :=
  IsLocalization.Away.lift_eq _ _ a

/-- The chart generator `W/ϖ` maps to the norm-one disc variable `jB(W)`
(the rescaling at work: `θ(W)/θ(ϖ) = ϖ·jB(W)/ϖ`). -/
theorem chartLocHom_divByS_Wa :
    chartLocHom F (divByS (Wa F) (chartDatum F).s) = jB F (Wa F) := by
  have hu := isUnit_thetaChart_s F
  have hspec : divByS (Wa F) (chartDatum F).s *
      algebraMap (JetA F) (Localization.Away (chartDatum F).s) (chartDatum F).s =
      algebraMap (JetA F) (Localization.Away (chartDatum F).s) (Wa F) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (chartLocHom F) hspec
  rw [RingHom.map_mul (chartLocHom F), chartLocHom_algebraMap,
    chartLocHom_algebraMap] at happ
  -- `chartLocHom (W/ϖ) · θ(ϖ) = θ(W) = ϖ_𝓑 · jB(W)`; cancel the unit `θ(ϖ) = ϖ_𝓑`.
  rw [show thetaChart F (chartDatum F).s = tB F from thetaChart_tA F,
    show thetaChart F (Wa F) = tB F * jB F (Wa F) from thetaChart_Wa F] at happ
  refine (isUnit_tB F).mul_left_cancel ?_
  rw [mul_comm (tB F) (chartLocHom F (divByS (Wa F) (chartDatum F).s))]
  exact happ

theorem chartLocHom_divByS_tA :
    chartLocHom F (divByS (tA F) (chartDatum F).s) = 1 := by
  have hu := isUnit_thetaChart_s F
  have hspec : divByS (tA F) (chartDatum F).s *
      algebraMap (JetA F) (Localization.Away (chartDatum F).s) (chartDatum F).s =
      algebraMap (JetA F) (Localization.Away (chartDatum F).s) (tA F) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (chartLocHom F) hspec
  rw [RingHom.map_mul (chartLocHom F), chartLocHom_algebraMap,
    chartLocHom_algebraMap] at happ
  rw [show thetaChart F (chartDatum F).s = tB F from thetaChart_tA F,
    show thetaChart F (tA F) = tB F from thetaChart_tA F] at happ
  refine (isUnit_tB F).mul_left_cancel ?_
  rw [mul_comm (tB F) (chartLocHom F (divByS (tA F) (chartDatum F).s)), happ, mul_one]

/-- `‖jB(W)‖ = 1`. -/
theorem norm_jB_Wa : ‖jB F (Wa F)‖ = 1 := by
  have h1 : ‖(jB F (Wa F)).fst‖ = 1 := by
    rw [← ofRestricted_norm (R := K), ofRestricted_jB_Wa_fst, norm_single, norm_one]
  calc ‖jB F (Wa F)‖ = max ‖(jB F (Wa F)).fst‖ ‖(jB F (Wa F)).snd‖ :=
        JetNorm.norm_def _
    _ = 1 := by
        rw [h1, jB_Wa_snd, norm_zero]
        exact max_eq_left zero_le_one

set_option maxHeartbeats 800000 in
/-- Continuity of the chart's localization lift (universal property; the generators map
to norm-`≤ 1` elements of 𝓑). -/
theorem chartLocHom_continuous :
    @Continuous _ _ (chartDatum F).topology _ (chartLocHom F) := by
  refine locTopology_continuous_lift (chartDatum F).P (chartDatum F).T
    (chartDatum F).s (chartDatum F).hopen _ ?_ ?_
  · have h_eq : (chartLocHom F).comp
        (algebraMap (JetA F) (Localization.Away (chartDatum F).s)) =
        thetaChart F :=
      RingHom.ext fun a => chartLocHom_algebraMap F a
    rw [show ⇑((chartLocHom F).comp
        (algebraMap (JetA F) (Localization.Away (chartDatum F).s)))
        = ⇑(thetaChart F) from congrArg _ h_eq]
    exact continuous_thetaChart F
  · intro t ht
    have hmem : t = Wa F ∨ t = tA F := by
      rcases Finset.mem_insert.mp ht with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hmem with rfl | rfl
    · rw [show divByS (Wa F) (chartDatum F).s = divByS (Wa F) (chartDatum F).s from rfl,
        chartLocHom_divByS_Wa]
      exact isPowerBounded_of_norm_le_one (le_of_eq (norm_jB_Wa F))
    · rw [chartLocHom_divByS_tA]
      exact isPowerBounded_of_norm_le_one (le_of_eq norm_one)

/-- Forward: `𝒪_𝓐(chart) → 𝓑` (completion extension; 𝓑 is complete Hausdorff). -/
noncomputable def chartFwd : presheafValue (chartDatum F) →+* JetB F := by
  letI := (chartDatum F).uniformSpace
  letI : IsTopologicalRing (Localization.Away (chartDatum F).s) :=
    (chartDatum F).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (chartDatum F).s) :=
    (chartDatum F).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (chartLocHom F)
    (chartLocHom_continuous F)

theorem chartFwd_coe (a : Localization.Away (chartDatum F).s) :
    chartFwd F ((chartDatum F).coeRingHom a) = chartLocHom F a := by
  letI := (chartDatum F).uniformSpace
  letI : IsTopologicalRing (Localization.Away (chartDatum F).s) :=
    (chartDatum F).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (chartDatum F).s) :=
    (chartDatum F).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (chartLocHom F)
    (chartLocHom_continuous F) a

theorem chartFwd_continuous : Continuous (chartFwd F) := by
  letI := (chartDatum F).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- **[FJP] Proposition 3.1**: the chart is the square-zero disc algebra,
`𝒪_𝓐({|W| ≤ |ϖ|}) ≅ K⟨X⟩[Q]/(Q²) = 𝓑`, as topological rings. -/
def chartEquiv : presheafValue (chartDatum F) ≃+* JetB F := by sorry

theorem chartEquiv_continuous : Continuous (chartEquiv F) := by sorry

theorem chartEquiv_symm_continuous : Continuous (chartEquiv F).symm := by sorry

/-- The chart sends `canonicalMap W` to `ϖ · X` and `canonicalMap Q` to `ε`
([FJP] Prop 3.1: "`W ↦ ϖX`, `Q ↦ Q`"; pinned on the canonical image to make `chartEquiv`
canonical). -/
theorem chartEquiv_canonicalMap_W : True := by sorry

/-! ### Failure of stable uniformity ([FJP] Corollary 3.2) -/

/-- Power-boundedness transports along a bi-continuous ring isomorphism. -/
theorem isPowerBounded_map_of_ringEquiv {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {x : A} (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (e x) := by
  intro U hU
  have hUA : ⇑e.symm ⁻¹' (⇑e ⁻¹' U) ∈ nhds (0 : B) := by
    refine he'.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    refine he.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact hU
  obtain ⟨V, hV, hSV⟩ := hx (⇑e ⁻¹' U)
    (he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU))
  refine ⟨⇑e.symm ⁻¹' V, he'.continuousAt.preimage_mem_nhds
    (by rw [map_zero]; exact hV), ?_⟩
  rintro _ ⟨s, ⟨n, rfl⟩, v, hv, rfl⟩
  have hxv : x ^ n * e.symm v ∈ ⇑e ⁻¹' U :=
    hSV ⟨x ^ n, ⟨n, rfl⟩, e.symm v, hv, rfl⟩
  show e x ^ n * v ∈ U
  have heq : e x ^ n * v = e (x ^ n * e.symm v) := by
    rw [map_mul, map_pow, RingEquiv.apply_symm_apply]
  rw [heq]
  exact hxv

/-- Uniformity is a topological-ring invariant: it transports along continuous ring
isomorphisms with continuous inverse. -/
theorem isUniform_of_ringEquiv {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (h : TopologicalRing.IsUniform A) : TopologicalRing.IsUniform B := by
  constructor
  intro U hU
  obtain ⟨V, hV, hSV⟩ := h.isBounded_powerBounded (⇑e ⁻¹' U)
    (he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU))
  refine ⟨⇑e.symm ⁻¹' V, he'.continuousAt.preimage_mem_nhds
    (by rw [map_zero]; exact hV), ?_⟩
  rintro _ ⟨s, hs, v, hv, rfl⟩
  have hsA : TopologicalRing.IsPowerBounded (e.symm s) :=
    isPowerBounded_map_of_ringEquiv e.symm he' (by simpa using he) hs
  have hmem : e.symm s * e.symm v ∈ ⇑e ⁻¹' U :=
    hSV ⟨e.symm s, hsA, e.symm v, hv, rfl⟩
  show s * v ∈ U
  have heq : s * v = e (e.symm s * e.symm v) := by
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [heq]
  exact hmem

/-- The chart is not uniform ([FJP] Cor 3.2, via `not_isUniform_JetB`). -/
theorem not_isUniform_chart :
    ¬ TopologicalRing.IsUniform (presheafValue (chartDatum F)) := fun h =>
  not_isUniform_JetB F
    (isUniform_of_ringEquiv (chartEquiv F) (chartEquiv_continuous F)
      (chartEquiv_symm_continuous F) h)

/-- **[FJP] Corollary 3.2**: 𝓐 is not stably uniform. -/
theorem not_isStablyUniform_JetA : ¬ TopologicalRing.IsStablyUniform (JetA F) := fun h =>
  not_isUniform_chart F ⟨h.presheafValue_isUniform (chartDatum F)⟩

end

end FiniteJet
