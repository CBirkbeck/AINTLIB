/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.Presentation
import «Adic spaces».FarguesFontaine.SheafyBI
import «Adic spaces».FarguesFontaine.ChartVObj

/-!
# Robba-localization presentations (T910, Kedlaya Lemma 4.9 cases 1–2)

The evaluation machinery for restricted series over `B^I` along a contracting
coefficient homomorphism into a sub-interval ring:

* `FarguesFontaine.wI_resIHom_le` : the interval restriction contracts `wI`;
* `FarguesFontaine.isRestricted_iff_wI` / `tendsto_wI_coeffSeq` :
  restrictedness over `B^I` in norm terms;
* `FarguesFontaine.exists_evalBI_series` : convergence of the evaluation;
* `FarguesFontaine.evalBIHom` : the presentation map `B^I⟨T⟩ →+* B^{I'}`,
  generic in the contracting carrier `φ` (instantiated at `resIHom`).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
  {hρ₂1 : ρ₂ < 1}

/-- **The interval restriction contracts the interval norm** (both target
radii are interpolants, each coordinate bounded by `valued_resI_le_wI`). -/
theorem wI_resIHom_le {θ η : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (hσ₂0 : 0 < ρ₁ ^ η * ρ₂ ^ (1 - η)) (hσ₂1 : ρ₁ ^ η * ρ₂ ^ (1 - η) < 1)
    (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
        ((resIHom p F ϖ hθ0 hθ1 hη0 hη1 hσ₁0 hσ₁1 hσ₂0 hσ₂1 z
          : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
  refine max_le ?_ ?_
  · exact valued_resI_le_wI p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2
  · exact valued_resI_le_wI p F ϖ hη0 hη1 hσ₂0 hσ₂1 z.2

/-- Coercion of a `B^I`-sum to the product, as a plain equation (kept as a
standalone micro-lemma so heavy contexts can rewrite with it instead of
paying the definitional check). -/
theorem BISub_coe_add {σ₁ σ₂ : NNReal} {h1 : 0 < σ₁} {h2 : σ₁ < 1}
    {h3 : 0 < σ₂} {h4 : σ₂ < 1} (x y : ↥(BISub p F ϖ h1 h2 h3 h4)) :
    ((x + y : ↥(BISub p F ϖ h1 h2 h3 h4))
      : (hatK p F h1 h2) × (hatK p F h3 h4))
      = ((x : ↥(BISub p F ϖ h1 h2 h3 h4))
          : (hatK p F h1 h2) × (hatK p F h3 h4))
        + ((y : ↥(BISub p F ϖ h1 h2 h3 h4))
            : (hatK p F h1 h2) × (hatK p F h3 h4)) := rfl

/-- **Restrictedness over `B^I` in interval-norm terms**: finitely many
coefficients above every positive threshold. -/
theorem isRestricted_iff_wI {k : ℕ}
    (f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    MvPowerSeries.IsRestricted f
      ↔ ∀ ε : NNReal, 0 < ε → {s : Fin k →₀ ℕ |
          ε < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
            ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}.Finite := by
  constructor
  · intro hf ε hε
    have hB : {a : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) |
        wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((a : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ ε}
        ∈ nhds (0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
      wI_ball_mem_nhds_BISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hε
    have hev := hf hB
    rw [Filter.mem_map, Filter.mem_cofinite] at hev
    refine hev.subset ?_
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq] at hs ⊢
    exact not_le.mpr hs
  · intro hf
    rw [MvPowerSeries.IsRestricted, Filter.tendsto_def]
    intro U hU
    rw [nhds_subtype_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    obtain ⟨ε, hε, hεV⟩ := exists_wI_ball_subset p F
      (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hV
    rw [Filter.mem_cofinite]
    refine ((hf ε hε).subset ?_)
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq] at hs ⊢
    by_contra hcon
    push Not at hcon
    exact hs (hVU (hεV hcon))

/-- A restricted one-variable series over `B^I` has null coefficient norms. -/
theorem tendsto_wI_coeffSeq
    {f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    Filter.Tendsto (fun n => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      Filter.atTop (nhds 0) := by
  refine tendsto_order.mpr
    ⟨fun c hc => absurd hc (not_lt.mpr zero_le), fun δ hδ => ?_⟩
  have hfin := (isRestricted_iff_wI p F ϖ f).mp hf (δ / 2) (half_pos hδ)
  have hpre : ((fun n : ℕ => (Finsupp.single (0 : Fin 1) n)) ⁻¹'
      {s : Fin 1 →₀ ℕ | δ / 2 < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}).Finite :=
    hfin.preimage ((Finsupp.single_injective (0 : Fin 1)).injOn)
  obtain ⟨N, hN⟩ := hpre.bddAbove
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnot : n ∉ ((fun n : ℕ => (Finsupp.single (0 : Fin 1) n)) ⁻¹'
      {s : Fin 1 →₀ ℕ | δ / 2 < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}) := by
    intro hmem
    have := hN hmem
    omega
  exact lt_of_le_of_lt (not_lt.mp hnot) (NNReal.half_lt_self hδ.ne')

/-- **Evaluation of a restricted series over `B^I` along a contracting
coefficient homomorphism converges** — the abstract engine: `φ` carries the
coefficients into the target interval ring without increasing the norm, the
terms decay because the series is restricted. -/
theorem exists_evalBI_series {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
    (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
        ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (a : ℕ → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (ha : Filter.Tendsto (fun l => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((a l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      Filter.atTop (nhds 0))
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1) :
    ∃ S : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1),
      S ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1
      ∧ Filter.Tendsto (fun n => ∑ l ∈ Finset.range n,
          ((φ (a l) : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l)
        Filter.atTop (nhds S) := by
  refine exists_BI_series_limit p F ϖ (u := fun l =>
    ((φ (a l) : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l)
    (fun l => mul_mem (φ (a l)).2 (pow_mem hbmem l))
    (C := fun l => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((a l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (fun l => ?_) ha
  refine le_trans (wI_mul_le p F _ _) ?_
  calc wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
        ((φ (a l) : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
        * wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 (b ^ l)
      ≤ wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
          ((φ (a l) : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        rw [wI_pow p F]
        exact pow_le_one₀ zero_le hb
    _ = wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
          ((φ (a l) : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) := mul_one _
    _ ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((a l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := hφ (a l)

section EvalBI

variable {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
  {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))

/-- The term of the `B^I`-evaluation series. -/
def evalBITerm (b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
    (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (l : ℕ) :
    (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1) :=
  ((φ (coeffSeq f l) : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
    : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l

variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))

include hφ in
/-- The evaluation terms have null interval norm. -/
theorem tendsto_wI_evalBITerm
    {f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    Filter.Tendsto (fun l => wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
        ((φ (coeffSeq f l) : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)))
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_wI_coeffSeq p F ϖ hf) (fun _ => zero_le)
    (fun l => hφ (coeffSeq f l))

include hφ in
/-- **The value of a restricted series over `B^I` along a contracting
coefficient homomorphism at a power-bounded element.** -/
def evalBI {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1) :=
  (exists_evalBI_series p F ϖ φ hφ
    (coeffSeq (f : MvPowerSeries (Fin 1)
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (tendsto_wI_coeffSeq p F ϖ f.2) hbmem hb).choose

theorem evalBI_mem {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    evalBI p F ϖ φ hφ hbmem hb f ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 :=
  (exists_evalBI_series p F ϖ φ hφ
    (coeffSeq (f : MvPowerSeries (Fin 1)
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (tendsto_wI_coeffSeq p F ϖ f.2) hbmem hb).choose_spec.1

theorem tendsto_evalBI {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    Filter.Tendsto (fun n => ∑ l ∈ Finset.range n,
        evalBITerm p F ϖ φ b
          (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
      Filter.atTop (nhds (evalBI p F ϖ φ hφ hbmem hb f)) :=
  (exists_evalBI_series p F ϖ φ hφ
    (coeffSeq (f : MvPowerSeries (Fin 1)
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (tendsto_wI_coeffSeq p F ϖ f.2) hbmem hb).choose_spec.2

/-- The carrier commutes with finite sums (by induction, avoiding class
search on the nested subring types). -/
theorem evalBI_carrier_sum {ι : Type*} (s : Finset ι)
    (a : ι → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    φ (∑ i ∈ s, a i) = ∑ i ∈ s, φ (a i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact φ.map_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, φ.map_add, ih]

/-- The `l`-th term is additive in the series. -/
theorem evalBITerm_add (b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
    (f g : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) (l : ℕ) :
    evalBITerm p F ϖ φ b ((f + g : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
      = evalBITerm p F ϖ φ b (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
        + evalBITerm p F ϖ φ b (g : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l := by
  have hc : φ (coeffSeq ((f + g : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
      = φ (coeffSeq (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
        + φ (coeffSeq (g : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l) := by
    rw [show coeffSeq ((f + g : ↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
        = coeffSeq (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
          + coeffSeq (g : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l from
      coeffSeq_add _ _ _, φ.map_add]
  calc evalBITerm p F ϖ φ b
        ((f + g : ↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
      = ((φ (coeffSeq (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
          + φ (coeffSeq (g : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
          : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l :=
        congrArg (fun z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) =>
          ((z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l) hc
    _ = (((φ (coeffSeq (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
          : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
        + ((φ (coeffSeq (g : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
            : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))) * b ^ l :=
        congrArg (· * b ^ l) (BISub_coe_add p F ϖ _ _)
    _ = evalBITerm p F ϖ φ b (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
        + evalBITerm p F ϖ φ b (g : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l :=
        add_mul _ _ _

/-- Evaluation is additive. -/
theorem evalBI_add {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (f g : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    evalBI p F ϖ φ hφ hbmem hb (f + g)
      = evalBI p F ϖ φ hφ hbmem hb f + evalBI p F ϖ φ hφ hbmem hb g := by
  refine tendsto_nhds_unique (tendsto_evalBI p F ϖ φ hφ hbmem hb (f + g)) ?_
  refine ((tendsto_evalBI p F ϖ φ hφ hbmem hb f).add
    (tendsto_evalBI p F ϖ φ hφ hbmem hb g)).congr fun n => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => (evalBITerm_add p F ϖ φ b f g l).symm

/-- The `l`-th term of a product is the antidiagonal convolution. -/
theorem evalBITerm_mul_sum (b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
    (f g : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) (l : ℕ) :
    evalBITerm p F ϖ φ b ((f * g : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
      = (∑ q ∈ Finset.antidiagonal l,
          ((φ (coeffSeq (f : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) q.1)
            : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
          * ((φ (coeffSeq (g : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) q.2)
            : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))) * b ^ l := by
  rw [evalBITerm]
  congr 1
  have hc : coeffSeq ((f * g : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
      = ∑ q ∈ Finset.antidiagonal l,
          coeffSeq (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) q.1
          * coeffSeq (g : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) q.2 :=
    coeffSeq_mul _ _ _
  rw [hc, evalBI_carrier_sum p F ϖ φ, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [φ.map_mul]
  rfl

/-- **Evaluation is multiplicative** — the Cauchy-product estimate at the
target radii. -/
theorem evalBI_mul {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (f g : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    evalBI p F ϖ φ hφ hbmem hb (f * g)
      = evalBI p F ϖ φ hφ hbmem hb f * evalBI p F ϖ φ hφ hbmem hb g := by
  refine tendsto_nhds_unique (tendsto_evalBI p F ϖ φ hφ hbmem hb (f * g)) ?_
  have hcp := tendsto_cauchy_product p F hb
    (fun i => ((φ (coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) i)
      : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)))
    (fun j => ((φ (coeffSeq (g : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) j)
      : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)))
    (tendsto_wI_evalBITerm p F ϖ φ hφ f.2)
    (tendsto_wI_evalBITerm p F ϖ φ hφ g.2)
    (tendsto_evalBI p F ϖ φ hφ hbmem hb f)
    (tendsto_evalBI p F ϖ φ hφ hbmem hb g)
  refine hcp.congr fun n => ?_
  exact Finset.sum_congr rfl fun l _ =>
    (evalBITerm_mul_sum p F ϖ φ b f g l).symm

/-- Evaluation sends `1` to `1`. -/
theorem evalBI_one {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1) :
    evalBI p F ϖ φ hφ hbmem hb 1 = 1 := by
  refine tendsto_nhds_unique (tendsto_evalBI p F ϖ φ hφ hbmem hb 1) ?_
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hterms : ∀ l ∈ Finset.range n,
      evalBITerm p F ϖ φ b
        (1 : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
        = if l = 0 then 1 else 0 := by
    intro l _
    rw [evalBITerm, coeffSeq_one]
    by_cases hl : l = 0
    · subst hl
      rw [if_pos rfl, if_pos rfl, φ.map_one, pow_zero, mul_one]
      rfl
    · rw [if_neg hl, if_neg hl, φ.map_zero]
      show (0 : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l = 0
      rw [zero_mul]
  show (1 : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
      = ∑ l ∈ Finset.range n,
        evalBITerm p F ϖ φ b
          (1 : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
  rw [Finset.sum_congr rfl hterms, Finset.sum_ite_eq' (Finset.range n) 0
    (fun _ => (1 : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)))]
  rw [if_pos (Finset.mem_range.mpr hn)]

/-- Evaluation sends `0` to `0`. -/
theorem evalBI_zero {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1) :
    evalBI p F ϖ φ hφ hbmem hb 0 = 0 := by
  refine tendsto_nhds_unique (tendsto_evalBI p F ϖ φ hφ hbmem hb 0) ?_
  refine tendsto_const_nhds.congr fun n => ?_
  refine (Finset.sum_eq_zero fun l _ => ?_).symm
  rw [evalBITerm]
  rw [show coeffSeq ((0 : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
      = 0 from coeffSeq_zero l, φ.map_zero]
  show (0 : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l = 0
  rw [zero_mul]

include hφ in
/-- **The Robba-localization evaluation, as a ring homomorphism**
`B^I⟨T⟩ →+* B^{I'}` — Kedlaya's case-1/2 presentation map, generic in the
contracting coefficient carrier. -/
def evalBIHom {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1) :
    ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) where
  toFun f := ⟨evalBI p F ϖ φ hφ hbmem hb f, evalBI_mem p F ϖ φ hφ hbmem hb f⟩
  map_one' := Subtype.ext (evalBI_one p F ϖ φ hφ hbmem hb)
  map_mul' := fun f g => Subtype.ext (evalBI_mul p F ϖ φ hφ hbmem hb f g)
  map_zero' := Subtype.ext (evalBI_zero p F ϖ φ hφ hbmem hb)
  map_add' := fun f g => Subtype.ext (evalBI_add p F ϖ φ hφ hbmem hb f g)

end EvalBI


/-! ### The interval Gauss norm on restricted series (T910 P3 substrate) -/

variable {k : ℕ}

/-- **The interval Gauss norm** on multivariate power series over `B^I`
(radius-1 variables): the supremum of the coefficient interval norms. -/
def wIRPS (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : NNReal :=
  ⨆ s : Fin k →₀ ℕ, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
    ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))

/-- Restricted series have bounded coefficient norms. -/
theorem bddAbove_wIRPS
    {f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    BddAbove (Set.range (fun s : Fin k →₀ ℕ =>
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))) := by
  have hfin := (isRestricted_iff_wI p F ϖ f).mp hf 1 one_pos
  refine ⟨max 1 ((hfin.toFinset).sup (fun s =>
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))), ?_⟩
  rintro t ⟨s, rfl⟩
  rcases le_or_gt (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) 1 with h1 | h1
  · exact le_max_of_le_left h1
  · refine le_max_of_le_right (Finset.le_sup
      (f := fun s => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ?_)
    rw [Set.Finite.mem_toFinset]
    exact h1

/-- Each coefficient norm is bounded by the interval Gauss norm. -/
theorem wI_coeff_le_wIRPS
    {f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) (s : Fin k →₀ ℕ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      ≤ wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 f :=
  le_ciSup (bddAbove_wIRPS p F ϖ hf) s

/-- The interval Gauss norm of `0`. -/
theorem wIRPS_zero :
    wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (0 : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) = 0 := by
  rw [wIRPS]
  refine le_antisymm (ciSup_le fun s => ?_) zero_le
  rw [map_zero]
  rw [show (((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 0 from rfl]
  rw [wI_zero p F]

/-- Coefficientwise limit input: each coefficient column of a
`wIRPS`-controlled series of restricted series converges in `B^I`
(the `exists_BI_series_limit`-engine, coefficientwise). -/
theorem exists_BI_coeff_column_limit
    {u : ℕ → ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))} {C : ℕ → NNReal}
    (hC : ∀ l, wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((u l : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ≤ C l)
    (hC0 : Filter.Tendsto C Filter.atTop (nhds 0)) (K : Fin k →₀ ℕ) :
    ∃ S : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1),
      S ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ∧ Filter.Tendsto (fun n => ∑ l ∈ Finset.range n,
          ((MvPowerSeries.coeff K
            ((u l : ↥(restrictedMvPowerSeriesSubring k
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin k)
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
        Filter.atTop (nhds S) := by
  refine exists_BI_series_limit p F ϖ
    (u := fun l => ((MvPowerSeries.coeff K
      ((u l : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (fun l => (MvPowerSeries.coeff K
      ((u l : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))).2)
    (C := C) (fun l => ?_) hC0
  exact le_trans (wI_coeff_le_wIRPS p F ϖ (u l).2 K) (hC l)

/-- **The residual-form series limit in `B^I`**: a `wI`-dominated series of
interval-ring elements has a sum whose tails obey every eventual bound. -/
theorem exists_wI_series_limit
    {u : ℕ → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)} {C : ℕ → NNReal}
    (hC : ∀ l, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ C l)
    (hC0 : Filter.Tendsto C Filter.atTop (nhds 0)) :
    ∃ S : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      ∀ (n : ℕ) (b : NNReal), 0 < b → (∀ l, n ≤ l → C l ≤ b) →
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (((S : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          - ∑ l ∈ Finset.range n,
            ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ≤ b := by
  obtain ⟨Sp, hSmem, htend⟩ := exists_BI_series_limit p F ϖ
    (u := fun l => ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (fun l => (u l).2) (C := C) hC hC0
  refine ⟨⟨Sp, hSmem⟩, fun n b hb0 hbnd => ?_⟩
  have htail : Filter.Tendsto (fun m => (∑ l ∈ Finset.range m,
      ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      - ∑ l ∈ Finset.range n,
        ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      Filter.atTop (nhds (Sp - ∑ l ∈ Finset.range n,
        ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))) :=
    htend.sub_const _
  refine (isClosed_wI_ball p F hb0).mem_of_tendsto htail ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  have hIco : (∑ l ∈ Finset.range m,
      ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      - ∑ l ∈ Finset.range n,
        ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = ∑ l ∈ Finset.Ico n m,
        ((u l : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :=
    (Finset.sum_Ico_eq_sub _ hm).symm
  show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 _ ≤ b
  rw [hIco]
  refine wI_sum_le p F _ _ (fun l hl => ?_)
  exact le_trans (hC l) (hbnd l (Finset.mem_Ico.mp hl).1)

/-- Coercion of an RPS-difference over `B^I` (plain equation). -/
theorem RPS_BI_coe_sub
    (a b : ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    ((a - b : ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      = (a : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        - (b : MvPowerSeries (Fin k)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := rfl

/-- Coefficients of a difference over `B^I`, at the product level. -/
theorem coeff_sub_eq_BI
    (y w : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (K : Fin k →₀ ℕ) :
    ((MvPowerSeries.coeff K (y - w)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = ((MvPowerSeries.coeff K y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        - ((MvPowerSeries.coeff K w : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :=
  congrArg (fun t : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) =>
    (t : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (map_sub (MvPowerSeries.coeff K) y w)

/-- Coefficients of a partial sum of restricted series, at the product level. -/
theorem coeff_partial_sum_BI
    (u : ℕ → ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (n : ℕ) (K : Fin k →₀ ℕ) :
    ((MvPowerSeries.coeff K
      ((∑ l ∈ Finset.range n, u l : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = ∑ l ∈ Finset.range n,
        ((MvPowerSeries.coeff K
          ((u l : ↥(restrictedMvPowerSeriesSubring k
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
  rw [show ((∑ l ∈ Finset.range n, u l : ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    = ∑ l ∈ Finset.range n,
      ((u l : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) from
    AddSubmonoidClass.coe_finsetSum _ _]
  rw [map_sum]
  rw [show ((∑ l ∈ Finset.range n, MvPowerSeries.coeff K
      ((u l : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    = ∑ l ∈ Finset.range n,
      ((MvPowerSeries.coeff K
        ((u l : ↥(restrictedMvPowerSeriesSubring k
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) from
    AddSubmonoidClass.coe_finsetSum _ _]

/-- **Restrictedness of columnwise limits**: if each coefficient column of a
`wIRPS`-vanishing series of restricted series converges with the tail
estimates, the limit series is restricted. -/
theorem isRestricted_column_limits
    {u : ℕ → ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))} {C : ℕ → NNReal}
    (hC0 : Filter.Tendsto C Filter.atTop (nhds 0))
    (S : (Fin k →₀ ℕ) → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hS : ∀ K, ∀ (n : ℕ) (b : NNReal), 0 < b → (∀ l, n ≤ l → C l ≤ b) →
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (((S K : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          - ∑ l ∈ Finset.range n,
            ((MvPowerSeries.coeff K
              ((u l : ↥(restrictedMvPowerSeriesSubring k
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
                : MvPowerSeries (Fin k)
                  ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ≤ b) :
    MvPowerSeries.IsRestricted
      (fun K => S K
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  set Ufun : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    (fun K => S K) with hUfun
  rw [isRestricted_iff_wI]
  intro t ht
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hC0.eventually_lt_const ht)
  have hsub : {K : Fin k →₀ ℕ | t < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff K Ufun
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}
      ⊆ ⋃ l ∈ Finset.range N, {K : Fin k →₀ ℕ |
        t < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((MvPowerSeries.coeff K
            ((u l : ↥(restrictedMvPowerSeriesSubring k
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin k)
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))} := by
    intro K hK
    rw [Set.mem_setOf_eq] at hK
    have hSK : ((MvPowerSeries.coeff K Ufun
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = ((S K : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := rfl
    rw [hSK] at hK
    have htail := hS K N t ht (fun l hl => (hN l hl).le)
    have hbig : t < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (∑ l ∈ Finset.range N,
          ((MvPowerSeries.coeff K
            ((u l : ↥(restrictedMvPowerSeriesSubring k
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin k)
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := by
      by_contra hcon
      push Not at hcon
      have hsplit : ((S K : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          = (((S K : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            - ∑ l ∈ Finset.range N,
              ((MvPowerSeries.coeff K
                ((u l : ↥(restrictedMvPowerSeriesSubring k
                  ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
                  : MvPowerSeries (Fin k)
                    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
                : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
                : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
            + ∑ l ∈ Finset.range N,
              ((MvPowerSeries.coeff K
                ((u l : ↥(restrictedMvPowerSeriesSubring k
                  ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
                  : MvPowerSeries (Fin k)
                    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
                : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
                : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
        ring
      rw [hsplit] at hK
      exact absurd (le_trans (wI_add_le p F _ _) (max_le htail hcon))
        (not_le.mpr hK)
    have hex : ∃ l ∈ Finset.range N, t < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff K
          ((u l : ↥(restrictedMvPowerSeriesSubring k
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin k)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
      by_contra hcon
      push Not at hcon
      exact absurd (wI_sum_le p F _ _ hcon) (not_le.mpr hbig)
    obtain ⟨l, hlN, hl⟩ := hex
    exact Set.mem_biUnion hlN hl
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.range N).finite_toSet
    fun l _ => ?_) hsub
  exact (isRestricted_iff_wI p F ϖ
    ((u l : ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin k)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))).mp (u l).2 t ht

/-- **Ultrametric series converge in the `B^I`-Tate algebra**: a
`wIRPS`-vanishing series of restricted series over `B^I` has a restricted
limit with the tail estimates (the analytic engine of the case-1/2
Robba-localization surjectivity). -/
theorem exists_rps_series_limit_BI
    {u : ℕ → ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))} {C : ℕ → NNReal}
    (hC : ∀ l, wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((u l : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ≤ C l)
    (hC0 : Filter.Tendsto C Filter.atTop (nhds 0)) :
    ∃ U : ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      ∀ (n : ℕ) (b : NNReal), 0 < b → (∀ l, n ≤ l → C l ≤ b) →
      wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((U - ∑ l ∈ Finset.range n, u l
          : ↥(restrictedMvPowerSeriesSubring k
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin k)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ≤ b := by
  have hcol : ∀ K : Fin k →₀ ℕ,
      ∃ S : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      ∀ (n : ℕ) (b : NNReal), 0 < b → (∀ l, n ≤ l → C l ≤ b) →
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (((S : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          - ∑ l ∈ Finset.range n,
            ((MvPowerSeries.coeff K
              ((u l : ↥(restrictedMvPowerSeriesSubring k
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
                : MvPowerSeries (Fin k)
                  ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ≤ b := by
    intro K
    refine exists_wI_series_limit p F ϖ
      (u := fun l => (MvPowerSeries.coeff K
        ((u l : ↥(restrictedMvPowerSeriesSubring k
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))))
      (C := C) (fun l => ?_) hC0
    exact le_trans (wI_coeff_le_wIRPS p F ϖ (u l).2 K) (hC l)
  choose S hS using hcol
  have hres := isRestricted_column_limits p F ϖ (u := u) hC0 S hS
  refine ⟨⟨(fun K => S K), hres⟩, fun n b hb0 hb => ?_⟩
  refine ciSup_le fun K => ?_
  have hcoe : ((MvPowerSeries.coeff K
      (((⟨(fun K => S K), hres⟩ : ↥(restrictedMvPowerSeriesSubring k
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        - ∑ l ∈ Finset.range n, u l
        : ↥(restrictedMvPowerSeriesSubring k
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = ((S K : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        - ∑ l ∈ Finset.range n,
          ((MvPowerSeries.coeff K
            ((u l : ↥(restrictedMvPowerSeriesSubring k
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin k)
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
    rw [RPS_BI_coe_sub p F ϖ, coeff_sub_eq_BI p F ϖ]
    rw [coeff_partial_sum_BI p F ϖ]
    rfl
  rw [hcoe]
  exact hS K n b hb0 hb

section EvalBIBounds

variable {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
  {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))

/-- **The evaluation-value bound**: if every coefficient of `f` has interval
norm at most `ε`, so does the value of the evaluation. -/
theorem wI_evalBI_le {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    {ε : NNReal} (hε : 0 < ε)
    (hf : ∀ l, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ ε) :
    wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 (evalBI p F ϖ φ hφ hbmem hb f) ≤ ε := by
  refine (isClosed_wI_ball p F hε).mem_of_tendsto
    (tendsto_evalBI p F ϖ φ hφ hbmem hb f)
    (Filter.Eventually.of_forall fun n => ?_)
  refine wI_sum_le p F _ _ (fun l _ => ?_)
  show wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
    (((φ (coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
      : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l) ≤ ε
  refine le_trans (wI_mul_le p F _ _) ?_
  calc wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
        ((φ (coeffSeq (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l)
          : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
        * wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 (b ^ l)
      ≤ ε * 1 := by
        refine mul_le_mul (le_trans (hφ _) (hf l)) ?_ zero_le zero_le
        rw [wI_pow p F]
        exact pow_le_one₀ zero_le hb
    _ = ε := mul_one ε

/-- **The residual estimate for a corrected approximation**: adding a
correction of small norm does not worsen a small residual. -/
theorem wI_z_sub_evalBI_add_le
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
    (SS V : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    {ε : NNReal} (hε : 0 < ε)
    (h1 : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
      (z - evalBI p F ϖ φ hφ hbmem hb SS) ≤ ε)
    (h2 : wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (V : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ≤ ε) :
    wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
      (z - evalBI p F ϖ φ hφ hbmem hb (SS + V)) ≤ ε := by
  have hVle : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
      (evalBI p F ϖ φ hφ hbmem hb V) ≤ ε := by
    refine wI_evalBI_le p F ϖ φ hφ hbmem hb V hε (fun l => ?_)
    exact le_trans (wI_coeff_le_wIRPS p F ϖ V.2 _) h2
  have hsplit : z - evalBI p F ϖ φ hφ hbmem hb (SS + V)
      = (z - evalBI p F ϖ φ hφ hbmem hb SS)
        + (-(evalBI p F ϖ φ hφ hbmem hb V)) := by
    rw [evalBI_add p F ϖ φ hφ hbmem hb]
    ring
  rw [hsplit]
  refine le_trans (wI_add_le p F _ _) (max_le h1 ?_)
  rw [wI_neg]
  exact hVle

end EvalBIBounds


/-! ### The case-1/2 generator and the per-monomial twist (T910 P3d) -/

/-- **The case-1/2 Robba generator** `[z̄]/p^m ∈ B_loc` — the element whose
`T`-substitution cuts the interval at `|z̄|^{1/m}`. -/
def teichPowGen (zb : OF F) (m : ℕ) : Bloc p F ϖ :=
  algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p zb)
    * (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ) ^ m

/-- `p`-cancellation against the generator's inverse powers. -/
theorem algebraMap_p_pow_mul_vp_pow (m : ℕ) :
    algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ m)
      * (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ) ^ m = 1 := by
  have hvpmul : algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)
      * (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ) = 1 := by
    have h := (isUnit_p_image p F ϖ).unit.mul_inv
    rwa [(isUnit_p_image p F ϖ).unit_spec] at h
  rw [map_pow, ← mul_pow, hvpmul, one_pow]

/-- **The exact per-monomial lift identity** (Kedlaya ln 546–551, the
substitution side): a Teichmüller monomial whose coordinate is divisible by
`zb^j` is the generator's `j`-th power times the twisted monomial. -/
theorem teichPowGen_pow_mul_twist (zb : OF F) (m : ℕ) (i j : ℕ)
    (c c' : OF F) (hc : c = zb ^ j * c') :
    teichPowGen p F ϖ zb m ^ j
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          ((p : Ainf p F) ^ (i + m * j) * WittVector.teichmuller p c')
      = algebraMap (Ainf p F) (Bloc p F ϖ)
          ((p : Ainf p F) ^ i * WittVector.teichmuller p c) := by
  have hcancel := algebraMap_p_pow_mul_vp_pow p F ϖ (m * j)
  rw [teichPowGen, mul_pow, ← pow_mul,
    ← map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
    ← map_pow (WittVector.teichmuller p)]
  rw [hc, map_mul (WittVector.teichmuller p),
    map_pow (WittVector.teichmuller p)]
  rw [show (p : Ainf p F) ^ (i + m * j)
      = (p : Ainf p F) ^ i * (p : Ainf p F) ^ (m * j) from pow_add _ _ _]
  rw [map_mul (algebraMap (Ainf p F) (Bloc p F ϖ))
      ((p : Ainf p F) ^ i * (p : Ainf p F) ^ (m * j))
      (WittVector.teichmuller p c'),
    map_mul (algebraMap (Ainf p F) (Bloc p F ϖ))
      ((p : Ainf p F) ^ i) ((p : Ainf p F) ^ (m * j)),
    map_mul (algebraMap (Ainf p F) (Bloc p F ϖ))
      ((p : Ainf p F) ^ i)
      (WittVector.teichmuller p zb ^ j * WittVector.teichmuller p c'),
    map_mul (algebraMap (Ainf p F) (Bloc p F ϖ))
      (WittVector.teichmuller p zb ^ j) (WittVector.teichmuller p c')]
  generalize hA : algebraMap (Ainf p F) (Bloc p F ϖ)
    (WittVector.teichmuller p zb ^ j) = A
  generalize hP2 : algebraMap (Ainf p F) (Bloc p F ϖ)
    ((p : Ainf p F) ^ (m * j)) = P2 at hcancel ⊢
  generalize hV : (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ) ^ (m * j)
    = V at hcancel ⊢
  generalize hP1 : algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ i)
    = P1
  generalize hC : algebraMap (Ainf p F) (Bloc p F ϖ)
    (WittVector.teichmuller p c') = C
  calc A * V * (P1 * P2 * C) = P1 * (A * C) * (P2 * V) := by ring
    _ = P1 * (A * C) := by rw [hcancel, mul_one]

/-- **The maximal-twist normalization** (Kedlaya's `j`-choice, in the
integral-coordinate direction): a nonzero integral coordinate factors as
`zb^j · c'` with the cofactor's value strictly above `|zb|`. -/
theorem exists_twist (zb c : OF F)
    (hzb0 : perfectoidValuation p F (zb : F) ≠ 0)
    (hzb1 : perfectoidValuation p F (zb : F) < 1)
    (hc0 : perfectoidValuation p F (c : F) ≠ 0) :
    ∃ (j : ℕ) (c' : OF F), c = zb ^ j * c'
      ∧ perfectoidValuation p F (zb : F)
        < perfectoidValuation p F (c' : F) := by
  have hcpos : 0 < perfectoidValuation p F (c : F) :=
    pos_iff_ne_zero.mpr hc0
  -- some power of `zb` drops strictly below `|c|`
  obtain ⟨j₀, hj₀⟩ := NNReal.exists_pow_lt_of_lt_one hcpos hzb1
  -- the largest `j ≤ j₀` with `|c| ≤ |zb|^j`
  set P : ℕ → Prop := fun j => perfectoidValuation p F (c : F)
    ≤ perfectoidValuation p F (zb : F) ^ j with hP
  have hP0 : P 0 := by
    show perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F (zb : F) ^ 0
    rw [pow_zero]
    exact perfectoidValuation_le_one p F c
  have hnot : ¬ P j₀ := by
    show ¬ (perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F (zb : F) ^ j₀)
    exact not_le.mpr hj₀
  set j := Nat.findGreatest P j₀ with hj
  have hPj : P j := Nat.findGreatest_spec (Nat.zero_le j₀) hP0
  have hjlt : j < j₀ := by
    rcases lt_or_eq_of_le (Nat.findGreatest_le (P := P) j₀) with h | h
    · exact h
    · exact absurd (h ▸ hPj) hnot
  have hnext : ¬ P (j + 1) := by
    intro hcon
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self j)
      (Nat.succ_le_of_lt hjlt) hcon
  -- divisibility from the value comparison
  have hdvd := (perfectoidValuation_integers p F).dvd_of_le
    (x := c) (y := zb ^ j) ?_
  · obtain ⟨c', hc'⟩ := hdvd
    refine ⟨j, c', hc', ?_⟩
    -- multiplicativity gives |c| = |zb|^j·|c'|; maximality gives the bound
    have hval : perfectoidValuation p F (c : F)
        = perfectoidValuation p F (zb : F) ^ j
          * perfectoidValuation p F (c' : F) := by
      rw [hc']
      rw [show ((zb ^ j * c' : OF F) : F) = ((zb : F)) ^ j * (c' : F) from by
        push_cast; rfl]
      rw [Valuation.map_mul, map_pow]
    have hnext' : ¬ (perfectoidValuation p F (c : F)
        ≤ perfectoidValuation p F (zb : F) ^ (j + 1)) := hnext
    have hlt : perfectoidValuation p F (zb : F) ^ (j + 1)
        < perfectoidValuation p F (c : F) := not_le.mp hnext
    rw [hval, pow_succ] at hlt
    have hzjpos : 0 < perfectoidValuation p F (zb : F) ^ j :=
      pow_pos (pos_iff_ne_zero.mpr hzb0) j
    exact lt_of_mul_lt_mul_left (by rwa [mul_comm] at hlt ⊢) zero_le
  · show perfectoidValuation p F
        ((algebraMap ↥(powerBoundedSubring.toSubring F) F) c)
      ≤ perfectoidValuation p F
        ((algebraMap ↥(powerBoundedSubring.toSubring F) F) (zb ^ j))
    rw [show ((algebraMap ↥(powerBoundedSubring.toSubring F) F) c)
        = (c : F) from rfl,
      show ((algebraMap ↥(powerBoundedSubring.toSubring F) F) (zb ^ j))
        = ((zb : OF F) : F) ^ j from by push_cast; rfl,
      map_pow]
    exact hPj

/-- **The twist reaches within one generator-step of the denominator**: under
the `σ₁`-Gauss bound (in the `m`-th-power multiplicative form
`|c|^m ≤ |zb|^{k−i}`), the maximal twist depth `j` satisfies
`i + m·j + m > k` — the residual denominator-dominance is less than one
generator-step. -/
theorem exists_twist_deep (zb c : OF F) (m : ℕ) (hm : 0 < m)
    (hzb0 : perfectoidValuation p F (zb : F) ≠ 0)
    (hzb1 : perfectoidValuation p F (zb : F) < 1)
    (hc0 : perfectoidValuation p F (c : F) ≠ 0) (i k : ℕ)
    (hcm : perfectoidValuation p F (c : F) ^ m
      ≤ perfectoidValuation p F (zb : F) ^ (k - i)) :
    ∃ (j : ℕ) (c' : OF F), c = zb ^ j * c'
      ∧ k < i + m * j + m
      ∧ perfectoidValuation p F (zb : F)
        < perfectoidValuation p F (c' : F) := by
  obtain ⟨j, c', hc', hlt⟩ := exists_twist p F zb c hzb0 hzb1 hc0
  refine ⟨j, c', hc', ?_, hlt⟩
  -- maximality: |c| > |zb|^{j+1}
  have hmax : perfectoidValuation p F (zb : F) ^ (j + 1)
      < perfectoidValuation p F (c : F) := by
    have hval : perfectoidValuation p F (c : F)
        = perfectoidValuation p F (zb : F) ^ j
          * perfectoidValuation p F (c' : F) := by
      rw [hc']
      rw [show ((zb ^ j * c' : OF F) : F) = ((zb : F)) ^ j * (c' : F) from by
        push_cast; rfl]
      rw [Valuation.map_mul, map_pow]
    rw [hval, pow_succ]
    exact mul_lt_mul_of_pos_left hlt
      (pos_iff_ne_zero.mpr (pow_ne_zero _ hzb0))
  -- power comparison: |zb|^{m(j+1)} < |c|^m ≤ |zb|^{k−i}
  have hpow : perfectoidValuation p F (zb : F) ^ (m * (j + 1))
      < perfectoidValuation p F (zb : F) ^ (k - i) := by
    calc perfectoidValuation p F (zb : F) ^ (m * (j + 1))
        = (perfectoidValuation p F (zb : F) ^ (j + 1)) ^ m := by
          rw [← pow_mul, mul_comm]
      _ < perfectoidValuation p F (c : F) ^ m := by
          exact pow_lt_pow_left₀ hmax zero_le (Nat.pos_iff_ne_zero.mp hm)
      _ ≤ perfectoidValuation p F (zb : F) ^ (k - i) := hcm
  -- exponent reversal for a base < 1
  have hexp : k - i < m * (j + 1) := by
    by_contra hcon
    push Not at hcon
    exact absurd (pow_le_pow_of_le_one zero_le hzb1.le hcon)
      (not_le.mpr hpow)
  have hexp' : k - i < m * j + m := by
    rw [Nat.mul_succ] at hexp
    exact hexp
  omega

/-- The Gauss value of the monomial `p^i·[c]`. -/
theorem gaussValue_p_pow_mul_teichmuller {ρ : NNReal} (hρ1 : ρ ≤ 1)
    (i : ℕ) (c : OF F) :
    gaussValue p F ρ ((p : Ainf p F) ^ i * WittVector.teichmuller p c)
      = ρ ^ i * perfectoidValuation p F (c : F) := by
  induction i with
  | zero =>
    rw [pow_zero, one_mul, pow_zero, one_mul,
      gaussValue_teichmuller p F hρ1]
  | succ n ih =>
    rw [show (p : Ainf p F) ^ (n + 1) * WittVector.teichmuller p c
        = (p : Ainf p F) * ((p : Ainf p F) ^ n
          * WittVector.teichmuller p c) from by ring,
      gaussValue_p_mul p F hρ1, ih, pow_succ]
    ring

/-- The localized norm of the monomial fraction `p^i[c]/(p[ϖ])^k`. -/
theorem wLoc_mk'_monomial {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (i k : ℕ) (c : OF F) :
    wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k))
      = ρ ^ i * perfectoidValuation p F (c : F)
        * (((ρ * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k)⁻¹) := by
  rw [wLoc_mk' p F ϖ hρ0 hρ1, gaussValue_sPow p F ϖ hρ0 hρ1 k,
    gaussValue_p_pow_mul_teichmuller p F hρ1.le]

/-- **The twisted factorization of a monomial fraction**: extracting `zb^j`
from the Teichmüller coordinate is multiplication by the generator's `j`-th
power. -/
theorem mk'_monomial_twist_factor (zb : OF F) (m : ℕ) (i j k : ℕ)
    (c c' : OF F) (hc : c = zb ^ j * c') :
    IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
      = teichPowGen p F ϖ zb m ^ j
        * IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ (i + m * j) * WittVector.teichmuller p c')
          (sPow p F ϖ k) := by
  rw [show IsLocalization.mk' (Bloc p F ϖ)
      ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
    = algebraMap (Ainf p F) (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p c)
      * IsLocalization.mk' (Bloc p F ϖ) 1 (sPow p F ϖ k) from
    IsLocalization.mk'_eq_mul_mk'_one _ _]
  rw [show IsLocalization.mk' (Bloc p F ϖ)
      ((p : Ainf p F) ^ (i + m * j) * WittVector.teichmuller p c')
      (sPow p F ϖ k)
    = algebraMap (Ainf p F) (Bloc p F ϖ)
        ((p : Ainf p F) ^ (i + m * j) * WittVector.teichmuller p c')
      * IsLocalization.mk' (Bloc p F ϖ) 1 (sPow p F ϖ k) from
    IsLocalization.mk'_eq_mul_mk'_one _ _]
  calc algebraMap (Ainf p F) (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p c)
        * IsLocalization.mk' (Bloc p F ϖ) 1 (sPow p F ϖ k)
      = (teichPowGen p F ϖ zb m ^ j
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            ((p : Ainf p F) ^ (i + m * j) * WittVector.teichmuller p c'))
          * IsLocalization.mk' (Bloc p F ϖ) 1 (sPow p F ϖ k) := by
        rw [teichPowGen_pow_mul_twist p F ϖ zb m i j c c' hc]
    _ = teichPowGen p F ϖ zb m ^ j
        * (algebraMap (Ainf p F) (Bloc p F ϖ)
            ((p : Ainf p F) ^ (i + m * j) * WittVector.teichmuller p c')
          * IsLocalization.mk' (Bloc p F ϖ) 1 (sPow p F ϖ k)) := by
        ring

/-- **The zone-dispatched twist data of a monomial coordinate**: in the
numerator zone no twist; in the denominator zone the deficit-bounded maximal
twist supplied by the `σ₁`-Gauss bound. -/
theorem exists_monomial_twist_data (zb : OF F) (m : ℕ) (hm : 0 < m)
    (hzb0 : perfectoidValuation p F (zb : F) ≠ 0)
    (hzb1 : perfectoidValuation p F (zb : F) < 1)
    (i k : ℕ) (c : OF F) (hc0 : perfectoidValuation p F (c : F) ≠ 0)
    (hcm : i < k → perfectoidValuation p F (c : F) ^ m
      ≤ perfectoidValuation p F (zb : F) ^ (k - i)) :
    ∃ (j : ℕ) (c' : OF F), c = zb ^ j * c'
      ∧ perfectoidValuation p F (c' : F) ≠ 0
      ∧ (i < k → (k < i + m * j + m
          ∧ perfectoidValuation p F (zb : F)
            < perfectoidValuation p F (c' : F)))
      ∧ (k ≤ i → j = 0) := by
  by_cases hik : i < k
  · obtain ⟨j, c', hc', hdeep, hlt⟩ := exists_twist_deep p F zb c m hm
      hzb0 hzb1 hc0 i k (hcm hik)
    refine ⟨j, c', hc', ?_, fun _ => ⟨hdeep, hlt⟩, fun hk => absurd hik
      (not_lt.mpr hk)⟩
    intro h0
    have hval : perfectoidValuation p F (c : F)
        = perfectoidValuation p F (zb : F) ^ j
          * perfectoidValuation p F (c' : F) := by
      rw [hc']
      rw [show ((zb ^ j * c' : OF F) : F) = ((zb : F)) ^ j * (c' : F) from by
        push_cast; rfl]
      rw [Valuation.map_mul, map_pow]
    rw [hval, h0, mul_zero] at hc0
    exact hc0 rfl
  · refine ⟨0, c, by rw [pow_zero, one_mul], hc0,
      fun h => absurd h hik, fun _ => rfl⟩

/-- **The floor-division twist**: under the direct divisibility bound the
coordinate factors through `zb^{(k−i)/m}`, with the twisted exponent landing
in the window `(k − m, k]` — no overshoot. -/
theorem exists_monomial_twist_div (zb : OF F) (m : ℕ) (hm : 0 < m)
    (i k : ℕ) (c : OF F)
    (hdvd : perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F (zb : F) ^ ((k - i) / m)) :
    ∃ c' : OF F, c = zb ^ ((k - i) / m) * c'
      ∧ k < i + m * ((k - i) / m) + m := by
  have hdv := (perfectoidValuation_integers p F).dvd_of_le
    (x := c) (y := zb ^ ((k - i) / m)) ?_
  · obtain ⟨c', hc'⟩ := hdv
    refine ⟨c', hc', ?_⟩
    have hdm := Nat.div_add_mod (k - i) m
    have hmod := Nat.mod_lt (k - i) hm
    omega
  · show perfectoidValuation p F
        ((algebraMap ↥(powerBoundedSubring.toSubring F) F) c)
      ≤ perfectoidValuation p F
        ((algebraMap ↥(powerBoundedSubring.toSubring F) F)
          (zb ^ ((k - i) / m)))
    rw [show ((algebraMap ↥(powerBoundedSubring.toSubring F) F) c)
        = (c : F) from rfl,
      show ((algebraMap ↥(powerBoundedSubring.toSubring F) F)
          (zb ^ ((k - i) / m)))
        = ((zb : OF F) : F) ^ ((k - i) / m) from by push_cast; rfl,
      map_pow]
    exact hdvd

/-- Cross-multiplied radial monotonicity: for `a ≤ b` and `k ≤ n`,
`a^n b^k ≤ b^n a^k` — the engine of all zone norm-comparisons. -/
theorem pow_mul_pow_le_of_le {a b : NNReal} (hab : a ≤ b) {k n : ℕ}
    (hkn : k ≤ n) : a ^ n * b ^ k ≤ b ^ n * a ^ k := by
  have h1 : a ^ n = a ^ k * a ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : b ^ n = b ^ k * b ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  calc a ^ n * b ^ k = a ^ k * b ^ k * a ^ (n - k) := by rw [h1]; ring
    _ ≤ a ^ k * b ^ k * b ^ (n - k) :=
        mul_le_mul_right (pow_le_pow_left' hab _) _
    _ = b ^ n * a ^ k := by rw [h2]; ring

omit [CharP F p] in
/-- The value of a `zb^j`-factored coordinate. -/
theorem perfectoidValuation_twist_factor (zb c c' : OF F) (j : ℕ)
    (hfact : c = zb ^ j * c') :
    perfectoidValuation p F (c : F)
      = perfectoidValuation p F (zb : F) ^ j
        * perfectoidValuation p F (c' : F) := by
  rw [hfact]
  rw [show ((zb ^ j * c' : OF F) : F) = ((zb : F)) ^ j * (c' : F) from by
    push_cast; rfl]
  rw [Valuation.map_mul, map_pow]

/-- **The zone norm-comparison, formula level** (denominator zone): the
twisted monomial's values at the outer radii are controlled by the original
at the cut radius — exactly at the top, by the `m`-step constant at the
bottom. -/
theorem twisted_formula_le {ρ₁ σ₁ ρ₂ V vc vc' : NNReal}
    (hρ₁0 : 0 < ρ₁) (hσ₁0 : 0 < σ₁) (hρ₂0 : 0 < ρ₂) (hV0 : 0 < V)
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂) {m i k j : ℕ}
    (hval : vc = σ₁ ^ (m * j) * vc') (he : i + m * j ≤ k)
    (hwin : k < i + m * j + m) :
    ρ₂ ^ (i + m * j) * vc' * (((ρ₂ * V) ^ k)⁻¹)
      ≤ σ₁ ^ i * vc * (((σ₁ * V) ^ k)⁻¹)
    ∧ ρ₁ ^ (i + m * j) * vc' * (((ρ₁ * V) ^ k)⁻¹)
      ≤ σ₁ ^ m * ((ρ₁ ^ m)⁻¹)
        * (σ₁ ^ i * vc * (((σ₁ * V) ^ k)⁻¹)) := by
  have hfold : σ₁ ^ i * vc = σ₁ ^ (i + m * j) * vc' := by
    rw [hval, pow_add]
    ring
  have hρ₂V : (0 : NNReal) < (ρ₂ * V) ^ k :=
    pow_pos (mul_pos hρ₂0 hV0) k
  have hσ₁V : (0 : NNReal) < (σ₁ * V) ^ k :=
    pow_pos (mul_pos hσ₁0 hV0) k
  have hρ₁V : (0 : NNReal) < (ρ₁ * V) ^ k :=
    pow_pos (mul_pos hρ₁0 hV0) k
  constructor
  · rw [hfold, mul_comm (ρ₂ ^ (i + m * j)) vc',
      mul_comm (σ₁ ^ (i + m * j)) vc', mul_assoc, mul_assoc]
    refine mul_le_mul_right ?_ vc'
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hρ₂V hσ₁V]
    calc ρ₂ ^ (i + m * j) * (σ₁ * V) ^ k
        = (σ₁ ^ k * ρ₂ ^ (i + m * j)) * V ^ k := by rw [mul_pow]; ring
      _ ≤ (ρ₂ ^ k * σ₁ ^ (i + m * j)) * V ^ k :=
          mul_le_mul_left (pow_mul_pow_le_of_le hσρ he) _
      _ = σ₁ ^ (i + m * j) * (ρ₂ * V) ^ k := by rw [mul_pow]; ring
  · rw [hfold, mul_comm (ρ₁ ^ (i + m * j)) vc', mul_assoc]
    rw [show σ₁ ^ m * ((ρ₁ ^ m)⁻¹) * (σ₁ ^ (i + m * j) * vc'
          * (((σ₁ * V) ^ k)⁻¹))
        = vc' * (σ₁ ^ (i + m * j + m)
          * ((ρ₁ ^ m * (σ₁ * V) ^ k)⁻¹)) from by
      rw [pow_add (σ₁) (i + m * j) m, mul_inv]
      ring]
    refine mul_le_mul_right ?_ vc'
    rw [← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ hρ₁V
        (mul_pos (pow_pos hρ₁0 m) (pow_pos (mul_pos hσ₁0 hV0) k))]
    calc ρ₁ ^ (i + m * j) * (ρ₁ ^ m * (σ₁ * V) ^ k)
        = (ρ₁ ^ (i + m * j + m) * σ₁ ^ k) * V ^ k := by
          rw [mul_pow, pow_add (ρ₁) (i + m * j) m]
          ring
      _ ≤ (σ₁ ^ (i + m * j + m) * ρ₁ ^ k) * V ^ k :=
          mul_le_mul_left (pow_mul_pow_le_of_le hρσ hwin.le) _
      _ = σ₁ ^ (i + m * j + m) * (ρ₁ * V) ^ k := by
          rw [mul_pow]
          ring

/-- **The numerator-zone comparison**: for `k ≤ i` the monomial's value at
the inner radius is dominated by its value at the cut radius. -/
theorem numerator_formula_le {ρ₁ σ₁ V vc : NNReal}
    (hρ₁0 : 0 < ρ₁) (hσ₁0 : 0 < σ₁) (hV0 : 0 < V)
    (hρσ : ρ₁ ≤ σ₁) {i k : ℕ} (hki : k ≤ i) :
    ρ₁ ^ i * vc * (((ρ₁ * V) ^ k)⁻¹)
      ≤ σ₁ ^ i * vc * (((σ₁ * V) ^ k)⁻¹) := by
  have hρ₁V : (0 : NNReal) < (ρ₁ * V) ^ k :=
    pow_pos (mul_pos hρ₁0 hV0) k
  have hσ₁V : (0 : NNReal) < (σ₁ * V) ^ k :=
    pow_pos (mul_pos hσ₁0 hV0) k
  rw [mul_comm (ρ₁ ^ i) vc, mul_comm (σ₁ ^ i) vc, mul_assoc, mul_assoc]
  refine mul_le_mul_right ?_ vc
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hρ₁V hσ₁V]
  calc ρ₁ ^ i * (σ₁ * V) ^ k
      = (ρ₁ ^ i * σ₁ ^ k) * V ^ k := by rw [mul_pow]; ring
    _ ≤ (σ₁ ^ i * ρ₁ ^ k) * V ^ k :=
        mul_le_mul_left (pow_mul_pow_le_of_le hρσ hki) _
    _ = σ₁ ^ i * (ρ₁ * V) ^ k := by rw [mul_pow]; ring

/-- **The per-monomial lift package**: every monomial fraction with the
cut-radius divisibility factors through a generator power, with the cofactor
controlled at the outer radii by the original at the `σ`-radii. -/
theorem exists_monomial_lift_package {ρ₁ σ₁ ρ₂ : NNReal}
    (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hσ₁0 : 0 < σ₁) (hσ₁1 : σ₁ < 1)
    (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m : ℕ) (hm : 0 < m)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m)
    (i k : ℕ) (c : OF F)
    (hdvd : i < k → perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F (zb : F) ^ ((k - i) / m)) :
    ∃ (j : ℕ) (e : ℕ) (c' : OF F),
      IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
        = teichPowGen p F ϖ zb m ^ j
          * IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ e * WittVector.teichmuller p c')
            (sPow p F ϖ k)
      ∧ wLoc p F ϖ hρ₁0 hρ₁1 (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ e * WittVector.teichmuller p c')
          (sPow p F ϖ k))
        ≤ σ₁ ^ m * ((ρ₁ ^ m)⁻¹)
          * (wLoc p F ϖ hσ₁0 hσ₁1 (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ i * WittVector.teichmuller p c)
            (sPow p F ϖ k)))
      ∧ wLoc p F ϖ hρ₂0 hρ₂1 (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ e * WittVector.teichmuller p c')
          (sPow p F ϖ k))
        ≤ max (wLoc p F ϖ hσ₁0 hσ₁1 (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ i * WittVector.teichmuller p c)
            (sPow p F ϖ k)))
          (wLoc p F ϖ hρ₂0 hρ₂1 (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ i * WittVector.teichmuller p c)
            (sPow p F ϖ k))) := by
  have hK1 : (1 : NNReal) ≤ σ₁ ^ m * ((ρ₁ ^ m)⁻¹) :=
    calc (1 : NNReal) = ρ₁ ^ m * ((ρ₁ ^ m)⁻¹) :=
        (mul_inv_cancel₀ (pow_pos hρ₁0 m).ne').symm
      _ ≤ σ₁ ^ m * ((ρ₁ ^ m)⁻¹) :=
        mul_le_mul_left (pow_le_pow_left' hρσ m) _
  by_cases hik : i < k
  · obtain ⟨c', hfact, hwin⟩ := exists_monomial_twist_div p F zb m hm i k c
      (hdvd hik)
    set j := (k - i) / m with hj
    have he : i + m * j ≤ k := by
      have h1 : j * m ≤ k - i := Nat.div_mul_le_self (k - i) m
      have h2 : m * j ≤ k - i := by rwa [mul_comm]
      omega
    have hval : perfectoidValuation p F (c : F)
        = σ₁ ^ (m * j) * perfectoidValuation p F (c' : F) := by
      rw [perfectoidValuation_twist_factor p F zb c c' j hfact, hgen,
        ← pow_mul]
    have hcmp := twisted_formula_le (V := perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F))
      (vc := perfectoidValuation p F (c : F))
      (vc' := perfectoidValuation p F (c' : F))
      hρ₁0 hσ₁0 hρ₂0 (vpi_pos p F ϖ) hρσ hσρ (m := m) (i := i) (k := k)
      (j := j) hval he hwin
    refine ⟨j, i + m * j, c',
      mk'_monomial_twist_factor p F ϖ zb m i j k c c' hfact, ?_, ?_⟩
    · rw [wLoc_mk'_monomial p F ϖ hρ₁0 hρ₁1,
        wLoc_mk'_monomial p F ϖ hσ₁0 hσ₁1]
      exact hcmp.2
    · rw [wLoc_mk'_monomial p F ϖ hρ₂0 hρ₂1 (i + m * j) k c',
        wLoc_mk'_monomial p F ϖ hσ₁0 hσ₁1 i k c]
      exact le_trans hcmp.1 (le_max_left _ _)
  · refine ⟨0, i, c, ?_, ?_, ?_⟩
    · rw [pow_zero, one_mul]
    · rw [wLoc_mk'_monomial p F ϖ hρ₁0 hρ₁1,
        wLoc_mk'_monomial p F ϖ hσ₁0 hσ₁1]
      refine le_trans (numerator_formula_le hρ₁0 hσ₁0 (vpi_pos p F ϖ)
        hρσ (not_lt.mp hik)) ?_
      exact le_mul_of_one_le_left zero_le hK1
    · exact le_max_right _ _

/-- **The cut-radius Gauss bound supplies the twist divisibility**: for a
`σ₁`-bounded fraction, every denominator-zone Teichmüller coordinate is
divisible to the floor-division depth. -/
theorem monomial_dvd_of_wLoc_le_one {σ₁ : NNReal}
    (hσ₁0 : 0 < σ₁) (hσ₁1 : σ₁ < 1)
    (zb : OF F) (m : ℕ)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m)
    (w : Ainf p F) (k : ℕ)
    (hw : wLoc p F ϖ hσ₁0 hσ₁1
      (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k)) ≤ 1)
    (i : ℕ) (hik : i < k) :
    perfectoidValuation p F ((teichCoeff p F w i : OF F) : F)
      ≤ perfectoidValuation p F (zb : F) ^ ((k - i) / m) := by
  have hterm := gaussTerm_le_of_wLoc_mk'_le_one p F ϖ hσ₁0 hσ₁1 w k hw i
  -- σ₁^i·v(c) ≤ (σ₁·V)^k ⇒ v(c) ≤ σ₁^{k−i}·V^k
  have hstep : perfectoidValuation p F ((teichCoeff p F w i : OF F) : F)
      ≤ σ₁ ^ (k - i)
        * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k := by
    have hsplit : (σ₁ * perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k
        = σ₁ ^ i * (σ₁ ^ (k - i)
          * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k) := by
      rw [mul_pow, show σ₁ ^ k = σ₁ ^ i * σ₁ ^ (k - i) from by
        rw [← pow_add]
        congr 1
        omega]
      ring
    rw [hsplit] at hterm
    exact le_of_mul_le_mul_left hterm (pow_pos hσ₁0 i)
  refine le_trans hstep ?_
  calc σ₁ ^ (k - i)
      * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k
      ≤ σ₁ ^ (k - i) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        exact pow_le_one₀ zero_le (perfectoidValuation_toOF_lt_one p F ϖ).le
    _ = σ₁ ^ (k - i) := mul_one _
    _ ≤ σ₁ ^ (m * ((k - i) / m)) := by
        refine pow_le_pow_of_le_one zero_le hσ₁1.le ?_
        have h1 : ((k - i) / m) * m ≤ k - i := Nat.div_mul_le_self (k - i) m
        have h2 : m * ((k - i) / m) ≤ k - i := by rwa [mul_comm]
        exact h2
    _ = perfectoidValuation p F (zb : F) ^ ((k - i) / m) := by
        rw [hgen, ← pow_mul]

/-- The interval restriction carries `Bloc`-images to `Bloc`-images. -/
theorem resIHom_blocToBI {θ η : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (hσ₂0 : 0 < ρ₁ ^ η * ρ₂ ^ (1 - η)) (hσ₂1 : ρ₁ ^ η * ρ₂ ^ (1 - η) < 1)
    (x : Bloc p F ϖ) :
    ((resIHom p F ϖ hθ0 hθ1 hη0 hη1 hσ₁0 hσ₁1 hσ₂0 hσ₂1
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
        : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
      = BIProd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 x := by
  refine Prod.ext ?_ ?_
  · show resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1
        ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = (BIProd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 x).1
    rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x from rfl]
    rw [resI_BIProd p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 x,
      BIProd_fst p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 x]
  · show resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₂0 hσ₂1
        ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = (BIProd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 x).2
    rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x from rfl]
    rw [resI_BIProd p F ϖ hη0 hη1 hσ₂0 hσ₂1 x,
      BIProd_snd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 x]

/-- Each monomial's localized norm is bounded by the element's. -/
theorem wLoc_mk'_monomial_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (w : Ainf p F) (k i : ℕ) :
    wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p (teichCoeff p F w i))
        (sPow p F ϖ k))
      ≤ wLoc p F ϖ hρ0 hρ1
          (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k)) := by
  rw [wLoc_mk'_monomial p F ϖ hρ0 hρ1, wLoc_mk' p F ϖ hρ0 hρ1,
    gaussValue_sPow p F ϖ hρ0 hρ1 k]
  refine mul_le_mul_left ?_ _
  exact le_ciSup (bddAbove_range_gaussTerm p F hρ1.le w) i

/-- Monomials over `B^I` are restricted. -/
theorem isRestricted_monomial_BI {J : Fin k →₀ ℕ}
    (a : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    MvPowerSeries.IsRestricted
      (MvPowerSeries.monomial J a
        : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  rw [MvPowerSeries.IsRestricted, Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_cofinite]
  refine (Set.finite_singleton J).subset ?_
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  by_contra hne
  rw [Set.mem_singleton_iff] at hne
  refine hs ?_
  rw [MvPowerSeries.coeff_monomial, if_neg hne]
  exact mem_of_mem_nhds hU

section EvalBIMonomial

variable {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
  {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))

/-- **The evaluation of a monomial**: `y·T^l ↦ φ(y)·b^l`. -/
theorem evalBI_monomial {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1) (l : ℕ)
    (y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hres : MvPowerSeries.IsRestricted
      (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) l) y)) :
    evalBI p F ϖ φ hφ hbmem hb ⟨_, hres⟩
      = ((φ y : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l := by
  classical
  refine tendsto_nhds_unique (tendsto_evalBI p F ϖ φ hφ hbmem hb ⟨_, hres⟩) ?_
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨l + 1, fun n hn => ?_⟩
  have hterm : ∀ m ∈ Finset.range n,
      evalBITerm p F ϖ φ b
          (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) l)
            (y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) m
        = if m = l then ((φ y : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
            : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l
          else 0 := by
    intro m _
    rw [evalBITerm]
    have hcoeff : coeffSeq (MvPowerSeries.monomial
        (Finsupp.single (0 : Fin 1) l)
        (y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) m
        = if m = l then y else 0 := by
      rw [coeffSeq, MvPowerSeries.coeff_monomial]
      by_cases hm : m = l
      · subst hm
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hm, if_neg]
        intro hcon
        exact hm ((Finsupp.single_injective (0 : Fin 1)) hcon)
    rw [hcoeff]
    by_cases hm : m = l
    · subst hm
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hm, if_neg hm, φ.map_zero]
      show (0 : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ m = 0
      rw [zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range n) l
    (fun _ => ((φ y : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) * b ^ l),
    if_pos (Finset.mem_range.mpr (by omega))]

end EvalBIMonomial

/-- The interval Gauss norm of a monomial. -/
theorem wIRPS_monomial (J : Fin k →₀ ℕ)
    (y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (MvPowerSeries.monomial J y
          : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
  refine le_antisymm (ciSup_le fun s => ?_) ?_
  · rw [MvPowerSeries.coeff_monomial]
    by_cases hs : s = J
    · rw [if_pos hs]
    · rw [if_neg hs]
      rw [show (((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 0 from rfl,
        wI_zero p F]
      exact zero_le
  · have h := le_ciSup (bddAbove_wIRPS p F ϖ
      (isRestricted_monomial_BI p F ϖ (J := J) y)) J
    rw [MvPowerSeries.coeff_monomial, if_pos rfl] at h
    exact h

/-- Ultrametric bound for sums of restricted series. -/
theorem wIRPS_add_le
    {f g : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) (hg : MvPowerSeries.IsRestricted g) :
    wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (f + g)
      ≤ max (wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 f)
          (wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 g) := by
  refine ciSup_le fun s => ?_
  rw [map_add, BISub_coe_add p F ϖ]
  refine le_trans (wI_add_le p F _ _) (max_le_max ?_ ?_)
  · exact wI_coeff_le_wIRPS p F ϖ hf s
  · exact wI_coeff_le_wIRPS p F ϖ hg s

/-- The interval Gauss norm of a finite sum of restricted series is bounded
by any common bound. -/
theorem wIRPS_finset_sum_le {ι : Type*} (s : Finset ι)
    (f : ι → ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (B : NNReal)
    (hf : ∀ i ∈ s, wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((f i : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ≤ B) :
    wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (((∑ i ∈ s, f i : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hzero : ((0 : ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin k)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) = 0 := rfl
    rw [Finset.sum_empty, hzero, wIRPS_zero]
    exact zero_le
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have hcoe : (((f a + ∑ i ∈ t, f i
          : ↥(restrictedMvPowerSeriesSubring k
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))))
          : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        = ((f a : ↥(restrictedMvPowerSeriesSubring k
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          + ((∑ i ∈ t, f i : ↥(restrictedMvPowerSeriesSubring k
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin k)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := rfl
    rw [hcoe]
    refine le_trans (wIRPS_add_le p F ϖ (f a).2
      (∑ i ∈ t, f i).2) (max_le (hf a (Finset.mem_insert_self a t)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

section EvalBISum

variable {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
  {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))

include hφ in
/-- Evaluation commutes with finite sums. -/
theorem evalBI_finset_sum {ι : Type*} (s : Finset ι)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 b ≤ 1)
    (g : ι → ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    evalBI p F ϖ φ hφ hbmem hb (∑ i ∈ s, g i)
      = ∑ i ∈ s, evalBI p F ϖ φ hφ hbmem hb (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact evalBI_zero p F ϖ φ hφ hbmem hb
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalBI_add p F ϖ φ hφ hbmem hb, ih]

end EvalBISum

end FarguesFontaine

end
