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


/-! ### The first approximation (T910 case 1, the Kedlaya lift) -/

section Assembly

variable {σ₁ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
variable (hφb : ∀ x : Bloc p F ϖ,
  ((φ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
    : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
    : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x)

include hφb in
/-- **The first approximation** (T910 case 1, the Kedlaya lift on the dense
layer): a doubly-bounded fraction is approximated to any accuracy by the
evaluation of a `T`-polynomial with `K`-controlled coefficients. -/
theorem exists_evalBI_approx_bloc
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m : ℕ) (hm : 0 < m)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m))
    (w : Ainf p F) (k : ℕ) {W : NNReal} (hWle : W ≤ 1)
    (hw1 : wLoc p F ϖ hσ₁0 hσ₁1
      (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k)) ≤ W)
    (hw2 : wLoc p F ϖ hρ₂0 hρ₂1
      (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k)) ≤ W)
    {ε : NNReal} (hε : 0 < ε) :
    ∃ f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
        (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k))
        - evalBI p F ϖ φ hφ hbmem hb f) ≤ ε
      ∧ wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        ≤ σ₁ ^ m * ((ρ₁ ^ m)⁻¹) * W := by
  -- the tail cutoffs, one per σ-radius
  have hD1 : (0 : NNReal) < ε * ((σ₁ * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k) :=
    mul_pos hε (pow_pos (mul_pos hσ₁0 (vpi_pos p F ϖ)) k)
  have hD2 : (0 : NNReal) < ε * ((ρ₂ * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k) :=
    mul_pos hε (pow_pos (mul_pos hρ₂0 (vpi_pos p F ϖ)) k)
  obtain ⟨N₁, hN₁⟩ := NNReal.exists_pow_lt_of_lt_one hD1 hσ₁1
  obtain ⟨N₂, hN₂⟩ := NNReal.exists_pow_lt_of_lt_one hD2 hρ₂1
  set N := max N₁ N₂ with hNdef
  -- the head/tail split
  obtain ⟨w', hwd⟩ :=
    WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff w N
  have hsplit := mk'_sPow_split p F ϖ w k N w' hwd
  -- per-monomial data
  choose Jf Ef Cf hfact hbnd1 hbnd2 using fun i : ℕ =>
    exists_monomial_lift_package p F ϖ hρ₁0 hρ₁1 hσ₁0 hσ₁1 hρ₂0 hρ₂1
      hρσ hσρ zb m hm hgen i k (teichCoeff p F w i)
      (fun hik => monomial_dvd_of_wLoc_le_one p F ϖ hσ₁0 hσ₁1 zb m hgen
        w k (le_trans hw1 hWle) i hik)
  refine ⟨∑ i ∈ Finset.Iic N,
    ⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) (Jf i))
      (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ (Ef i) * WittVector.teichmuller p (Cf i))
          (sPow p F ϖ k))),
      isRestricted_monomial_BI p F ϖ _⟩, ?_, ?_⟩
  · -- the residual
    rw [evalBI_finset_sum p F ϖ φ hφ]
    have hterm : ∀ i ∈ Finset.Iic N,
        evalBI p F ϖ φ hφ hbmem hb
          ⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) (Jf i))
            (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
              (IsLocalization.mk' (Bloc p F ϖ)
                ((p : Ainf p F) ^ (Ef i)
                  * WittVector.teichmuller p (Cf i))
                (sPow p F ϖ k))),
            isRestricted_monomial_BI p F ϖ _⟩
          = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
              (IsLocalization.mk' (Bloc p F ϖ)
                ((p : Ainf p F) ^ i
                  * WittVector.teichmuller p (teichCoeff p F w i))
                (sPow p F ϖ k)) := by
      intro i _
      rw [evalBI_monomial p F ϖ φ hφ hbmem hb]
      rw [hφb, hbg, ← map_pow (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1),
        ← map_mul (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)]
      congr 1
      rw [mul_comm]
      exact (hfact i).symm
    rw [Finset.sum_congr rfl hterm]
    rw [← map_sum (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)]
    rw [show BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k))
        - BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ i
              * WittVector.teichmuller p (teichCoeff p F w i))
            (sPow p F ϖ k))
      = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ (N + 1) * w') (sPow p F ϖ k)) from by
      rw [← map_sub (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)]
      congr 1
      rw [hsplit]
      ring]
    rw [wI_BIProd p F ϖ]
    rw [valued_BlocToHatK p F ϖ, valued_BlocToHatK p F ϖ]
    refine max_le ?_ ?_
    · refine le_trans (wLoc_mk'_tail_le p F ϖ hσ₁0 hσ₁1 k N w') ?_
      rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos (mul_pos hσ₁0
        (vpi_pos p F ϖ)) k)]
      calc σ₁ ^ (N + 1)
          ≤ σ₁ ^ N₁ := pow_le_pow_of_le_one zero_le hσ₁1.le
            (le_trans (le_max_left _ _) (Nat.le_succ N))
        _ ≤ ε * ((σ₁ * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k) := hN₁.le
    · refine le_trans (wLoc_mk'_tail_le p F ϖ hρ₂0 hρ₂1 k N w') ?_
      rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos (mul_pos hρ₂0
        (vpi_pos p F ϖ)) k)]
      calc ρ₂ ^ (N + 1)
          ≤ ρ₂ ^ N₂ := pow_le_pow_of_le_one zero_le hρ₂1.le
            (le_trans (le_max_right _ _) (Nat.le_succ N))
        _ ≤ ε * ((ρ₂ * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k) := hN₂.le
  · -- the norm
    refine wIRPS_finset_sum_le p F ϖ _ _ _ (fun i _ => ?_)
    rw [wIRPS_monomial p F ϖ]
    rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ (Ef i) * WittVector.teichmuller p (Cf i))
          (sPow p F ϖ k))
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ (Ef i) * WittVector.teichmuller p (Cf i))
            (sPow p F ϖ k)) from rfl]
    rw [wI_BIProd p F ϖ, valued_BlocToHatK p F ϖ, valued_BlocToHatK p F ϖ]
    have hK1 : (1 : NNReal) ≤ σ₁ ^ m * ((ρ₁ ^ m)⁻¹) :=
      calc (1 : NNReal) = ρ₁ ^ m * ((ρ₁ ^ m)⁻¹) :=
          (mul_inv_cancel₀ (pow_pos hρ₁0 m).ne').symm
        _ ≤ σ₁ ^ m * ((ρ₁ ^ m)⁻¹) :=
          mul_le_mul_left (pow_le_pow_left' hρσ m) _
    refine max_le ?_ ?_
    · refine le_trans (hbnd1 i) ?_
      have hm1 : wLoc p F ϖ hσ₁0 hσ₁1 (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F w i))
          (sPow p F ϖ k)) ≤ W :=
        le_trans (wLoc_mk'_monomial_le p F ϖ hσ₁0 hσ₁1 w k i) hw1
      exact mul_le_mul_right hm1 _
    · refine le_trans (hbnd2 i) ?_
      have hm1 : wLoc p F ϖ hσ₁0 hσ₁1 (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F w i))
          (sPow p F ϖ k)) ≤ W :=
        le_trans (wLoc_mk'_monomial_le p F ϖ hσ₁0 hσ₁1 w k i) hw1
      have hm2 : wLoc p F ϖ hρ₂0 hρ₂1 (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F w i))
          (sPow p F ϖ k)) ≤ W :=
        le_trans (wLoc_mk'_monomial_le p F ϖ hρ₂0 hρ₂1 w k i) hw2
      refine le_trans (max_le hm1 hm2) ?_
      exact le_mul_of_one_le_left zero_le hK1

end Assembly


/-! ### The correction round (T910 P3e) -/

section Correction

variable {σ₁ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
variable (hφb : ∀ x : Bloc p F ϖ,
  ((φ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
    : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
    : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x)

include hφb in
/-- **The correction round** (case 1): a residual of size `W·2⁻ᵐ` is reduced
to `W·2⁻⁽ᵐ⁺¹⁾` by a lift of `K`-controlled round norm. -/
theorem exists_correction_step_BI
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m₀ : ℕ) (hm₀ : 0 < m₀)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m₀)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀))
    {W : NNReal} (hW0 : 0 < W) (hWle : W ≤ 1) (n : ℕ)
    (r : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
    (hrmem : r ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hrbnd : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 r ≤ W * (2⁻¹ : NNReal) ^ n) :
    ∃ f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        ≤ σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) * (W * (2⁻¹ : NNReal) ^ n)
      ∧ (r - evalBI p F ϖ φ hφ hbmem hb f)
          ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      ∧ wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 (r - evalBI p F ϖ φ hφ hbmem hb f)
        ≤ W * (2⁻¹ : NNReal) ^ (n + 1) := by
  have hhalf0 : (0 : NNReal) < 2⁻¹ := by norm_num
  have hhalf1 : ((2 : NNReal)⁻¹) ≤ 1 := by norm_num
  have hε : (0 : NNReal) < W * (2⁻¹ : NNReal) ^ (n + 1) :=
    mul_pos hW0 (pow_pos hhalf0 _)
  -- the Bloc approximant
  obtain ⟨x, hxapp⟩ := exists_BIProd_approx p F ϖ hrmem hε
  have hxle : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x) ≤ W * (2⁻¹ : NNReal) ^ n := by
    have hrw : BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x
        = r + -(r - BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x) := by ring
    calc (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x))
        = wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (r + -(r - BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x)) := by
          rw [← hrw]
      _ ≤ max (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 r)
          (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
            (-(r - BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x))) :=
          wI_add_le p F _ _
      _ = max (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 r)
          (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
            (r - BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x)) := by rw [wI_neg]
      _ ≤ W * (2⁻¹ : NNReal) ^ n := by
          refine max_le hrbnd (le_trans hxapp ?_)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one zero_le hhalf1 (Nat.le_succ n)) zero_le
  -- destructure the approximant as a fraction
  obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))
    (S := Bloc p F ϖ) x
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have hs : s = sPow p F ϖ k := Subtype.ext hk.symm
  subst hs
  -- the per-radius bounds of the approximant
  have hxw := hxle
  rw [wI_BIProd p F ϖ, valued_BlocToHatK p F ϖ, valued_BlocToHatK p F ϖ]
    at hxw
  have hw1 : wLoc p F ϖ hσ₁0 hσ₁1
      (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k))
      ≤ W * (2⁻¹ : NNReal) ^ n := le_trans (le_max_left _ _) hxw
  have hw2 : wLoc p F ϖ hρ₂0 hρ₂1
      (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k))
      ≤ W * (2⁻¹ : NNReal) ^ n := le_trans (le_max_right _ _) hxw
  -- the round-budget is ≤ 1
  have hWn : W * (2⁻¹ : NNReal) ^ n ≤ 1 := by
    calc W * (2⁻¹ : NNReal) ^ n
        ≤ 1 * 1 := mul_le_mul hWle (pow_le_one₀ zero_le hhalf1)
          zero_le zero_le
      _ = 1 := one_mul 1
  -- the first approximation of the approximant
  obtain ⟨f, hfres, hfnorm⟩ := exists_evalBI_approx_bloc p F ϖ φ hφ hφb
    hρσ hσρ zb m₀ hm₀ hgen hbmem hb hbg w k hWn hw1 hw2 hε
  refine ⟨f, hfnorm, ?_, ?_⟩
  · exact sub_mem hrmem (evalBI_mem p F ϖ φ hφ hbmem hb f)
  · have hsplit : r - evalBI p F ϖ φ hφ hbmem hb f
        = (r - BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
            (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k)))
          + (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
              (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k))
            - evalBI p F ϖ φ hφ hbmem hb f) := by ring
    rw [hsplit]
    exact le_trans (wI_add_le p F _ _) (max_le hxapp hfres)

include hφ in
/-- Telescope base: the empty partial sum. -/
theorem evalBI_partial_zero
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
    (u : ℕ → ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    z - evalBI p F ϖ φ hφ hbmem hb (∑ l ∈ Finset.range 0, u l) = z := by
  rw [Finset.sum_range_zero, evalBI_zero p F ϖ φ hφ hbmem hb, sub_zero]

include hφ in
/-- Telescope step: peeling one correction. -/
theorem evalBI_partial_succ
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
    (u : ℕ → ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) (m : ℕ) :
    (z - evalBI p F ϖ φ hφ hbmem hb (∑ l ∈ Finset.range m, u l))
        - evalBI p F ϖ φ hφ hbmem hb (u m)
      = z - evalBI p F ϖ φ hφ hbmem hb
          (∑ l ∈ Finset.range (m + 1), u l) := by
  rw [Finset.sum_range_succ, evalBI_add p F ϖ φ hφ hbmem hb, sub_sub]

include hφb in
/-- **The correction sequence** (case 1): successive approximation with
geometrically shrinking residuals and `K`-scaled round norms. -/
theorem exists_correction_chain_BI
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m₀ : ℕ) (hm₀ : 0 < m₀)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m₀)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀))
    {z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    {W : NNReal} (hW0 : 0 < W) (hWle : W ≤ 1)
    (hzW : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z ≤ W) :
    ∃ (u : ℕ → ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      (r : ℕ → (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)),
      r 0 = z
      ∧ (∀ m, r (m + 1) = r m - evalBI p F ϖ φ hφ hbmem hb (u m))
      ∧ (∀ l, wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((u l : ↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        ≤ σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) * (W * (2⁻¹ : NNReal) ^ l))
      ∧ ∀ m, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 (r m)
            ≤ W * (2⁻¹ : NNReal) ^ m := by
  have hK0 : (0 : NNReal) < σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) :=
    mul_pos (pow_pos hσ₁0 m₀) (inv_pos.mpr (pow_pos hρ₁0 m₀))
  set K : NNReal := σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) with hKdef
  have hstep : ∀ (m : ℕ)
      (r : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)),
      r ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 →
      wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 r ≤ W * (2⁻¹ : NNReal) ^ m →
      ∃ f : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
        ((K)⁻¹)
            * wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
              ((f : ↥(restrictedMvPowerSeriesSubring 1
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
                : MvPowerSeries (Fin 1)
                  ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          ≤ W * (2⁻¹ : NNReal) ^ m
        ∧ (r - evalBI p F ϖ φ hφ hbmem hb f)
            ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
        ∧ wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
            (r - evalBI p F ϖ φ hφ hbmem hb f)
          ≤ W * (2⁻¹ : NNReal) ^ (m + 1) := by
    intro m r hrmem hrbnd
    obtain ⟨f, hfnorm, hfmem, hfres⟩ := exists_correction_step_BI p F ϖ
      φ hφ hφb hρσ hσρ zb m₀ hm₀ hgen hbmem hb hbg hW0 hWle m r hrmem hrbnd
    refine ⟨f, ?_, hfmem, hfres⟩
    calc ((K)⁻¹)
          * wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
            ((f : ↥(restrictedMvPowerSeriesSubring 1
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin 1)
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        ≤ ((K)⁻¹)
          * (K * (W * (2⁻¹ : NNReal) ^ m)) :=
          mul_le_mul_right hfnorm _
      _ = W * (2⁻¹ : NNReal) ^ m := by
          rw [← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul]
  obtain ⟨u, r, hr0, hrrec, hCbnd, hrmem, hrbnd⟩ :=
    exists_chain (fun v => v ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
      (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1)
      (fun f : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) =>
        ((K)⁻¹)
          * wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
            ((f : ↥(restrictedMvPowerSeriesSubring 1
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin 1)
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      (fun v f => v - evalBI p F ϖ φ hφ hbmem hb f)
      (fun m => W * (2⁻¹ : NNReal) ^ m) z hz
      (by rw [pow_zero, mul_one]; exact hzW) hstep
  refine ⟨u, r, hr0, hrrec, fun l => ?_, hrbnd⟩
  have h := hCbnd l
  calc wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((u l : ↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      = (K)
        * (((K)⁻¹)
          * wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
            ((u l : ↥(restrictedMvPowerSeriesSubring 1
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin 1)
                ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul]
    _ ≤ (K) * (W * (2⁻¹ : NNReal) ^ l) :=
        mul_le_mul_right h _

include hφb in
/-- **The correction sequence, telescoped** (case 1): partial-sum residuals
shrink geometrically with `K`-scaled round norms. -/
theorem exists_correction_sequence_BI
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m₀ : ℕ) (hm₀ : 0 < m₀)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m₀)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀))
    {z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    {W : NNReal} (hW0 : 0 < W) (hWle : W ≤ 1)
    (hzW : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z ≤ W) :
    ∃ u : ℕ → ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      (∀ l, wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((u l : ↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        ≤ σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) * (W * (2⁻¹ : NNReal) ^ l))
      ∧ ∀ m, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (z - evalBI p F ϖ φ hφ hbmem hb (∑ l ∈ Finset.range m, u l))
            ≤ W * (2⁻¹ : NNReal) ^ m := by
  obtain ⟨u, r, hr0, hrrec, hnorm, hres⟩ := exists_correction_chain_BI
    p F ϖ φ hφ hφb hρσ hσρ zb m₀ hm₀ hgen hbmem hb hbg hz hW0 hWle hzW
  refine ⟨u, hnorm, fun m => ?_⟩
  have hpartial : ∀ m', r m'
      = z - evalBI p F ϖ φ hφ hbmem hb (∑ l ∈ Finset.range m', u l) := by
    intro m'
    induction m' with
    | zero =>
      exact hr0.trans (evalBI_partial_zero p F ϖ φ hφ hbmem hb z u).symm
    | succ n ih =>
      exact (hrrec n).trans
        ((congrArg (· - evalBI p F ϖ φ hφ hbmem hb (u n)) ih).trans
          (evalBI_partial_succ p F ϖ φ hφ hbmem hb z u n))
  rw [← hpartial m]
  exact hres m

include hφ in
/-- **The correction limit** (case 1): a `K`-normed correction sequence with
geometrically vanishing residuals sums to an exact preimage of `K`-controlled
norm. -/
theorem exists_evalBI_eq_of_correction_BI
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
    {K W : NNReal} (hK1 : 1 ≤ K) (hW : 0 < W)
    (u : ℕ → ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (hCbnd : ∀ l, wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((u l : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      ≤ K * (W * (2⁻¹ : NNReal) ^ l))
    (hres : ∀ m, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (z - evalBI p F ϖ φ hφ hbmem hb (∑ l ∈ Finset.range m, u l))
        ≤ W * (2⁻¹ : NNReal) ^ m) :
    ∃ U : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      evalBI p F ϖ φ hφ hbmem hb U = z
      ∧ wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (U : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ≤ K * W := by
  have hhalf1 : ((2 : NNReal)⁻¹) ≤ 1 := by norm_num
  have hhalf0 : (0 : NNReal) < 2⁻¹ := by norm_num
  have hK0 : (0 : NNReal) < K := lt_of_lt_of_le one_pos hK1
  have hC0 : Filter.Tendsto (fun l : ℕ => K * (W * (2⁻¹ : NNReal) ^ l))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun l : ℕ => ((2 : NNReal)⁻¹) ^ l)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have h2 := (h1.const_mul W).const_mul K
    simpa [mul_assoc] using h2
  obtain ⟨U, hU⟩ := exists_rps_series_limit_BI p F ϖ hCbnd hC0
  have hUnorm : wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((U : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ≤ K * W := by
    have h0 := hU 0 (K * W) (mul_pos hK0 hW) (fun l _ => by
      calc K * (W * (2⁻¹ : NNReal) ^ l)
          ≤ K * (W * 1) := by
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            exact mul_le_mul_of_nonneg_left
              (pow_le_one₀ zero_le hhalf1) zero_le
        _ = K * W := by rw [mul_one])
    rwa [Finset.sum_range_zero, sub_zero] at h0
  have hdiff : ∀ m : ℕ, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (z - evalBI p F ϖ φ hφ hbmem hb U)
        ≤ K * (W * (2⁻¹ : NNReal) ^ m) := by
    intro m
    have hε : (0 : NNReal) < K * (W * (2⁻¹ : NNReal) ^ m) :=
      mul_pos hK0 (mul_pos hW (pow_pos hhalf0 _))
    have htail := hU m (K * (W * (2⁻¹ : NNReal) ^ m)) hε (fun l hl => by
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one zero_le hhalf1 hl) zero_le)
    have hcancel : (∑ l ∈ Finset.range m, u l)
        + (U - ∑ l ∈ Finset.range m, u l) = U := by abel
    have h := wI_z_sub_evalBI_add_le p F ϖ φ hφ hbmem hb z
      (∑ l ∈ Finset.range m, u l) (U - ∑ l ∈ Finset.range m, u l) hε
      (le_trans (hres m) (le_mul_of_one_le_left zero_le hK1)) htail
    exact le_trans (le_of_eq (congrArg
      (fun t => wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
        (z - evalBI p F ϖ φ hφ hbmem hb t)) hcancel.symm)) h
  have hle0 : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (z - evalBI p F ϖ φ hφ hbmem hb U) ≤ 0 :=
    ge_of_tendsto hC0 (Filter.Eventually.of_forall hdiff)
  have h0 : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (z - evalBI p F ϖ φ hφ hbmem hb U) = 0 := le_antisymm hle0 zero_le
  exact ⟨U, (sub_eq_zero.mp ((wI_eq_zero_iff p F _).mp h0)).symm, hUnorm⟩

include hφb in
/-- **Strict surjectivity of the case-1 presentation on the unit ball**
(Kedlaya Lemma 4.9, case 1, surjectivity with (4.9.1)-norm control): every
`≤ 1`-normalized element of the cut interval ring is the value of a
restricted series over `B^I` of norm at most `K = σ₁^m(ρ₁^m)⁻¹`. -/
theorem exists_evalBI_eq_of_le_one
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m₀ : ℕ) (hm₀ : 0 < m₀)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m₀)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀))
    {z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hzle : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z ≤ 1) :
    ∃ U : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      evalBI p F ϖ φ hφ hbmem hb U = z
      ∧ wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (U : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        ≤ σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) := by
  have hK1 : (1 : NNReal) ≤ σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) :=
    calc (1 : NNReal) = ρ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) :=
        (mul_inv_cancel₀ (pow_pos hρ₁0 m₀).ne').symm
      _ ≤ σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) :=
        mul_le_mul_left (pow_le_pow_left' hρσ m₀) _
  obtain ⟨u, hCbnd, hres⟩ := exists_correction_sequence_BI p F ϖ φ hφ hφb
    hρσ hσρ zb m₀ hm₀ hgen hbmem hb hbg hz one_pos le_rfl hzle
  obtain ⟨U, hUeq, hUnorm⟩ := exists_evalBI_eq_of_correction_BI p F ϖ
    φ hφ hbmem hb z hK1 one_pos u hCbnd hres
  refine ⟨U, hUeq, ?_⟩
  rwa [mul_one] at hUnorm

end Correction


/-! ### The per-radius component norms (T910 P4) -/

/-- The first-component Gauss norm on restricted series over `B^I`. -/
def NfstRPS (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : NNReal :=
  ⨆ s : Fin k →₀ ℕ, Valued.v
    (((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)

/-- The second-component Gauss norm on restricted series over `B^I`. -/
def NsndRPS (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : NNReal :=
  ⨆ s : Fin k →₀ ℕ, Valued.v
    (((MvPowerSeries.coeff s f : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)

/-- The interval Gauss norm is the maximum of the component norms. -/
theorem wIRPS_eq_max_NfstRPS_NsndRPS
    {f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 f
      = max (NfstRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 f)
          (NsndRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 f) := by
  refine le_antisymm (ciSup_le fun s => ?_) (max_le ?_ ?_)
  · refine max_le ?_ ?_
    · refine le_trans ?_ (le_max_left _ _)
      have hb : BddAbove (Set.range (fun s : Fin k →₀ ℕ => Valued.v
          (((MvPowerSeries.coeff s f
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))) := by
        obtain ⟨B, hB⟩ := bddAbove_wIRPS p F ϖ hf
        refine ⟨B, ?_⟩
        rintro t ⟨s, rfl⟩
        exact le_trans (le_max_left _ _) (hB ⟨s, rfl⟩)
      exact le_ciSup hb s
    · refine le_trans ?_ (le_max_right _ _)
      have hb : BddAbove (Set.range (fun s : Fin k →₀ ℕ => Valued.v
          (((MvPowerSeries.coeff s f
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))) := by
        obtain ⟨B, hB⟩ := bddAbove_wIRPS p F ϖ hf
        refine ⟨B, ?_⟩
        rintro t ⟨s, rfl⟩
        exact le_trans (le_max_right _ _) (hB ⟨s, rfl⟩)
      exact le_ciSup hb s
  · refine ciSup_le fun s => ?_
    exact le_trans (le_max_left _ _) (wI_coeff_le_wIRPS p F ϖ hf s)
  · refine ciSup_le fun s => ?_
    exact le_trans (le_max_right _ _) (wI_coeff_le_wIRPS p F ϖ hf s)

/-- **The generator-multiplication coefficient recursion**: multiplying by
`T − C g` acts on coefficients as shift-minus-scale. -/
theorem coeffSeq_Gelt_mul {A : Type*} [CommRing A] (gB : A)
    (x : MvPowerSeries (Fin 1) A) (n : ℕ) :
    coeffSeq ((MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 1) (1 : A)
        - MvPowerSeries.monomial 0 gB) * x) n
      = (if 1 ≤ n then coeffSeq x (n - 1) else 0) - gB * coeffSeq x n := by
  rw [sub_mul, coeffSeq, map_sub]
  congr 1
  · rw [MvPowerSeries.coeff_monomial_mul]
    by_cases hn : 1 ≤ n
    · rw [if_pos (by
        rw [Finsupp.single_le_iff, Finsupp.single_eq_same]
        exact hn), if_pos hn, one_mul, coeffSeq, ← Finsupp.single_tsub]
    · rw [if_neg (by
        rw [Finsupp.single_le_iff, Finsupp.single_eq_same]
        exact hn), if_neg hn]
  · rw [MvPowerSeries.coeff_monomial_mul,
      if_pos (zero_le : (0 : Fin 1 →₀ ℕ) ≤ Finsupp.single (0 : Fin 1) n),
      tsub_zero,
      coeffSeq]

/-- **The downward telescope bound** (Kedlaya's `t ≥ t₀` branch): under the
shift-minus-scale recursion with a contracting scale, every `X`-value is
bounded by the `Y`-supremum. -/
theorem telescope_down_bound {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (g : hatK p F hρ0 hρ1) (hg : Valued.v g ≤ 1)
    (X Y : ℕ → hatK p F hρ0 hρ1)
    (hrec : ∀ n, Y n = (if 1 ≤ n then X (n - 1) else 0) - g * X n)
    (hbdd : BddAbove (Set.range (fun n => Valued.v (Y n))))
    (hX0 : Filter.Tendsto (fun n => Valued.v (X n)) Filter.atTop (nhds 0))
    (m : ℕ) :
    Valued.v (X m) ≤ ⨆ n, Valued.v (Y n) := by
  -- the finite telescope identity
  have htel : ∀ M : ℕ, X m
      = (∑ j ∈ Finset.range M, g ^ j * Y (m + 1 + j))
        + g ^ M * X (m + M) := by
    intro M
    induction M with
    | zero =>
      rw [Finset.sum_range_zero, pow_zero, one_mul, Nat.add_zero, zero_add]
    | succ M ih =>
      have hstep : X (m + M) = Y (m + M + 1) + g * X (m + M + 1) := by
        have h := hrec (m + M + 1)
        rw [if_pos (Nat.succ_le_succ (Nat.zero_le _)),
          Nat.add_sub_cancel] at h
        rw [h]
        ring
      calc X m = (∑ j ∈ Finset.range M, g ^ j * Y (m + 1 + j))
            + g ^ M * X (m + M) := ih
        _ = (∑ j ∈ Finset.range M, g ^ j * Y (m + 1 + j))
            + (g ^ M * Y (m + M + 1) + g ^ (M + 1) * X (m + M + 1)) := by
            rw [hstep]
            ring
        _ = (∑ j ∈ Finset.range (M + 1), g ^ j * Y (m + 1 + j))
            + g ^ (M + 1) * X (m + (M + 1)) := by
            rw [Finset.sum_range_succ]
            rw [show m + 1 + M = m + M + 1 from by omega,
              show m + (M + 1) = m + M + 1 from by omega]
            ring
  -- per-M ultrametric bound
  have hbound : ∀ M : ℕ, Valued.v (X m)
      ≤ max (⨆ n, Valued.v (Y n)) (Valued.v (X (m + M))) := by
    intro M
    rw [htel M]
    refine le_trans (Valuation.map_add _ _ _) (max_le_max ?_ ?_)
    · refine Valuation.map_sum_le _ (fun j _ => ?_)
      rw [Valuation.map_mul]
      calc Valued.v (g ^ j) * Valued.v (Y (m + 1 + j))
          ≤ 1 * Valued.v (Y (m + 1 + j)) := by
            refine mul_le_mul_of_nonneg_right ?_ zero_le
            rw [Valuation.map_pow]
            exact pow_le_one₀ zero_le hg
        _ = Valued.v (Y (m + 1 + j)) := one_mul _
        _ ≤ ⨆ n, Valued.v (Y n) := le_ciSup hbdd (m + 1 + j)
    · rw [Valuation.map_mul]
      calc Valued.v (g ^ M) * Valued.v (X (m + M))
          ≤ 1 * Valued.v (X (m + M)) := by
            refine mul_le_mul_of_nonneg_right ?_ zero_le
            rw [Valuation.map_pow]
            exact pow_le_one₀ zero_le hg
        _ = Valued.v (X (m + M)) := one_mul _
  -- the tail vanishes
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ M in Filter.atTop,
      Valued.v (X (m + M)) < Valued.v (X m) := by
    have h1 := (hX0.comp (Filter.tendsto_add_atTop_nat m)).congr
      (fun a => by
        show Valued.v (X (a + m)) = Valued.v (X (m + a))
        rw [Nat.add_comm])
    exact h1.eventually_lt_const (lt_of_le_of_lt zero_le hcon)
  obtain ⟨M, hM⟩ := hev.exists
  exact absurd (hbound M)
    (not_le.mpr (max_lt hcon (by exact hM)))

/-- **The upward telescope bound** (Kedlaya's `t < t₀` branch): under the
shift-minus-scale recursion with an expanding scale, every `X`-value is
bounded by `v(g)⁻¹` times the `Y`-supremum. -/
theorem telescope_up_bound {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (g : hatK p F hρ0 hρ1) (hg : 1 < Valued.v g)
    (X Y : ℕ → hatK p F hρ0 hρ1)
    (hrec : ∀ n, Y n = (if 1 ≤ n then X (n - 1) else 0) - g * X n)
    (hbdd : BddAbove (Set.range (fun n => Valued.v (Y n)))) :
    ∀ n, Valued.v (X n)
      ≤ (Valued.v g)⁻¹ * (⨆ n, Valued.v (Y n)) := by
  have hg0 : (0 : NNReal) < Valued.v g := lt_trans one_pos hg
  have hcancel : ∀ x : hatK p F hρ0 hρ1, Valued.v x
      = (Valued.v g)⁻¹ * Valued.v (g * x) := by
    intro x
    rw [Valuation.map_mul, ← mul_assoc, inv_mul_cancel₀ hg0.ne', one_mul]
  intro n
  induction n with
  | zero =>
    have h0 := hrec 0
    rw [if_neg (by omega), zero_sub] at h0
    rw [hcancel (X 0)]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [show g * X 0 = -(Y 0) from by rw [h0]; ring, Valuation.map_neg]
    exact le_ciSup hbdd 0
  | succ n ih =>
    have h1 := hrec (n + 1)
    rw [if_pos (Nat.succ_le_succ (Nat.zero_le _)), Nat.add_sub_cancel] at h1
    rw [hcancel (X (n + 1))]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [show g * X (n + 1) = X n - Y (n + 1) from by rw [h1]; ring]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · refine le_trans ih ?_
      calc (Valued.v g)⁻¹ * (⨆ n, Valued.v (Y n))
          ≤ 1 * (⨆ n, Valued.v (Y n)) := by
            refine mul_le_mul_of_nonneg_right ?_ zero_le
            exact (inv_le_one₀ (lt_trans one_pos hg)).mpr hg.le
        _ = ⨆ n, Valued.v (Y n) := one_mul _
    · exact le_ciSup hbdd (n + 1)

/-- Coercion of a `B^I`-difference (micro-lemma). -/
theorem BISub_coe_sub {σ₁ σ₂ : NNReal} {h1 : 0 < σ₁} {h2 : σ₁ < 1}
    {h3 : 0 < σ₂} {h4 : σ₂ < 1} (x y : ↥(BISub p F ϖ h1 h2 h3 h4)) :
    ((x - y : ↥(BISub p F ϖ h1 h2 h3 h4))
      : (hatK p F h1 h2) × (hatK p F h3 h4))
      = ((x : ↥(BISub p F ϖ h1 h2 h3 h4))
          : (hatK p F h1 h2) × (hatK p F h3 h4))
        - ((y : ↥(BISub p F ϖ h1 h2 h3 h4))
            : (hatK p F h1 h2) × (hatK p F h3 h4)) := rfl

/-- Coercion of a `B^I`-product (micro-lemma). -/
theorem BISub_coe_mul {σ₁ σ₂ : NNReal} {h1 : 0 < σ₁} {h2 : σ₁ < 1}
    {h3 : 0 < σ₂} {h4 : σ₂ < 1} (x y : ↥(BISub p F ϖ h1 h2 h3 h4)) :
    ((x * y : ↥(BISub p F ϖ h1 h2 h3 h4))
      : (hatK p F h1 h2) × (hatK p F h3 h4))
      = ((x : ↥(BISub p F ϖ h1 h2 h3 h4))
          : (hatK p F h1 h2) × (hatK p F h3 h4))
        * ((y : ↥(BISub p F ϖ h1 h2 h3 h4))
            : (hatK p F h1 h2) × (hatK p F h3 h4)) := rfl

/-- The first-component norm as a sequence supremum. -/
theorem NfstRPS_eq_iSup_coeffSeq
    (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    NfstRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 f
      = ⨆ n : ℕ, Valued.v
          (((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) := by
  have hrange : Set.range (fun s : Fin 1 →₀ ℕ => Valued.v
        (((MvPowerSeries.coeff s f
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
      = Set.range (fun n : ℕ => Valued.v
        (((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)) := by
    ext t
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s 0, ?_⟩
      have hs : Finsupp.single (0 : Fin 1) (s 0) = s := by
        refine Finsupp.ext fun i => ?_
        rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]
      exact congrArg (fun s' : Fin 1 →₀ ℕ => Valued.v
        (((MvPowerSeries.coeff s' f
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)) hs
    · rintro ⟨n, rfl⟩
      exact ⟨Finsupp.single (0 : Fin 1) n, rfl⟩
  rw [NfstRPS, show (⨆ s : Fin 1 →₀ ℕ, Valued.v
      (((MvPowerSeries.coeff s f
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
    = sSup (Set.range (fun s : Fin 1 →₀ ℕ => Valued.v
      (((MvPowerSeries.coeff s f
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))) from rfl,
    hrange]
  rfl

/-- The second-component norm as a sequence supremum. -/
theorem NsndRPS_eq_iSup_coeffSeq
    (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    NsndRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 f
      = ⨆ n : ℕ, Valued.v
          (((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) := by
  have hrange : Set.range (fun s : Fin 1 →₀ ℕ => Valued.v
        (((MvPowerSeries.coeff s f
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))
      = Set.range (fun n : ℕ => Valued.v
        (((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)) := by
    ext t
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s 0, ?_⟩
      have hs : Finsupp.single (0 : Fin 1) (s 0) = s := by
        refine Finsupp.ext fun i => ?_
        rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]
      exact congrArg (fun s' : Fin 1 →₀ ℕ => Valued.v
        (((MvPowerSeries.coeff s' f
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)) hs
    · rintro ⟨n, rfl⟩
      exact ⟨Finsupp.single (0 : Fin 1) n, rfl⟩
  rw [NsndRPS, show (⨆ s : Fin 1 →₀ ℕ, Valued.v
      (((MvPowerSeries.coeff s f
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))
    = sSup (Set.range (fun s : Fin 1 →₀ ℕ => Valued.v
      (((MvPowerSeries.coeff s f
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))) from rfl,
    hrange]
  rfl

/-- **The presentation generator** `T − C g` as a restricted series. -/
noncomputable def GeltElt (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    ↥(restrictedMvPowerSeriesSubring 1 ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
  ⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 1)
      (1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    - MvPowerSeries.monomial 0 gB,
    sub_mem (isRestricted_monomial_BI p F ϖ _)
      (isRestricted_monomial_BI p F ϖ _)⟩

/-- Coercion of an RPS-product over `B^I` (micro-lemma). -/
theorem RPS_BI_coe_mul
    (a b : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    ((a * b : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      = (a : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        * (b : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := rfl

/-- The generator's underlying series (micro-lemma). -/
theorem GeltElt_coe (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    ((GeltElt p F ϖ gB : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      = MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 1)
          (1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        - MvPowerSeries.monomial 0 gB := rfl

/-- The first-component coefficient recursion of generator multiplication. -/
theorem coeffSeq_GeltElt_mul_fst (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) (n : ℕ) :
    ((coeffSeq ((GeltElt p F ϖ gB * f
        : ↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
      = (if 1 ≤ n then
          ((coeffSeq (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (n - 1)
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
        else 0)
        - ((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
          * ((coeffSeq (f : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
              : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1 := by
  have hrec := coeffSeq_Gelt_mul gB
    (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
  rw [RPS_BI_coe_mul p F ϖ, GeltElt_coe p F ϖ, hrec]
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, if_pos hn]
    rfl
  · rw [if_neg hn, if_neg hn]
    rfl

/-- The second-component coefficient recursion of generator multiplication. -/
theorem coeffSeq_GeltElt_mul_snd (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) (n : ℕ) :
    ((coeffSeq ((GeltElt p F ϖ gB * f
        : ↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = (if 1 ≤ n then
          ((coeffSeq (f : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (n - 1)
            : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
        else 0)
        - ((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
          * ((coeffSeq (f : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
              : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 := by
  have hrec := coeffSeq_Gelt_mul gB
    (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
  rw [RPS_BI_coe_mul p F ϖ, GeltElt_coe p F ϖ, hrec]
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, if_pos hn]
    rfl
  · rw [if_neg hn, if_neg hn]
    rfl

/-- The telescope dispatch: under the recursion the `X`-supremum is bounded
by the `Y`-supremum, whatever the scale. -/
theorem telescope_iSup_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (g : hatK p F hρ0 hρ1) (X Y : ℕ → hatK p F hρ0 hρ1)
    (hrec : ∀ n, Y n = (if 1 ≤ n then X (n - 1) else 0) - g * X n)
    (hbdd : BddAbove (Set.range (fun n => Valued.v (Y n))))
    (hX0 : Filter.Tendsto (fun n => Valued.v (X n)) Filter.atTop (nhds 0)) :
    (⨆ n, Valued.v (X n)) ≤ ⨆ n, Valued.v (Y n) := by
  by_cases hg : Valued.v g ≤ 1
  · exact ciSup_le fun m =>
      telescope_down_bound p F g hg X Y hrec hbdd hX0 m
  · refine ciSup_le fun m => le_trans
      (telescope_up_bound p F g (not_le.mp hg) X Y hrec hbdd m) ?_
    calc (Valued.v g)⁻¹ * (⨆ n, Valued.v (Y n))
        ≤ 1 * (⨆ n, Valued.v (Y n)) := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          exact (inv_le_one₀ (lt_trans one_pos (not_le.mp hg))).mpr
            (not_le.mp hg).le
      _ = ⨆ n, Valued.v (Y n) := one_mul _

/-- The first-component norm does not drop under generator multiplication. -/
theorem NfstRPS_le_GeltElt_mul (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    NfstRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      ≤ NfstRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((GeltElt p F ϖ gB * f
            : ↥(restrictedMvPowerSeriesSubring 1
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  have hbdd : BddAbove (Set.range (fun n => Valued.v
      (((coeffSeq ((GeltElt p F ϖ gB * f
          : ↥(restrictedMvPowerSeriesSubring 1
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))) := by
    obtain ⟨B, hB⟩ := bddAbove_wIRPS p F ϖ (GeltElt p F ϖ gB * f).2
    refine ⟨B, ?_⟩
    rintro t ⟨n, rfl⟩
    exact le_trans (le_max_left _ _)
      (hB ⟨Finsupp.single (0 : Fin 1) n, rfl⟩)
  have hX0 : Filter.Tendsto (fun n => Valued.v
      (((coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_wI_coeffSeq p F ϖ f.2) (fun _ => zero_le)
      (fun n => le_max_left _ _)
  rw [NfstRPS_eq_iSup_coeffSeq p F ϖ, NfstRPS_eq_iSup_coeffSeq p F ϖ]
  exact telescope_iSup_le p F _ _ _
    (fun n => coeffSeq_GeltElt_mul_fst p F ϖ gB f n) hbdd hX0

/-- The second-component norm does not drop under generator multiplication. -/
theorem NsndRPS_le_GeltElt_mul (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    NsndRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      ≤ NsndRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((GeltElt p F ϖ gB * f
            : ↥(restrictedMvPowerSeriesSubring 1
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  have hbdd : BddAbove (Set.range (fun n => Valued.v
      (((coeffSeq ((GeltElt p F ϖ gB * f
          : ↥(restrictedMvPowerSeriesSubring 1
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))) := by
    obtain ⟨B, hB⟩ := bddAbove_wIRPS p F ϖ (GeltElt p F ϖ gB * f).2
    refine ⟨B, ?_⟩
    rintro t ⟨n, rfl⟩
    exact le_trans (le_max_right _ _)
      (hB ⟨Finsupp.single (0 : Fin 1) n, rfl⟩)
  have hX0 : Filter.Tendsto (fun n => Valued.v
      (((coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_wI_coeffSeq p F ϖ f.2) (fun _ => zero_le)
      (fun n => le_max_right _ _)
  rw [NsndRPS_eq_iSup_coeffSeq p F ϖ, NsndRPS_eq_iSup_coeffSeq p F ϖ]
  exact telescope_iSup_le p F _ _ _
    (fun n => coeffSeq_GeltElt_mul_snd p F ϖ gB f n) hbdd hX0

/-- **Strictness of generator multiplication** (Kedlaya ln 527–533):
multiplying by `T − C g` does not decrease the interval Gauss norm — a
strict injective endomorphism with closed image. -/
theorem wIRPS_le_GeltElt_mul (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      ≤ wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((GeltElt p F ϖ gB * f
            : ↥(restrictedMvPowerSeriesSubring 1
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin 1)
              ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  rw [wIRPS_eq_max_NfstRPS_NsndRPS p F ϖ f.2,
    wIRPS_eq_max_NfstRPS_NsndRPS p F ϖ (GeltElt p F ϖ gB * f).2]
  exact max_le_max (NfstRPS_le_GeltElt_mul p F ϖ gB f)
    (NsndRPS_le_GeltElt_mul p F ϖ gB f)

/-- **The restriction at the top radius is the second component.** -/
theorem resI_eq_snd {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hρ₂0 hρ₂1 z = z.2 := by
  haveI := neBot_comap_of_mem_BISub p F ϖ hz
  refine Filter.Tendsto.limUnder_eq ?_
  have h1 : Filter.Tendsto (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds z) := Filter.tendsto_comap
  have h2 : Filter.Tendsto
      (fun x => (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x).2)
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds z.2) := (continuous_snd.tendsto z).comp h1
  refine h2.congr fun x => ?_
  exact BIProd_snd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x

/-- **The restriction at the bottom radius is the first component.** -/
theorem resI_eq_fst {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hρ₁0 hρ₁1 z = z.1 := by
  haveI := neBot_comap_of_mem_BISub p F ϖ hz
  refine Filter.Tendsto.limUnder_eq ?_
  have h1 : Filter.Tendsto (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds z) := Filter.tendsto_comap
  have h2 : Filter.Tendsto
      (fun x => (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x).1)
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds z.1) := (continuous_fst.tendsto z).comp h1
  refine h2.congr fun x => ?_
  exact BIProd_fst p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x

/-- **The formal kernel recursion, generic form**: over any commutative ring
with `g·V = 1`, the explicit solution satisfies the shift-minus-scale
equations. -/
theorem kerSol_rec_generic {A : Type*} [CommRing A] (g V : A)
    (hinv : g * V = 1) (y : ℕ → A) (n : ℕ) :
    (if 1 ≤ n then -(V ^ n * ∑ i ∈ Finset.range n, y i * g ^ i) else 0)
      - g * -(V ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), y i * g ^ i)
      = y n := by
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, Finset.sum_range_succ]
    have h3 : (V * g) ^ n = 1 := by
      rw [show V * g = 1 from by rw [mul_comm]; exact hinv, one_pow]
    calc -(V ^ n * ∑ i ∈ Finset.range n, y i * g ^ i)
          - g * -(V ^ (n + 1)
            * ((∑ i ∈ Finset.range n, y i * g ^ i) + y n * g ^ n))
        = (g * V) * (V ^ n
            * ((∑ i ∈ Finset.range n, y i * g ^ i) + y n * g ^ n))
          - V ^ n * ∑ i ∈ Finset.range n, y i * g ^ i := by
          rw [show V ^ (n + 1) = V * V ^ n from by rw [pow_succ]; ring]
          ring
      _ = V ^ n * ((∑ i ∈ Finset.range n, y i * g ^ i) + y n * g ^ n)
          - V ^ n * ∑ i ∈ Finset.range n, y i * g ^ i := by
          rw [hinv, one_mul]
      _ = (V * g) ^ n * y n := by
          rw [mul_pow]
          ring
      _ = y n := by rw [h3, one_mul]
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst hn0
    rw [Finset.sum_range_one, pow_zero, mul_one, pow_one]
    calc 0 - g * -(V * y 0) = (g * V) * y 0 := by ring
      _ = y 0 := by rw [hinv, one_mul]

/-- **Kernel-solution decay, contracting scale** (the top-radius component):
with `v(g) ≤ 1` and the vanishing of the full series, the solution values
decay. -/
theorem kerSol_decay_of_le_one {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (g V : hatK p F hρ0 hρ1) (hinv : g * V = 1)
    (hg : Valued.v g ≤ 1) (y : ℕ → hatK p F hρ0 hρ1)
    (hy0 : Filter.Tendsto (fun n => Valued.v (y n)) Filter.atTop (nhds 0))
    (hvan : Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range (n + 1), y i * g ^ i)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => Valued.v
      (-(V ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), y i * g ^ i)))
      Filter.atTop (nhds 0) := by
  have hg0 : (0 : NNReal) < Valued.v g := by
    rcases eq_or_ne (Valued.v g) 0 with h0 | hne
    · exfalso
      have hgz : g = 0 := (Valuation.zero_iff _).mp h0
      rw [hgz, zero_mul] at hinv
      exact zero_ne_one hinv
    · exact pos_iff_ne_zero.mpr hne
  have hVg : Valued.v V * Valued.v g = 1 := by
    rw [← Valuation.map_mul, mul_comm V g, hinv, Valuation.map_one]
  refine tendsto_order.mpr
    ⟨fun c hc => absurd hc (not_lt.mpr zero_le), fun δ hδ => ?_⟩
  have hδ2 : (0 : NNReal) < δ / 2 := half_pos hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((hy0.eventually_lt_const hδ2).mono fun i h => h.le)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  -- the tail bound on the partial sum
  have hS : Valued.v (∑ i ∈ Finset.range (n + 1), y i * g ^ i)
      ≤ Valued.v g ^ (n + 1) * (δ / 2) := by
    have htail : ∀ M, n ≤ M → Valued.v
        ((∑ i ∈ Finset.range (M + 1), y i * g ^ i)
          - ∑ i ∈ Finset.range (n + 1), y i * g ^ i)
        ≤ Valued.v g ^ (n + 1) * (δ / 2) := by
      intro M hM
      rw [show (∑ i ∈ Finset.range (M + 1), y i * g ^ i)
          - ∑ i ∈ Finset.range (n + 1), y i * g ^ i
        = ∑ i ∈ Finset.Ico (n + 1) (M + 1), y i * g ^ i from
        (Finset.sum_Ico_eq_sub _ (by omega)).symm]
      refine Valuation.map_sum_le _ (fun i hi => ?_)
      obtain ⟨hi1, -⟩ := Finset.mem_Ico.mp hi
      rw [Valuation.map_mul, Valuation.map_pow]
      calc Valued.v (y i) * Valued.v g ^ i
          ≤ (δ / 2) * Valued.v g ^ i := by
            refine mul_le_mul_of_nonneg_right ?_ zero_le
            exact hN i (by omega)
        _ ≤ (δ / 2) * Valued.v g ^ (n + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            exact pow_le_pow_of_le_one zero_le hg hi1
        _ = Valued.v g ^ (n + 1) * (δ / 2) := mul_comm _ _
    -- let M → ∞ through the vanishing
    have hε : (0 : NNReal) < Valued.v g ^ (n + 1) * (δ / 2) :=
      mul_pos (pow_pos hg0 _) hδ2
    obtain ⟨M, hM, hSM⟩ : ∃ M, n ≤ M ∧ Valued.v
        (∑ i ∈ Finset.range (M + 1), y i * g ^ i)
        ≤ Valued.v g ^ (n + 1) * (δ / 2) := by
      obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp
        (hvan.eventually (valued_ball_mem_nhds_zero p F
          (hρ0 := hρ0) (hρ1 := hρ1) hε))
      exact ⟨max n M₀, le_max_left _ _, hM₀ _ (le_max_right _ _)⟩
    calc Valued.v (∑ i ∈ Finset.range (n + 1), y i * g ^ i)
        = Valued.v ((∑ i ∈ Finset.range (M + 1), y i * g ^ i)
          - ((∑ i ∈ Finset.range (M + 1), y i * g ^ i)
            - ∑ i ∈ Finset.range (n + 1), y i * g ^ i)) := by
          congr 1
          ring
      _ ≤ max (Valued.v (∑ i ∈ Finset.range (M + 1), y i * g ^ i))
          (Valued.v ((∑ i ∈ Finset.range (M + 1), y i * g ^ i)
            - ∑ i ∈ Finset.range (n + 1), y i * g ^ i)) :=
          Valuation.map_sub _ _ _
      _ ≤ Valued.v g ^ (n + 1) * (δ / 2) := max_le hSM (htail M hM)
  calc Valued.v (-(V ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), y i * g ^ i))
      = Valued.v V ^ (n + 1)
        * Valued.v (∑ i ∈ Finset.range (n + 1), y i * g ^ i) := by
        rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_pow]
    _ ≤ Valued.v V ^ (n + 1) * (Valued.v g ^ (n + 1) * (δ / 2)) :=
        mul_le_mul_of_nonneg_left hS zero_le
    _ = (Valued.v V * Valued.v g) ^ (n + 1) * (δ / 2) := by
        rw [mul_pow]
        ring
    _ = δ / 2 := by rw [hVg, one_pow, one_mul]
    _ < δ := NNReal.half_lt_self hδ.ne'

/-- **Kernel-solution decay, expanding scale** (the bottom-radius
component): with `1 < v(g)` the inverse powers contract and the solution
values decay — no vanishing hypothesis needed. -/
theorem kerSol_decay_of_one_lt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (g V : hatK p F hρ0 hρ1) (hinv : g * V = 1)
    (hg : 1 < Valued.v g) (y : ℕ → hatK p F hρ0 hρ1)
    (hy0 : Filter.Tendsto (fun n => Valued.v (y n)) Filter.atTop (nhds 0))
    (hybdd : BddAbove (Set.range (fun n => Valued.v (y n)))) :
    Filter.Tendsto (fun n => Valued.v
      (-(V ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), y i * g ^ i)))
      Filter.atTop (nhds 0) := by
  have hg0 : (0 : NNReal) < Valued.v g := lt_trans one_pos hg
  have hVg : Valued.v V * Valued.v g = 1 := by
    rw [← Valuation.map_mul, mul_comm V g, hinv, Valuation.map_one]
  have hV1 : Valued.v V < 1 := by
    by_contra hcon
    push Not at hcon
    have h2 : (1 : NNReal) * 1 < Valued.v V * Valued.v g := by
      calc (1 : NNReal) * 1 = 1 := one_mul 1
        _ ≤ 1 * Valued.v V := by rw [one_mul]; exact hcon
        _ < Valued.v g * Valued.v V := by
            exact mul_lt_mul_of_pos_right hg
              (lt_of_lt_of_le one_pos hcon)
        _ = Valued.v V * Valued.v g := mul_comm _ _
    rw [one_mul, hVg] at h2
    exact absurd h2 (lt_irrefl _)
  obtain ⟨B, hB⟩ := hybdd
  refine tendsto_order.mpr
    ⟨fun c hc => absurd hc (not_lt.mpr zero_le), fun δ hδ => ?_⟩
  have hδ2 : (0 : NNReal) < δ / 2 := half_pos hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((hy0.eventually_lt_const hδ2).mono fun i h => h.le)
  -- the head constant dies under the inverse powers
  have hhead : Filter.Tendsto
      (fun n : ℕ => B * Valued.v g ^ N * Valued.v V ^ (n + 1))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => Valued.v V ^ (n + 1))
        Filter.atTop (nhds 0) := by
      have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hV1
      have h3 := h2.comp (Filter.tendsto_add_atTop_nat 1)
      exact h3
    have h4 := h1.const_mul (B * Valued.v g ^ N)
    simpa using h4
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (hhead.eventually_lt_const hδ2)
  rw [Filter.eventually_atTop]
  refine ⟨max N N₂, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  -- the split sum bound
  have hS : Valued.v (∑ i ∈ Finset.range (n + 1), y i * g ^ i)
      ≤ max (B * Valued.v g ^ N) ((δ / 2) * Valued.v g ^ n) := by
    refine Valuation.map_sum_le _ (fun i hi => ?_)
    have hin : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    rw [Valuation.map_mul, Valuation.map_pow]
    by_cases hiN : i ≤ N
    · refine le_trans ?_ (le_max_left _ _)
      refine mul_le_mul (hB ⟨i, rfl⟩) ?_ zero_le zero_le
      exact pow_le_pow_right₀ hg.le hiN
    · refine le_trans ?_ (le_max_right _ _)
      refine mul_le_mul ?_ ?_ zero_le zero_le
      · exact hN i (by omega)
      · exact pow_le_pow_right₀ hg.le hin
  calc Valued.v (-(V ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), y i * g ^ i))
      = Valued.v V ^ (n + 1)
        * Valued.v (∑ i ∈ Finset.range (n + 1), y i * g ^ i) := by
        rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_pow]
    _ ≤ Valued.v V ^ (n + 1)
        * max (B * Valued.v g ^ N) ((δ / 2) * Valued.v g ^ n) :=
        mul_le_mul_of_nonneg_left hS zero_le
    _ = max (B * Valued.v g ^ N * Valued.v V ^ (n + 1))
        ((δ / 2) * (Valued.v g ^ n * Valued.v V ^ (n + 1))) := by
        rw [mul_max_of_nonneg _ _ (zero_le
          : (0:NNReal) ≤ Valued.v V ^ (n + 1))]
        congr 1
        · ring
        · ring
    _ ≤ max (δ / 2) (δ / 2) := by
        refine max_le_max ?_ ?_
        · exact (hN₂ n hnN₂).le
        · calc (δ / 2) * (Valued.v g ^ n * Valued.v V ^ (n + 1))
              = (δ / 2) * ((Valued.v V * Valued.v g) ^ n * Valued.v V) := by
                rw [mul_pow]
                ring
            _ = (δ / 2) * Valued.v V := by rw [hVg, one_pow, one_mul]
            _ ≤ (δ / 2) * 1 :=
                mul_le_mul_of_nonneg_left hV1.le zero_le
            _ = δ / 2 := mul_one _
    _ = δ / 2 := max_self _
    _ < δ := NNReal.half_lt_self hδ.ne'

/-- **The kernel solution at the subring level.** -/
noncomputable def kerSolElt (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hgu : IsUnit gB) (y : ℕ → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (n : ℕ) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  -(((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ^ (n + 1)
    * ∑ i ∈ Finset.range (n + 1), y i * gB ^ i)

/-- **Restrictedness of the kernel solution** from the interval-norm
decay. -/
theorem isRestricted_kerSol (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hgu : IsUnit gB) (y : ℕ → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hd : Filter.Tendsto (fun n => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((kerSolElt p F ϖ gB hgu y n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      Filter.atTop (nhds 0)) :
    MvPowerSeries.IsRestricted
      ((fun s => kerSolElt p F ϖ gB hgu y (s 0))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  set Ufun : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    (fun s => kerSolElt p F ϖ gB hgu y (s 0)) with hUdef
  rw [isRestricted_iff_wI]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hd.eventually_lt_const hε)
  have hsub : {s : Fin 1 →₀ ℕ | ε < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff s Ufun
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}
      ⊆ (fun s : Fin 1 →₀ ℕ => s 0) ⁻¹' {n : ℕ | n < N} := by
    intro s hs
    rw [Set.mem_setOf_eq] at hs
    show s 0 < N
    by_contra hcon
    push Not at hcon
    have hcoeff : (MvPowerSeries.coeff s Ufun
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        = kerSolElt p F ϖ gB hgu y (s 0) := rfl
    rw [hcoeff] at hs
    exact absurd (hN (s 0) hcon) (not_lt.mpr hs.le)
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.preimage ?_ (Set.finite_Iio N)
  intro a _ b _ hab
  have ha : a = Finsupp.single (0 : Fin 1) (a 0) := by
    refine Finsupp.ext fun i => ?_
    rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]
  have hb : b = Finsupp.single (0 : Fin 1) (b 0) := by
    refine Finsupp.ext fun i => ?_
    rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]
  have hab' : a 0 = b 0 := hab
  rw [ha, hb, hab']

/-- The per-coefficient kernel identity (hoisted for budget). -/
theorem kerSol_coeff_identity (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hgu : IsUnit gB)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) (n : ℕ) :
    (if 1 ≤ n then kerSolElt p F ϖ gB hgu
        (fun m => coeffSeq (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) m) (n - 1) else 0)
      - gB * kerSolElt p F ϖ gB hgu
        (fun m => coeffSeq (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) m) n
      = coeffSeq (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n := by
  have hinv : gB * (((hgu.unit⁻¹
      : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) = 1 := by
    have h := hgu.unit.mul_inv
    rwa [hgu.unit_spec] at h
  cases n with
  | zero =>
    exact kerSol_rec_generic gB
      (((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) hinv
      (fun m => coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) m) 0
  | succ m =>
    exact kerSol_rec_generic gB
      (((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) hinv
      (fun m' => coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) m') (m + 1)

/-- **The kernel factorization**: the generator times the kernel solution
recovers the original series. -/
theorem GeltElt_mul_kerSol (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hgu : IsUnit gB)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (hres : MvPowerSeries.IsRestricted
      ((fun s => kerSolElt p F ϖ gB hgu
        (fun n => coeffSeq (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n) (s 0))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    GeltElt p F ϖ gB * ⟨_, hres⟩ = f := by
  have hinv : gB * (((hgu.unit⁻¹
      : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) = 1 := by
    have h := hgu.unit.mul_inv
    rwa [hgu.unit_spec] at h
  apply Subtype.ext
  refine MvPowerSeries.ext fun s => ?_
  have hs : s = Finsupp.single (0 : Fin 1) (s 0) := by
    refine Finsupp.ext fun i => ?_
    rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]
  rw [hs]
  show coeffSeq ((GeltElt p F ϖ gB * (⟨_, hres⟩
      : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (s 0)
    = coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (s 0)
  rw [RPS_BI_coe_mul p F ϖ, GeltElt_coe p F ϖ, coeffSeq_Gelt_mul]
  have hcs : ∀ m : ℕ, coeffSeq (((⟨_, hres⟩
      : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : ↥(restrictedMvPowerSeriesSubring 1
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) m
      = kerSolElt p F ϖ gB hgu
        (fun n => coeffSeq (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n) m := fun m =>
    congrArg (kerSolElt p F ϖ gB hgu
      (fun n => coeffSeq (f : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n)) Finsupp.single_eq_same
  rw [hcs (s 0 - 1), hcs (s 0)]
  exact kerSol_coeff_identity p F ϖ gB hgu f (s 0)

/-- The kernel solution's second component. -/
theorem kerSolElt_coe_snd (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hgu : IsUnit gB) (y : ℕ → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (n : ℕ) :
    ((kerSolElt p F ϖ gB hgu y n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = -(((((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 ^ (n + 1)
        * ∑ i ∈ Finset.range (n + 1),
            ((y i : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
            * (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ i)) := by
  have hsum : ((((∑ i ∈ Finset.range (n + 1), y i * gB ^ i)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = ∑ i ∈ Finset.range (n + 1),
        ((y i : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
        * (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ i := by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact map_sum (AddMonoidHom.snd (hatK p F hρ₁0 hρ₁1)
      (hatK p F hρ₂0 hρ₂1)) _ _
  rw [kerSolElt]
  exact congrArg (fun t =>
    -((((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 ^ (n + 1) * t))
    hsum

/-- The kernel solution's first component. -/
theorem kerSolElt_coe_fst (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hgu : IsUnit gB) (y : ℕ → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (n : ℕ) :
    ((kerSolElt p F ϖ gB hgu y n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
      = -(((((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1 ^ (n + 1)
        * ∑ i ∈ Finset.range (n + 1),
            ((y i : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
            * (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ^ i)) := by
  have hsum : ((((∑ i ∈ Finset.range (n + 1), y i * gB ^ i)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
      = ∑ i ∈ Finset.range (n + 1),
        ((y i : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
        * (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ^ i := by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact map_sum (AddMonoidHom.fst (hatK p F hρ₁0 hρ₁1)
      (hatK p F hρ₂0 hρ₂1)) _ _
  rw [kerSolElt]
  exact congrArg (fun t =>
    -((((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1 ^ (n + 1) * t))
    hsum

/-- **The interval-norm decay of the kernel solution** from the two
component regimes. -/
theorem kerSolElt_wI_decay (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hgu : IsUnit gB)
    (hg1 : 1 < Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
    (hg2 : Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ≤ 1)
    (y : ℕ → ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hy1 : Filter.Tendsto (fun n => Valued.v
      (((y n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
      Filter.atTop (nhds 0))
    (hyb : BddAbove (Set.range (fun n => Valued.v
      (((y n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))))
    (hy2 : Filter.Tendsto (fun n => Valued.v
      (((y n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))
      Filter.atTop (nhds 0))
    (hvan : Filter.Tendsto (fun n => ∑ i ∈ Finset.range (n + 1),
        ((y i : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
        * (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ i)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((kerSolElt p F ϖ gB hgu y n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      Filter.atTop (nhds 0) := by
  have hinvS : gB * (((hgu.unit⁻¹
      : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) = 1 := by
    have h := hgu.unit.mul_inv
    rwa [hgu.unit_spec] at h
  have hinv1 : (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)
      * ((((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) = 1 :=
    congrArg (fun t : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) =>
      ((t : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) hinvS
  have hinv2 : (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
      * ((((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ)
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) = 1 :=
    congrArg (fun t : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) =>
      ((t : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) hinvS
  have hd1 := kerSol_decay_of_one_lt p F _ _ hinv1 hg1 _
    hy1 hyb
  have hd2 := kerSol_decay_of_le_one p F _ _ hinv2 hg2 _
    hy2 hvan
  have hd1' := hd1.congr (fun n =>
    (congrArg Valued.v (kerSolElt_coe_fst p F ϖ gB hgu y n)).symm)
  have hd2' := hd2.congr (fun n =>
    (congrArg Valued.v (kerSolElt_coe_snd p F ϖ gB hgu y n)).symm)
  have hmax := hd1'.max hd2'
  rw [max_self] at hmax
  exact hmax

section KerTransport

variable {σ₁ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))

/-- **The kernel-to-vanishing transport** (shared-top setting): if a
restricted series evaluates to zero, the second components of its partial
sums — which the contraction `φ` leaves untouched — tend to zero at the
top radius. -/
theorem tendsto_snd_partial_sums_of_evalBI_eq_zero
    (hφsnd : ∀ z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hb2 : b.2 = ((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    (U : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (hU : evalBI p F ϖ φ hφ hbmem hb U = 0) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range (n + 1),
        ((coeffSeq (U : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) i
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
        * (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ i)
      Filter.atTop (nhds 0) := by
  have h0 := tendsto_evalBI p F ϖ φ hφ hbmem hb U
  rw [hU] at h0
  have h2 : Filter.Tendsto (fun n => (∑ l ∈ Finset.range n,
      evalBITerm p F ϖ φ b
        (U : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l).2)
      Filter.atTop (nhds (0 : hatK p F hρ₂0 hρ₂1)) := by
    have hc := (continuous_snd.tendsto
      (0 : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))).comp h0
    exact hc
  have hterm : ∀ n, (∑ l ∈ Finset.range n,
      evalBITerm p F ϖ φ b
        (U : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l).2
      = ∑ l ∈ Finset.range n,
        ((coeffSeq (U : MvPowerSeries (Fin 1)
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
        * (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ l := by
    intro n
    refine (map_sum (AddMonoidHom.snd (hatK p F hσ₁0 hσ₁1)
      (hatK p F hρ₂0 hρ₂1)) _ (Finset.range n)).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    show (evalBITerm p F ϖ φ b
      (U : MvPowerSeries (Fin 1)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) l).2 = _
    rw [evalBITerm, Prod.snd_mul, Prod.pow_snd, hφsnd, hb2]
  have h3 := h2.congr hterm
  exact h3.comp (Filter.tendsto_add_atTop_nat 1)

end KerTransport

/-- First-component valuation decay of a restricted series' coefficients. -/
theorem tendsto_v_fst_coeffSeq
    {f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    Filter.Tendsto (fun n => Valued.v
        (((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_wI_coeffSeq p F ϖ hf)
    (fun n => (zero_le : (0 : NNReal) ≤ _))
    (fun n => le_max_left _ _)

/-- Second-component valuation decay of a restricted series' coefficients. -/
theorem tendsto_v_snd_coeffSeq
    {f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    Filter.Tendsto (fun n => Valued.v
        (((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2))
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_wI_coeffSeq p F ϖ hf)
    (fun n => (zero_le : (0 : NNReal) ≤ _))
    (fun n => le_max_right _ _)

/-- Boundedness of the first-component valuations of a restricted series'
coefficients. -/
theorem bddAbove_v_fst_coeffSeq
    {f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    BddAbove (Set.range (fun n => Valued.v
        (((coeffSeq f n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))) :=
  (tendsto_v_fst_coeffSeq p F ϖ hf).bddAbove_range

/-- Existence packaging of the kernel factorization (slim context). -/
theorem exists_factor_of_isRestricted_kerSol
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (hgu : IsUnit gB)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (hres : MvPowerSeries.IsRestricted
      ((fun s => kerSolElt p F ϖ gB hgu
        (fun n => coeffSeq (f : MvPowerSeries (Fin 1)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n) (s 0))
        : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    ∃ V : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      GeltElt p F ϖ gB * V = f :=
  ⟨⟨_, hres⟩, GeltElt_mul_kerSol p F ϖ gB hgu f hres⟩

/-- The degree-one monomial element (slim context). -/
noncomputable def GeltEltM1 : ↥(restrictedMvPowerSeriesSubring 1
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
  ⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 1)
      (1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
    isRestricted_monomial_BI p F ϖ _⟩

/-- The constant monomial element on the generator (slim context). -/
noncomputable def GeltEltM0 (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
  ⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 0) gB,
    isRestricted_monomial_BI p F ϖ _⟩

/-- The generator plus the constant term is the degree-one monomial
(slim context; keeps subtype subtraction out of evaluation contexts). -/
theorem GeltElt_add_M0 (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    GeltElt p F ϖ gB + GeltEltM0 p F ϖ gB = GeltEltM1 p F ϖ := by
  refine Subtype.ext ?_
  show (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 1)
      (1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    - MvPowerSeries.monomial 0 gB)
    + MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 0) gB
    = MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 1)
      (1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
  rw [Finsupp.single_zero, sub_add_cancel]

section KerAssembly

variable {σ₁ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))

/-- The evaluation hom's underlying value (micro-lemma). -/
theorem evalBIHom_coe
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) :
    ((evalBIHom p F ϖ φ hφ hbmem hb f : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
      = evalBI p F ϖ φ hφ hbmem hb f := rfl

/-- **The kernel factorization from vanishing evaluation** (Kedlaya Lemma
4.9, case 1, injectivity direction): any restricted series killed by the
evaluation is divisible by the generator `T - g`. -/
theorem exists_factor_of_evalBI_eq_zero
    (hφsnd : ∀ z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (hgu : IsUnit gB)
    (hb2 : b.2 = ((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    (hg1 : 1 < Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
    (hg2 : Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ≤ 1)
    (U : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (hU : evalBI p F ϖ φ hφ hbmem hb U = 0) :
    ∃ V : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      GeltElt p F ϖ gB * V = U := by
  have hvan := tendsto_snd_partial_sums_of_evalBI_eq_zero p F ϖ φ hφ
    hφsnd hbmem hb gB hb2 U hU
  have hd := kerSolElt_wI_decay p F ϖ gB hgu hg1 hg2
    (fun n => coeffSeq (U : MvPowerSeries (Fin 1)
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n)
    (tendsto_v_fst_coeffSeq p F ϖ U.2)
    (bddAbove_v_fst_coeffSeq p F ϖ U.2)
    (tendsto_v_snd_coeffSeq p F ϖ U.2) hvan
  have hres := isRestricted_kerSol p F ϖ gB hgu
    (fun n => coeffSeq (U : MvPowerSeries (Fin 1)
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) n) hd
  exact exists_factor_of_isRestricted_kerSol p F ϖ gB hgu U hres

/-- The evaluation of the degree-one monomial element. -/
theorem evalBI_GeltEltM1
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    evalBI p F ϖ φ hφ hbmem hb (GeltEltM1 p F ϖ) = b := by
  refine (evalBI_monomial p F ϖ φ hφ hbmem hb 1
    (1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (isRestricted_monomial_BI p F ϖ _)).trans ?_
  rw [map_one, OneMemClass.coe_one, one_mul, pow_one]

/-- The evaluation of the constant monomial element on the generator. -/
theorem evalBI_GeltEltM0
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hφgB : ((φ gB : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) = b) :
    evalBI p F ϖ φ hφ hbmem hb (GeltEltM0 p F ϖ gB) = b := by
  refine (evalBI_monomial p F ϖ φ hφ hbmem hb 0 gB
    (isRestricted_monomial_BI p F ϖ _)).trans ?_
  rw [hφgB, pow_zero, mul_one]

/-- **The generator is killed by the evaluation.** -/
theorem evalBIHom_GeltElt
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hφgB : ((φ gB : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) = b) :
    evalBIHom p F ϖ φ hφ hbmem hb (GeltElt p F ϖ gB) = 0 := by
  have h1 : evalBI p F ϖ φ hφ hbmem hb
      (GeltElt p F ϖ gB + GeltEltM0 p F ϖ gB)
      = evalBI p F ϖ φ hφ hbmem hb (GeltEltM1 p F ϖ) :=
    congrArg (evalBI p F ϖ φ hφ hbmem hb) (GeltElt_add_M0 p F ϖ gB)
  have h3 := (evalBI_add p F ϖ φ hφ hbmem hb
    (GeltElt p F ϖ gB) (GeltEltM0 p F ϖ gB)).symm.trans h1
  rw [evalBI_GeltEltM0 p F ϖ φ hφ hbmem hb gB hφgB,
    evalBI_GeltEltM1 p F ϖ φ hφ hbmem hb] at h3
  refine Subtype.ext ?_
  rw [evalBIHom_coe p F ϖ φ hφ hbmem hb, ZeroMemClass.coe_zero]
  exact add_right_cancel (h3.trans (zero_add b).symm)

end KerAssembly

/-- Span membership from a generator factorization (slim context). -/
theorem mem_span_GeltElt_of_factor (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (U : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (h : ∃ V : ↥(restrictedMvPowerSeriesSubring 1
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      GeltElt p F ϖ gB * V = U) :
    U ∈ Ideal.span {GeltElt p F ϖ gB} := by
  obtain ⟨V, hV⟩ := h
  exact hV ▸ Ideal.mul_mem_right V _
    (Ideal.subset_span (Set.mem_singleton _))

section KerAssembly

variable {σ₁ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))

/-- The span of the generator sits inside the kernel (easy inclusion). -/
theorem span_GeltElt_le_ker
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hφgB : ((φ gB : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) = b) :
    Ideal.span {GeltElt p F ϖ gB}
      ≤ RingHom.ker (evalBIHom p F ϖ φ hφ hbmem hb) := by
  refine Ideal.span_le.mpr ?_
  refine Set.singleton_subset_iff.mpr ?_
  exact RingHom.mem_ker.mpr (evalBIHom_GeltElt p F ϖ φ hφ hbmem hb gB hφgB)

/-- The kernel sits inside the span of the generator (hard inclusion). -/
theorem ker_le_span_GeltElt
    (hφsnd : ∀ z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (hgu : IsUnit gB)
    (hb2 : b.2 = ((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    (hg1 : 1 < Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
    (hg2 : Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ≤ 1) :
    RingHom.ker (evalBIHom p F ϖ φ hφ hbmem hb)
      ≤ Ideal.span {GeltElt p F ϖ gB} := by
  intro U hUker
  have hU : evalBI p F ϖ φ hφ hbmem hb U = 0 := by
    rw [← evalBIHom_coe p F ϖ φ hφ hbmem hb U, RingHom.mem_ker.mp hUker]
    exact ZeroMemClass.coe_zero _
  exact mem_span_GeltElt_of_factor p F ϖ gB U
    (exists_factor_of_evalBI_eq_zero p F ϖ φ hφ hφsnd
      hbmem hb gB hgu hb2 hg1 hg2 U hU)

/-- **The kernel of the case-1 presentation is the principal ideal on the
generator** (Kedlaya Lemma 4.9, case 1, the kernel computation). -/
theorem ker_evalBIHom_eq_span
    (hφsnd : ∀ z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (hgu : IsUnit gB)
    (hφgB : ((φ gB : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) = b)
    (hg1 : 1 < Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
    (hg2 : Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ≤ 1) :
    RingHom.ker (evalBIHom p F ϖ φ hφ hbmem hb)
      = Ideal.span {GeltElt p F ϖ gB} := by
  have hb2 : b.2 = ((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 := by
    rw [← hφgB, hφsnd]
  exact le_antisymm
    (ker_le_span_GeltElt p F ϖ φ hφ hφsnd hbmem hb gB hgu hb2 hg1 hg2)
    (span_GeltElt_le_ker p F ϖ φ hφ hbmem hb gB hφgB)

end KerAssembly

section Surjectivity

variable {σ₁ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
variable (hφb : ∀ x : Bloc p F ϖ,
  ((φ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
    : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
    : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x)

/-- The evaluation of a constant coefficient element. -/
theorem evalBI_GeltEltM0_eq
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (c : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    evalBI p F ϖ φ hφ hbmem hb (GeltEltM0 p F ϖ c)
      = ((φ c : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
  refine (evalBI_monomial p F ϖ φ hφ hbmem hb 0 c
    (isRestricted_monomial_BI p F ϖ _)).trans ?_
  rw [pow_zero, mul_one]

/-- The scaled element stays in the interval subring with unit norm. -/
theorem exists_p_scaling
    (z : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    ∃ k : ℕ, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (pImage p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 ^ k * z) ≤ 1 := by
  have hbound : ∀ k : ℕ, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (pImage p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 ^ k * z)
      ≤ (max σ₁ ρ₂) ^ k * wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z := by
    intro k
    refine le_trans (wI_mul_le p F _ _) ?_
    rw [wI_pow, pImage, wI_p_image]
  rcases eq_or_ne (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z) 0 with h0 | hne
  · exact ⟨0, le_trans (hbound 0) (by rw [h0, mul_zero]; exact zero_le_one)⟩
  · have hr1 : max σ₁ ρ₂ < 1 := max_lt hσ₁1 hρ₂1
    have hipos : (0 : NNReal) < (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z)⁻¹ :=
      inv_pos.mpr (pos_of_ne_zero hne)
    obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hipos hr1
    refine ⟨k, le_trans (hbound k) ?_⟩
    refine le_of_lt ?_
    calc (max σ₁ ρ₂) ^ k * wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z
        < (wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z)⁻¹
          * wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 z := by
          exact mul_lt_mul_of_pos_right hk (pos_of_ne_zero hne)
      _ = 1 := inv_mul_cancel₀ hne

include hφb in
/-- **Surjectivity of the case-1 evaluation** (Kedlaya Lemma 4.9, case 1):
every element of the cut interval ring is a value, by `p`-power rescaling
into the unit ball. -/
theorem surjective_evalBIHom
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m₀ : ℕ) (hm₀ : 0 < m₀)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m₀)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀)) :
    Function.Surjective (evalBIHom p F ϖ φ hφ hbmem hb) := by
  intro zsub
  obtain ⟨k, hk⟩ := exists_p_scaling p F ϖ
    ((zsub : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  have hz'mem : pImage p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 ^ k
      * ((zsub : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
      ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 :=
    mul_mem (pow_mem (BIProd_mem_BISub p F ϖ _) k) zsub.2
  obtain ⟨U', hU'eq, -⟩ := exists_evalBI_eq_of_le_one p F ϖ φ hφ hφb
    hρσ hσρ zb m₀ hm₀ hgen hbmem hb hbg hz'mem hk
  refine ⟨GeltEltM0 p F ϖ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
    (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ k)) * U', ?_⟩
  have hinv : (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)
      * algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) = 1 := by
    have h := (isUnit_p_image p F ϖ).unit.inv_mul
    rwa [(isUnit_p_image p F ϖ).unit_spec] at h
  have hvpalg : ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ k
      * algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) ^ k = 1 := by
    rw [← mul_pow, hinv, one_pow]
  have h1 : pImage p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 ^ k
      = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
        (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) ^ k) :=
    (map_pow (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
      (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)) k).symm
  have h2 : BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
        (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ k)
      * BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
        (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) ^ k) = 1 :=
    ((map_mul (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
        (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ k)
        (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) ^ k)).symm).trans
      ((congrArg (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1) hvpalg).trans
        (map_one _))
  have hfinal : BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
        (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ k)
      * (pImage p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 ^ k
        * ((zsub : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)))
      = ((zsub : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
    rw [h1, ← mul_assoc, h2, one_mul]
  refine Subtype.ext ?_
  rw [evalBIHom_coe p F ϖ φ hφ hbmem hb,
    evalBI_mul p F ϖ φ hφ hbmem hb,
    evalBI_GeltEltM0_eq p F ϖ φ hφ hbmem hb]
  exact (congrArg (fun t =>
      ((φ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ k))
        : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) * t) hU'eq).trans
    ((congrArg (fun s => s * (pImage p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 ^ k
        * ((zsub : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))))
      (hφb (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ k))).trans
      hfinal)

end Surjectivity

section Case1Iso

variable {σ₁ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
variable (hφb : ∀ x : Bloc p F ϖ,
  ((φ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
    : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
    : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x)

include φ hφ hφb in
/-- **The case-1 Robba presentation** (Kedlaya Lemma 4.9, case 1): the cut
interval ring is the quotient of the restricted power series ring over
`B^I` by the principal ideal on `T - g`. -/
theorem nonempty_case1_quotient_equiv
    (hφsnd : ∀ z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m₀ : ℕ) (hm₀ : 0 < m₀)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m₀)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀))
    (gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (hgu : IsUnit gB)
    (hφgB : ((φ gB : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) = b)
    (hg1 : 1 < Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1))
    (hg2 : Valued.v (((gB : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ≤ 1) :
    Nonempty
      ((↥(restrictedMvPowerSeriesSubring 1
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        ⧸ Ideal.span {GeltElt p F ϖ gB})
      ≃+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)) := by
  have hker := ker_evalBIHom_eq_span p F ϖ φ hφ hφsnd hbmem hb
    gB hgu hφgB hg1 hg2
  have hsurj := surjective_evalBIHom p F ϖ φ hφ hφb
    hρσ hσρ zb m₀ hm₀ hgen hbmem hb hbg
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)⟩

end Case1Iso

/-- A nonzero-valuation integral element divides a pseudo-uniformizer power. -/
theorem dvd_pow_pseudoUniformizer (zb : OF F)
    (hzb : perfectoidValuation p F (zb : F) ≠ 0) :
    ∃ j : ℕ, zb ∣ PseudoUniformizer.toOF F ϖ ^ j := by
  obtain ⟨j, hj⟩ := NNReal.exists_pow_lt_of_lt_one (pos_of_ne_zero hzb)
    (perfectoidValuation_toOF_lt_one p F ϖ)
  refine ⟨j, (perfectoidValuation_integers p F).dvd_of_le ?_⟩
  have hcoe : ((PseudoUniformizer.toOF F ϖ ^ j : OF F) : F)
      = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ j := by
    push_cast
    rfl
  calc perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ ^ j : OF F) : F)
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ j := by
        rw [hcoe, map_pow]
    _ ≤ perfectoidValuation p F (zb : F) := hj.le

/-- **The generator's Teichmüller factor is a unit of `B_loc`**: its
coordinate divides a pseudo-uniformizer power, whose Teichmüller image is
inverted. -/
theorem isUnit_teichmuller_image (zb : OF F)
    (hzb : perfectoidValuation p F (zb : F) ≠ 0) :
    IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ)
      (WittVector.teichmuller p zb)) := by
  obtain ⟨j, c, hc⟩ := dvd_pow_pseudoUniformizer p F ϖ zb hzb
  refine isUnit_of_mul_isUnit_left
    (y := algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c)) ?_
  rw [← map_mul, ← map_mul]
  have hteich : WittVector.teichmuller p (zb * c)
      = teichPi p F ϖ ^ j := by
    rw [← hc, teichPi, ← teichPi_pow]
    rfl
  rw [hteich, map_pow]
  exact (isUnit_teichPi_image p F ϖ).pow j

/-- **The case-1 generator is a unit of `B_loc`.** -/
theorem isUnit_teichPowGen (zb : OF F)
    (hzb : perfectoidValuation p F (zb : F) ≠ 0) (m₀ : ℕ) :
    IsUnit (teichPowGen p F ϖ zb m₀) := by
  rw [teichPowGen]
  exact (isUnit_teichmuller_image p F ϖ zb hzb).mul
    (((isUnit_p_image p F ϖ).unit⁻¹).isUnit.pow m₀)

/-- **The generator's local valuation** at radius `ρ`. -/
theorem wLoc_teichPowGen {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (zb : OF F) (m₀ : ℕ) :
    wLoc p F ϖ hρ0 hρ1 (teichPowGen p F ϖ zb m₀)
      = perfectoidValuation p F (zb : F) * (ρ ^ m₀)⁻¹ := by
  rw [teichPowGen, map_mul, map_pow, wLoc_algebraMap,
    gaussValue_teichmuller p F hρ1.le, wLoc_p_inv, inv_pow]

/-- **The generator's valuation at the interval endpoints** (`B^I`-level). -/
theorem valued_blocToBI_teichPowGen_fst
    {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (zb : OF F) (m₀ : ℕ) :
    Valued.v (((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowGen p F ϖ zb m₀)
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)
      = perfectoidValuation p F (zb : F) * (ρ₁ ^ m₀)⁻¹ := by
  rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
    = BlocToHatK p F ϖ hρ₁0 hρ₁1 (teichPowGen p F ϖ zb m₀) from rfl,
    valued_BlocToHatK, wLoc_teichPowGen]

/-- **The generator's valuation at the top endpoint** (`B^I`-level). -/
theorem valued_blocToBI_teichPowGen_snd
    {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (zb : OF F) (m₀ : ℕ) :
    Valued.v (((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowGen p F ϖ zb m₀)
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
      = perfectoidValuation p F (zb : F) * (ρ₂ ^ m₀)⁻¹ := by
  rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m₀)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
    = BlocToHatK p F ϖ hρ₂0 hρ₂1 (teichPowGen p F ϖ zb m₀) from rfl,
    valued_BlocToHatK, wLoc_teichPowGen]

/-- The strict lower generator bound at the bottom radius. -/
theorem one_lt_gen_val {ρ₁ σ₁ : NNReal} (hρ₁0 : 0 < ρ₁)
    (hρσ : ρ₁ < σ₁) (m₀ : ℕ) (hm₀ : 0 < m₀) :
    1 < σ₁ ^ m₀ * (ρ₁ ^ m₀)⁻¹ := by
  have hpow : ρ₁ ^ m₀ < σ₁ ^ m₀ :=
    pow_lt_pow_left₀ hρσ hρ₁0.le hm₀.ne'
  have hpos : (0 : NNReal) < (ρ₁ ^ m₀)⁻¹ :=
    inv_pos.mpr (pow_pos hρ₁0 m₀)
  calc (1 : NNReal) = ρ₁ ^ m₀ * (ρ₁ ^ m₀)⁻¹ :=
      (mul_inv_cancel₀ (pow_pos hρ₁0 m₀).ne').symm
    _ < σ₁ ^ m₀ * (ρ₁ ^ m₀)⁻¹ := mul_lt_mul_of_pos_right hpow hpos

/-- The generator bound at the top radius. -/
theorem gen_val_le_one {σ₁ ρ₂ : NNReal} (hρ₂0 : 0 < ρ₂)
    (hσρ : σ₁ ≤ ρ₂) (m₀ : ℕ) :
    σ₁ ^ m₀ * (ρ₂ ^ m₀)⁻¹ ≤ 1 := by
  have hpow : σ₁ ^ m₀ ≤ ρ₂ ^ m₀ := pow_le_pow_left' hσρ m₀
  calc σ₁ ^ m₀ * (ρ₂ ^ m₀)⁻¹ ≤ ρ₂ ^ m₀ * (ρ₂ ^ m₀)⁻¹ :=
      mul_le_mul_left hpow _
    _ = 1 := mul_inv_cancel₀ (pow_pos hρ₂0 m₀).ne'

/-- **The top-anchored restriction pair lands in the sub-interval ring**:
the second coordinate is kept literally. -/
theorem resI_top_pair_mem {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1 z, z.2)
      ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 := by
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hz
  have h1 := tendsto_resI p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 hz
  have h2 : Filter.Tendsto (fun x => BlocToHatK p F ϖ hρ₂0 hρ₂1 x)
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds z.2) := by
    have hb : Filter.Tendsto
        (fun x => (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x).2)
        (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
        (nhds z.2) :=
      (continuous_snd.tendsto z).comp Filter.tendsto_comap
    refine hb.congr fun x => ?_
    exact BIProd_snd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
  have hpair : Filter.Tendsto (fun x => (BlocToHatK p F ϖ hσ₁0 hσ₁1 x,
        BlocToHatK p F ϖ hρ₂0 hρ₂1 x))
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1 z, z.2)) :=
    Filter.Tendsto.prodMk_nhds h1 h2
  have hmem : ∀ᶠ x in Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      (nhds z),
      (BlocToHatK p F ϖ hσ₁0 hσ₁1 x, BlocToHatK p F ϖ hρ₂0 hρ₂1 x)
        ∈ (Set.range (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)) :=
    Filter.Eventually.of_forall fun x => ⟨x, rfl⟩
  exact mem_closure_of_tendsto hpair hmem

/-- **The top-anchored restriction hom** `B^I → B^{[σ₁,ρ₂]}`: first
coordinate restricted, top coordinate kept literally (so the shared-top
kernel machinery applies without radius transport). -/
def resIHomTop {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1) :
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1) where
  toFun z := ⟨(resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1 (z : _),
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2),
    resI_top_pair_mem p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2⟩
  map_one' := by
    have hone : ((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 1 := by
      rw [map_one]
      rfl
    have e1 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1
        ((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 1 := by
      rw [hone, resI_BIProd p F ϖ hθ0 hθ1 hσ₁0 hσ₁1, map_one]
    have e2 : ((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 = 1 := rfl
    refine Subtype.ext ?_
    rw [show ((1 : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) = (1, 1) from rfl]
    exact Prod.ext e1 e2
  map_mul' := fun z z' => by
    have e1 := resI_mul p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2 z'.2
    refine Subtype.ext ?_
    exact Prod.ext e1 rfl
  map_zero' := by
    have hzero : ((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 0 := by
      rw [map_zero]
      rfl
    have e1 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1
        ((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 0 := by
      rw [hzero, resI_BIProd p F ϖ hθ0 hθ1 hσ₁0 hσ₁1, map_zero]
    have e2 : ((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 = 0 := rfl
    refine Subtype.ext ?_
    rw [show ((0 : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)) = (0, 0) from rfl]
    exact Prod.ext e1 e2
  map_add' := fun z z' => by
    have e1 := resI_add p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2 z'.2
    refine Subtype.ext ?_
    exact Prod.ext e1 rfl

/-- The top-anchored restriction contracts the interval norm. -/
theorem wI_resIHomTop_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
        ((resIHomTop p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z
          : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
          : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
  refine max_le ?_ ?_
  · exact valued_resI_le_wI p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2
  · exact le_max_right _ _

/-- The top-anchored restriction fixes the second coordinate. -/
theorem resIHomTop_snd {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    ((resIHomTop p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z
      : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 := rfl

/-- The top-anchored restriction carries `Bloc`-images to `Bloc`-images. -/
theorem resIHomTop_blocToBI {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (x : Bloc p F ϖ) :
    ((resIHomTop p F ϖ hθ0 hθ1 hσ₁0 hσ₁1
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
        : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x := by
  refine Prod.ext ?_ ?_
  · show resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1
        ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x).1
    rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x from rfl]
    rw [resI_BIProd p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 x,
      BIProd_fst p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x]
  · show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = (BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x).2
    rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x from rfl]
    rw [BIProd_snd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x,
      BIProd_snd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x]

/-- **Every intermediate radius is a geometric interpolant** of the interval
endpoints. -/
theorem exists_interpolant {ρ₁ σ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁)
    (hρσ : ρ₁ ≤ σ) (hσρ : σ ≤ ρ₂) (hρ₂1 : ρ₂ < 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ ρ₁ ^ θ * ρ₂ ^ (1 - θ) = σ := by
  have hσ0 : 0 < σ := lt_of_lt_of_le hρ₁0 hρσ
  have hρ₂0 : 0 < ρ₂ := lt_of_lt_of_le hσ0 hσρ
  rcases eq_or_lt_of_le (le_trans hρσ hσρ) with heq | hlt
  · -- ρ₁ = ρ₂ forces σ = ρ₁; θ = 1 works
    have hσeq : σ = ρ₁ := le_antisymm (heq ▸ hσρ) hρσ
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [sub_self, NNReal.rpow_one, NNReal.rpow_zero, mul_one, hσeq]
  · -- strict case: solve on the log scale
    have ha : (0 : ℝ) < (ρ₁ : ℝ) := hρ₁0
    have hb : (0 : ℝ) < (ρ₂ : ℝ) := hρ₂0
    have hs : (0 : ℝ) < (σ : ℝ) := hσ0
    have hab : (ρ₁ : ℝ) < (ρ₂ : ℝ) := hlt
    have hlog : Real.log (ρ₁ : ℝ) < Real.log (ρ₂ : ℝ) :=
      Real.log_lt_log ha hab
    have hden : Real.log (ρ₁ : ℝ) - Real.log (ρ₂ : ℝ) < 0 :=
      sub_neg.mpr hlog
    have hnum : Real.log (σ : ℝ) - Real.log (ρ₂ : ℝ) ≤ 0 :=
      sub_nonpos.mpr (Real.log_le_log hσ0 hσρ)
    have hnum' : Real.log (ρ₁ : ℝ) - Real.log (ρ₂ : ℝ)
        ≤ Real.log (σ : ℝ) - Real.log (ρ₂ : ℝ) :=
      sub_le_sub_right (Real.log_le_log hρ₁0 hρσ) _
    refine ⟨(Real.log (σ : ℝ) - Real.log (ρ₂ : ℝ))
      / (Real.log (ρ₁ : ℝ) - Real.log (ρ₂ : ℝ)),
      by
        rw [← neg_div_neg_eq]
        exact div_nonneg (neg_nonneg.mpr hnum) (neg_nonneg.mpr hden.le),
      ?_, ?_⟩
    · rw [div_le_one_of_neg hden]
      exact hnum'
    · set θ := (Real.log (σ : ℝ) - Real.log (ρ₂ : ℝ))
        / (Real.log (ρ₁ : ℝ) - Real.log (ρ₂ : ℝ)) with hθdef
      have hd0 : Real.log (ρ₁ : ℝ) - Real.log (ρ₂ : ℝ) ≠ 0 := hden.ne
      have hkey : Real.log (ρ₁ : ℝ) * θ + Real.log (ρ₂ : ℝ) * (1 - θ)
          = Real.log (σ : ℝ) := by
        calc Real.log (ρ₁ : ℝ) * θ + Real.log (ρ₂ : ℝ) * (1 - θ)
            = θ * (Real.log (ρ₁ : ℝ) - Real.log (ρ₂ : ℝ))
              + Real.log (ρ₂ : ℝ) := by ring
          _ = (Real.log (σ : ℝ) - Real.log (ρ₂ : ℝ)) + Real.log (ρ₂ : ℝ) := by
              rw [hθdef, div_mul_cancel₀ _ hd0]
          _ = Real.log (σ : ℝ) := sub_add_cancel _ _
      refine NNReal.coe_injective ?_
      push_cast [NNReal.coe_rpow]
      rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb,
        ← Real.exp_add, hkey, Real.exp_log hs]

end FarguesFontaine

end
