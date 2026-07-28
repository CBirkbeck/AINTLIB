/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Heads

/-!
# The tail decomposition and the twisted `c₀`-sum ([WP] §6.4)

The isometric Banach-decomposition `𝒜 ≅ ⊕̂^{c₀}_μ 𝒜_N e_μ` ([WP]
eq:tail-decomposition) is carried COEFFICIENTWISE: for each tail index `μ` the
`μ`-th component of `f ∈ 𝒜` is a head element (`tailCoeff`), the `μ = 0` component is
the norm-nonincreasing algebra retraction `ρ_N` ([WP] eq:head-retraction), and
multiplication obeys the twisted rule `e_μ e_λ = W^{ω(μ)+ω(λ)−ω(μ+λ)} e_{μ+λ}`
([WP] eq:tail-multiplication).

The abstract receptacle is `TailC0`: for a normed ultrametric commutative ring `P`
and a "twist element" `ρ` of norm `≤ 1` (the image of `W`), the null families
`TailIdx N → P` with sup norm and `ρ`-twisted convolution.  Instances of `TailC0`
appear as: the model of every rational localization of `𝒜`
([WP] prop:coefficientwise-localization, cor:finite-head-presentation) and the bad
chart `ℬ` itself ([WP] §6.2 — the weighted norm of eq:weighted-chart-norm is exactly
the plain sup norm in the twisted coordinates).

The embedding `Φ : TailC0 → MvPowerSeries` ([WP] eq:formal-embedding,
`x ↦ ∑ ρ^{ω(μ)} x_μ U^μ`) is also defined here; it is multiplicative BECAUSE of the
twist and injective when `ρ` is regular, and serves both the reducedness theorem
([WP] thm:parity-rationally-reduced) and the domain property of the chart
([WP] prop:weighted-chart-domain-nonuniform).
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver Filter Topology

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-! ### Coefficientwise tail decomposition of `𝒜` -/

/-- The `μ`-th tail coefficient of `f ∈ 𝒜`: the head element whose `h`-th coefficient
is the `(h + tailShift μ)`-th coefficient of `f` ([WP] eq:tail-decomposition, read
coefficientwise via the exponent splitting of `WP/Weight.lean`). -/
noncomputable def tailCoeff (μ : TailIdx N) (f : WPA K w) : WPHead K w N := by
  classical
  refine ⟨⟨fun h => if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0, ?_⟩,
    fun h hh => by
      show (if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0) = 0
      rw [if_neg hh]⟩
  show MvPowerSeries.IsRestrictedGauss _ _
  have hchar : ∀ ε' : ℝ, 0 < ε' → {h : ℕ →₀ ℕ |
      ε' ≤ ‖(if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0 : K)‖}.Finite := by
    intro ε' hε'
    have hfin := finite_setOf_le_norm_coeff (f := f.1) hε'
    refine (hfin.preimage
      (Set.injOn_of_injective (add_left_injective (tailShift w μ)))).subset ?_
    intro h hu
    rw [Set.mem_setOf_eq] at hu
    by_cases hmem : HeadMem w N h
    · rw [if_pos hmem] at hu
      exact hu
    · rw [if_neg hmem, norm_zero] at hu
      exact absurd (hε'.trans_le hu) (lt_irrefl 0)
  show Filter.Tendsto _ Filter.cofinite (nhds 0)
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  rw [Filter.eventually_cofinite]
  refine (hchar ε' hε').subset ?_
  intro h hu
  rw [Set.mem_setOf_eq] at hu ⊢
  rw [Real.dist_eq, sub_zero, prod_one_weights, mul_one] at hu
  rw [abs_of_nonneg (norm_nonneg _)] at hu
  exact not_lt.mp hu

open scoped Classical in
variable {K w N} in
/-- The coefficients of a tail coefficient, unconditionally. -/
theorem coeff_tailCoeff (μ : TailIdx N) (f : WPA K w) (h : ℕ →₀ ℕ) :
    MvPowerSeries.coeff h (tailCoeff K w N μ f).1.1 =
      if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0 := rfl

@[simp] theorem coeffA_tailCoeff (μ : TailIdx N) (f : WPA K w) {h : ℕ →₀ ℕ}
    (hh : HeadMem w N h) :
    MvPowerSeries.coeff h (tailCoeff K w N μ f).1.1 =
      coeffA K w (h + tailShift w μ) f := by
  classical
  rw [coeff_tailCoeff, if_pos hh]

theorem tailCoeff_add (μ : TailIdx N) (f g : WPA K w) :
    tailCoeff K w N μ (f + g) = tailCoeff K w N μ f + tailCoeff K w N μ g := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  show MvPowerSeries.coeff h (tailCoeff K w N μ (f + g)).1.1 =
    MvPowerSeries.coeff h ((tailCoeff K w N μ f).1.1 + (tailCoeff K w N μ g).1.1)
  rw [map_add, coeff_tailCoeff, coeff_tailCoeff, coeff_tailCoeff]
  have hadd : coeffA K w (h + tailShift w μ) (f + g) =
      coeffA K w (h + tailShift w μ) f + coeffA K w (h + tailShift w μ) g := by
    show MvPowerSeries.coeff (h + tailShift w μ) ((f + g).1.1) = _
    rw [show ((f + g).1.1 : MvPowerSeries ℕ K) = f.1.1 + g.1.1 from rfl, map_add]
    rfl
  rw [hadd]
  split_ifs <;> simp

theorem norm_tailCoeff_le (μ : TailIdx N) (f : WPA K w) :
    ‖tailCoeff K w N μ f‖ ≤ ‖f‖ := by
  classical
  rw [show ‖tailCoeff K w N μ f‖ = ‖headIncl K w N (tailCoeff K w N μ f)‖ from rfl,
    norm_eq_iSup_coeffA]
  refine ciSup_le fun t => ?_
  show ‖MvPowerSeries.coeff t (tailCoeff K w N μ f).1.1‖ ≤ ‖f‖
  rw [coeff_tailCoeff]
  split_ifs with hmem
  · exact norm_coeffA_le K w _ f
  · simpa using norm_nonneg f

/-- The tail coefficients of a fixed element form a null family ([WP]
eq:tail-decomposition: the decomposition is a `c₀`-sum). -/
theorem tendsto_norm_tailCoeff_cofinite (f : WPA K w) :
    Tendsto (fun μ : TailIdx N => ‖tailCoeff K w N μ f‖) cofinite (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hfin := finite_setOf_le_norm_coeff (f := f.1) (half_pos hε)
  refine ((hfin.image fun t => tailPart N t).subset ?_)
  intro μ hμ
  rw [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _),
    not_lt] at hμ
  by_contra hcon
  have hall : ∀ h : ℕ →₀ ℕ,
      ‖MvPowerSeries.coeff h (tailCoeff K w N μ f).1.1‖ ≤ ε / 2 := by
    intro h
    rw [coeff_tailCoeff]
    split_ifs with hmem
    · by_contra hgt
      push_neg at hgt
      exact hcon ⟨h + tailShift w μ, hgt.le, tailPart_of_headMem_add hmem μ⟩
    · simpa using (half_pos hε).le
  have hnorm : ‖tailCoeff K w N μ f‖ ≤ ε / 2 := by
    rw [show ‖tailCoeff K w N μ f‖ = ‖headIncl K w N (tailCoeff K w N μ f)‖ from rfl,
      norm_eq_iSup_coeffA]
    exact ciSup_le fun t => hall t
  linarith [hμ.trans hnorm]

theorem norm_eq_iSup_tailCoeff (f : WPA K w) :
    ‖f‖ = ⨆ μ : TailIdx N, ‖tailCoeff K w N μ f‖ := by
  classical
  have hbdd : BddAbove (Set.range fun μ : TailIdx N => ‖tailCoeff K w N μ f‖) :=
    ⟨‖f‖, Set.forall_mem_range.mpr fun μ => norm_tailCoeff_le K w N μ f⟩
  apply le_antisymm
  · rw [norm_eq_iSup_coeffA]
    refine ciSup_le fun t => ?_
    by_cases ht : WPMem w t
    · have hh := headMem_headPart (w := w) (N := N) ht
      have hco : coeffA K w t f =
          MvPowerSeries.coeff (headPart w N t)
            (tailCoeff K w N (tailPart N t) f).1.1 := by
        rw [coeffA_tailCoeff K w N (tailPart N t) f hh,
          headPart_add_tailShift (w := w) (N := N) ht]
      rw [hco]
      exact le_trans
        (norm_coeff_le_one_norm (tailCoeff K w N (tailPart N t) f).1 (headPart w N t))
        (le_ciSup hbdd (tailPart N t))
    · rw [coeffA_of_not_wpMem K w ht f, norm_zero]
      exact le_trans (norm_nonneg (tailCoeff K w N 0 f)) (le_ciSup hbdd 0)
  · exact ciSup_le fun μ => norm_tailCoeff_le K w N μ f

/-- Separation: an element of `𝒜` is determined by its tail coefficients. -/
theorem tailCoeff_injective :
    Function.Injective (fun (f : WPA K w) (μ : TailIdx N) => tailCoeff K w N μ f) := by
  classical
  intro f g hfg
  apply coeffA_injective K w
  funext t
  show coeffA K w t f = coeffA K w t g
  by_cases ht : WPMem w t
  · have hh := headMem_headPart (w := w) (N := N) ht
    have h1 : tailCoeff K w N (tailPart N t) f = tailCoeff K w N (tailPart N t) g :=
      congrFun hfg (tailPart N t)
    rw [← headPart_add_tailShift (w := w) (N := N) ht,
      ← coeffA_tailCoeff K w N (tailPart N t) f hh,
      ← coeffA_tailCoeff K w N (tailPart N t) g hh, h1]
  · rw [coeffA_of_not_wpMem K w ht f, coeffA_of_not_wpMem K w ht g]

/-- The `e_μ` basis element `W^{ω(μ)} U^μ` of `𝒜` ([WP] eq:tail-basis). -/
noncomputable def eTail (μ : TailIdx N) : WPA K w :=
  wpMonomial K w (wpMem_tailShift w μ) 1

@[simp] theorem tailCoeff_headIncl_mul_eTail (μ ν : TailIdx N) (x : WPHead K w N) :
    tailCoeff K w N ν (headIncl K w N x * eTail K w N μ) =
      if ν = μ then x else 0 := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff]
  have hco : coeffA K w (h + tailShift w ν) (headIncl K w N x * eTail K w N μ) =
      MvPowerSeries.coeff (h + tailShift w ν)
        (x.1.1 * MvPowerSeries.monomial (tailShift w μ) (1 : K)) := rfl
  by_cases hνμ : ν = μ
  · subst hνμ
    rw [if_pos rfl]
    by_cases hmem : HeadMem w N h
    · rw [if_pos hmem, hco, MvPowerSeries.coeff_add_mul_monomial, mul_one]
    · rw [if_neg hmem]
      exact (x.2 h hmem).symm
  · rw [if_neg hνμ]
    have h0 : MvPowerSeries.coeff h ((0 : WPHead K w N)).1.1 = 0 := by
      show MvPowerSeries.coeff h (0 : MvPowerSeries ℕ K) = 0
      simp
    rw [h0]
    by_cases hmem : HeadMem w N h
    · rw [if_pos hmem, hco, MvPowerSeries.coeff_mul_monomial]
      split_ifs with hle
      · rw [mul_one]
        refine x.2 _ fun hE => hνμ (Subtype.ext (Finsupp.ext fun n => ?_))
        by_cases hn : N < n
        · have hh0 : h n = 0 := hmem.2 n hn
          have hE0 := hE.2 n hn
          have hlen : (tailShift w μ) n ≤ (h + tailShift w ν) n :=
            Finsupp.le_def.mp hle n
          have hsμ : (tailShift w μ) n = μ.1 n := by
            show (Finsupp.single 0 (wpWeight w μ.1) + μ.1 : ℕ →₀ ℕ) n = μ.1 n
            rw [Finsupp.add_apply, Finsupp.single_apply,
              if_neg (by omega : ¬ (0 = n)), zero_add]
          have hsν : (tailShift w ν) n = ν.1 n := by
            show (Finsupp.single 0 (wpWeight w ν.1) + ν.1 : ℕ →₀ ℕ) n = ν.1 n
            rw [Finsupp.add_apply, Finsupp.single_apply,
              if_neg (by omega : ¬ (0 = n)), zero_add]
          rw [Finsupp.tsub_apply, Finsupp.add_apply, hsμ, hsν, hh0] at hE0
          rw [Finsupp.add_apply, hsμ, hsν, hh0] at hlen
          omega
        · rw [μ.prop n (by omega), ν.prop n (by omega)]
      · rfl
    · rw [if_neg hmem]

variable {w N} in
@[simp] theorem tailShift_zero : tailShift w (0 : TailIdx N) = 0 := by
  show Finsupp.single 0 (wpWeight w (0 : TailIdx N).1) + (0 : TailIdx N).1 = 0
  rw [TailIdx.zero_val, wpWeight_zero, Finsupp.single_zero, add_zero]

open scoped Classical in
variable {K w N} in
/-- The `μ = 0` tail coefficient reads the head coefficients in place. -/
theorem coeff_tailCoeff_zero (f : WPA K w) (h : ℕ →₀ ℕ) :
    MvPowerSeries.coeff h (tailCoeff K w N 0 f).1.1 =
      if HeadMem w N h then coeffA K w h f else 0 := by
  rw [coeff_tailCoeff, tailShift_zero, add_zero]

theorem tailCoeff_zero_map (μ : TailIdx N) :
    tailCoeff K w N μ (0 : WPA K w) = 0 := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff]
  show _ = MvPowerSeries.coeff h (0 : MvPowerSeries ℕ K)
  have hz : coeffA K w (h + tailShift w μ) (0 : WPA K w) = 0 := by
    show MvPowerSeries.coeff (h + tailShift w μ) (0 : MvPowerSeries ℕ K) = 0
    simp
  rw [hz]
  split_ifs <;> simp

theorem tailCoeff_zero_one : tailCoeff K w N 0 (1 : WPA K w) = 1 := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff_zero]
  show _ = MvPowerSeries.coeff h (1 : MvPowerSeries ℕ K)
  by_cases hmem : HeadMem w N h
  · rw [if_pos hmem]
    rfl
  · rw [if_neg hmem, MvPowerSeries.coeff_one, if_neg]
    intro h0
    subst h0
    exact hmem ⟨wpMem_zero w, fun n _ => rfl⟩

theorem tailCoeff_zero_mul (f g : WPA K w) :
    tailCoeff K w N 0 (f * g) = tailCoeff K w N 0 f * tailCoeff K w N 0 g := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff_zero]
  show _ = MvPowerSeries.coeff h ((tailCoeff K w N 0 f).1.1 * (tailCoeff K w N 0 g).1.1)
  by_cases hmem : HeadMem w N h
  · rw [if_pos hmem]
    show MvPowerSeries.coeff h (f.1.1 * g.1.1) = _
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsum : p.1 + p.2 = h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have htails1 : ∀ n, N < n → p.1 n = 0 := by
      intro n hn
      have hhn : h n = 0 := hmem.2 n hn
      have hpn : p.1 n + p.2 n = h n := by rw [← hsum, Finsupp.add_apply]
      omega
    have htails2 : ∀ n, N < n → p.2 n = 0 := by
      intro n hn
      have hhn : h n = 0 := hmem.2 n hn
      have hpn : p.1 n + p.2 n = h n := by rw [← hsum, Finsupp.add_apply]
      omega
    rw [coeff_tailCoeff_zero, coeff_tailCoeff_zero]
    by_cases h1 : HeadMem w N p.1
    · by_cases h2 : HeadMem w N p.2
      · rw [if_pos h1, if_pos h2]
        rfl
      · rw [if_pos h1, if_neg h2]
        have hz : MvPowerSeries.coeff p.2 g.1.1 = 0 :=
          g.2 p.2 fun hwp => h2 ⟨hwp, htails2⟩
        show MvPowerSeries.coeff p.1 f.1.1 * MvPowerSeries.coeff p.2 g.1.1 = _
        rw [hz, mul_zero, mul_zero]
    · rw [if_neg h1]
      have hz : MvPowerSeries.coeff p.1 f.1.1 = 0 :=
        f.2 p.1 fun hwp => h1 ⟨hwp, htails1⟩
      show MvPowerSeries.coeff p.1 f.1.1 * MvPowerSeries.coeff p.2 g.1.1 = _
      rw [hz, zero_mul, zero_mul]
  · rw [if_neg hmem]
    exact ((tailCoeff K w N 0 f * tailCoeff K w N 0 g).2 h hmem).symm

/-- The head retraction `ρ_N` — the `μ = 0` tail coefficient — is a ring homomorphism
([WP] eq:head-retraction: "Projection to the coefficient of `e_0` is a
norm-nonincreasing algebra retraction"). -/
noncomputable def rhoHead : WPA K w →+* WPHead K w N where
  toFun := tailCoeff K w N 0
  map_one' := tailCoeff_zero_one K w N
  map_mul' := tailCoeff_zero_mul K w N
  map_zero' := tailCoeff_zero_map K w N 0
  map_add' := tailCoeff_add K w N 0

@[simp] theorem rhoHead_apply (f : WPA K w) :
    rhoHead K w N f = tailCoeff K w N 0 f := rfl

@[simp] theorem rhoHead_headIncl (x : WPHead K w N) :
    rhoHead K w N (headIncl K w N x) = x := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  show MvPowerSeries.coeff h (tailCoeff K w N 0 (headIncl K w N x)).1.1 = _
  rw [coeff_tailCoeff_zero]
  by_cases hmem : HeadMem w N h
  · rw [if_pos hmem]
    rfl
  · rw [if_neg hmem]
    exact (x.2 h hmem).symm

theorem norm_rhoHead_le (f : WPA K w) : ‖rhoHead K w N f‖ ≤ ‖f‖ :=
  norm_tailCoeff_le K w N 0 f

/-- The variable `W` as a head element. -/
noncomputable def WaHead : WPHead K w N :=
  ⟨⟨MvPowerSeries.monomial (Finsupp.single 0 1) (1 : K),
      MvPowerSeries.isRestrictedGauss_monomial _ _ _⟩, fun s hs => by
    show MvPowerSeries.coeff s
      (MvPowerSeries.monomial (Finsupp.single 0 1) (1 : K)) = 0
    classical
    rw [MvPowerSeries.coeff_monomial, if_neg]
    intro h0
    subst h0
    refine hs ⟨wpMem_single_zero w 1, fun n hn => ?_⟩
    rw [Finsupp.single_apply, if_neg (by omega : ¬ (0 = n))]⟩

@[simp] theorem headIncl_WaHead : headIncl K w N (WaHead K w N) = Wa K w := rfl

/-- **The twisted multiplication rule** ([WP] eq:tail-multiplication:
`e_μ e_λ = W^{ω(μ)+ω(λ)−ω(μ+λ)} e_{μ+λ}`; the excess exponent is `≥ 0` by
subadditivity of `ω`). -/
theorem eTail_mul (μ ν : TailIdx N) :
    eTail K w N μ * eTail K w N ν =
      headIncl K w N (WaHead K w N ^
          (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)) *
        eTail K w N (μ + ν) := by
  classical
  refine Subtype.ext (Subtype.ext ?_)
  let V : WPHead K w N →+* MvPowerSeries ℕ K :=
    ((MvPowerSeries.isSubring (fun _ : ℕ => (1 : ℝ))).subtype).comp
      (wpHeadSupport K w N).subtype
  have hV : ∀ g : WPHead K w N, V g = g.1.1 := fun _ => rfl
  have hpow : (WaHead K w N ^
      (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)).1.1 =
      MvPowerSeries.monomial
        (Finsupp.single 0
          (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)) (1 : K) := by
    rw [← hV, map_pow]
    have hX : V (WaHead K w N) = MvPowerSeries.X 0 := rfl
    rw [hX, MvPowerSeries.X_pow_eq]
  have hexp : tailShift w μ + tailShift w ν =
      Finsupp.single 0
          (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1) +
        tailShift w (μ + ν) := by
    have hsub : wpWeight w (μ.1 + ν.1) ≤ wpWeight w μ.1 + wpWeight w ν.1 :=
      wpWeight_add_le w μ.1 ν.1
    ext n
    simp only [tailShift, TailIdx.add_val, Finsupp.add_apply, Finsupp.single_apply]
    by_cases h0 : 0 = n
    · subst h0
      have hμ0 : μ.1 0 = 0 := μ.prop 0 (Nat.zero_le N)
      have hν0 : ν.1 0 = 0 := ν.prop 0 (Nat.zero_le N)
      simp only [if_true, hμ0, hν0]
      omega
    · simp only [if_neg h0]
      omega
  show MvPowerSeries.monomial (tailShift w μ) (1 : K) *
      MvPowerSeries.monomial (tailShift w ν) 1 =
      (WaHead K w N ^
        (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)).1.1 *
      MvPowerSeries.monomial (tailShift w (μ + ν)) 1
  rw [hpow, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial,
    one_mul, hexp]

/-! ### The twisted `c₀`-sum `TailC0` -/

/-- A twist element: a norm-`≤ 1` element of a normed ring (the image of `W`).
Norm `≤ 1` is what keeps the twisted convolution submultiplicative and `c₀`-valued. -/
structure TwistElem (P : Type*) [NormedCommRing P] where
  /-- The underlying element. -/
  val : P
  /-- The twist element lies in the unit ball. -/
  norm_le_one : ‖val‖ ≤ 1

/-- The twisted `c₀`-sum `⊕̂^{c₀}_μ P e_μ` ([WP] eq:tail-decomposition's receptacle):
null families `TailIdx N → P` with sup norm and `ρ`-twisted convolution
`(x*y)_τ = ∑_{μ+λ=τ} ρ^{ω(μ)+ω(λ)−ω(τ)} x_μ y_λ` (the weight `w` enters through the
twist exponents, so it is a genuine parameter of the ring structure). -/
def TailC0 (w : ℕ → ℕ) (N : ℕ) (P : Type*) [NormedCommRing P] [IsUltrametricDist P]
    (ρ : TwistElem P) : Type _ :=
  have _ := w
  have _ := ρ
  {x : TailIdx N → P // Tendsto (fun μ => ‖x μ‖) cofinite (𝓝 0)}

namespace TailC0

variable {w : ℕ → ℕ} {N : ℕ} {P : Type*} [NormedCommRing P] [IsUltrametricDist P]
  {ρ : TwistElem P}

noncomputable instance : CommRing (TailC0 w N P ρ) := by sorry

noncomputable instance : NormedCommRing (TailC0 w N P ρ) := by sorry

instance : IsUltrametricDist (TailC0 w N P ρ) := by sorry

instance [CompleteSpace P] : CompleteSpace (TailC0 w N P ρ) := by sorry

instance [NormOneClass P] [Nontrivial P] : NormOneClass (TailC0 w N P ρ) := by sorry

/-- The coefficient of a twisted `c₀`-family. -/
def coeff (μ : TailIdx N) (x : TailC0 w N P ρ) : P := x.1 μ

/-- The single-index family `p·e_μ`. -/
noncomputable def single (μ : TailIdx N) (p : P) : TailC0 w N P ρ := by
  sorry

@[simp] theorem coeff_single (μ ν : TailIdx N) (p : P) :
    coeff ν (single (w := w) (ρ := ρ) μ p) = if ν = μ then p else 0 := by sorry

/-- The twisted product of single families ([WP] eq:tail-multiplication in the
abstract model): `(p·e_μ)(q·e_ν) = ρ^{ω(μ)+ω(ν)−ω(μ+ν)}·pq·e_{μ+ν}`. -/
theorem single_mul_single (μ ν : TailIdx N) (p q : P) :
    single (w := w) (ρ := ρ) μ p * single (w := w) (ρ := ρ) ν q =
      single (w := w) (ρ := ρ) (μ + ν)
        (ρ.val ^ (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1) * (p * q)) := by
  sorry

theorem norm_eq_iSup_coeff (x : TailC0 w N P ρ) :
    ‖x‖ = ⨆ μ : TailIdx N, ‖coeff μ x‖ := by sorry

/-- The head inclusion `P → TailC0` at `μ = 0` is an isometric ring homomorphism. -/
noncomputable def ofHead : P →+* TailC0 w N P ρ := by sorry

@[simp] theorem norm_ofHead (p : P) :
    ‖ofHead (w := w) (N := N) (ρ := ρ) p‖ = ‖p‖ := by sorry

/-- The head projection `TailC0 → P` at `μ = 0` is a norm-nonincreasing ring
homomorphism splitting `ofHead`. -/
noncomputable def toHead : TailC0 w N P ρ →+* P := by sorry

@[simp] theorem toHead_ofHead (p : P) :
    toHead (ofHead (w := w) (N := N) (ρ := ρ) p) = p := by
  sorry

end TailC0

/-! ### The formal-series embedding `Φ` ([WP] eq:formal-embedding) -/

/-- The tail variable type `{n : ℕ // N < n}` — the `U_n`, `n > N`. -/
def TailVar (N : ℕ) : Type := {n : ℕ // N < n}

/-- Tail indices are finitely supported exponent vectors on the tail variables. -/
noncomputable def tailIdxEquivFinsupp : TailIdx N ≃ (TailVar N →₀ ℕ) := by sorry

variable {P : Type*} [NormedCommRing P] [IsUltrametricDist P]

/-- **The formal-series embedding** `Φ : TailC0 → ℱ_J(P) = MvPowerSeries J P`,
`Φ(∑ x_μ e_μ) = ∑ ρ^{ω(μ)} x_μ U^μ` ([WP] eq:formal-embedding).  Multiplicative
because the `ρ`-powers absorb the twist (eq:tail-multiplication); it forgets the
topology (the target is the full formal product). -/
noncomputable def tailC0ToMvPowerSeries (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P) :
    TailC0 w N P ρ →+* MvPowerSeries (TailVar N) P := by sorry

/-- `Φ` is injective when the twist element is regular
([WP] thm:parity-rationally-reduced: "The `W`-regularity of `P` then gives
`x_μ = 0`"). -/
theorem tailC0ToMvPowerSeries_injective (ρ : TwistElem P)
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    Function.Injective (tailC0ToMvPowerSeries w N ρ) := by sorry

/-- Reducedness descends through `Φ` ([WP] thm:parity-rationally-reduced, final
step; with `WP/Reduced.lean`'s `IsReduced (MvPowerSeries J P)`). -/
theorem isReduced_tailC0 (ρ : TwistElem P) [IsReduced P]
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    IsReduced (TailC0 w N P ρ) := by sorry

/-- Domain-ness descends through `Φ` (used for the bad chart ℬ,
[WP] prop:weighted-chart-domain-nonuniform; with mathlib's
`NoZeroDivisors (MvPowerSeries σ R)`). -/
theorem isDomain_tailC0 (ρ : TwistElem P) [IsDomain P]
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    IsDomain (TailC0 w N P ρ) := by sorry

end WeightedParity
