/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.SheafyBI

/-!
# The chart data: Kedlaya's windows as rational-localization data over `(A_inf, A_inf)`

The two charts of the Fargues–Fontaine curve are the windows
`U₀ = {κ ∈ [1, c]}`, `V₀ = {κ ∈ [c, p]}` of `𝒴 ⊂ Spa(A_inf, A_inf)`. Each window
`{κ ∈ [a₁/b₁, a₂/b₂]}` is a rational subset with the single-denominator presentation

  `R({p^{a₁+a₂}, [ϖ]^{b₁+b₂}} / p^{a₁}·[ϖ]^{b₂})`,

whose fractions encode `κ ≥ a₁/b₁` and `κ ≤ a₂/b₂`. This file constructs the
underlying `RationalLocData` over the non-Tate Huber pair `(A_inf, A_inf)` — the pair
of definition `(⊤, (p,[ϖ]))`, the datum `chartData` with its Wedhorn §8.1 openness
condition (`hopen`), and Wedhorn Definition 7.29's rationality (`isRational_chartData`:
the span of the numerators contains the open `I_inf^N`).

## Main definitions and results

* `FarguesFontaine.podAinf` : the `(⊤, (p,[ϖ]))` pair of definition on `A_inf`.
* `FarguesFontaine.chartData u v a b` : the datum with `s = pᵘ[ϖ]ᵛ`,
  `T = {p^{a+1}, [ϖ]^{b+1}}`.
* `FarguesFontaine.isRational_chartData` : the datum presents a rational subset.

## Sources

* Consult `chatgpt-reply-campaign8-adic-space-2026-07-26.md` §5;
  [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.29, §8.1.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

universe u

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- The subspace topology on `⊤` is `idealToTop I`-adic whenever the ambient topology
is `I`-adic (the `isAdic_idealToTop` transfer, for an arbitrary adic ideal rather
than the ideal's own canonical topology). -/
theorem isAdic_idealToTop_of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {I : Ideal R} (hadic : IsAdic I) :
    IsAdic (idealToTop I) := by
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [idealToTop_pow_eq_preimage I n]
    exact (isAdic_iff.mp hadic).1 n |>.preimage continuous_subtype_val
  · rw [nhds_subtype_eq_comap] at hs
    obtain ⟨U, hU, hsU⟩ := Filter.mem_comap.mp hs
    rw [show (0 : ↥(⊤ : Subring R)).val = (0 : R) from rfl] at hU
    obtain ⟨n, -, hn⟩ := hadic.hasBasis_nhds_zero.mem_iff.mp hU
    exact ⟨n, (idealToTop_pow_eq_preimage I n ▸ Set.preimage_mono hn).trans hsU⟩

/-- **The `(⊤, (p, [ϖ]))` pair of definition on `A_inf`**, at the section's
pseudo-uniformizer (any `ϖ` works: the filtrations are mutually cofinal). -/
def podAinf : PairOfDefinition (Ainf p F) where
  A₀ := ⊤
  I := idealToTop (Iinf p F ϖ)
  isOpen := isOpen_univ
  fg := idealToTop_fg _ (Submodule.fg_span (Set.toFinite _))
  isAdic := isAdic_idealToTop_of_isAdic (isAdic_Iinf p F ϖ)

/-- `t/s = (algebraMap t) · (1/s)` — the normal form for fraction arithmetic. -/
theorem divByS_eq_mul_inv {A : Type*} [CommRing A] (t s : A) :
    divByS t s = algebraMap A (Localization.Away s) t
      * IsLocalization.mk' (Localization.Away s) 1
        (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s) := by
  rw [divByS, ← IsLocalization.mk'_eq_mul_mk'_one]

/-- Fractions with a factored numerator: `(c·t)/s = c·(t/s)`. -/
theorem divByS_mul_left {A : Type*} [CommRing A] (c t s : A) :
    divByS (c * t) s = algebraMap A (Localization.Away s) c * divByS t s := by
  rw [divByS_eq_mul_inv, divByS_eq_mul_inv, map_mul, mul_assoc]

/-- `(c·s)/s = c`. -/
theorem divByS_mul_cancel {A : Type*} [CommRing A] (c s : A) :
    divByS (c * s) s = algebraMap A (Localization.Away s) c := by
  rw [divByS, IsLocalization.mk'_eq_iff_eq_mul, map_mul]

/-- Fractions are additive in the numerator. -/
theorem divByS_add {A : Type*} [CommRing A] (t t' s : A) :
    divByS (t + t') s = divByS t s + divByS t' s := by
  rw [divByS_eq_mul_inv, divByS_eq_mul_inv, divByS_eq_mul_inv, map_add, add_mul]

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _

/-- The numerator set of the chart datum: `{p^{a+1}, [ϖ]^{b+1}}`. -/
def chartT (a b : ℕ) : Finset (Ainf p F) :=
  {(p : Ainf p F) ^ (a + 1), teichPi p F ϖ ^ (b + 1)}

/-- The denominator of the chart datum: `p^u·[ϖ]^v`. -/
def chartS (u v : ℕ) : Ainf p F :=
  (p : Ainf p F) ^ u * teichPi p F ϖ ^ v

/-- **The elements whose fractions land in the ring of definition form an ideal.** -/
def divBySIdeal (T : Finset (Ainf p F)) (s : Ainf p F) : Ideal (Ainf p F) where
  carrier := {x : Ainf p F | divByS x s ∈ locSubring (podAinf p F ϖ) T s}
  zero_mem' := by
    show divByS 0 s ∈ locSubring (podAinf p F ϖ) T s
    have h0 : divByS (0 : Ainf p F) s = 0 := by
      rw [show (0 : Ainf p F) = 0 * s from (zero_mul s).symm, divByS_mul_cancel,
        map_zero]
    rw [h0]
    exact zero_mem _
  add_mem' := by
    intro x y hx hy
    show divByS (x + y) s ∈ locSubring (podAinf p F ϖ) T s
    rw [divByS_add]
    exact add_mem hx hy
  smul_mem' := by
    intro c x hx
    show divByS (c • x) s ∈ locSubring (podAinf p F ϖ) T s
    rw [smul_eq_mul, divByS_mul_left]
    refine mul_mem ?_ hx
    have hmem : algebraMap (Ainf p F) (Localization.Away s) c
        ∈ (algebraMap (Ainf p F) (Localization.Away s)) ''
          ((podAinf p F ϖ).A₀ : Set (Ainf p F)) :=
      ⟨c, by simp [podAinf], rfl⟩
    exact algebraMap_A₀_subset_locSubring _ _ _ hmem

/-- The degree-`N` monomials `pⁱ·[ϖ]^{N-i}`. -/
def chartMonomials (N : ℕ) : Finset (Ainf p F) :=
  (Finset.range (N + 1)).image
    (fun i => (p : Ainf p F) ^ i * teichPi p F ϖ ^ (N - i))

/-- `I_inf^N` is spanned by the degree-`N` monomials. -/
theorem Iinf_pow_le_span_chartMonomials (N : ℕ) :
    Iinf p F ϖ ^ N ≤ Ideal.span (chartMonomials p F ϖ N : Set (Ainf p F)) := by
  induction N with
  | zero =>
    rw [pow_zero]
    have h1 : (1 : Ainf p F) ∈ (chartMonomials p F ϖ 0 : Set (Ainf p F)) := by
      rw [chartMonomials]
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨0, by simp⟩)
    intro x _
    have : Ideal.span {(1 : Ainf p F)} ≤
        Ideal.span (chartMonomials p F ϖ 0 : Set (Ainf p F)) :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr h1)
    exact this (by rw [Ideal.span_singleton_one]; trivial)
  | succ N ih =>
    rw [pow_succ, mul_comm]
    refine le_trans (Ideal.mul_mono le_rfl ih) ?_
    rw [Iinf, Ideal.span_mul_span]
    rw [Ideal.span_le]
    rintro x ⟨g, hg, m, hm, rfl⟩
    rw [chartMonomials, Finset.coe_image] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    rw [Finset.mem_coe, Finset.mem_range] at hi
    rcases hg with hg | hg
    · -- g = p
      rw [hg]
      refine Ideal.subset_span ?_
      rw [chartMonomials, Finset.coe_image]
      refine ⟨i + 1, by simp; omega, ?_⟩
      show (p : Ainf p F) ^ (i + 1) * teichPi p F ϖ ^ (N + 1 - (i + 1))
        = (p : Ainf p F) * ((p : Ainf p F) ^ i * teichPi p F ϖ ^ (N - i))
      rw [show N + 1 - (i + 1) = N - i from by omega, pow_succ]
      ring
    · -- g = [ϖ]
      rw [Set.mem_singleton_iff.mp hg]
      refine Ideal.subset_span ?_
      rw [chartMonomials, Finset.coe_image]
      refine ⟨i, by simp; omega, ?_⟩
      show (p : Ainf p F) ^ i * teichPi p F ϖ ^ (N + 1 - i)
        = teichPi p F ϖ * ((p : Ainf p F) ^ i * teichPi p F ϖ ^ (N - i))
      rw [show N + 1 - i = (N - i) + 1 from by omega, pow_succ]
      ring

/-- Every degree-`(a+b+2)` monomial divided by `s = p[ϖ]^b` lies in the ring of
definition of the localization: factor out `[ϖ]^{b+1}` (when `i ≤ a`) or `p^{a+1}`
(when `i > a`). -/
theorem span_chartMonomials_le_divBySIdeal (u v a b : ℕ) :
    Ideal.span (chartMonomials p F ϖ (a + b + 2) : Set (Ainf p F))
      ≤ divBySIdeal p F ϖ (chartT p F ϖ a b) (chartS p F ϖ u v) := by
  rw [Ideal.span_le]
  rintro x hx
  rw [chartMonomials, Finset.coe_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_coe, Finset.mem_range] at hi
  show divByS ((p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i))
    (chartS p F ϖ u v) ∈ locSubring (podAinf p F ϖ) (chartT p F ϖ a b)
      (chartS p F ϖ u v)
  by_cases hia : i ≤ a
  · have hsplit : (p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i)
        = ((p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i - (b + 1)))
          * teichPi p F ϖ ^ (b + 1) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hsplit, divByS_mul_left]
    refine mul_mem ?_ (divByS_mem_locSubring _ _ _ ?_)
    · exact algebraMap_A₀_subset_locSubring _ _ _ ⟨_, by simp [podAinf], rfl⟩
    · rw [chartT]
      simp
  · have hia' : a + 1 ≤ i := by omega
    have hexp : i = (i - (a + 1)) + (a + 1) := by omega
    have hsplit : (p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i)
        = ((p : Ainf p F) ^ (i - (a + 1)) * teichPi p F ϖ ^ (a + b + 2 - i))
          * (p : Ainf p F) ^ (a + 1) := by
      calc (p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i)
          = (p : Ainf p F) ^ ((i - (a + 1)) + (a + 1))
            * teichPi p F ϖ ^ (a + b + 2 - i) := by rw [← hexp]
        _ = ((p : Ainf p F) ^ (i - (a + 1)) * teichPi p F ϖ ^ (a + b + 2 - i))
            * (p : Ainf p F) ^ (a + 1) := by
            rw [pow_add]
            ring
    rw [hsplit, divByS_mul_left]
    refine mul_mem ?_ (divByS_mem_locSubring _ _ _ ?_)
    · exact algebraMap_A₀_subset_locSubring _ _ _ ⟨_, by simp [podAinf], rfl⟩
    · rw [chartT]
      simp

/-- **The chart datum for the window `U₀`** (Kedlaya's `U₀ = R(T_U/s_U)` with
`s_U = p[ϖ]^b`, `T_U = {p^{a+1}, [ϖ]^{b+1}}`, for `c = a/b`): a rational-localization
datum over the non-Tate Huber pair `(A_inf, A_inf)`. -/
def chartData (u v a b : ℕ) : RationalLocData (Ainf p F) where
  P := podAinf p F ϖ
  T := chartT p F ϖ a b
  s := chartS p F ϖ u v
  hopen := by
    refine ⟨a + b + 2, fun bb hbb => ?_⟩
    have h1 : (↑bb : Ainf p F) ∈ Iinf p F ϖ ^ (a + b + 2) := by
      have hset := idealToTop_pow_eq_preimage (Iinf p F ϖ) (a + b + 2)
      have hmem : bb ∈ ((idealToTop (Iinf p F ϖ) ^ (a + b + 2) :
          Ideal ↥(⊤ : Subring (Ainf p F))) :
          Set ↥(⊤ : Subring (Ainf p F))) := hbb
      rw [hset] at hmem
      exact hmem
    exact span_chartMonomials_le_divBySIdeal p F ϖ u v a b
      (Iinf_pow_le_span_chartMonomials p F ϖ (a + b + 2) h1)

/-- **The chart datum is rational** (Wedhorn Definition 7.29's openness): the span of
`{p^{a+1}, [ϖ]^{b+1}}` contains the open `I_inf^{a+b+2}`. -/
theorem isRational_chartData (u v a b : ℕ) :
    (chartData p F ϖ u v a b).IsRational := by
  have hsub : ((Iinf p F ϖ ^ (a + b + 2) : Ideal (Ainf p F)) : Set (Ainf p F))
      ⊆ ((Ideal.span ((chartT p F ϖ a b) : Set (Ainf p F)) : Ideal (Ainf p F))
        : Set (Ainf p F)) := by
    intro x hx
    have h2 := Iinf_pow_le_span_chartMonomials p F ϖ (a + b + 2) hx
    refine (Ideal.span_le.mpr ?_) h2
    rintro y hy
    rw [chartMonomials, Finset.coe_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_coe, Finset.mem_range] at hi
    show (p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i)
      ∈ ((Ideal.span ((chartT p F ϖ a b : Finset (Ainf p F)) : Set (Ainf p F))
        : Ideal (Ainf p F)) : Set (Ainf p F))
    by_cases hia : i ≤ a
    · have hsplit : (p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i)
          = ((p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i - (b + 1)))
            * teichPi p F ϖ ^ (b + 1) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      rw [hsplit]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      rw [chartT]
      simp
    · have hexp : i = (i - (a + 1)) + (a + 1) := by omega
      have hsplit : (p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i)
          = ((p : Ainf p F) ^ (i - (a + 1)) * teichPi p F ϖ ^ (a + b + 2 - i))
            * (p : Ainf p F) ^ (a + 1) := by
        calc (p : Ainf p F) ^ i * teichPi p F ϖ ^ (a + b + 2 - i)
            = (p : Ainf p F) ^ ((i - (a + 1)) + (a + 1))
              * teichPi p F ϖ ^ (a + b + 2 - i) := by rw [← hexp]
          _ = ((p : Ainf p F) ^ (i - (a + 1)) * teichPi p F ϖ ^ (a + b + 2 - i))
              * (p : Ainf p F) ^ (a + 1) := by
              rw [pow_add]
              ring
      rw [hsplit]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      rw [chartT]
      simp
  have hIopen : IsOpen ((Iinf p F ϖ ^ (a + b + 2) : Ideal (Ainf p F))
      : Set (Ainf p F)) := (isAdic_iff.mp (isAdic_Iinf p F ϖ)).1 _
  show IsOpen (((Ideal.span (((chartData p F ϖ u v a b).T : Finset (Ainf p F))
    : Set (Ainf p F)) : Ideal (Ainf p F)).toAddSubgroup
      : AddSubgroup (Ainf p F)) : Set (Ainf p F))
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (hIopen.mem_nhds (zero_mem _)) hsub)

/-- **The chart datum presents the two-sided window** (raw-exponent form): a
valuation lies in `R({p^{a₁+a₂}, [ϖ]^{b₁+b₂}}/p^{a₁}[ϖ]^{b₂})` iff it lies in `𝒴`
with `v([ϖ])^{b₁} ≤ v(p)^{a₁}` (κ ≥ a₁/b₁) and `v(p)^{a₂} ≤ v([ϖ])^{b₂}`
(κ ≤ a₂/b₂). -/
theorem mem_rationalOpen_chartData_iff (a₁ b₁ a₂ b₂ : ℕ)
    (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (ha₂ : 0 < a₂) (hb₂ : 0 < b₂)
    (v : Spv (Ainf p F)) :
    v ∈ rationalOpen (chartT p F ϖ (a₁ + a₂ - 1) (b₁ + b₂ - 1))
        (chartS p F ϖ a₁ b₂)
      ↔ v ∈ Y p F ϖ
          ∧ v.vle (teichPi p F ϖ ^ b₁) ((p : Ainf p F) ^ a₁)
          ∧ v.vle ((p : Ainf p F) ^ a₂) (teichPi p F ϖ ^ b₂) := by
  letI : ValuativeRel (Ainf p F) := v.toValuativeRel
  have hbridge : ∀ s t : Ainf p F, v.vle s t ↔
      ValuativeRel.valuation (Ainf p F) s ≤ ValuativeRel.valuation (Ainf p F) t :=
    fun s t => (ValuativeRel.valuation (Ainf p F)).vle_iff_le
  set w := ValuativeRel.valuation (Ainf p F) with hw
  have hexpa : (a₁ + a₂ - 1) + 1 = a₁ + a₂ := by omega
  have hexpb : (b₁ + b₂ - 1) + 1 = b₁ + b₂ := by omega
  constructor
  · rintro ⟨hspa, hT, hs⟩
    have h1 : v.vle ((p : Ainf p F) ^ ((a₁ + a₂ - 1) + 1))
        (chartS p F ϖ a₁ b₂) := hT _ (by rw [chartT]; simp)
    have h2 : v.vle (teichPi p F ϖ ^ ((b₁ + b₂ - 1) + 1))
        (chartS p F ϖ a₁ b₂) := hT _ (by rw [chartT]; simp)
    rw [hexpa] at h1
    rw [hexpb] at h2
    have hsval : w (chartS p F ϖ a₁ b₂) ≠ 0 := by
      intro h0
      refine hs ?_
      rw [hbridge, map_zero, h0]
    have hpϖ : w ((p : Ainf p F)) ≠ 0 ∧ w (teichPi p F ϖ) ≠ 0 := by
      rw [chartS, map_mul, map_pow, map_pow] at hsval
      constructor
      · intro h
        exact hsval (by rw [h, zero_pow ha₁.ne', zero_mul])
      · intro h
        exact hsval (by rw [h, zero_pow hb₂.ne', mul_zero])
    have hY2 : ¬ v.vle ((p : Ainf p F) * teichPi p F ϖ) 0 := by
      rw [hbridge, map_mul, map_zero]
      intro hle
      rcases mul_eq_zero.mp (le_zero_iff.mp hle) with h | h
      · exact hpϖ.1 h
      · exact hpϖ.2 h
    have hc1 : v.vle (teichPi p F ϖ ^ b₁) ((p : Ainf p F) ^ a₁) := by
      rw [hbridge, map_pow, map_pow]
      rw [hbridge, chartS, map_mul, map_pow, map_pow, map_pow] at h2
      rw [pow_add] at h2
      have hcinv := mul_le_mul_right h2 ((w (teichPi p F ϖ) ^ b₂)⁻¹)
      rwa [mul_comm (w (teichPi p F ϖ) ^ b₁) (w (teichPi p F ϖ) ^ b₂),
        mul_comm (w ((p : Ainf p F)) ^ a₁) (w (teichPi p F ϖ) ^ b₂),
        ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hpϖ.2),
        one_mul, one_mul] at hcinv
    have hc2 : v.vle ((p : Ainf p F) ^ a₂) (teichPi p F ϖ ^ b₂) := by
      rw [hbridge, map_pow, map_pow]
      rw [hbridge, chartS, map_mul, map_pow, map_pow, map_pow] at h1
      rw [pow_add] at h1
      have h1' : w ((p : Ainf p F)) ^ a₁ * w ((p : Ainf p F)) ^ a₂
          ≤ w ((p : Ainf p F)) ^ a₁ * w (teichPi p F ϖ) ^ b₂ := h1
      have hcinv := mul_le_mul_left h1' ((w ((p : Ainf p F)) ^ a₁)⁻¹)
      rwa [mul_comm (w ((p : Ainf p F)) ^ a₁) (w ((p : Ainf p F)) ^ a₂),
        mul_comm (w ((p : Ainf p F)) ^ a₁) (w (teichPi p F ϖ) ^ b₂),
        mul_assoc, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpϖ.1),
        mul_one, mul_one] at hcinv
    exact ⟨⟨hspa, hY2⟩, hc1, hc2⟩
  · rintro ⟨⟨hspa, hY2⟩, hc1, hc2⟩
    have hpϖ : w ((p : Ainf p F)) ≠ 0 ∧ w (teichPi p F ϖ) ≠ 0 := by
      constructor
      · intro h
        refine hY2 ?_
        rw [hbridge, map_mul, map_zero, h, zero_mul]
      · intro h
        refine hY2 ?_
        rw [hbridge, map_mul, map_zero, h, mul_zero]
    refine ⟨hspa, ?_, ?_⟩
    · intro t ht
      rw [chartT] at ht
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · -- t = p^{(a₁+a₂-1)+1}
        rw [hbridge, hexpa, map_pow, chartS, map_mul, map_pow, map_pow, pow_add]
        rw [hbridge, map_pow, map_pow] at hc2
        exact mul_le_mul' le_rfl hc2
      · -- t = [ϖ]^{(b₁+b₂-1)+1}
        rw [Finset.mem_singleton.mp ht']
        rw [hbridge, hexpb, map_pow, chartS, map_mul, map_pow, map_pow, pow_add]
        rw [hbridge, map_pow, map_pow] at hc1
        exact mul_le_mul' hc1 le_rfl
    · intro hle
      rw [hbridge, map_zero, chartS, map_mul, map_pow, map_pow] at hle
      rcases mul_eq_zero.mp (le_zero_iff.mp hle) with h | h
      · exact hpϖ.1 (pow_eq_zero_iff ha₁.ne' |>.mp h)
      · exact hpϖ.2 (pow_eq_zero_iff hb₂.ne' |>.mp h)

/-- **The chart `U₀` is a rational subset**: the window `κ ∈ [1, c]`
(`c = (p+1)/2`) is `R({p^{p+2}, [ϖ]³} / p·[ϖ]²)`. -/
theorem windowU_zero_eq_rationalOpen (hp : 1 < p) :
    windowU p F ϖ 0
      = rationalOpen (chartT p F ϖ (1 + (p + 1) - 1) (1 + 2 - 1))
          (chartS p F ϖ 1 2) := by
  ext v
  rw [mem_rationalOpen_chartData_iff p F ϖ 1 1 (p + 1) 2 one_pos one_pos
    (by omega) (by norm_num)]
  rw [windowU, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hY, hKGE, hKLE⟩
    refine ⟨hY, ?_, ?_⟩
    · have h := (KGE_iff hY (q := (p : ℚ) ^ (0 : ℤ)) (by simp)
        (a := 1) (b := 1) one_pos (by simp)).mp hKGE
      simpa using h
    · have h := (KLE_iff hY (q := cFF p * (p : ℚ) ^ (0 : ℤ))
        (by simp; exact lt_trans one_pos (one_lt_cFF hp))
        (a := p + 1) (b := 2) (by norm_num)
        (by rw [zpow_zero, mul_one, cFF]; push_cast; ring)).mp hKLE
      exact h
  · rintro ⟨hY, h1, h2⟩
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY (q := (p : ℚ) ^ (0 : ℤ)) (by simp)
        (a := 1) (b := 1) one_pos (by simp)).mpr ?_
      simpa using h1
    · exact (KLE_iff hY (q := cFF p * (p : ℚ) ^ (0 : ℤ))
        (by simp; exact lt_trans one_pos (one_lt_cFF hp))
        (a := p + 1) (b := 2) (by norm_num)
        (by rw [zpow_zero, mul_one, cFF]; push_cast; ring)).mpr h2

/-- **The chart `V₀` is a rational subset**: the window `κ ∈ [c, p]` is
`R({p^{2p+1}, [ϖ]³} / p^{p+1}·[ϖ])`. -/
theorem windowV_zero_eq_rationalOpen (hp : 1 < p) :
    windowV p F ϖ 0
      = rationalOpen (chartT p F ϖ ((p + 1) + p - 1) (2 + 1 - 1))
          (chartS p F ϖ (p + 1) 1) := by
  ext v
  rw [mem_rationalOpen_chartData_iff p F ϖ (p + 1) 2 p 1 (by omega) (by norm_num)
    (by omega) one_pos]
  rw [windowV, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hY, hKGE, hKLE⟩
    refine ⟨hY, ?_, ?_⟩
    · exact (KGE_iff hY (q := cFF p * (p : ℚ) ^ (0 : ℤ))
        (by simp; exact lt_trans one_pos (one_lt_cFF hp))
        (a := p + 1) (b := 2) (by norm_num)
        (by rw [zpow_zero, mul_one, cFF]; push_cast; ring)).mp hKGE
    · have h := (KLE_iff hY (q := (p : ℚ) ^ ((0 : ℤ) + 1))
        (by simp; omega) (a := p) (b := 1) (by omega) (by simp)).mp hKLE
      simpa using h
  · rintro ⟨hY, h1, h2⟩
    refine ⟨hY, ?_, ?_⟩
    · exact (KGE_iff hY (q := cFF p * (p : ℚ) ^ (0 : ℤ))
        (by simp; exact lt_trans one_pos (one_lt_cFF hp))
        (a := p + 1) (b := 2) (by norm_num)
        (by rw [zpow_zero, mul_one, cFF]; push_cast; ring)).mpr h1
    · refine (KLE_iff hY (q := (p : ℚ) ^ ((0 : ℤ) + 1))
        (by simp; omega) (a := p) (b := 1) (by omega) (by simp)).mpr ?_
      simpa using h2

/-- The chart denominator decomposes off the standard `Bloc`-denominator:
`(p·[ϖ]^b)^k = (p·[ϖ])^k · [ϖ]^{k(b-1)}`. -/
theorem chartS_pow_eq (b k : ℕ) (hb : 0 < b) :
    chartS p F ϖ 1 b ^ k
      = ((p : Ainf p F) * teichPi p F ϖ) ^ k * teichPi p F ϖ ^ (k * (b - 1)) := by
  rw [chartS, pow_one, mul_pow, mul_pow, mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  have : b = 1 + (b - 1) := by omega
  calc b * k = (1 + (b - 1)) * k := by rw [← this]
    _ = k + k * (b - 1) := by ring

/-- **`Bloc` is also the localization away from the chart denominator `p·[ϖ]^b`**
(the two multiplicative sets have the same saturation). -/
theorem isLocalization_chartS_Bloc (b : ℕ) (hb : 0 < b) :
    IsLocalization (Submonoid.powers (chartS p F ϖ 1 b)) (Bloc p F ϖ) where
  map_units := by
    rintro ⟨y, m, rfl⟩
    have hunit : IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (chartS p F ϖ 1 b)) := by
      rw [chartS, pow_one, map_mul, map_pow]
      exact (isUnit_p_image p F ϖ).mul ((isUnit_teichPi_image p F ϖ).pow b)
    show IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (chartS p F ϖ 1 b ^ m))
    rw [map_pow]
    exact hunit.pow m
  surj := by
    intro z
    obtain ⟨⟨a, y⟩, hz⟩ := IsLocalization.surj
      (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) z
    obtain ⟨k, hk⟩ := y.2
    refine ⟨⟨a * teichPi p F ϖ ^ (k * (b - 1)),
      ⟨chartS p F ϖ 1 b ^ k, k, rfl⟩⟩, ?_⟩
    show z * algebraMap (Ainf p F) (Bloc p F ϖ) (chartS p F ϖ 1 b ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) (a * teichPi p F ϖ ^ (k * (b - 1)))
    rw [chartS_pow_eq p F ϖ b k hb, map_mul, map_mul, ← mul_assoc]
    have hz' : z * algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) * teichPi p F ϖ) ^ k) = algebraMap (Ainf p F) (Bloc p F ϖ) a := by
      rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) from hk]
      exact hz
    rw [hz']
  exists_of_eq := by
    intro x y h
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) (S := Bloc p F ϖ) h
    obtain ⟨k, hk⟩ := c.2
    refine ⟨⟨chartS p F ϖ 1 b ^ k, k, rfl⟩, ?_⟩
    show chartS p F ϖ 1 b ^ k * x = chartS p F ϖ 1 b ^ k * y
    rw [chartS_pow_eq p F ϖ b k hb]
    have hc' : ((p : Ainf p F) * teichPi p F ϖ) ^ k * x
        = ((p : Ainf p F) * teichPi p F ϖ) ^ k * y := by
      rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ k = (c : Ainf p F) from hk]
      exact hc
    calc ((p : Ainf p F) * teichPi p F ϖ) ^ k * teichPi p F ϖ ^ (k * (b - 1)) * x
        = teichPi p F ϖ ^ (k * (b - 1)) * (((p : Ainf p F) * teichPi p F ϖ) ^ k * x) := by
          ring
      _ = teichPi p F ϖ ^ (k * (b - 1)) * (((p : Ainf p F) * teichPi p F ϖ) ^ k * y) := by
          rw [hc']
      _ = ((p : Ainf p F) * teichPi p F ϖ) ^ k * teichPi p F ϖ ^ (k * (b - 1)) * y := by
          ring

/-- **ID2a: the chart localization is `Bloc`** — the canonical ring isomorphism
`A_inf[1/(p[ϖ]^b)] ≃+* A_inf[1/(p[ϖ])]`. -/
def blocEquivAwayChartS (b : ℕ) (hb : 0 < b) :
    Localization.Away (chartS p F ϖ 1 b) ≃+* Bloc p F ϖ :=
  letI := isLocalization_chartS_Bloc p F ϖ b hb
  (IsLocalization.algEquiv (Submonoid.powers (chartS p F ϖ 1 b))
    (Localization.Away (chartS p F ϖ 1 b)) (Bloc p F ϖ)).toRingEquiv

variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

/-- The first chart fraction `[ϖ]/p ∈ Bloc` (the image of `[ϖ]^{b+1}/s`). -/
def chartFracPi : Bloc p F ϖ :=
  algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ)
    * ↑(isUnit_p_image p F ϖ).unit⁻¹

/-- The second chart fraction `p^a/[ϖ]^b ∈ Bloc` (the image of `p^{a+1}/s`). -/
def chartFracP (a b : ℕ) : Bloc p F ϖ :=
  algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ a)
    * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) ^ b

/-- `wI([ϖ]/p) ≤ 1` exactly when both radii are at least `|ϖ|` (the left-endpoint
condition of the chart window `κ ≥ 1`). -/
theorem wI_chartFracPi_le_one
    (h1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (h2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (chartFracPi p F ϖ)) ≤ 1 := by
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK, chartFracPi]
  have hval : ∀ (ρ : NNReal) (hρ0 : 0 < ρ) (hρ1 : ρ < 1),
      wLoc p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ)
        * ↑(isUnit_p_image p F ϖ).unit⁻¹)
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) * ρ⁻¹ := by
    intro ρ hρ0 hρ1
    rw [Valuation.map_mul, wLoc_algebraMap, wLoc_p_inv p F ϖ hρ0 hρ1, teichPi,
      gaussValue_teichmuller p F hρ1.le]
  rw [hval ρ₁ hρ₁0 hρ₁1, hval ρ₂ hρ₂0 hρ₂1]
  refine max_le ?_ ?_
  · calc perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) * ρ₁⁻¹
        ≤ ρ₁ * ρ₁⁻¹ := mul_le_mul_of_nonneg_right h1 zero_le
      _ = 1 := mul_inv_cancel₀ hρ₁0.ne'
  · calc perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) * ρ₂⁻¹
        ≤ ρ₂ * ρ₂⁻¹ := mul_le_mul_of_nonneg_right h2 zero_le
      _ = 1 := mul_inv_cancel₀ hρ₂0.ne'

/-- `wI(p^a/[ϖ]^b) ≤ 1` exactly when `ρ^a ≤ |ϖ|^b` at both radii (the
right-endpoint condition of the chart window `κ ≤ a/b`). -/
theorem wI_chartFracP_le_one (a b : ℕ)
    (h1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (h2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (chartFracP p F ϖ a b)) ≤ 1 := by
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
  have hϖ0 : 0 < perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) :=
    pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK, chartFracP]
  have hval : ∀ (ρ : NNReal) (hρ0 : 0 < ρ) (hρ1 : ρ < 1),
      wLoc p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ a)
        * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) ^ b)
      = ρ ^ a * ((perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ b := by
    intro ρ hρ0 hρ1
    rw [Valuation.map_mul, Valuation.map_pow, wLoc_algebraMap,
      show ((p : Ainf p F) ^ a) = (p : Ainf p F) ^ a * 1 from (mul_one _).symm,
      gaussValue_p_pow_mul p F hρ1.le a 1, gaussValue_one p F hρ1.le, mul_one,
      wLoc_AlocToBloc p F ϖ hρ0 hρ1, wAloc_teichPiInvAloc p F ϖ hρ0 hρ1]
  rw [hval ρ₁ hρ₁0 hρ₁1, hval ρ₂ hρ₂0 hρ₂1]
  have hkey : ∀ ρa : NNReal, ρa ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b →
      ρa * ((perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ b ≤ 1 := by
    intro ρa h
    rw [inv_pow]
    calc ρa * (perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)⁻¹
        ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b
          * (perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)⁻¹ :=
          mul_le_mul_of_nonneg_right h zero_le
      _ = 1 := mul_inv_cancel₀ (pow_pos hϖ0 b).ne'
  exact max_le (hkey _ h1) (hkey _ h2)

/-- **The unit ball of `Bloc`** for the interval norm, as a subring (carrier given
explicitly per PERF-1). -/
def blocUnitBall (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) :
    Subring (Bloc p F ϖ) where
  carrier := {x : Bloc p F ϖ | wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
    (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) ≤ 1}
  zero_mem' := by
    show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 0) ≤ 1
    rw [map_zero, wI_zero p F]
    exact zero_le_one
  one_mem' := by
    show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 1) ≤ 1
    rw [map_one, wI_one p F]
  add_mem' := by
    intro x y hx hy
    show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (x + y)) ≤ 1
    rw [map_add]
    exact le_trans (wI_add_le p F _ _) (max_le hx hy)
  mul_mem' := by
    intro x y hx hy
    show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (x * y)) ≤ 1
    rw [map_mul]
    calc wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          * BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y)
        ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
          * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y) :=
          wI_mul_le p F _ _
      _ ≤ 1 * 1 := mul_le_mul hx hy zero_le zero_le
      _ = 1 := one_mul 1
  neg_mem' := by
    intro x hx
    show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (-x)) ≤ 1
    rw [map_neg, wI_neg p F]
    exact hx

/-- `A_inf`-images lie in the unit ball (all Gauss values at radii `< 1` are `≤ 1`). -/
theorem algebraMap_mem_blocUnitBall (x : Ainf p F) :
    algebraMap (Ainf p F) (Bloc p F ϖ) x
      ∈ blocUnitBall p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
  show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
    (algebraMap (Ainf p F) (Bloc p F ϖ) x)) ≤ 1
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK, wLoc_algebraMap,
    wLoc_algebraMap]
  exact max_le (gaussValue_le_one p F hρ₁1.le x) (gaussValue_le_one p F hρ₂1.le x)

/-- **The chart subring generated by `A_inf` and the two window fractions lies in
the unit ball** — the forward half's generator step for the topology comparison. -/
theorem closure_chart_le_blocUnitBall (a b : ℕ)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Subring.closure
        (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
          ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})
      ≤ blocUnitBall p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
  rw [Subring.closure_le]
  rintro x (⟨y, rfl⟩ | hx)
  · exact algebraMap_mem_blocUnitBall p F ϖ y
  · rcases hx with rfl | hx
    · exact wI_chartFracPi_le_one p F ϖ hπ1 hπ2
    · rw [Set.mem_singleton_iff.mp hx]
      exact wI_chartFracP_le_one p F ϖ a b hr1 hr2

/-- Under the localization identification, the fraction `[ϖ]^{b+1}/s` is `[ϖ]/p`. -/
theorem blocEquiv_divByS_teichPi (b : ℕ) (hb : 0 < b) :
    blocEquivAwayChartS p F ϖ b hb
        (divByS (teichPi p F ϖ ^ (b + 1)) (chartS p F ϖ 1 b))
      = chartFracPi p F ϖ := by
  letI := isLocalization_chartS_Bloc p F ϖ b hb
  rw [blocEquivAwayChartS, divByS]
  rw [show (IsLocalization.algEquiv (Submonoid.powers (chartS p F ϖ 1 b))
      (Localization.Away (chartS p F ϖ 1 b)) (Bloc p F ϖ)).toRingEquiv
      (IsLocalization.mk' (Localization.Away (chartS p F ϖ 1 b))
        (teichPi p F ϖ ^ (b + 1))
        (⟨chartS p F ϖ 1 b, ⟨1, pow_one _⟩⟩ : Submonoid.powers (chartS p F ϖ 1 b)))
      = IsLocalization.mk' (Bloc p F ϖ) (teichPi p F ϖ ^ (b + 1))
        (⟨chartS p F ϖ 1 b, ⟨1, pow_one _⟩⟩ : Submonoid.powers (chartS p F ϖ 1 b))
    from IsLocalization.algEquiv_mk' _ _]
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  rw [chartFracPi, chartS, pow_one]
  have hvp : algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F))
      * ↑(isUnit_p_image p F ϖ).unit⁻¹ = 1 := by
    have h := (isUnit_p_image p F ϖ).unit.mul_inv
    rwa [(isUnit_p_image p F ϖ).unit_spec] at h
  calc algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ (b + 1))
      = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ)
        * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ b) := by
        rw [← map_mul, ← pow_succ']
    _ = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ)
        * (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F))
          * ↑(isUnit_p_image p F ϖ).unit⁻¹)
        * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ b) := by
        rw [hvp, mul_one]
    _ = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ)
        * ↑(isUnit_p_image p F ϖ).unit⁻¹
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          ((p : Ainf p F) * teichPi p F ϖ ^ b) := by
        rw [map_mul]
        ring

/-- Under the localization identification, the fraction `p^{a+1}/s` is `p^a/[ϖ]^b`. -/
theorem blocEquiv_divByS_p (a b : ℕ) (hb : 0 < b) :
    blocEquivAwayChartS p F ϖ b hb
        (divByS ((p : Ainf p F) ^ (a + 1)) (chartS p F ϖ 1 b))
      = chartFracP p F ϖ a b := by
  letI := isLocalization_chartS_Bloc p F ϖ b hb
  rw [blocEquivAwayChartS, divByS]
  rw [show (IsLocalization.algEquiv (Submonoid.powers (chartS p F ϖ 1 b))
      (Localization.Away (chartS p F ϖ 1 b)) (Bloc p F ϖ)).toRingEquiv
      (IsLocalization.mk' (Localization.Away (chartS p F ϖ 1 b))
        ((p : Ainf p F) ^ (a + 1))
        (⟨chartS p F ϖ 1 b, ⟨1, pow_one _⟩⟩ : Submonoid.powers (chartS p F ϖ 1 b)))
      = IsLocalization.mk' (Bloc p F ϖ) ((p : Ainf p F) ^ (a + 1))
        (⟨chartS p F ϖ 1 b, ⟨1, pow_one _⟩⟩ : Submonoid.powers (chartS p F ϖ 1 b))
    from IsLocalization.algEquiv_mk' _ _]
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  rw [chartFracP, chartS, pow_one]
  have hvt : AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) = 1 := by
    have h := AlocToBloc_teichPiInv_mul p F ϖ 1
    rwa [pow_one, pow_one] at h
  have hvtb : (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) ^ b
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ b) = 1 := by
    rw [map_pow, ← mul_pow, hvt, one_pow]
  calc algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ (a + 1))
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ a)
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) := by
        rw [← map_mul, ← pow_succ]
    _ = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ a)
        * ((AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) ^ b
          * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ b))
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) := by
        rw [hvtb, mul_one]
    _ = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ a)
        * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) ^ b
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          ((p : Ainf p F) * teichPi p F ϖ ^ b) := by
        rw [map_mul]
        ring

/-- The localization identification commutes with the structure maps. -/
theorem blocEquivAwayChartS_algebraMap (b : ℕ) (hb : 0 < b) (y : Ainf p F) :
    blocEquivAwayChartS p F ϖ b hb
        (algebraMap (Ainf p F) (Localization.Away (chartS p F ϖ 1 b)) y)
      = algebraMap (Ainf p F) (Bloc p F ϖ) y := by
  letI := isLocalization_chartS_Bloc p F ϖ b hb
  exact (IsLocalization.algEquiv (Submonoid.powers (chartS p F ϖ 1 b))
    (Localization.Away (chartS p F ϖ 1 b)) (Bloc p F ϖ)).commutes y

/-- **The ring-of-definition of the chart localization transports to the chart
subring of `Bloc`**: the image of `locSubring` under the localization
identification is the subring generated by `A_inf` and the two window
fractions. -/
theorem map_locSubring_chartData (a b : ℕ) (hb : 0 < b) :
    (locSubring (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)).map
        (blocEquivAwayChartS p F ϖ b hb).toRingHom
      = Subring.closure
          (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
            ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}) := by
  rw [locSubring, RingHom.map_closure]
  congr 1
  rw [Set.image_union]
  congr 1
  · -- the A₀ = ⊤ part: images of algebraMap through the equiv are algebraMap-images
    ext z
    constructor
    · rintro ⟨-, ⟨y, -, rfl⟩, rfl⟩
      exact ⟨y, (blocEquivAwayChartS_algebraMap p F ϖ b hb y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨algebraMap (Ainf p F) (Localization.Away (chartS p F ϖ 1 b)) y,
        ⟨y, by simp [podAinf], rfl⟩, blocEquivAwayChartS_algebraMap p F ϖ b hb y⟩
  · -- the two fractions
    ext z
    constructor
    · rintro ⟨-, ⟨t, rfl⟩, rfl⟩
      rcases t with ⟨t, ht⟩
      rw [chartT] at ht
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact Or.inr (Set.mem_singleton_iff.mpr
          (blocEquiv_divByS_p p F ϖ a b hb))
      · obtain rfl := Finset.mem_singleton.mp ht'
        exact Or.inl (blocEquiv_divByS_teichPi p F ϖ b hb)
    · rintro (rfl | hz)
      · refine ⟨divByS (teichPi p F ϖ ^ (b + 1)) (chartS p F ϖ 1 b),
          ⟨⟨teichPi p F ϖ ^ (b + 1), by rw [chartT]; simp⟩, rfl⟩,
          blocEquiv_divByS_teichPi p F ϖ b hb⟩
      · rw [Set.mem_singleton_iff.mp hz]
        refine ⟨divByS ((p : Ainf p F) ^ (a + 1)) (chartS p F ϖ 1 b),
          ⟨⟨(p : Ainf p F) ^ (a + 1), by rw [chartT]; simp⟩, rfl⟩,
          blocEquiv_divByS_p p F ϖ a b hb⟩

/-- **The forward half of the topology comparison, assembled**: the ring of
definition of the chart localization lands inside the `wI`-unit ball. -/
theorem map_locSubring_le_blocUnitBall (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    (locSubring (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)).map
        (blocEquivAwayChartS p F ϖ b hb).toRingHom
      ≤ blocUnitBall p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
  rw [map_locSubring_chartData p F ϖ a b hb]
  exact closure_chart_le_blocUnitBall p F ϖ a b hπ1 hπ2 hr1 hr2

/-- **Elements of `I_inf^n` have Gauss value at most `max(ρ, |ϖ|)^n`** (each
degree-`n` monomial does, and the bound-set is an ideal). -/
theorem gaussValue_le_of_mem_Iinf_pow {ρ : NNReal} (hρ1 : ρ < 1) (n : ℕ)
    {w : Ainf p F} (hw : w ∈ Iinf p F ϖ ^ n) :
    gaussValue p F ρ w
      ≤ (max ρ (perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F))) ^ n := by
  set q : NNReal := max ρ (perfectoidValuation p F
    ((PseudoUniformizer.toOF F ϖ : OF F) : F)) with hqdef
  -- the bound-set is an ideal
  set BdIdeal : Ideal (Ainf p F) :=
    { carrier := {w : Ainf p F | gaussValue p F ρ w ≤ q ^ n}
      zero_mem' := by
        show gaussValue p F ρ 0 ≤ q ^ n
        rw [gaussValue_zero p F]
        exact zero_le
      add_mem' := by
        intro x y hx hy
        show gaussValue p F ρ (x + y) ≤ q ^ n
        exact le_trans (gaussValue_add_le p F hρ1.le x y) (max_le hx hy)
      smul_mem' := by
        intro c x hx
        show gaussValue p F ρ (c * x) ≤ q ^ n
        calc gaussValue p F ρ (c * x)
            ≤ gaussValue p F ρ c * gaussValue p F ρ x :=
              gaussValue_mul_le p F hρ1 c x
          _ ≤ 1 * (q ^ n) := mul_le_mul (gaussValue_le_one p F hρ1.le c) hx
              zero_le zero_le
          _ = q ^ n := one_mul _ } with hBd
  have hmono : Ideal.span (chartMonomials p F ϖ n : Set (Ainf p F)) ≤ BdIdeal := by
    rw [Ideal.span_le]
    rintro x hx
    rw [chartMonomials, Finset.coe_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_coe, Finset.mem_range] at hi
    show gaussValue p F ρ ((p : Ainf p F) ^ i * teichPi p F ϖ ^ (n - i)) ≤ q ^ n
    have hval : gaussValue p F ρ ((p : Ainf p F) ^ i * teichPi p F ϖ ^ (n - i))
        = ρ ^ i * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (n - i) := by
      rw [show (p : Ainf p F) ^ i * teichPi p F ϖ ^ (n - i)
          = (p : Ainf p F) ^ i * (teichPi p F ϖ ^ (n - i) * 1) from by ring,
        gaussValue_p_pow_mul p F hρ1.le i, mul_one]
      congr 1
      rw [show teichPi p F ϖ ^ (n - i)
          = WittVector.teichmuller p ((PseudoUniformizer.toOF F ϖ) ^ (n - i))
          from by rw [map_pow]; rfl,
        gaussValue_teichmuller p F hρ1.le]
      rw [show (((PseudoUniformizer.toOF F ϖ) ^ (n - i) : OF F) : F)
          = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (n - i) from by
        push_cast; rfl, map_pow]
    rw [hval]
    calc ρ ^ i * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (n - i)
        ≤ q ^ i * q ^ (n - i) := by
          refine mul_le_mul (pow_le_pow_left₀ zero_le (le_max_left _ _) i)
            (pow_le_pow_left₀ zero_le (le_max_right _ _) (n - i)) zero_le zero_le
      _ = q ^ n := by
          rw [← pow_add]
          congr 1
          omega
  exact hmono (Iinf_pow_le_span_chartMonomials p F ϖ n hw)

/-- The transported image of an `A_inf`-element has interval norm bounded by the
maximum of the two Gauss values. -/
theorem wI_BIProd_algebraMap (x : Ainf p F) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (algebraMap (Ainf p F) (Bloc p F ϖ) x))
      = max (gaussValue p F ρ₁ x) (gaussValue p F ρ₂ x) := by
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK, wLoc_algebraMap,
    wLoc_algebraMap]

/-- **The `J^n`-cofinality estimate**: elements of the `n`-th power of the ideal of
definition of the chart localization transport into the `q^n`-ball of `B^I`, where
`q = max(ρ₁, ρ₂, |ϖ|) < 1`. -/
theorem wI_le_of_mem_locIdeal_pow (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) (n : ℕ)
    {y : ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b))}
    (hy : y ∈ locIdeal (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) ^ n) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (blocEquivAwayChartS p F ϖ b hb (↑y : Localization.Away (chartS p F ϖ 1 b))))
      ≤ (max (max ρ₁ ρ₂) (perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F))) ^ n := by
  set q : NNReal := max (max ρ₁ ρ₂) (perfectoidValuation p F
    ((PseudoUniformizer.toOF F ϖ : OF F) : F)) with hqdef
  set Bd : Ideal ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b)
      (chartS p F ϖ 1 b)) :=
    { carrier := {z | wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (blocEquivAwayChartS p F ϖ b hb
          (↑z : Localization.Away (chartS p F ϖ 1 b)))) ≤ q ^ n}
      zero_mem' := by
        show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (blocEquivAwayChartS p F ϖ b hb
            ((0 : ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b)
              (chartS p F ϖ 1 b))) : Localization.Away (chartS p F ϖ 1 b)))) ≤ q ^ n
        rw [ZeroMemClass.coe_zero, map_zero, map_zero, wI_zero p F]
        exact zero_le
      add_mem' := by
        intro x z hx hz
        show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (blocEquivAwayChartS p F ϖ b hb
            ((x + z : ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b)
              (chartS p F ϖ 1 b))) : Localization.Away (chartS p F ϖ 1 b)))) ≤ q ^ n
        rw [AddMemClass.coe_add, map_add, map_add]
        exact le_trans (wI_add_le p F _ _) (max_le hx hz)
      smul_mem' := by
        intro c z hz
        show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (blocEquivAwayChartS p F ϖ b hb
            ((c • z : ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b)
              (chartS p F ϖ 1 b))) : Localization.Away (chartS p F ϖ 1 b)))) ≤ q ^ n
        have hcoe : ((c • z : ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b)
            (chartS p F ϖ 1 b))) : Localization.Away (chartS p F ϖ 1 b))
            = (↑c : Localization.Away (chartS p F ϖ 1 b)) * ↑z := rfl
        rw [hcoe, map_mul, map_mul]
        have hcball : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
            (blocEquivAwayChartS p F ϖ b hb
              (↑c : Localization.Away (chartS p F ϖ 1 b)))) ≤ 1 :=
          map_locSubring_le_blocUnitBall p F ϖ a b hb hπ1 hπ2 hr1 hr2
            ⟨c, c.2, rfl⟩
        exact le_trans (wI_mul_le p F _ _)
          (le_trans (mul_le_mul hcball hz zero_le zero_le)
            (le_of_eq (one_mul _))) } with hBd
  suffices hle : locIdeal (podAinf p F ϖ) (chartT p F ϖ a b)
      (chartS p F ϖ 1 b) ^ n ≤ Bd from hle hy
  rw [locIdeal, ← Ideal.map_pow, Ideal.map, Ideal.span_le]
  rintro z ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe] at hw
  show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
    (blocEquivAwayChartS p F ϖ b hb
      (↑(algebraMapD (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) w)
        : Localization.Away (chartS p F ϖ 1 b)))) ≤ q ^ n
  have hcoe : (↑(algebraMapD (podAinf p F ϖ) (chartT p F ϖ a b)
      (chartS p F ϖ 1 b) w) : Localization.Away (chartS p F ϖ 1 b))
      = algebraMap (Ainf p F) (Localization.Away (chartS p F ϖ 1 b)) ↑w := rfl
  rw [hcoe, blocEquivAwayChartS_algebraMap p F ϖ b hb, wI_BIProd_algebraMap p F ϖ]
  have hwmem : (↑w : Ainf p F) ∈ Iinf p F ϖ ^ n := by
    have hset := idealToTop_pow_eq_preimage (Iinf p F ϖ) n
    have hmem : w ∈ ((idealToTop (Iinf p F ϖ) ^ n :
        Ideal ↥(⊤ : Subring (Ainf p F))) :
        Set ↥(⊤ : Subring (Ainf p F))) := hw
    rw [hset] at hmem
    exact hmem
  refine max_le ?_ ?_
  · calc gaussValue p F ρ₁ ↑w
        ≤ (max ρ₁ (perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F))) ^ n :=
          gaussValue_le_of_mem_Iinf_pow p F ϖ hρ₁1 n hwmem
      _ ≤ q ^ n := by
          refine pow_le_pow_left₀ zero_le (max_le ?_ (le_max_right _ _)) n
          exact le_trans (le_max_left _ _) (le_max_left _ _)
  · calc gaussValue p F ρ₂ ↑w
        ≤ (max ρ₂ (perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F))) ^ n :=
          gaussValue_le_of_mem_Iinf_pow p F ϖ hρ₂1 n hwmem
      _ ≤ q ^ n := by
          refine pow_le_pow_left₀ zero_le (max_le ?_ (le_max_right _ _)) n
          exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- **Coefficient bounds from an interval-norm bound**: if
`x = A/(p[ϖ])^k ∈ Bloc` has `wI(x) ≤ ε`, then every Teichmüller coordinate of `A`
satisfies `ρ^m·|a_m| ≤ ε·(ρ·|ϖ|)^k` at both radii. -/
theorem gaussTerm_le_of_wI_le {ε : NNReal} (k : ℕ) (A : Ainf p F)
    {x : Bloc p F ϖ}
    (hx : x * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ k) = algebraMap (Ainf p F) (Bloc p F ϖ) A)
    (hwI : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) ≤ ε)
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρmem : ρ = ρ₁ ∨ ρ = ρ₂) (m : ℕ) :
    gaussTerm p F ρ A m
      ≤ ε * (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := by
  have hval : wLoc p F ϖ hρ0 hρ1 x * (ρ * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k = gaussValue p F ρ A := by
    have h2 := congrArg (wLoc p F ϖ hρ0 hρ1) hx
    rw [Valuation.map_mul, map_pow, Valuation.map_pow, wLoc_algebraMap,
      wLoc_algebraMap, gaussValue_p_teichPi p F ϖ hρ1] at h2
    exact h2
  have hwLoc : wLoc p F ϖ hρ0 hρ1 x ≤ ε := by
    rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK] at hwI
    rcases hρmem with rfl | rfl
    · exact le_trans (le_max_left _ _) hwI
    · exact le_trans (le_max_right _ _) hwI
  calc gaussTerm p F ρ A m
      ≤ gaussValue p F ρ A := gaussTerm_le_gaussValue p F hρ1.le A m
    _ = wLoc p F ϖ hρ0 hρ1 x * (ρ * perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := hval.symm
    _ ≤ ε * (ρ * perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k :=
        mul_le_mul_of_nonneg_right hwLoc zero_le

/-- The chart-to-`B^I` ring homomorphism on the localization (before completion).
Defined with an explicit `toFun` so that its coercion is definitionally the plain
composite (PERF: keeps the localization equivalence's body out of coe-unfolds). -/
noncomputable def chartToBIProd (b : ℕ) (hb : 0 < b) :
    Localization.Away (chartS p F ϖ 1 b) →+*
      (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) where
  toFun z := BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (blocEquivAwayChartS p F ϖ b hb z)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

/-- **The forward ball inclusion, basis form**: for every `ε > 0` some
`locNhd`-basic set maps into the `ε`-ball of `B^I` — the topology-free core of the
continuity of the chart map (packaged into `Tendsto` at the assembly stage). -/
theorem exists_locNhd_le_ball (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    {ε : NNReal} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ locNhd (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) n,
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (blocEquivAwayChartS p F ϖ b hb z)) ≤ ε := by
  set q : NNReal := max (max ρ₁ ρ₂) (perfectoidValuation p F
    ((PseudoUniformizer.toOF F ϖ : OF F) : F)) with hqdef
  have hq1 : q < 1 := by
    rw [hqdef]
    exact max_lt (max_lt hρ₁1 hρ₂1) (perfectoidValuation_toOF_lt_one p F ϖ)
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    hq1).eventually_le_const hε).exists
  refine ⟨n, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  exact le_trans (wI_le_of_mem_locIdeal_pow p F ϖ a b hb hπ1 hπ2 hr1 hr2 n hy) hn

/-- The chart topology, behind a non-reducible definition so statements never
unfold the `RingSubgroupsBasis` construction (PERF). -/
noncomputable def chartTopology (a b : ℕ) :
    TopologicalSpace (Localization.Away (chartS p F ϖ 1 b)) :=
  (chartData p F ϖ 1 b a b).topology

/-- The chart-map is continuous at zero for the chart topology. -/
theorem tendsto_chartToBIProd (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    @Filter.Tendsto _ _
      (fun z => BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (blocEquivAwayChartS p F ϖ b hb z))
      (@nhds _ (chartTopology p F ϖ a b) 0) (nhds 0) := by
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hball⟩ := exists_wI_ball_subset p F hU
  obtain ⟨n, hn⟩ := exists_locNhd_le_ball p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2 hε
  have hmem : ((locNhd (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) n
      : AddSubgroup (Localization.Away (chartS p F ϖ 1 b)))
      : Set (Localization.Away (chartS p F ϖ 1 b)))
      ∈ @nhds _ (chartTopology p F ϖ a b) 0 := by
    show _ ∈ @nhds _ ((chartData p F ϖ 1 b a b).topology) 0
    exact (locBasis (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)
      (chartData p F ϖ 1 b a b).hopen).hasBasis_nhds_zero.mem_of_mem
        (i := n) trivial
  refine Filter.mem_of_superset hmem ?_
  intro z hz
  refine hball ?_
  exact hn z hz

/-- The coe-form of `tendsto_chartToBIProd` (isolated so the coercion-vs-lambda
defeq check happens once). -/
theorem tendsto_chartToBIProd_coe (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Filter.Tendsto ⇑(chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb)
      (@nhds _ (chartTopology p F ϖ a b) 0) (nhds 0) := by
  refine (tendsto_chartToBIProd p F ϖ a b hb hπ1 hπ2 hr1 hr2).congr fun z => ?_
  rfl

/-- The ring-topology instance at the opaque chart topology (elaborated once). -/
theorem chartTopologicalRing (a b : ℕ) :
    @IsTopologicalRing (Localization.Away (chartS p F ϖ 1 b))
      (chartTopology p F ϖ a b) _ :=
  (chartData p F ϖ 1 b a b).isTopologicalRing

/-- The chart map is continuous for the chart topology. -/
theorem continuous_chartToBIProd (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    @Continuous _ _ (chartTopology p F ϖ a b) _
      (chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb) := by
  letI : TopologicalSpace (Localization.Away (chartS p F ϖ 1 b)) :=
    chartTopology p F ϖ a b
  haveI : IsTopologicalRing (Localization.Away (chartS p F ϖ 1 b)) :=
    chartTopologicalRing p F ϖ a b
  haveI : IsTopologicalAddGroup (Localization.Away (chartS p F ϖ 1 b)) :=
    (chartTopologicalRing p F ϖ a b).to_topologicalAddGroup
  refine continuous_of_tendsto_nhds_zero
    (chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb) ?_
  exact tendsto_chartToBIProd_coe p F ϖ a b hb hπ1 hπ2 hr1 hr2

set_option warn.classDefReducibility false in
/-- The chart uniformity (right uniformity of the chart topology), opaque. -/
noncomputable def chartUniformity (a b : ℕ) :
    UniformSpace (Localization.Away (chartS p F ϖ 1 b)) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _ (chartTopology p F ϖ a b)
    (@IsTopologicalRing.to_topologicalAddGroup _ _ (chartTopology p F ϖ a b)
      (chartTopologicalRing p F ϖ a b))

/-- The uniform-add-group property at the chart uniformity. -/
theorem chartIsUniformAddGroup (a b : ℕ) :
    @IsUniformAddGroup (Localization.Away (chartS p F ϖ 1 b))
      (chartUniformity p F ϖ a b) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (chartTopology p F ϖ a b)
    (@IsTopologicalRing.to_topologicalAddGroup _ _ (chartTopology p F ϖ a b)
      (chartTopologicalRing p F ϖ a b))

/-- **The chart map extended to the completion**: the canonical continuous ring
homomorphism from the completed chart localization to the product of completed
fields (landing, by density, in `B^I`). -/
noncomputable def chartCompletionToBIProd (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    letI : UniformSpace (Localization.Away (chartS p F ϖ 1 b)) :=
      chartUniformity p F ϖ a b
    letI : IsTopologicalRing (Localization.Away (chartS p F ϖ 1 b)) :=
      chartTopologicalRing p F ϖ a b
    letI : IsUniformAddGroup (Localization.Away (chartS p F ϖ 1 b)) :=
      chartIsUniformAddGroup p F ϖ a b
    (UniformSpace.Completion (Localization.Away (chartS p F ϖ 1 b))) →+*
      (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
  letI : UniformSpace (Localization.Away (chartS p F ϖ 1 b)) :=
    chartUniformity p F ϖ a b
  letI : IsTopologicalRing (Localization.Away (chartS p F ϖ 1 b)) :=
    chartTopologicalRing p F ϖ a b
  letI : IsUniformAddGroup (Localization.Away (chartS p F ϖ 1 b)) :=
    chartIsUniformAddGroup p F ϖ a b
  UniformSpace.Completion.extensionHom
    (chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb)
    (continuous_chartToBIProd p F ϖ a b hb hπ1 hπ2 hr1 hr2)

/-- The chart uniformity is (definitionally) the rational-datum uniformity. -/
theorem chartUniformity_eq (a b : ℕ) :
    chartUniformity p F ϖ a b = (chartData p F ϖ 1 b a b).uniformSpace := rfl

/-- **The presheaf value of the chart datum maps to the product of completed
fields**: the canonical continuous ring homomorphism
`𝒪(R(T/s)) = A_inf⟨T/s⟩ →+* hatK ρ₁ × hatK ρ₂` extending the chart map. -/
noncomputable def presheafChartToBIProd (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    presheafValue (chartData p F ϖ 1 b a b) →+*
      (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
  chartCompletionToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2

/-- The presheaf-value chart map extends the chart map along the completion
coercion. -/
theorem presheafChartToBIProd_coe (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (z : Localization.Away (chartS p F ϖ 1 b)) :
    presheafChartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2
        ((chartData p F ϖ 1 b a b).coeRingHom z)
      = chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb z := by
  letI : UniformSpace (Localization.Away (chartS p F ϖ 1 b)) :=
    chartUniformity p F ϖ a b
  letI : IsTopologicalRing (Localization.Away (chartS p F ϖ 1 b)) :=
    chartTopologicalRing p F ϖ a b
  letI : IsUniformAddGroup (Localization.Away (chartS p F ϖ 1 b)) :=
    chartIsUniformAddGroup p F ϖ a b
  exact UniformSpace.Completion.extensionHom_coe
    (chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb)
    (continuous_chartToBIProd p F ϖ a b hb hπ1 hπ2 hr1 hr2) z

/-- **Division by a pseudo-uniformizer power in `O_F`**: an element of value at
most `|ϖ|^e` factors as `c'·ϖ^e`. -/
theorem exists_factor_toOF (e : ℕ) (c : OF F)
    (h : perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ e) :
    ∃ c' : OF F, c = c' * PseudoUniformizer.toOF F ϖ ^ e := by
  have hπne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
  have hπ0 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact hπne
  have hle1 : perfectoidValuation p F ((c : F)
      * ((((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ e)⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, map_inv₀, Valuation.map_pow]
    calc perfectoidValuation p F (c : F)
          * (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ e)⁻¹
        ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ e
          * (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ e)⁻¹ :=
          mul_le_mul_of_nonneg_right h zero_le
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero e hπ0)
  obtain ⟨u, hu⟩ := (perfectoidValuation_integers p F).exists_of_le_one hle1
  refine ⟨u, Subtype.ext ?_⟩
  have hu' : ((u : OF F) : F) = (c : F)
      * ((((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ e)⁻¹ := hu
  have hcoe : ((↑(u * PseudoUniformizer.toOF F ϖ ^ e) : OF F) : F)
      = ((u : OF F) : F) * (((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ e := by
    push_cast
    ring
  rw [hcoe, hu', mul_assoc, inv_mul_cancel₀ (pow_ne_zero e hπne), mul_one]

/-- `([ϖ]/p)^e · p^e = [ϖ]^e` in `Bloc`. -/
theorem chartFracPi_pow_mul_p_pow (e : ℕ) :
    chartFracPi p F ϖ ^ e
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ e)
      = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ e) := by
  have hone : chartFracPi p F ϖ * algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)
      = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) := by
    rw [chartFracPi, mul_assoc, IsUnit.val_inv_mul, mul_one]
  rw [map_pow, map_pow, ← mul_pow, hone]

/-- `(p^a/[ϖ]^b)^t · [ϖ]^{bt} = p^{at}` in `Bloc`. -/
theorem chartFracP_pow_mul_teichPi_pow (a b t : ℕ) :
    chartFracP p F ϖ a b ^ t
        * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ (b * t))
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ (a * t)) := by
  have hw : (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) ^ (b * t)
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ (b * t)) = 1 := by
    have h := AlocToBloc_teichPiInv_mul p F ϖ (b * t)
    rwa [map_pow] at h
  rw [chartFracP, mul_pow, ← pow_mul, mul_assoc, hw, mul_one, ← map_pow,
    ← pow_mul]


/-- The `A_inf`-side of the low-term split: `[ϖ]^{k-m}·([c']·(p^m·[ϖ]^k)) = [c]·p^m`
when `c = c'·ϖ^{2k-m}`. -/
theorem teich_shift_low (k m : ℕ) (hm : m ≤ k) (c c' : OF F)
    (hc : c = c' * PseudoUniformizer.toOF F ϖ ^ (2 * k - m)) :
    teichPi p F ϖ ^ (k - m) * (WittVector.teichmuller p c'
        * ((p : Ainf p F) ^ m * teichPi p F ϖ ^ k))
      = WittVector.teichmuller p c * (p : Ainf p F) ^ m := by
  rw [hc, show PseudoUniformizer.toOF F ϖ ^ (2 * k - m)
      = PseudoUniformizer.toOF F ϖ ^ (k - m) * PseudoUniformizer.toOF F ϖ ^ k from by
        rw [← pow_add]; congr 1; omega,
    map_mul (WittVector.teichmuller p), map_mul (WittVector.teichmuller p),
    teichPi_pow, teichPi_pow]
  ring

/-- The `A_inf`-side of the high-term cross identity: `[c']·[ϖ]^k = [c]·[ϖ]^e`
when `c·ϖ^e = c'·ϖ^k`. -/
theorem teich_cross (e f : ℕ) (c c' : OF F)
    (hc : c * PseudoUniformizer.toOF F ϖ ^ e = c' * PseudoUniformizer.toOF F ϖ ^ f) :
    WittVector.teichmuller p c' * teichPi p F ϖ ^ f
      = WittVector.teichmuller p c * teichPi p F ϖ ^ e := by
  rw [teichPi_pow, teichPi_pow, ← map_mul (WittVector.teichmuller p),
    ← map_mul (WittVector.teichmuller p), ← hc]

/-- **The low-term identity**: for `m ≤ k` and `c = c'·ϖ^{2k-m}`, the subring
element `([ϖ]/p)^{k-m}·[c']` multiplies with the denominator to `[c]·p^m`. -/
theorem chart_term_low_eq (k m : ℕ) (hm : m ≤ k) (c c' : OF F)
    (hc : c = c' * PseudoUniformizer.toOF F ϖ ^ (2 * k - m)) :
    chartFracPi p F ϖ ^ (k - m)
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')
        * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c * (p : Ainf p F) ^ m) := by
  rw [mul_assoc, ← map_mul,
    show WittVector.teichmuller p c' * ((p : Ainf p F) * teichPi p F ϖ) ^ k
        = (p : Ainf p F) ^ (k - m) * (WittVector.teichmuller p c'
            * ((p : Ainf p F) ^ m * teichPi p F ϖ ^ k)) from by
      rw [mul_pow, show (p : Ainf p F) ^ k
          = (p : Ainf p F) ^ (k - m) * (p : Ainf p F) ^ m from by
        rw [← pow_add]; congr 1; omega]
      ring,
    map_mul, ← mul_assoc, chartFracPi_pow_mul_p_pow, ← map_mul,
    teich_shift_low p F ϖ k m hm c c' hc]

/-- The `A_inf`-side regrouping for the high terms. -/
theorem high_arg_split (b k t j : ℕ) (c c' : OF F)
    (hc : c * PseudoUniformizer.toOF F ϖ ^ (b * t)
      = c' * PseudoUniformizer.toOF F ϖ ^ k) :
    (p : Ainf p F) ^ j * WittVector.teichmuller p c'
        * ((p : Ainf p F) * teichPi p F ϖ) ^ k
      = teichPi p F ϖ ^ (b * t)
          * (WittVector.teichmuller p c * (p : Ainf p F) ^ (k + j)) := by
  rw [mul_pow]
  calc (p : Ainf p F) ^ j * WittVector.teichmuller p c'
        * ((p : Ainf p F) ^ k * teichPi p F ϖ ^ k)
      = WittVector.teichmuller p c' * teichPi p F ϖ ^ k
          * (p : Ainf p F) ^ (k + j) := by
        rw [pow_add]; ring
    _ = WittVector.teichmuller p c * teichPi p F ϖ ^ (b * t)
          * (p : Ainf p F) ^ (k + j) := by
        rw [teich_cross p F ϖ (b * t) k c c' hc]
    _ = teichPi p F ϖ ^ (b * t)
          * (WittVector.teichmuller p c * (p : Ainf p F) ^ (k + j)) := by
        ring

/-- The `A_inf`-side final power collection for the high terms. -/
theorem high_arg_final (a k t j : ℕ) (c : OF F) :
    (p : Ainf p F) ^ (a * t) * (WittVector.teichmuller p c * (p : Ainf p F) ^ (k + j))
      = WittVector.teichmuller p c * (p : Ainf p F) ^ (k + a * t + j) := by
  rw [show k + a * t + j = a * t + (k + j) from by omega, pow_add]
  ring

/-- **The high-term identity**: for `c·ϖ^{bt} = c'·ϖ^k`, the subring element
`(p^a/[ϖ]^b)^t·(p^j·[c'])` multiplies with the denominator to `[c]·p^{k+at+j}`. -/
theorem chart_term_high_eq (a b k t j : ℕ) (c c' : OF F)
    (hc : c * PseudoUniformizer.toOF F ϖ ^ (b * t)
      = c' * PseudoUniformizer.toOF F ϖ ^ k) :
    chartFracP p F ϖ a b ^ t
        * algebraMap (Ainf p F) (Bloc p F ϖ)
            ((p : Ainf p F) ^ j * WittVector.teichmuller p c')
        * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c * (p : Ainf p F) ^ (k + a * t + j)) := by
  rw [mul_assoc, ← map_mul, high_arg_split p F ϖ b k t j c c' hc, map_mul,
    ← mul_assoc, chartFracP_pow_mul_teichPi_pow, ← map_mul,
    high_arg_final p F a k t j c]

/-- The `A_inf`-side regrouping for the tail. -/
theorem tail_arg_split (b k : ℕ) (hb : 0 < b) (z : Ainf p F) :
    teichPi p F ϖ ^ (b * k - k) * z * ((p : Ainf p F) * teichPi p F ϖ) ^ k
      = teichPi p F ϖ ^ (b * k) * ((p : Ainf p F) ^ k * z) := by
  rw [mul_pow, show teichPi p F ϖ ^ (b * k)
      = teichPi p F ϖ ^ (b * k - k) * teichPi p F ϖ ^ k from by
    rw [← pow_add]; congr 1
    have := Nat.le_mul_of_pos_left k hb
    omega]
  ring

/-- The `A_inf`-side final power collection for the tail. -/
theorem tail_arg_final (a k : ℕ) (z : Ainf p F) :
    (p : Ainf p F) ^ (a * k) * ((p : Ainf p F) ^ k * z)
      = (p : Ainf p F) ^ (k + a * k) * z := by
  rw [show k + a * k = a * k + k from Nat.add_comm k (a * k), pow_add]
  ring

/-- **The tail identity**: the `p^N`-tail of the prefix decomposition
(`N = k + ak`) multiplies with the denominator to `p^N·z` through
`(p^a/[ϖ]^b)^k·[ϖ]^{bk-k}`. -/
theorem chart_tail_eq (a b k : ℕ) (hb : 0 < b) (z : Ainf p F) :
    chartFracP p F ϖ a b ^ k
        * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ (b * k - k) * z)
        * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ (k + a * k) * z) := by
  rw [mul_assoc, ← map_mul, tail_arg_split p F ϖ b k hb z, map_mul, ← mul_assoc,
    chartFracP_pow_mul_teichPi_pow, ← map_mul, tail_arg_final p F a k z]


/-- **Existence of the low-term factor**: at the exact left endpoint
`ρ₁ = |ϖ|`, the `m ≤ k` Teichmüller coordinates of a numerator of an element in
the `|ϖ|^b`-ball divide by `ϖ^{2k-m}`. -/
theorem exists_teichCoeff_factor_low (b k m : ℕ) (hm : m ≤ k)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (A : Ainf p F) {x : Bloc p F ϖ}
    (hx : x * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ k) = algebraMap (Ainf p F) (Bloc p F ϖ) A)
    (hwI : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    ∃ c' : OF F, teichCoeff p F A m
      = c' * PseudoUniformizer.toOF F ϖ ^ (2 * k - m) := by
  set vπ : NNReal :=
    perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hvπ
  have hπ0 : 0 < vπ := hexact1 ▸ hρ₁0
  have hπ1 : vπ < 1 := hexact1 ▸ hρ₁1
  have hterm := gaussTerm_le_of_wI_le p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) k A hx hwI hρ₁0 hρ₁1 (Or.inl rfl) m
  rw [gaussTerm, ← hexact1, ← hvπ] at hterm
  refine exists_factor_toOF p F ϖ (2 * k - m) _ ?_
  rw [← hvπ]
  have hcollect : vπ ^ b * (vπ * vπ) ^ k = vπ ^ m * vπ ^ (2 * k - m + b) := by
    rw [← pow_two, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [hcollect] at hterm
  have hcancel : perfectoidValuation p F ((teichCoeff p F A m : OF F) : F)
      ≤ vπ ^ (2 * k - m + b) :=
    le_of_mul_le_mul_left hterm (pow_pos hπ0 m)
  exact le_trans hcancel (pow_le_pow_of_le_one zero_le hπ1.le (by omega))

/-- **Existence of the high-term factor**: at the exact right endpoint
`ρ₂^a = |ϖ|^b`, the `m > k` Teichmüller coordinates satisfy
`a_m·ϖ^{bt} ∈ ϖ^k·O_F` for `t = (m-k)/a`. -/
theorem exists_teichCoeff_factor_high (a b k m : ℕ) (ha : 0 < a) (hm : k < m)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (A : Ainf p F) {x : Bloc p F ϖ}
    (hx : x * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ k) = algebraMap (Ainf p F) (Bloc p F ϖ) A)
    (hwI : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    ∃ c' : OF F, teichCoeff p F A m
        * PseudoUniformizer.toOF F ϖ ^ (b * ((m - k) / a))
      = c' * PseudoUniformizer.toOF F ϖ ^ k := by
  set vπ : NNReal :=
    perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hvπ
  have hπ0 : 0 < vπ := by
    have hπne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
      fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
    rw [hvπ, pos_iff_ne_zero, Ne, Valuation.zero_iff]
    exact hπne
  have hπ1 : vπ < 1 := by
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · exfalso
        have h1 : ρ₂ ^ a < 1 := pow_lt_one₀ zero_le hρ₂1 ha.ne'
        rw [hexact2, hb0, pow_zero] at h1
        exact absurd h1 (lt_irrefl 1)
      · exact hb0
    have h1 : vπ ^ b < 1 := by
      rw [hvπ, ← hexact2]
      exact pow_lt_one₀ zero_le hρ₂1 ha.ne'
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd (one_le_pow₀ hcon) (not_le.mpr h1)
  set i : ℕ := m - k with hidef
  have hik : m = k + i := by omega
  set t : ℕ := i / a with htdef
  have hterm := gaussTerm_le_of_wI_le p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) k A hx hwI hρ₂0 hρ₂1 (Or.inr rfl) m
  rw [gaussTerm, ← hvπ] at hterm
  set X : NNReal := perfectoidValuation p F ((teichCoeff p F A m : OF F) : F)
    with hXdef
  have h2 : ρ₂ ^ i * X ≤ vπ ^ (b + k) := by
    refine le_of_mul_le_mul_left ?_ (pow_pos hρ₂0 k)
    calc ρ₂ ^ k * (ρ₂ ^ i * X) = ρ₂ ^ m * X := by rw [hik, pow_add]; ring
      _ ≤ vπ ^ b * (ρ₂ * vπ) ^ k := hterm
      _ = ρ₂ ^ k * (vπ ^ (b + k)) := by rw [mul_pow, pow_add]; ring
  have h4 : vπ ^ (b * i) * X ^ a ≤ vπ ^ (a * b + a * k) := by
    have h3 := pow_le_pow_left₀ zero_le h2 a
    calc vπ ^ (b * i) * X ^ a
        = (ρ₂ ^ a) ^ i * X ^ a := by rw [hexact2, ← pow_mul]
      _ = (ρ₂ ^ i * X) ^ a := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ (vπ ^ (b + k)) ^ a := h3
      _ = vπ ^ (a * b + a * k) := by rw [← pow_mul]; congr 1; ring
  have key : k * a + b * i ≤ a * b + a * k + b * t * a := by
    have hmod := Nat.div_add_mod i a
    have hlt : i % a < a := Nat.mod_lt i ha
    calc k * a + b * i = k * a + b * (a * (i / a) + i % a) := by rw [hmod]
      _ = k * a + (b * t * a + b * (i % a)) := by rw [← htdef]; ring
      _ ≤ k * a + (b * t * a + b * a) := by
          exact Nat.add_le_add_left (Nat.add_le_add_left
            (Nat.mul_le_mul_left b (le_of_lt hlt)) _) _
      _ = a * b + a * k + b * t * a := by ring
  have h6 : X ^ a * vπ ^ (b * t * a) ≤ (vπ ^ k) ^ a := by
    refine le_of_mul_le_mul_right ?_ (pow_pos hπ0 (b * i))
    calc X ^ a * vπ ^ (b * t * a) * vπ ^ (b * i)
        = vπ ^ (b * i) * X ^ a * vπ ^ (b * t * a) := by ring
      _ ≤ vπ ^ (a * b + a * k) * vπ ^ (b * t * a) :=
          mul_le_mul_of_nonneg_right h4 zero_le
      _ = vπ ^ (a * b + a * k + b * t * a) := by rw [← pow_add]
      _ ≤ vπ ^ (k * a + b * i) := pow_le_pow_of_le_one zero_le hπ1.le key
      _ = (vπ ^ k) ^ a * vπ ^ (b * i) := by rw [← pow_mul, ← pow_add]
  have h7 : X * vπ ^ (b * t) ≤ vπ ^ k := by
    refine le_of_pow_le_pow_left₀ ha.ne' zero_le ?_
    calc (X * vπ ^ (b * t)) ^ a = X ^ a * vπ ^ (b * t * a) := by
          rw [mul_pow, ← pow_mul]
      _ ≤ (vπ ^ k) ^ a := h6
  refine exists_factor_toOF p F ϖ k _ ?_
  rw [← hvπ]
  calc perfectoidValuation p F
        ((↑(teichCoeff p F A m * PseudoUniformizer.toOF F ϖ ^ (b * t)) : OF F) : F)
      = X * vπ ^ (b * t) := by
        rw [hXdef, hvπ]
        push_cast
        rw [Valuation.map_mul, Valuation.map_pow]
    _ ≤ vπ ^ k := h7


/-- **The reverse inclusion at the exact chart interval (Kedlaya's plus-ring
arithmetic on the dense layer)**: at the exact endpoints `ρ₁ = |ϖ|`,
`ρ₂^a = |ϖ|^b`, every element of `Bloc` in the `|ϖ|^b`-ball lies in the subring
generated by `A_inf` and the two chart fractions. -/
theorem mem_chartSubring_of_wI_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    {x : Bloc p F ϖ}
    (hwI : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    x ∈ Subring.closure
      (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
        ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}) := by
  set S : Subring (Bloc p F ϖ) := Subring.closure
    (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
      ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}) with hSdef
  have hmemAm : ∀ y : Ainf p F, algebraMap (Ainf p F) (Bloc p F ϖ) y ∈ S :=
    fun y => Subring.subset_closure (Or.inl ⟨y, rfl⟩)
  have hmemU : chartFracPi p F ϖ ∈ S :=
    Subring.subset_closure (Or.inr (Set.mem_insert _ _))
  have hmemV : chartFracP p F ϖ a b ∈ S :=
    Subring.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  obtain ⟨⟨A, s⟩, hs⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) x
  obtain ⟨k, hk⟩ := s.2
  have hx : x * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) A := by
    rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ k = (s : Ainf p F) from hk]
    exact hs
  set N : ℕ := k + a * k with hNdef
  obtain ⟨z, hzA⟩ := exists_eq_sum_teichCoeff_add p F A N
  have key : ∀ m, m < N → ∃ y, y ∈ S ∧
      y * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k)
        = algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p (teichCoeff p F A m) * (p : Ainf p F) ^ m) := by
    intro m hmN
    by_cases hmk : m ≤ k
    · obtain ⟨c', hc'⟩ := exists_teichCoeff_factor_low p F ϖ
        (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
        b k m hmk hexact1 A hx hwI
      exact ⟨chartFracPi p F ϖ ^ (k - m)
          * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'),
        mul_mem (pow_mem hmemU _) (hmemAm _),
        chart_term_low_eq p F ϖ k m hmk _ c' hc'⟩
    · push Not at hmk
      obtain ⟨c', hc'⟩ := exists_teichCoeff_factor_high p F ϖ
        (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
        a b k m ha hmk hexact2 A hx hwI
      have hexp : k + a * ((m - k) / a) + (m - k) % a = m := by
        have := Nat.div_add_mod (m - k) a
        omega
      have h := chart_term_high_eq p F ϖ a b k ((m - k) / a) ((m - k) % a) _ c' hc'
      rw [hexp] at h
      exact ⟨_, mul_mem (pow_mem hmemV _) (hmemAm _), h⟩
  choose! y hyS hyEq using key
  have htail := chart_tail_eq p F ϖ a b k hb z
  have htotal : ((∑ m ∈ Finset.range N, y m)
        + chartFracP p F ϖ a b ^ k * algebraMap (Ainf p F) (Bloc p F ϖ)
            (teichPi p F ϖ ^ (b * k - k) * z))
      * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) A := by
    rw [add_mul, Finset.sum_mul]
    have hsum : (∑ m ∈ Finset.range N, y m * algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) * teichPi p F ϖ) ^ k))
        = ∑ m ∈ Finset.range N, algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p (teichCoeff p F A m) * (p : Ainf p F) ^ m) :=
      Finset.sum_congr rfl fun m hm => hyEq m (Finset.mem_range.mp hm)
    rw [hsum, ← map_sum, htail, ← map_add, ← hzA]
  have hunit : IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ k)) := by
    rw [map_pow]
    exact (isUnit_p_teichPi_image p F ϖ).pow k
  have hxeq : x = (∑ m ∈ Finset.range N, y m)
      + chartFracP p F ϖ a b ^ k * algebraMap (Ainf p F) (Bloc p F ϖ)
          (teichPi p F ϖ ^ (b * k - k) * z) :=
    hunit.mul_right_cancel (hx.trans htotal.symm)
  rw [hxeq]
  exact add_mem (sum_mem fun m hm => hyS m (Finset.mem_range.mp hm))
    (mul_mem (pow_mem hmemV _) (hmemAm _))

/-- **The scaled reverse inclusion**: an element of the `min(ρ₁,ρ₂)^n·|ϖ|^b`-ball
of `Bloc` is `p^n` times an element of the chart subring. -/
theorem exists_p_pow_mul_mem_chartSubring (a b n : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    {x : Bloc p F ϖ}
    (hwI : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
      ≤ min ρ₁ ρ₂ ^ n * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    ∃ x' ∈ Subring.closure
        (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
          ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}),
      x = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ n) * x' := by
  set u := (isUnit_p_image p F ϖ).unit with hudef
  set x' : Bloc p F ϖ := (↑u⁻¹ : Bloc p F ϖ) ^ n * x with hx'def
  have hxeq : x = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ n) * x' := by
    rw [hx'def, map_pow, ← mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow,
      one_mul]
  have hloc : ∀ (ρ : NNReal) (hρ0 : 0 < ρ) (hρ1 : ρ < 1), ρ = ρ₁ ∨ ρ = ρ₂ →
      wLoc p F ϖ hρ0 hρ1 x' ≤ perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
    intro ρ hρ0 hρ1 hρmem
    have hwx : wLoc p F ϖ hρ0 hρ1 x ≤ min ρ₁ ρ₂ ^ n * perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
      rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK] at hwI
      rcases hρmem with rfl | rfl
      · exact le_trans (le_max_left _ _) hwI
      · exact le_trans (le_max_right _ _) hwI
    have hmin : min ρ₁ ρ₂ ≤ ρ := by
      rcases hρmem with rfl | rfl
      · exact min_le_left _ _
      · exact min_le_right _ _
    calc wLoc p F ϖ hρ0 hρ1 x'
        = (ρ⁻¹) ^ n * wLoc p F ϖ hρ0 hρ1 x := by
          rw [hx'def, Valuation.map_mul, Valuation.map_pow,
            wLoc_p_inv p F ϖ hρ0 hρ1]
      _ ≤ (ρ⁻¹) ^ n * (min ρ₁ ρ₂ ^ n * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :=
          mul_le_mul_of_nonneg_left hwx zero_le
      _ ≤ (ρ⁻¹) ^ n * (ρ ^ n * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ zero_le hmin n) zero_le) zero_le
      _ = (ρ⁻¹ * ρ) ^ n * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
          rw [mul_pow, mul_assoc]
      _ = perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
          rw [inv_mul_cancel₀ hρ0.ne', one_pow, one_mul]
  have hwI' : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x')
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
    rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK]
    exact max_le (hloc ρ₁ hρ₁0 hρ₁1 (Or.inl rfl)) (hloc ρ₂ hρ₂0 hρ₂1 (Or.inr rfl))
  exact ⟨x', mem_chartSubring_of_wI_le p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hexact1 hexact2 hwI', hxeq⟩


/-- **The reverse basis inclusion**: the `min(ρ₁,ρ₂)^n·|ϖ|^b`-ball of the chart
localization is contained in the `n`-th chart neighborhood of zero. -/
theorem ball_le_locNhd (a b n : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    {z : Localization.Away (chartS p F ϖ 1 b)}
    (hz : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (blocEquivAwayChartS p F ϖ b hb z))
      ≤ min ρ₁ ρ₂ ^ n * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    z ∈ locNhd (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) n := by
  obtain ⟨x', hx'S, hxeq⟩ := exists_p_pow_mul_mem_chartSubring p F ϖ
    (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
    a b n ha hb hexact1 hexact2 hz
  rw [← map_locSubring_chartData p F ϖ a b hb] at hx'S
  obtain ⟨y, hymem, hyeq⟩ := hx'S
  have hyeq' : blocEquivAwayChartS p F ϖ b hb y = x' := hyeq
  have hzeq : z = algebraMap (Ainf p F) (Localization.Away (chartS p F ϖ 1 b))
      ((p : Ainf p F) ^ n) * y := by
    refine (blocEquivAwayChartS p F ϖ b hb).injective ?_
    rw [map_mul, blocEquivAwayChartS_algebraMap, hyeq']
    exact hxeq
  have hpMem : algebraMapD (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)
      ⟨(p : Ainf p F), trivial⟩
      ∈ locIdeal (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) := by
    refine Ideal.mem_map_of_mem _ ?_
    show (⟨(p : Ainf p F), trivial⟩ : ↥(⊤ : Subring (Ainf p F))) ∈ (podAinf p F ϖ).I
    have hp : (p : Ainf p F) ∈ Iinf p F ϖ :=
      Ideal.subset_span (Set.mem_insert _ _)
    exact Ideal.mem_map_of_mem _ hp
  set w : ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)) :=
    algebraMapD (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)
        ⟨(p : Ainf p F), trivial⟩ ^ n
      * ⟨y, hymem⟩ with hwdef
  have hwmem : w ∈ locIdeal (podAinf p F ϖ) (chartT p F ϖ a b)
      (chartS p F ϖ 1 b) ^ n :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpMem n)
  refine ⟨w, hwmem, ?_⟩
  show (↑w : Localization.Away (chartS p F ϖ 1 b)) = z
  have hcoe : (↑w : Localization.Away (chartS p F ϖ 1 b))
      = (algebraMap (Ainf p F) (Localization.Away (chartS p F ϖ 1 b))
          (p : Ainf p F)) ^ n * y := rfl
  rw [hcoe, ← map_pow, ← hzeq]

end FarguesFontaine

end
