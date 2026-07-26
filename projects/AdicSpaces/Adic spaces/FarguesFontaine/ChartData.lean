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

end FarguesFontaine

end
