/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.WellQuasiOrder
import Mathlib.Data.DFinsupp.WellFounded

import «Adic spaces».FarguesFontaine.Euclidean
import «Adic spaces».RestrictedPowerSeries

/-!
# Gröbner data for restricted power series over `A^r` (Kedlaya §3)

Kedlaya (*Noetherian properties of Fargues–Fontaine curves*, §3) proves that `A^r`
is strongly noetherian via a Gröbner-basis argument on the Tate algebras
`A^r⟨T₁,…,Tₖ⟩` (Theorem 3.2, radius 1 in the campaign specialization AD-5). This
file builds the foundation layer: the bridge between the repo's topological
restricted-series predicate and coefficientwise value decay, the radius-1 Gauss
norm, and its attainment machinery.

## Main definitions/results

* `FarguesFontaine.isRestricted_iff_valued` : a multivariate power series over `A^r`
  is restricted iff for every `ε > 0` only finitely many coefficients have value
  above `ε`.
* `FarguesFontaine.leadIdxRPS`, `FarguesFontaine.leadCoeffRPS`, `FarguesFontaine.dIdx`,
  `FarguesFontaine.groebnerSet` : Kedlaya's Gröbner data (Definitions 3.4–3.7).
* `FarguesFontaine.approx_generation` : Lemma 3.8 (approximate ideal generation).
* `FarguesFontaine.ideal_eq_span_groebner` : Lemma 3.9 (the generators generate).
* `FarguesFontaine.isStronglyNoetherian_ArSub` : Theorem 3.2 — `A^r` is strongly
  noetherian.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Definition 3.1, Theorem 3.2, Definitions 3.4–3.7.
-/

open TopologicalRing ValuationSpectrum WittVector Filter

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- Closed value balls in `hatK` are neighborhoods of `0`. -/
theorem valued_ball_mem_nhds_zero {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {ε : NNReal} (hε : 0 < ε) :
    {z : hatK p F hρ0 hρ1 | Valued.v z ≤ ε} ∈ nhds (0 : hatK p F hρ0 hρ1) := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hρ1
  set z₀ : hatK p F hρ0 hρ1 := toHatK p F hρ0 hρ1 ((p : Ainf p F) ^ N) with hz₀
  have hvz₀ : Valued.v z₀ = ρ ^ N := by
    rw [hz₀, valued_toHatK]
    have h0 : gaussValue p F ρ ((p : Ainf p F) ^ N)
        = (gaussValue p F ρ (p : Ainf p F)) ^ N := map_pow (gaussVal p F hρ0 hρ1) _ N
    rw [h0]
    congr 1
    calc gaussValue p F ρ (p : Ainf p F)
        = gaussValue p F ρ ((p : Ainf p F) * 1) := by rw [mul_one]
      _ = ρ * gaussValue p F ρ 1 := gaussValue_p_mul p F hρ1.le 1
      _ = ρ := by rw [gaussValue_one p F hρ1.le, mul_one]
  have hvz₀ne : Valued.v z₀ ≠ 0 := by
    rw [hvz₀]
    exact (pow_pos hρ0 N).ne'
  have hrne : (Valued.v).restrict z₀ ≠ 0 := by
    refine fun h0 => hvz₀ne ?_
    rcases eq_or_ne (Valued.v z₀) 0 with h | h
    · exact h
    · exact absurd ((Valuation.restrict_pos_iff (v := (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal)) z₀).mpr (pos_iff_ne_zero.mpr h))
        (by rw [h0]; exact lt_irrefl 0)
  set γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)))ˣ := Units.mk0 _ hrne with hγ
  have hball : {z : hatK p F hρ0 hρ1 |
      (Valued.v).restrict (z - 0) < γ.1} ∈ nhds (0 : hatK p F hρ0 hρ1) := by
    rw [Valued.mem_nhds]
    exact ⟨γ, fun z hz => hz⟩
  refine Filter.mem_of_superset hball ?_
  intro z hz
  have hcast : (Units.mk0 ((Valued.v).restrict z₀) hrne).1
      = (Valued.v).restrict z₀ := rfl
  rw [Set.mem_setOf_eq, hγ, hcast, sub_zero] at hz
  have hlt : Valued.v z < Valued.v z₀ :=
    (Valuation.restrict_lt_iff (v := (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal))).mp hz
  rw [hvz₀] at hlt
  exact le_of_lt (lt_of_lt_of_le hlt hN.le)

/-- Every neighborhood of `0` in `hatK` contains a closed value ball. -/
theorem exists_valued_ball_subset {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {V : Set (hatK p F hρ0 hρ1)} (hV : V ∈ nhds (0 : hatK p F hρ0 hρ1)) :
    ∃ ε : NNReal, 0 < ε ∧ {z : hatK p F hρ0 hρ1 | Valued.v z ≤ ε} ⊆ V := by
  rw [Valued.mem_nhds] at hV
  obtain ⟨γ, hγ⟩ := hV
  have hγpos : (0 : NNReal) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine pos_iff_ne_zero.mpr fun h0 => ?_
    have hinj := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      (f := MonoidWithZeroHom.ofClass (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal))).injective
    have h00 : MonoidWithZeroHom.ValueGroup₀.embedding (0 :
        MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v :
          Valuation (hatK p F hρ0 hρ1) NNReal))) = 0 := map_zero _
    exact γ.ne_zero (hinj (h0.trans h00.symm))
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hγpos hρ1
  refine ⟨ρ ^ (N + 1), pow_pos hρ0 (N + 1), fun z hz => ?_⟩
  refine hγ ?_
  rw [Set.mem_setOf_eq, sub_zero]
  have hlt : Valued.v z < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine lt_of_le_of_lt hz (lt_of_lt_of_le ?_ hN.le)
    exact pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 (Nat.lt_succ_self N)
  have hsm := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
    (f := MonoidWithZeroHom.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal))
  refine hsm.lt_iff_lt.mp ?_
  rw [Valuation.embedding_restrict]
  exact hlt

/-- **The restricted-series bridge**: over the subring `A^r`, the repo's topological
restrictedness is exactly coefficientwise value decay. -/
theorem isRestricted_iff_valued {k : ℕ} {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :
    MvPowerSeries.IsRestricted f
      ↔ ∀ ε : NNReal, 0 < ε → {s : Fin k →₀ ℕ |
          ε < Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1)}.Finite := by
  constructor
  · intro hf ε hε
    have hB : {a : ↥(ArSub p F ϖ hρ0 hρ1) |
        Valued.v (a : hatK p F hρ0 hρ1) ≤ ε} ∈ nhds (0 : ↥(ArSub p F ϖ hρ0 hρ1)) := by
      rw [nhds_subtype_eq_comap]
      refine Filter.mem_comap.mpr ⟨{z : hatK p F hρ0 hρ1 | Valued.v z ≤ ε}, ?_, ?_⟩
      · exact valued_ball_mem_nhds_zero p F (hρ0 := hρ0) (hρ1 := hρ1) hε
      · intro a ha
        exact ha
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
    obtain ⟨ε, hε, hεV⟩ := exists_valued_ball_subset p F
      (hρ0 := hρ0) (hρ1 := hρ1) hV
    rw [Filter.mem_cofinite]
    refine ((hf ε hε).subset ?_)
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq] at hs ⊢
    by_contra hcon
    push Not at hcon
    exact hs (hVU (hεV hcon))

/-- Attainment for `NNReal` families with finitely many terms above every positive
threshold (the index-free generalization of the sequence attainment lemma). -/
theorem exists_iSup_eq_of_finite_above {ι : Type*} [Nonempty ι] {g : ι → NNReal}
    (hfin : ∀ ε : NNReal, 0 < ε → {i | ε < g i}.Finite)
    (hne : (⨆ i, g i) ≠ 0) :
    ∃ i₀, (⨆ i, g i) = g i₀ ∧ ∀ i, g i ≤ g i₀ := by
  have hB : BddAbove (Set.range g) := by
    refine ⟨max 1 (((hfin 1 one_pos).toFinset).sup g), ?_⟩
    rintro t ⟨i, rfl⟩
    rcases le_or_gt (g i) 1 with h1 | h1
    · exact le_max_of_le_left h1
    · refine le_max_of_le_right (Finset.le_sup ?_)
      rw [Set.Finite.mem_toFinset]
      exact h1
  have hpos : 0 < ⨆ i, g i := pos_iff_ne_zero.mpr hne
  obtain ⟨b, hb0, hbs⟩ := exists_between hpos
  have hSne : {i | b < g i}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hall : ∀ i, g i ≤ b := by
      intro i
      by_contra hcon2
      push Not at hcon2
      have h2 : i ∈ {i | b < g i} := hcon2
      rw [hcon] at h2
      exact h2
    exact absurd (lt_of_le_of_lt (ciSup_le hall) hbs) (lt_irrefl _)
  have hfinb := hfin b hb0
  set Sfin := hfinb.toFinset with hSfin
  have hSfinne : Sfin.Nonempty := by
    obtain ⟨i, hi⟩ := hSne
    exact ⟨i, by rw [hSfin, Set.Finite.mem_toFinset]; exact hi⟩
  obtain ⟨i₀, hi₀mem, hi₀⟩ := Finset.exists_mem_eq_sup Sfin hSfinne g
  have hdom : ∀ i, g i ≤ g i₀ := by
    intro i
    rcases le_or_gt (g i) b with h1 | h1
    · refine le_trans h1 ?_
      have hi₀b : b < g i₀ := by
        rw [hSfin, Set.Finite.mem_toFinset] at hi₀mem
        exact hi₀mem
      exact hi₀b.le
    · have himem : i ∈ Sfin := by
        rw [hSfin, Set.Finite.mem_toFinset]
        exact h1
      have := Finset.le_sup (f := g) himem
      rw [← hi₀]
      exact this
  exact ⟨i₀, le_antisymm (ciSup_le hdom) (le_ciSup hB i₀), hdom⟩

variable {k : ℕ}

/-- **The radius-1 Gauss norm** on multivariate power series over `A^r`
(Kedlaya (3.1.1) with all `ρᵢ = 1`). -/
def gaussNormRPS {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : NNReal :=
  ⨆ s : Fin k →₀ ℕ, Valued.v ((MvPowerSeries.coeff s f :
    ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)

/-- Restricted series have attained Gauss norm (at some coefficient), provided they
are nonzero. -/
theorem exists_gaussNormRPS_eq {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) :
    ∃ s₀ : Fin k →₀ ℕ, gaussNormRPS p F ϖ hρ0 hρ1 f
        = Valued.v ((MvPowerSeries.coeff s₀ f : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
      ∧ ∀ s, Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        ≤ Valued.v ((MvPowerSeries.coeff s₀ f : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) := by
  have hfin := (isRestricted_iff_valued p F ϖ f).mp hf
  have hne : gaussNormRPS p F ϖ hρ0 hρ1 f ≠ 0 := by
    intro h0
    refine hf0 (MvPowerSeries.ext fun s => ?_)
    have h1 : Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) = 0 := by
      have hB : BddAbove (Set.range (fun s : Fin k →₀ ℕ =>
          Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1))) := by
        refine ⟨max 1 (((hfin 1 one_pos).toFinset).sup (fun s =>
          Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1))), ?_⟩
        rintro t ⟨s, rfl⟩
        rcases le_or_gt (Valued.v ((MvPowerSeries.coeff s f :
            ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) 1 with h1 | h1
        · exact le_max_of_le_left h1
        · refine le_max_of_le_right (Finset.le_sup
            (f := fun s => Valued.v ((MvPowerSeries.coeff s f :
              ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) ?_)
          rw [Set.Finite.mem_toFinset]
          exact h1
      have h2 := le_ciSup hB s
      rw [show (⨆ s : Fin k →₀ ℕ, Valued.v ((MvPowerSeries.coeff s f :
          ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1))
        = gaussNormRPS p F ϖ hρ0 hρ1 f from rfl, h0] at h2
      exact le_antisymm h2 zero_le
    have h3 : ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) = 0 :=
      (Valuation.zero_iff (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal)).mp h1
    rw [map_zero]
    exact Subtype.ext h3
  obtain ⟨s₀, hs₀, hdom⟩ := exists_iSup_eq_of_finite_above hfin hne
  exact ⟨s₀, hs₀, hdom⟩

/-- Nonzero restricted series have nonzero Gauss norm. -/
theorem gaussNormRPS_ne_zero {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) :
    gaussNormRPS p F ϖ hρ0 hρ1 f ≠ 0 := by
  intro h0
  refine hf0 (MvPowerSeries.ext fun s => ?_)
  have hfin := (isRestricted_iff_valued p F ϖ f).mp hf
  have hB : BddAbove (Set.range (fun s : Fin k →₀ ℕ =>
      Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1))) := by
    refine ⟨max 1 (((hfin 1 one_pos).toFinset).sup (fun s =>
      Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1))), ?_⟩
    rintro t ⟨s, rfl⟩
    rcases le_or_gt (Valued.v ((MvPowerSeries.coeff s f :
        ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) 1 with h1 | h1
    · exact le_max_of_le_left h1
    · refine le_max_of_le_right (Finset.le_sup
        (f := fun s => Valued.v ((MvPowerSeries.coeff s f :
          ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) ?_)
      rw [Set.Finite.mem_toFinset]
      exact h1
  have h2 := le_ciSup hB s
  rw [show (⨆ s : Fin k →₀ ℕ, Valued.v ((MvPowerSeries.coeff s f :
      ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1))
    = gaussNormRPS p F ϖ hρ0 hρ1 f from rfl, h0] at h2
  have h3 : ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1) = 0 :=
    (Valuation.zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp (le_antisymm h2 zero_le)
  rw [map_zero]
  exact Subtype.ext h3

/-- **The attainment set** of a series: the multi-indices realizing the Gauss norm. -/
def attainSetRPS {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : Set (Fin k →₀ ℕ) :=
  {s | Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
    : hatK p F hρ0 hρ1) = gaussNormRPS p F ϖ hρ0 hρ1 f}

theorem attainSetRPS_finite {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) :
    (attainSetRPS p F ϖ hρ0 hρ1 f).Finite := by
  have hne := gaussNormRPS_ne_zero p F ϖ hf hf0
  have hfin := (isRestricted_iff_valued p F ϖ f).mp hf
  refine (hfin (gaussNormRPS p F ϖ hρ0 hρ1 f / 2)
    (div_pos (pos_iff_ne_zero.mpr hne) two_pos)).subset ?_
  intro s hs
  rw [attainSetRPS, Set.mem_setOf_eq] at hs
  rw [Set.mem_setOf_eq, hs]
  exact NNReal.half_lt_self hne

theorem attainSetRPS_nonempty {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) :
    (attainSetRPS p F ϖ hρ0 hρ1 f).Nonempty := by
  obtain ⟨s₀, hs₀, -⟩ := exists_gaussNormRPS_eq p F ϖ hf hf0
  exact ⟨s₀, hs₀.symm⟩

open scoped Classical in
/-- **The leading index** (Kedlaya Definition 3.6): the graded-lex-maximal
norm-attaining multi-index (junk `0` off the restricted-nonzero locus). -/
noncomputable def leadIdxRPS {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : Fin k →₀ ℕ :=
  if h : MvPowerSeries.IsRestricted f ∧ f ≠ 0 then
    (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn.symm
      ((((attainSetRPS_finite p F ϖ h.1 h.2).toFinset).image
        (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn).max'
        (by
          refine Finset.Nonempty.image ?_ _
          rw [Set.Finite.toFinset_nonempty]
          exact attainSetRPS_nonempty p F ϖ h.1 h.2))
  else 0

/-- The leading index attains the norm and degLex-dominates all attaining indices. -/
theorem leadIdxRPS_spec {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) :
    leadIdxRPS p F ϖ hρ0 hρ1 f ∈ attainSetRPS p F ϖ hρ0 hρ1 f
      ∧ ∀ s ∈ attainSetRPS p F ϖ hρ0 hρ1 f,
        (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn s
          ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
            (leadIdxRPS p F ϖ hρ0 hρ1 f) := by
  classical
  rw [leadIdxRPS, dif_pos ⟨hf, hf0⟩]
  set m : MonomialOrder (Fin k) := MonomialOrder.degLex with hm
  set At := (attainSetRPS_finite p F ϖ hf hf0).toFinset with hAt
  have hAtne : At.Nonempty := by
    rw [hAt, Set.Finite.toFinset_nonempty]
    exact attainSetRPS_nonempty p F ϖ hf hf0
  set M := ((At.image m.toSyn).max' (hAtne.image _)) with hM
  constructor
  · have hmem : M ∈ At.image m.toSyn := Finset.max'_mem _ _
    obtain ⟨s₁, hs₁mem, hs₁eq⟩ := Finset.mem_image.mp hmem
    have h1 : m.toSyn.symm M = s₁ := by
      rw [← hs₁eq]
      exact m.toSyn.symm_apply_apply s₁
    rw [h1]
    rw [hAt, Set.Finite.mem_toFinset] at hs₁mem
    exact hs₁mem
  · intro s hs
    have hsmem : s ∈ At := by
      rw [hAt, Set.Finite.mem_toFinset]
      exact hs
    have h2 : m.toSyn s ≤ M :=
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ hsmem)
    rw [m.toSyn.apply_symm_apply]
    exact h2

/-- **The leading coefficient** (Kedlaya Definition 3.6). -/
noncomputable def leadCoeffRPS {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1) :=
  MvPowerSeries.coeff (leadIdxRPS p F ϖ hρ0 hρ1 f) f

/-- Bounded coefficient values for restricted series (the recurring bound). -/
theorem bddAbove_coeff_valued {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) :
    BddAbove (Set.range (fun s : Fin k →₀ ℕ =>
      Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1))) := by
  have hfin := (isRestricted_iff_valued p F ϖ f).mp hf
  refine ⟨max 1 (((hfin 1 one_pos).toFinset).sup (fun s =>
    Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1))), ?_⟩
  rintro t ⟨s, rfl⟩
  rcases le_or_gt (Valued.v ((MvPowerSeries.coeff s f :
      ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) 1 with h1 | h1
  · exact le_max_of_le_left h1
  · refine le_max_of_le_right (Finset.le_sup
      (f := fun s => Valued.v ((MvPowerSeries.coeff s f :
        ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) ?_)
    rw [Set.Finite.mem_toFinset]
    exact h1

/-- Monomials are restricted. -/
theorem isRestricted_monomial {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {J : Fin k →₀ ℕ} (a : ↥(ArSub p F ϖ hρ0 hρ1)) :
    MvPowerSeries.IsRestricted
      (MvPowerSeries.monomial J a : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := by
  rw [MvPowerSeries.IsRestricted, Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_cofinite]
  refine (Set.finite_singleton J).subset ?_
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  by_contra hne
  refine hs ?_
  rw [MvPowerSeries.coeff_monomial, if_neg (by
    intro h
    exact hne (by rw [h]; exact Set.mem_singleton J))]
  exact mem_of_mem_nhds hU

/-- The valued field `hatK` is nonarchimedean: value balls are open subgroups. -/
instance {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} :
    NonarchimedeanRing (hatK p F hρ0 hρ1) where
  is_nonarchimedean := by
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    set B : AddSubgroup (hatK p F hρ0 hρ1) :=
      { carrier := {z | (Valued.v).restrict z < γ.1}
        zero_mem' := by
          simp only [Set.mem_setOf_eq, map_zero]
          exact Units.zero_lt γ
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          exact lt_of_le_of_lt (Valuation.map_add _ a b) (max_lt ha hb)
        neg_mem' := fun {a} ha => by
          simpa only [Set.mem_setOf_eq, Valuation.map_neg] using ha } with hB
    have hBnhds : (B : Set (hatK p F hρ0 hρ1)) ∈ nhds (0 : hatK p F hρ0 hρ1) := by
      rw [Valued.mem_nhds]
      refine ⟨γ, fun z hz => ?_⟩
      rw [Set.mem_setOf_eq, sub_zero] at hz
      exact hz
    refine ⟨⟨B, AddSubgroup.isOpen_of_mem_nhds B hBnhds⟩, fun z hz => ?_⟩
    refine hγ ?_
    rw [Set.mem_setOf_eq, sub_zero]
    exact hz

/-- Subrings of nonarchimedean rings are nonarchimedean (pull the open subgroup
back along the inclusion). -/
instance {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} :
    NonarchimedeanRing ↥(ArSub p F ϖ hρ0 hρ1) where
  is_nonarchimedean := by
    intro U hU
    rw [nhds_subtype_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    obtain ⟨W, hW⟩ := NonarchimedeanRing.is_nonarchimedean V hV
    refine ⟨⟨W.1.comap ((ArSub p F ϖ hρ0 hρ1).subtype.toAddMonoidHom), ?_⟩,
      fun z hz => ?_⟩
    · exact W.isOpen.preimage continuous_subtype_val
    · exact hVU (hW hz)

/-- Coefficients of a monomial shift. -/
theorem coeff_monomialShift {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (J : Fin k →₀ ℕ) (f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
    (s : Fin k →₀ ℕ) :
    MvPowerSeries.coeff s
        ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f)
      = if J ≤ s then MvPowerSeries.coeff (s - J) f else 0 := by
  rw [MvPowerSeries.coeff_monomial_mul]
  split_ifs with h
  · rw [one_mul]
  · rfl

/-- Monomial shifts are restricted. -/
theorem isRestricted_monomialShift {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (J : Fin k →₀ ℕ) :
    MvPowerSeries.IsRestricted
      ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f) :=
  Subring.mul_mem (restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))
    (isRestricted_monomial p F ϖ (1 : ↥(ArSub p F ϖ hρ0 hρ1)) (J := J)) hf

/-- **Norm invariance of monomial shifts** (radius 1). -/
theorem gaussNormRPS_monomialShift {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (J : Fin k →₀ ℕ) :
    gaussNormRPS p F ϖ hρ0 hρ1
        ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f)
      = gaussNormRPS p F ϖ hρ0 hρ1 f := by
  have hprod := isRestricted_monomialShift p F ϖ hf J
  refine le_antisymm (ciSup_le fun s => ?_) (ciSup_le fun s => ?_)
  · rw [coeff_monomialShift]
    split_ifs with h
    · exact le_ciSup (bddAbove_coeff_valued p F ϖ hf) (s - J)
    · rw [ZeroMemClass.coe_zero, Valuation.map_zero]
      exact zero_le
  · have h1 : MvPowerSeries.coeff (s + J)
        ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f)
        = MvPowerSeries.coeff s f := by
      rw [coeff_monomialShift, if_pos le_add_self, add_tsub_cancel_right]
    calc Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        = Valued.v ((MvPowerSeries.coeff (s + J)
            ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f) :
            ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by rw [h1]
      _ ≤ _ := le_ciSup (bddAbove_coeff_valued p F ϖ hprod) (s + J)

/-- Monomial shifts of nonzero series are nonzero. -/
theorem monomialShift_ne_zero {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)} (hf0 : f ≠ 0)
    (J : Fin k →₀ ℕ) :
    (MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f ≠ 0 := by
  intro h0
  refine hf0 (MvPowerSeries.ext fun t => ?_)
  have h1 : MvPowerSeries.coeff (t + J)
      ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f)
      = MvPowerSeries.coeff t f := by
    rw [coeff_monomialShift, if_pos le_add_self, add_tsub_cancel_right]
  rw [h0, map_zero] at h1
  rw [map_zero, ← h1]

/-- **Attainment sets shift**: the attainers of a monomial shift are the translates. -/
theorem attainSetRPS_monomialShift {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) (J : Fin k →₀ ℕ) :
    attainSetRPS p F ϖ hρ0 hρ1
        ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f)
      = (fun t => J + t) '' attainSetRPS p F ϖ hρ0 hρ1 f := by
  have hnorm := gaussNormRPS_monomialShift p F ϖ hf J
  have hnne := gaussNormRPS_ne_zero p F ϖ hf hf0
  ext s
  simp only [attainSetRPS, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hs
    rw [coeff_monomialShift, hnorm] at hs
    by_cases hJs : J ≤ s
    · rw [if_pos hJs] at hs
      refine ⟨s - J, hs, ?_⟩
      rw [add_tsub_cancel_of_le hJs]
    · rw [if_neg hJs] at hs
      rw [ZeroMemClass.coe_zero, Valuation.map_zero] at hs
      exact absurd hs.symm hnne
  · rintro ⟨t, ht, rfl⟩
    rw [coeff_monomialShift, hnorm, if_pos le_self_add, add_tsub_cancel_left]
    exact ht

/-- **The leading index shifts additively** (Kedlaya's monomial multiplication). -/
theorem leadIdxRPS_monomialShift {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) (J : Fin k →₀ ℕ) :
    leadIdxRPS p F ϖ hρ0 hρ1
        ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f)
      = J + leadIdxRPS p F ϖ hρ0 hρ1 f := by
  set m : MonomialOrder (Fin k) := MonomialOrder.degLex with hm
  have hprod := isRestricted_monomialShift p F ϖ hf J
  have hprod0 := monomialShift_ne_zero p F ϖ hf0 J
  obtain ⟨hmemS, hdomS⟩ := leadIdxRPS_spec p F ϖ hprod hprod0
  obtain ⟨hmemf, hdomf⟩ := leadIdxRPS_spec p F ϖ hf hf0
  have hshift := attainSetRPS_monomialShift p F ϖ hf hf0 J
  -- the shifted leading index is an attainer of the shift
  have hJlead : J + leadIdxRPS p F ϖ hρ0 hρ1 f ∈ attainSetRPS p F ϖ hρ0 hρ1
      ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f) := by
    rw [hshift]
    exact ⟨leadIdxRPS p F ϖ hρ0 hρ1 f, hmemf, rfl⟩
  -- compare through the linear syn order and pull back by injectivity
  refine m.toSyn.injective (le_antisymm ?_ ?_)
  · have h1 := (subset_of_eq hshift) hmemS
    obtain ⟨t, ht, heq⟩ := h1
    rw [← heq]
    have h2 : m.toSyn t ≤ m.toSyn (leadIdxRPS p F ϖ hρ0 hρ1 f) := hdomf t ht
    have h3 := add_le_add_left h2 (m.toSyn J)
    rw [← map_add, ← map_add] at h3
    show m.toSyn (J + t) ≤ m.toSyn (J + leadIdxRPS p F ϖ hρ0 hρ1 f)
    rw [add_comm J t, add_comm J (leadIdxRPS p F ϖ hρ0 hρ1 f)]
    exact h3
  · exact hdomS _ hJlead

/-- **The leading coefficient is invariant under monomial shifts**. -/
theorem leadCoeffRPS_monomialShift {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) (J : Fin k →₀ ℕ) :
    leadCoeffRPS p F ϖ hρ0 hρ1
        ((MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1))) * f)
      = leadCoeffRPS p F ϖ hρ0 hρ1 f := by
  rw [leadCoeffRPS, leadCoeffRPS, leadIdxRPS_monomialShift p F ϖ hf hf0 J,
    coeff_monomialShift, if_pos le_self_add, add_tsub_cancel_left]

/-- **The degree data** `d_I` of Kedlaya Definition 3.7: the degrees of leading
coefficients of ideal elements with leading index `I`. -/
def degSetIdx {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
    (I : Fin k →₀ ℕ) : Set ℕ :=
  {d | ∃ x : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)),
    x ∈ H ∧ (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0
      ∧ leadIdxRPS p F ϖ hρ0 hρ1 (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        = I
      ∧ degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) = d}

/-- **Monotonicity of `d_I`** (Kedlaya Definition 3.7): a larger index realizes at
least the same degrees — multiply by the intervening monomial. -/
theorem degSetIdx_subset {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {I₁ I₂ : Fin k →₀ ℕ} (hI : I₁ ≤ I₂) :
    degSetIdx p F ϖ hρ0 hρ1 H I₁ ⊆ degSetIdx p F ϖ hρ0 hρ1 H I₂ := by
  rintro d ⟨x, hxH, hx0, hxlead, hxdeg⟩
  set J : Fin k →₀ ℕ := I₂ - I₁ with hJ
  set mono : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) :=
    ⟨MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1)),
      isRestricted_monomial p F ϖ (1 : ↥(ArSub p F ϖ hρ0 hρ1)) (J := J)⟩ with hmono
  have hxres : MvPowerSeries.IsRestricted
      (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := x.2
  have hcoe : ((mono * x : ↥(restrictedMvPowerSeriesSubring k
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
      = (MvPowerSeries.monomial J (1 : ↥(ArSub p F ϖ hρ0 hρ1)))
        * (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := rfl
  refine ⟨mono * x, Ideal.mul_mem_left H mono hxH, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact monomialShift_ne_zero p F ϖ hx0 J
  · rw [hcoe, leadIdxRPS_monomialShift p F ϖ hxres hx0 J, hxlead, hJ,
      tsub_add_cancel_of_le hI]
  · rw [hcoe, leadCoeffRPS_monomialShift p F ϖ hxres hx0 J]
    exact hxdeg

/-- The `d_I`-value: the smallest degree of a leading coefficient at index `I`
(`⊤` when no ideal element has that leading index). -/
def dIdx {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
    (I : Fin k →₀ ℕ) : ℕ∞ :=
  sInf ((fun d : ℕ => (d : ℕ∞)) '' degSetIdx p F ϖ hρ0 hρ1 H I)

/-- **`d_I` is antitone** (Kedlaya Definition 3.7). -/
theorem dIdx_antitone {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {I₁ I₂ : Fin k →₀ ℕ} (hI : I₁ ≤ I₂) :
    dIdx p F ϖ hρ0 hρ1 H I₂ ≤ dIdx p F ϖ hρ0 hρ1 H I₁ :=
  sInf_le_sInf (Set.image_mono (degSetIdx_subset p F ϖ hI))

/-- **Dickson, minimal-element form**: a well-quasi-ordered set has finitely many
minimal elements. -/
theorem finite_minimal {α : Type*} [PartialOrder α] [WellQuasiOrderedLE α]
    (T : Set α) : {I | I ∈ T ∧ ∀ I' ∈ T, I' ≤ I → I = I'}.Finite := by
  refine WellQuasiOrderedLE.finite_of_isAntichain ?_
  intro a ha b hb hab hle
  exact hab (hb.2 a ha.1 hle).symm

/-- Every element of a well-quasi-ordered set dominates a minimal element. -/
theorem exists_minimal_le {α : Type*} [PartialOrder α] [WellQuasiOrderedLE α]
    {T : Set α} {J : α} (hJ : J ∈ T) :
    ∃ I, (I ∈ T ∧ ∀ I' ∈ T, I' ≤ I → I = I') ∧ I ≤ J := by
  obtain ⟨I, ⟨hIT, hIJ⟩, hmin⟩ :=
    wellFounded_lt.has_min {I | I ∈ T ∧ I ≤ J} ⟨J, hJ, le_rfl⟩
  refine ⟨I, ⟨hIT, fun I' hI' hle => ?_⟩, hIJ⟩
  by_contra hne
  exact hmin I' ⟨hI', le_trans hle hIJ⟩ (lt_of_le_of_ne hle (Ne.symm hne))

/-- The index/degree pairs realized by an ideal (the graph of `d_I` as an up-set). -/
def groebnerPairs {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    Set ((Fin k →₀ ℕ) × ℕ) :=
  {q | dIdx p F ϖ hρ0 hρ1 H q.1 ≤ (q.2 : ℕ∞)}

/-- **The Gröbner index set `S`** (Kedlaya Definition 3.7): the first coordinates of
the minimal index/degree pairs. -/
def groebnerSet {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    Set (Fin k →₀ ℕ) :=
  Prod.fst '' {q | q ∈ groebnerPairs p F ϖ hρ0 hρ1 H
    ∧ ∀ q' ∈ groebnerPairs p F ϖ hρ0 hρ1 H, q' ≤ q → q = q'}

/-- **`S` is finite** (Dickson's lemma). -/
theorem groebnerSet_finite {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    (groebnerSet p F ϖ hρ0 hρ1 H).Finite :=
  Set.Finite.image _ (finite_minimal (groebnerPairs p F ϖ hρ0 hρ1 H))

/-- **`S` dominates from below at equal degree** (the property Kedlaya's Lemma 3.8
consumes): every realized leading index has an element of `S` beneath it with the
same degree datum. -/
theorem exists_mem_groebnerSet_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {J : Fin k →₀ ℕ} (hJ : dIdx p F ϖ hρ0 hρ1 H J ≠ ⊤) :
    ∃ I ∈ groebnerSet p F ϖ hρ0 hρ1 H, I ≤ J
      ∧ dIdx p F ϖ hρ0 hρ1 H I = dIdx p F ϖ hρ0 hρ1 H J := by
  set d : ℕ := (dIdx p F ϖ hρ0 hρ1 H J).untop hJ with hd
  have hdcoe : ((d : ℕ∞)) = dIdx p F ϖ hρ0 hρ1 H J := by
    rw [hd]
    exact_mod_cast WithTop.coe_untop _ hJ
  have hmem : (J, d) ∈ groebnerPairs p F ϖ hρ0 hρ1 H := by
    rw [groebnerPairs, Set.mem_setOf_eq, hdcoe]
  obtain ⟨⟨I, e⟩, hqmin, hqle⟩ := exists_minimal_le hmem
  obtain ⟨hIJ, hed⟩ := Prod.mk_le_mk.mp hqle
  have hIe : dIdx p F ϖ hρ0 hρ1 H I ≤ (e : ℕ∞) := hqmin.1
  refine ⟨I, ⟨(I, e), hqmin, rfl⟩, hIJ, le_antisymm ?_ ?_⟩
  · calc dIdx p F ϖ hρ0 hρ1 H I ≤ (e : ℕ∞) := hIe
      _ ≤ (d : ℕ∞) := by exact_mod_cast hed
      _ = dIdx p F ϖ hρ0 hρ1 H J := hdcoe
  · exact dIdx_antitone p F ϖ hIJ

/-- `d_I` is a lower bound for the leading-coefficient degrees at index `I`. -/
theorem dIdx_le_of_mem {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {x : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    (hxH : x ∈ H) (hx0 : (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0)
    {I : Fin k →₀ ℕ}
    (hxlead : leadIdxRPS p F ϖ hρ0 hρ1
      (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = I) :
    dIdx p F ϖ hρ0 hρ1 H I
      ≤ ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)) :=
  sInf_le ⟨_, ⟨x, hxH, hx0, hxlead, rfl⟩, rfl⟩

/-- A finite `d_I` is realized by an ideal element. -/
theorem degSetIdx_nonempty {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {I : Fin k →₀ ℕ} (hI : dIdx p F ϖ hρ0 hρ1 H I ≠ ⊤) :
    (degSetIdx p F ϖ hρ0 hρ1 H I).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  refine hI ?_
  rw [dIdx, hemp, Set.image_empty, sInf_empty]

/-- **The Gröbner generators** (Kedlaya Definition 3.7): for every index with finite
degree datum there is an ideal element with that leading index whose leading
coefficient realizes `d_I` exactly. -/
theorem exists_leadIdx_degAr_eq {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {I : Fin k →₀ ℕ} (hI : dIdx p F ϖ hρ0 hρ1 H I ≠ ⊤) :
    ∃ x : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)),
      x ∈ H ∧ (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0
        ∧ leadIdxRPS p F ϖ hρ0 hρ1
            (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = I
        ∧ ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
            (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞))
          = dIdx p F ϖ hρ0 hρ1 H I := by
  have hne := degSetIdx_nonempty p F ϖ hI
  obtain ⟨x, hxH, hx0, hxlead, hxdeg⟩ := Nat.sInf_mem hne
  refine ⟨x, hxH, hx0, hxlead, le_antisymm ?_ ?_⟩
  · rw [hxdeg, dIdx]
    refine le_sInf ?_
    rintro y ⟨d, hd, rfl⟩
    show ((sInf (degSetIdx p F ϖ hρ0 hρ1 H I) : ℕ) : ℕ∞) ≤ ((d : ℕ) : ℕ∞)
    exact_mod_cast Nat.sInf_le hd
  · exact dIdx_le_of_mem p F ϖ hxH hx0 hxlead

/-- Every coefficient value is at most the Gauss norm. -/
theorem valued_coeff_le_gaussNormRPS {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (s : Fin k →₀ ℕ) :
    Valued.v ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1) ≤ gaussNormRPS p F ϖ hρ0 hρ1 f :=
  le_ciSup (bddAbove_coeff_valued p F ϖ hf) s

open scoped Classical in
/-- **The strict tail bound** (the source of Kedlaya's `ε` in Lemma 3.8): past the
leading index, coefficient values are uniformly below the Gauss norm. -/
theorem exists_tail_bound_lt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) :
    ∃ ε : NNReal, ε < gaussNormRPS p F ϖ hρ0 hρ1 f
      ∧ ∀ J : Fin k →₀ ℕ,
        (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
            (leadIdxRPS p F ϖ hρ0 hρ1 f)
          < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J →
        Valued.v ((MvPowerSeries.coeff J f : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) ≤ ε := by
  set m : MonomialOrder (Fin k) := MonomialOrder.degLex with hm
  set A := gaussNormRPS p F ϖ hρ0 hρ1 f with hA
  have hA0 : 0 < A := pos_iff_ne_zero.mpr (gaussNormRPS_ne_zero p F ϖ hf hf0)
  obtain ⟨-, hdom⟩ := leadIdxRPS_spec p F ϖ hf hf0
  obtain ⟨b, hb0, hbA⟩ := exists_between hA0
  have hfin := (isRestricted_iff_valued p F ϖ f).mp hf b hb0
  set G : Finset (Fin k →₀ ℕ) := hfin.toFinset.filter
    (fun J => m.toSyn (leadIdxRPS p F ϖ hρ0 hρ1 f) < m.toSyn J) with hG
  set ε : NNReal := max b (G.sup (fun J =>
    Valued.v ((MvPowerSeries.coeff J f : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1))) with hε
  have hstrict : ∀ J : Fin k →₀ ℕ,
      m.toSyn (leadIdxRPS p F ϖ hρ0 hρ1 f) < m.toSyn J →
      Valued.v ((MvPowerSeries.coeff J f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) < A := by
    intro J hJ
    rcases lt_or_eq_of_le (valued_coeff_le_gaussNormRPS p F ϖ hf J) with h | h
    · exact h
    · exact absurd (hdom J h) (not_le.mpr hJ)
  refine ⟨ε, ?_, fun J hJ => ?_⟩
  · refine max_lt hbA ?_
    rcases Finset.eq_empty_or_nonempty G with hemp | hne
    · rw [hemp, Finset.sup_empty, bot_eq_zero]
      exact hA0
    · refine (Finset.sup_lt_iff (by rw [bot_eq_zero]; exact hA0)).mpr fun J hJG => ?_
      exact hstrict J (Finset.mem_filter.mp hJG).2
  · rcases le_or_gt (Valued.v ((MvPowerSeries.coeff J f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)) b with hle | hgt
    · exact le_max_of_le_left hle
    · refine le_max_of_le_right (Finset.le_sup
        (f := fun J => Valued.v ((MvPowerSeries.coeff J f
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) ?_)
      rw [hG, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hgt, hJ⟩

/-- The Gauss norm is the value of the leading coefficient. -/
theorem valued_leadCoeffRPS {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hf0 : f ≠ 0) :
    Valued.v ((leadCoeffRPS p F ϖ hρ0 hρ1 f : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1) = gaussNormRPS p F ϖ hρ0 hρ1 f :=
  (leadIdxRPS_spec p F ϖ hf hf0).1

/-- Monomials of bounded total degree form a finite set. -/
theorem finite_degree_le (D : ℕ) :
    {J : Fin k →₀ ℕ | Finsupp.degree J ≤ D}.Finite := by
  refine Set.Finite.of_finite_image (f := Finsupp.equivFunOnFinite) ?_
    (Finsupp.equivFunOnFinite.injective.injOn)
  refine Set.Finite.subset (Set.Finite.pi (fun _ : Fin k => Set.finite_Iic D)) ?_
  rintro g ⟨J, hJ, rfl⟩
  intro i _
  have h1 : J i ≤ Finsupp.degree J := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (f := fun i => J i) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  exact le_trans h1 hJ

/-- **Graded-lex lower sets are finite** (Kedlaya Remark 3.5). -/
theorem finite_degLex_le (Jtop : Fin k →₀ ℕ) :
    {J : Fin k →₀ ℕ | (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
      ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn Jtop}.Finite := by
  refine Set.Finite.subset (finite_degree_le (Finsupp.degree Jtop)) ?_
  intro J hJ
  rw [Set.mem_setOf_eq, MonomialOrder.degLex_le_iff, Finsupp.DegLex.le_iff] at hJ
  rcases hJ with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- The Gauss norm is ultrametric on sums. -/
theorem gaussNormRPS_add_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hg : MvPowerSeries.IsRestricted g) :
    gaussNormRPS p F ϖ hρ0 hρ1 (f + g)
      ≤ max (gaussNormRPS p F ϖ hρ0 hρ1 f) (gaussNormRPS p F ϖ hρ0 hρ1 g) := by
  refine ciSup_le fun s => ?_
  have hc : ((MvPowerSeries.coeff s (f + g) : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1)
      = ((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        + ((MvPowerSeries.coeff s g : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) := by
    rw [map_add, AddMemClass.coe_add]
  rw [hc]
  exact le_trans (Valuation.map_add _ _ _)
    (max_le_max (valued_coeff_le_gaussNormRPS p F ϖ hf s)
      (valued_coeff_le_gaussNormRPS p F ϖ hg s))

/-- The Gauss norm of a negation. -/
theorem gaussNormRPS_neg {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :
    gaussNormRPS p F ϖ hρ0 hρ1 (-f) = gaussNormRPS p F ϖ hρ0 hρ1 f := by
  rw [gaussNormRPS, gaussNormRPS]
  refine iSup_congr fun s => ?_
  have hc : ((MvPowerSeries.coeff s (-f) : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1)
      = -((MvPowerSeries.coeff s f : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) := by
    rw [map_neg, NegMemClass.coe_neg]
  rw [hc, Valuation.map_neg]

/-- The Gauss norm is ultrametric on differences. -/
theorem gaussNormRPS_sub_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hg : MvPowerSeries.IsRestricted g) :
    gaussNormRPS p F ϖ hρ0 hρ1 (f - g)
      ≤ max (gaussNormRPS p F ϖ hρ0 hρ1 f) (gaussNormRPS p F ϖ hρ0 hρ1 g) := by
  have hneg : MvPowerSeries.IsRestricted (-g) :=
    Subring.neg_mem (restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) hg
  have h1 := gaussNormRPS_add_le p F ϖ hf hneg
  rw [← sub_eq_add_neg, gaussNormRPS_neg] at h1
  exact h1

/-- The Gauss norm of a monomial. -/
theorem gaussNormRPS_monomial {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (J : Fin k →₀ ℕ) (a : ↥(ArSub p F ϖ hρ0 hρ1)) :
    gaussNormRPS p F ϖ hρ0 hρ1 (MvPowerSeries.monomial J a)
      = Valued.v ((a : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
  have hmono := isRestricted_monomial p F ϖ a (J := J)
  refine le_antisymm (ciSup_le fun s => ?_) ?_
  · rw [MvPowerSeries.coeff_monomial]
    split_ifs with h
    · exact le_rfl
    · rw [ZeroMemClass.coe_zero, Valuation.map_zero]
      exact zero_le
  · have h1 := valued_coeff_le_gaussNormRPS p F ϖ hmono J
    rwa [MvPowerSeries.coeff_monomial, if_pos rfl] at h1

/-- Coefficients of a monomial multiple, in range. -/
theorem coeff_monomialMul_pos {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {D K : Fin k →₀ ℕ} (zz : ↥(ArSub p F ϖ hρ0 hρ1))
    (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) (h : D ≤ K) :
    MvPowerSeries.coeff K ((MvPowerSeries.monomial D zz) * x)
      = zz * MvPowerSeries.coeff (K - D) x := by
  rw [MvPowerSeries.coeff_monomial_mul, if_pos h]

theorem coeff_monomialMul_neg {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {D K : Fin k →₀ ℕ} (zz : ↥(ArSub p F ϖ hρ0 hρ1))
    (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) (h : ¬ D ≤ K) :
    MvPowerSeries.coeff K ((MvPowerSeries.monomial D zz) * x) = 0 := by
  rw [MvPowerSeries.coeff_monomial_mul, if_neg h]

theorem isRestricted_monomialMul {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (D : Fin k →₀ ℕ) (zz : ↥(ArSub p F ϖ hρ0 hρ1))
    {x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hx : MvPowerSeries.IsRestricted x) :
    MvPowerSeries.IsRestricted ((MvPowerSeries.monomial D zz) * x) :=
  Subring.mul_mem (restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))
    (isRestricted_monomial p F ϖ zz (J := D)) hx

theorem coeff_sub_monomialMul_lead {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    {I J : Fin k →₀ ℕ} (hIJ : I ≤ J) (zz : ↥(ArSub p F ϖ hρ0 hρ1)) :
    MvPowerSeries.coeff J (y - (MvPowerSeries.monomial (J - I) zz) * x)
      = MvPowerSeries.coeff J y - zz * MvPowerSeries.coeff I x := by
  rw [map_sub, coeff_monomialMul_pos p F ϖ zz x tsub_le_self,
    tsub_tsub_cancel_of_le hIJ]

theorem groebner_step {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {ε : NNReal}
    {x y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hx : MvPowerSeries.IsRestricted x) (hy : MvPowerSeries.IsRestricted y)
    {I J : Fin k →₀ ℕ} {c : ↥(ArSub p F ϖ hρ0 hρ1)}
    (hcx : MvPowerSeries.coeff I x = c)
    (hc0 : ((c : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) ≠ 0)
    (hcnorm : Valued.v ((c : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
      = gaussNormRPS p F ϖ hρ0 hρ1 x)
    (hIJ : I ≤ J)
    (htail : ∀ K : Fin k →₀ ℕ,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn I
        < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
      Valued.v ((MvPowerSeries.coeff K x : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 x) :
    ∃ z : ↥(ArSub p F ϖ hρ0 hρ1),
      Valued.v ((z : hatK p F hρ0 hρ1)) * gaussNormRPS p F ϖ hρ0 hρ1 x
          ≤ gaussNormRPS p F ϖ hρ0 hρ1 y
        ∧ (∀ K : Fin k →₀ ℕ,
            (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
              < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
            Valued.v ((MvPowerSeries.coeff K
                ((MvPowerSeries.monomial (J - I) z) * x)
                : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
              ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 y)
        ∧ gaussNormRPS p F ϖ hρ0 hρ1
            (y - (MvPowerSeries.monomial (J - I) z) * x)
            ≤ gaussNormRPS p F ϖ hρ0 hρ1 y
        ∧ (((MvPowerSeries.coeff J
              (y - (MvPowerSeries.monomial (J - I) z) * x)
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) = 0
          ∨ degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J
                (y - (MvPowerSeries.monomial (J - I) z) * x)
                : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
              < degAr p F ϖ hρ0 hρ1 ((c : ↥(ArSub p F ϖ hρ0 hρ1))
                : hatK p F hρ0 hρ1)) := by
  obtain ⟨z, hzmem, hzval, hzdeg⟩ := exact_division p F ϖ
    (c : ↥(ArSub p F ϖ hρ0 hρ1)).2 hc0
    (MvPowerSeries.coeff J y : ↥(ArSub p F ϖ hρ0 hρ1)).2
  have hzc : Valued.v ((z : hatK p F hρ0 hρ1))
      * Valued.v ((c : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
      ≤ Valued.v ((MvPowerSeries.coeff J y : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) := by
    have heq : (z : hatK p F hρ0 hρ1)
        * ((c : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        = ((MvPowerSeries.coeff J y : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
          - (((MvPowerSeries.coeff J y : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1) - (z : hatK p F hρ0 hρ1)
            * ((c : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) := by
      ring
    rw [← Valuation.map_mul, heq]
    exact le_trans (Valuation.map_sub _ _ _) (max_le le_rfl hzval)
  have hzy : Valued.v ((z : hatK p F hρ0 hρ1)) * gaussNormRPS p F ϖ hρ0 hρ1 x
      ≤ gaussNormRPS p F ϖ hρ0 hρ1 y := by
    rw [← hcnorm]
    exact le_trans hzc (valued_coeff_le_gaussNormRPS p F ϖ hy J)
  refine ⟨⟨z, hzmem⟩, hzy, ?_, ?_, ?_⟩
  · intro K hK
    by_cases hDK : J - I ≤ K
    · rw [coeff_monomialMul_pos p F ϖ _ x hDK, MulMemClass.coe_mul,
        Valuation.map_mul]
      have hshift : (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn I
          < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn (K - (J - I)) := by
        have h1 : I + (J - I) = J := add_tsub_cancel_of_le hIJ
        have h2 : (K - (J - I)) + (J - I) = K := tsub_add_cancel_of_le hDK
        have h3 : (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn (I + (J - I))
            < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
              ((K - (J - I)) + (J - I)) := by
          rw [h1, h2]
          exact hK
        rw [map_add, map_add] at h3
        exact lt_of_add_lt_add_right h3
      calc Valued.v ((z : hatK p F hρ0 hρ1))
            * Valued.v ((MvPowerSeries.coeff (K - (J - I)) x
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
          ≤ Valued.v ((z : hatK p F hρ0 hρ1))
            * (ε * gaussNormRPS p F ϖ hρ0 hρ1 x) :=
            mul_le_mul_of_nonneg_left (htail (K - (J - I)) hshift) zero_le
        _ = ε * (Valued.v ((z : hatK p F hρ0 hρ1))
            * gaussNormRPS p F ϖ hρ0 hρ1 x) := by ring
        _ ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 y :=
            mul_le_mul_of_nonneg_left hzy zero_le
    · rw [coeff_monomialMul_neg p F ϖ _ x hDK, ZeroMemClass.coe_zero,
        Valuation.map_zero]
      exact zero_le
  · have haxnorm : gaussNormRPS p F ϖ hρ0 hρ1
        ((MvPowerSeries.monomial (J - I) (⟨z, hzmem⟩ :
          ↥(ArSub p F ϖ hρ0 hρ1))) * x) ≤ gaussNormRPS p F ϖ hρ0 hρ1 y := by
      refine ciSup_le fun K => ?_
      by_cases hDK : J - I ≤ K
      · rw [coeff_monomialMul_pos p F ϖ _ x hDK, MulMemClass.coe_mul,
          Valuation.map_mul]
        refine le_trans (mul_le_mul_of_nonneg_left
          (valued_coeff_le_gaussNormRPS p F ϖ hx (K - (J - I))) zero_le) hzy
      · rw [coeff_monomialMul_neg p F ϖ _ x hDK, ZeroMemClass.coe_zero,
          Valuation.map_zero]
        exact zero_le
    exact le_trans (gaussNormRPS_sub_le p F ϖ hy
      (isRestricted_monomialMul p F ϖ (J - I) _ hx)) (max_le le_rfl haxnorm)
  · have hcJ' : MvPowerSeries.coeff J (y - (MvPowerSeries.monomial (J - I)
        (⟨z, hzmem⟩ : ↥(ArSub p F ϖ hρ0 hρ1))) * x)
        = MvPowerSeries.coeff J y
          - (⟨z, hzmem⟩ : ↥(ArSub p F ϖ hρ0 hρ1)) * c := by
      rw [coeff_sub_monomialMul_lead p F ϖ hIJ, hcx]
    have hcJ : ((MvPowerSeries.coeff J (y - (MvPowerSeries.monomial (J - I)
        (⟨z, hzmem⟩ : ↥(ArSub p F ϖ hρ0 hρ1))) * x)
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        = ((MvPowerSeries.coeff J y : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
          - (z : hatK p F hρ0 hρ1)
            * ((c : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
      exact congrArg (fun w : ↥(ArSub p F ϖ hρ0 hρ1) =>
        (w : hatK p F hρ0 hρ1)) hcJ'
    rw [hcJ]
    exact hzdeg

/-- **The normalized strict tail bound**: past the leading index, coefficients are
uniformly `ε`-small relative to the Gauss norm, for some `ε < 1`. -/
theorem exists_normalized_tail_bound {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hx : MvPowerSeries.IsRestricted x) (hx0 : x ≠ 0) :
    ∃ ε : NNReal, ε < 1 ∧ ∀ K : Fin k →₀ ℕ,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
          (leadIdxRPS p F ϖ hρ0 hρ1 x)
        < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
      Valued.v ((MvPowerSeries.coeff K x : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 x := by
  obtain ⟨ε₀, hlt, htail⟩ := exists_tail_bound_lt p F ϖ hx hx0
  have hne : gaussNormRPS p F ϖ hρ0 hρ1 x ≠ 0 :=
    gaussNormRPS_ne_zero p F ϖ hx hx0
  refine ⟨ε₀ / gaussNormRPS p F ϖ hρ0 hρ1 x, ?_, fun K hK => ?_⟩
  · rw [div_lt_one (pos_iff_ne_zero.mpr hne)]
    exact hlt
  · rw [div_mul_cancel₀ _ hne]
    exact htail K hK

/-- **One Gröbner generator at a fixed index** (the per-index content of the
Gröbner package, standalone for the per-declaration budget). -/
theorem exists_groebner_generator {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
    (I : Fin k →₀ ℕ) (hI : dIdx p F ϖ hρ0 hρ1 H I ≠ ⊤) :
    ∃ (x : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
      (e : NNReal),
      x ∈ H ∧ ((x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0)
        ∧ leadIdxRPS p F ϖ hρ0 hρ1
            (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = I
        ∧ ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
              (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)
            = dIdx p F ϖ hρ0 hρ1 H I)
        ∧ e < 1
        ∧ (∀ K : Fin k →₀ ℕ,
            (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn I
              < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
            Valued.v ((MvPowerSeries.coeff K
                (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
                : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
              ≤ e * gaussNormRPS p F ϖ hρ0 hρ1
                (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) := by
  have h₁ := exists_leadIdx_degAr_eq p F ϖ hI
  have h₂ := exists_normalized_tail_bound p F ϖ h₁.choose.2 h₁.choose_spec.2.1
  exact ⟨h₁.choose, h₂.choose, h₁.choose_spec.1, h₁.choose_spec.2.1,
    h₁.choose_spec.2.2.1, h₁.choose_spec.2.2.2, h₂.choose_spec.1,
    fun K hK => h₂.choose_spec.2 K
      (by rw [h₁.choose_spec.2.2.1]; exact hK)⟩

open scoped Classical in
/-- **The Gröbner data package** (Kedlaya Definition 3.7 + the `ε` of Lemma 3.8):
a finite set of ideal generators, each with its leading data, and one `ε < 1`
bounding every generator's tail. -/
theorem exists_groebner_family {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    ∃ (G : Finset ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
      (ε : NNReal), 0 < ε ∧ ε < 1
      ∧ (∀ g ∈ G, g ∈ H)
      ∧ (∀ g ∈ G, ((g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0))
      ∧ (∀ g ∈ G, ∀ K : Fin k →₀ ℕ,
          (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
              (leadIdxRPS p F ϖ hρ0 hρ1
                (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
            < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
          Valued.v ((MvPowerSeries.coeff K
              (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
            ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1
              (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
      ∧ (∀ g ∈ G, ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
              (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)
          = dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1
              (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))))
      ∧ (∀ J : Fin k →₀ ℕ, dIdx p F ϖ hρ0 hρ1 H J ≠ ⊤ →
          ∃ g ∈ G, leadIdxRPS p F ϖ hρ0 hρ1
              (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ J
            ∧ dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1
                (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
              = dIdx p F ϖ hρ0 hρ1 H J) := by
  classical
  set T : Finset (Fin k →₀ ℕ) := (groebnerSet_finite p F ϖ H).toFinset with hT
  have hdIT : ∀ I ∈ T, dIdx p F ϖ hρ0 hρ1 H I ≠ ⊤ := by
    intro I hI
    rw [hT, Set.Finite.mem_toFinset] at hI
    obtain ⟨q, hqmin, hqfst⟩ := hI
    have hIe : dIdx p F ϖ hρ0 hρ1 H q.1 ≤ ((q.2 : ℕ) : ℕ∞) := hqmin.1
    rw [← hqfst]
    exact ne_top_of_le_ne_top (WithTop.natCast_ne_top q.2) hIe
  have hex : ∀ I : {I : Fin k →₀ ℕ // I ∈ T},
      ∃ (x : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
        (e : NNReal),
        x ∈ H ∧ ((x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0)
          ∧ leadIdxRPS p F ϖ hρ0 hρ1
              (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = I.1
          ∧ ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
                (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
                : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)
              = dIdx p F ϖ hρ0 hρ1 H I.1)
          ∧ e < 1
          ∧ (∀ K : Fin k →₀ ℕ,
              (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn I.1
                < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
              Valued.v ((MvPowerSeries.coeff K
                  (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
                  : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
                ≤ e * gaussNormRPS p F ϖ hρ0 hρ1
                  (x : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) :=
    fun I => exists_groebner_generator p F ϖ H I.1 (hdIT I.1 I.2)
  choose X E hXH hX0 hXlead hXdeg hElt hEtail using hex
  have himg : ∀ (P : ↥(restrictedMvPowerSeriesSubring k
        ↥(ArSub p F ϖ hρ0 hρ1)) → Prop),
      (∀ I : {I : Fin k →₀ ℕ // I ∈ T}, P (X I)) →
      ∀ g ∈ T.attach.image X, P g := by
    intro P hP g hg
    obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hg
    exact hP I
  refine ⟨T.attach.image X, max (T.attach.sup E) (1 / 2), ?_, ?_,
    himg _ (fun I => hXH I), himg _ (fun I => hX0 I),
    himg _ (fun I K hK => le_trans (hEtail I K
      ((congrArg (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
        (hXlead I)) ▸ hK))
      (mul_le_mul_of_nonneg_right
        (le_trans (Finset.le_sup (Finset.mem_attach T I)) (le_max_left _ _)) zero_le)),
    himg _ (fun I => (hXdeg I).trans
      (congrArg (dIdx p F ϖ hρ0 hρ1 H) (hXlead I).symm)), ?_⟩
  · refine lt_of_lt_of_le ?_ (le_max_right _ _)
    norm_num
  · refine max_lt ?_ (by norm_num)
    refine (Finset.sup_lt_iff (by rw [bot_eq_zero]; exact zero_lt_one)).mpr ?_
    intro I _
    exact hElt I
  · intro J hJ
    have hex2 := exists_mem_groebnerSet_le p F ϖ hJ
    have hIT : hex2.choose ∈ T := by
      rw [hT, Set.Finite.mem_toFinset]
      exact hex2.choose_spec.1
    refine ⟨X ⟨hex2.choose, hIT⟩,
      Finset.mem_image.mpr ⟨⟨hex2.choose, hIT⟩, Finset.mem_attach _ _, rfl⟩,
      ?_, ?_⟩
    · exact le_of_eq_of_le (hXlead ⟨hex2.choose, hIT⟩)
        hex2.choose_spec.2.1
    · exact (congrArg (dIdx p F ϖ hρ0 hρ1 H)
        (hXlead ⟨hex2.choose, hIT⟩)).trans hex2.choose_spec.2.2

/-- **Dominated perturbations preserve value and degree** (Remark 2.7, packaged). -/
theorem valued_degAr_eq_of_sub_lt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {u v : hatK p F hρ0 hρ1} (hu : u ∈ ArSub p F ϖ hρ0 hρ1)
    (hv : v ∈ ArSub p F ϖ hρ0 hρ1) (h : Valued.v (u - v) < Valued.v u) :
    Valued.v v = Valued.v u ∧ degAr p F ϖ hρ0 hρ1 v = degAr p F ϖ hρ0 hρ1 u :=
  ⟨valued_eq_of_valued_sub_lt p F h,
    (degAr_eq_of_valued_sub_lt p F ϖ hu hv h).symm⟩

/-- Coefficientwise form of a single subtraction. -/
theorem coeff_sub_eq {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (y w : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) (K : Fin k →₀ ℕ) :
    ((MvPowerSeries.coeff K (y - w) : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1)
      = ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        - ((MvPowerSeries.coeff K w : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) :=
  congrArg (fun t : ↥(ArSub p F ϖ hρ0 hρ1) => (t : hatK p F hρ0 hρ1))
    (map_sub (MvPowerSeries.coeff K) y w)

/-- **The frozen zone**: above the working index, a correction of value below the
coefficient's own value changes neither the value nor the degree. -/
theorem coeff_frozen {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {y w : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)} {K : Fin k →₀ ℕ}
    (hsmall : Valued.v ((MvPowerSeries.coeff K w : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)
      < Valued.v ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)) :
    Valued.v ((MvPowerSeries.coeff K (y - w) : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)
      = Valued.v ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)
    ∧ degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff K (y - w)
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
      = degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff K y
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
  have hdiff : ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)
      - ((MvPowerSeries.coeff K (y - w) : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)
      = ((MvPowerSeries.coeff K w : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) := by
    rw [coeff_sub_eq p F ϖ y w K]
    ring
  refine valued_degAr_eq_of_sub_lt p F ϖ
    (MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1)).2
    (MvPowerSeries.coeff K (y - w) : ↥(ArSub p F ϖ hρ0 hρ1)).2 ?_
  rw [hdiff]
  exact hsmall

/-- Coercion of a subring difference-of-product (stated in a small context so the
elaborator does not re-derive it under large goals). -/
theorem coe_sub_monomialMul {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (y g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
    (m : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
    (hm : MvPowerSeries.IsRestricted m) :
    ((y - (⟨m, hm⟩ : ↥(restrictedMvPowerSeriesSubring k
        ↥(ArSub p F ϖ hρ0 hρ1))) * g : ↥(restrictedMvPowerSeriesSubring k
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
      = (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        - m * (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := rfl

/-- **One Gröbner reduction** (Kedlaya Lemma 3.8, inner move at the ideal level):
a nonzero ideal element can be moved by a generator multiple so that the norm does
not grow, coefficients above the leading index move by at most `ε·|y|`, and the
leading coefficient's degree strictly drops. -/
theorem groebner_reduce {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {ε : NNReal}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {G : Finset ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    (hGH : ∀ g ∈ G, g ∈ H)
    (hG0 : ∀ g ∈ G, ((g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0))
    (hGtail : ∀ g ∈ G, ∀ K : Fin k →₀ ℕ,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
          (leadIdxRPS p F ϖ hρ0 hρ1
            (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
        < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
      Valued.v ((MvPowerSeries.coeff K
          (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1
          (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
    (hGdeg : ∀ g ∈ G, ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)
        = dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1
            (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))))
    (hGdom : ∀ J : Fin k →₀ ℕ, dIdx p F ϖ hρ0 hρ1 H J ≠ ⊤ →
      ∃ g ∈ G, leadIdxRPS p F ϖ hρ0 hρ1
          (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ J
        ∧ dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1
            (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
          = dIdx p F ϖ hρ0 hρ1 H J)
    {y : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    (hyH : y ∈ H)
    (hy0 : ((y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0)) :
    ∃ (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
      (m : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
      (J : Fin k →₀ ℕ), g ∈ G
      ∧ gaussNormRPS p F ϖ hρ0 hρ1
          (m : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        * gaussNormRPS p F ϖ hρ0 hρ1
          (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        ≤ gaussNormRPS p F ϖ hρ0 hρ1
          (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
      ∧ leadIdxRPS p F ϖ hρ0 hρ1
          (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = J
      ∧ gaussNormRPS p F ϖ hρ0 hρ1
          ((y - m * g : ↥(restrictedMvPowerSeriesSubring k
            ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
            ↥(ArSub p F ϖ hρ0 hρ1))
        ≤ gaussNormRPS p F ϖ hρ0 hρ1
          (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
      ∧ (∀ K : Fin k →₀ ℕ,
          (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
            < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
          Valued.v (((MvPowerSeries.coeff K
              ((y - m * g : ↥(restrictedMvPowerSeriesSubring k
                ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
                ↥(ArSub p F ϖ hρ0 hρ1))
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
            - ((MvPowerSeries.coeff K
              (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1))
            ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1
              (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
      ∧ (((MvPowerSeries.coeff J
            ((y - m * g : ↥(restrictedMvPowerSeriesSubring k
              ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
              ↥(ArSub p F ϖ hρ0 hρ1))
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) = 0
        ∨ degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J
              ((y - m * g : ↥(restrictedMvPowerSeriesSubring k
                ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
                ↥(ArSub p F ϖ hρ0 hρ1))
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
            < degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J
              (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
              : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) := by
  classical
  have hyres : MvPowerSeries.IsRestricted
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := y.2
  have hdJ : dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
      ≤ ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)) :=
    dIdx_le_of_mem p F ϖ hyH hy0 rfl
  have hdJtop : dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.natCast_ne_top _) hdJ
  have hgd := hGdom (leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) hdJtop
  have hgres : MvPowerSeries.IsRestricted
      (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :=
    hgd.choose.2
  have hg0 := hG0 hgd.choose hgd.choose_spec.1
  have hcnorm : Valued.v ((leadCoeffRPS p F ϖ hρ0 hρ1
        (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
      = gaussNormRPS p F ϖ hρ0 hρ1
        (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :=
    valued_leadCoeffRPS p F ϖ hgres hg0
  have hc0 : ((leadCoeffRPS p F ϖ hρ0 hρ1
        (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) ≠ 0 := by
    refine (Valuation.ne_zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp ?_
    rw [hcnorm]
    exact gaussNormRPS_ne_zero p F ϖ hgres hg0
  have hstep := groebner_step p F ϖ hgres hyres rfl hc0 hcnorm
    hgd.choose_spec.2.1 (hGtail hgd.choose hgd.choose_spec.1)
  refine ⟨hgd.choose, ⟨MvPowerSeries.monomial ((leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) - (leadIdxRPS p F ϖ hρ0 hρ1
              (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))) hstep.choose,
      isRestricted_monomial p F ϖ hstep.choose⟩, (leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))),
    hgd.choose_spec.1, ?_, rfl, ?_, ?_, ?_⟩
  · exact le_of_eq_of_le
      (congrArg (fun t : NNReal => t * gaussNormRPS p F ϖ hρ0 hρ1
        (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
        (gaussNormRPS_monomial p F ϖ _ hstep.choose))
      hstep.choose_spec.1
  · exact hstep.choose_spec.2.2.1
  · intro K hK
    have hdiff : ((MvPowerSeries.coeff K
          ((y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            - (MvPowerSeries.monomial ((leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) - (leadIdxRPS p F ϖ hρ0 hρ1
              (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))) hstep.choose)
              * (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        - ((MvPowerSeries.coeff K
          (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        = -((MvPowerSeries.coeff K
            ((MvPowerSeries.monomial ((leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) - (leadIdxRPS p F ϖ hρ0 hρ1
              (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))) hstep.choose)
              * (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) :=
      (congrArg (fun t : hatK p F hρ0 hρ1 => t
          - ((MvPowerSeries.coeff K
            (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1))
        (coeff_sub_eq p F ϖ _ _ K)).trans
        (sub_sub_cancel_left _ _)
    exact le_of_eq_of_le
      ((congrArg Valued.v hdiff).trans (Valuation.map_neg _ _))
      (hstep.choose_spec.2.1 K hK)
  · have hchain : ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ) : ℕ∞)
        ≤ ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ) : ℕ∞) :=
      ((hGdeg hgd.choose hgd.choose_spec.1).trans
        hgd.choose_spec.2.2).trans_le hdJ
    have hdegle : degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (hgd.choose : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        ≤ degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff (leadIdxRPS p F ϖ hρ0 hρ1
      (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
          (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
      exact_mod_cast hchain
    exact hstep.choose_spec.2.2.2.elim Or.inl
      (fun h => Or.inr (lt_of_lt_of_le h hdegle))


/-- The rank of a coefficient relative to a threshold `c`: the shifted degree if the
coefficient is `c`-large, and `0` otherwise (Kedlaya's `ε`-support with its degree
data). -/
def coeffRank {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : NNReal)
    (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) (K : Fin k →₀ ℕ) : ℕ :=
  if c < Valued.v ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1) then
    degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1) + 1
  else 0

/-- **Frozen ranks**: a `c`-small correction changes no rank. -/
theorem coeffRank_eq_of_diff_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {c : NNReal}
    {y y' : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)} {K : Fin k →₀ ℕ}
    (hd : Valued.v (((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)
      - ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1)) ≤ c) :
    coeffRank p F ϖ hρ0 hρ1 c y' K = coeffRank p F ϖ hρ0 hρ1 c y K := by
  by_cases hhigh : c < Valued.v ((MvPowerSeries.coeff K y
      : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
  · have hlt : Valued.v (((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        - ((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1))
        < Valued.v ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) := by
      have hswap : ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1)
          - ((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1)
          = -(((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1)
            - ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1)) := by ring
      rw [hswap, Valuation.map_neg]
      exact lt_of_le_of_lt hd hhigh
    obtain ⟨hval, hdeg⟩ := valued_degAr_eq_of_sub_lt p F ϖ
      (MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1)).2
      (MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1)).2 hlt
    rw [coeffRank, coeffRank, if_pos hhigh, if_pos (by rw [hval]; exact hhigh), hdeg]
  · push Not at hhigh
    have hy' : Valued.v ((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) ≤ c := by
      have hsplit : ((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1)
          = (((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1)
            - ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1))
            + ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_add _ _ _) (max_le hd hhigh)
    rw [coeffRank, coeffRank, if_neg (not_lt.mpr hy'), if_neg (not_lt.mpr hhigh)]

/-- **The rank drops** where the degree drops. -/
theorem coeffRank_lt_of_drop {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {c : NNReal}
    {y y' : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)} {J : Fin k →₀ ℕ}
    (hJhigh : c < Valued.v ((MvPowerSeries.coeff J y : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1))
    (hdrop : ((MvPowerSeries.coeff J y' : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) = 0
      ∨ degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J y'
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        < degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J y
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) :
    coeffRank p F ϖ hρ0 hρ1 c y' J < coeffRank p F ϖ hρ0 hρ1 c y J := by
  have hy : coeffRank p F ϖ hρ0 hρ1 c y J
      = degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J y
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) + 1 := by
    rw [coeffRank, if_pos hJhigh]
  rcases hdrop with hzero | hdeg
  · have hnot : ¬ (c < Valued.v ((MvPowerSeries.coeff J y'
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) := by
      rw [hzero, Valuation.map_zero]
      exact not_lt.mpr zero_le
    have hy' : coeffRank p F ϖ hρ0 hρ1 c y' J = 0 := by
      rw [coeffRank, if_neg hnot]
    rw [hy, hy']
    exact Nat.succ_pos _
  · rw [hy, coeffRank]
    split_ifs with h
    · exact Nat.succ_lt_succ hdeg
    · exact Nat.succ_pos _

/-- **The support invariant**: a step at `J` keeps the `c`-support inside the
graded-lex segment below `M`. -/
theorem support_step_subset {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {c : NNReal}
    {y y' : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)} {J M : Fin k →₀ ℕ}
    (hJM : (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
      ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M)
    (hsub : ∀ K : Fin k →₀ ℕ,
      c < Valued.v ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) →
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K
        ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M)
    (hdiff : ∀ K : Fin k →₀ ℕ,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
        < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
      Valued.v (((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        - ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)) ≤ c) :
    ∀ K : Fin k →₀ ℕ,
      c < Valued.v ((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
        : hatK p F hρ0 hρ1) →
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K
        ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M := by
  intro K hK
  rcases le_or_gt ((MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K)
    ((MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J) with hKJ | hKJ
  · exact le_trans hKJ hJM
  · refine hsub K ?_
    by_contra hcon
    push Not at hcon
    have hrank := coeffRank_eq_of_diff_le p F ϖ (c := c) (y := y) (y' := y')
      (K := K) (hdiff K hKJ)
    have hy'small : Valued.v ((MvPowerSeries.coeff K y'
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) ≤ c := by
      have hsplit : ((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
            : hatK p F hρ0 hρ1)
          = (((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1)
            - ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1))
            + ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
              : hatK p F hρ0 hρ1) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_add _ _ _) (max_le (hdiff K hKJ) hcon)
    exact absurd hK (not_lt.mpr hy'small)

@[simp]
theorem gaussNormRPS_zero {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} :
    gaussNormRPS p F ϖ hρ0 hρ1
      (0 : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = 0 := by
  refine le_antisymm (ciSup_le fun s => ?_) zero_le
  rw [map_zero, ZeroMemClass.coe_zero, Valuation.map_zero]

theorem gaussNormRPS_eq_zero_iff {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) :
    gaussNormRPS p F ϖ hρ0 hρ1 f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hne
    exact gaussNormRPS_ne_zero p F ϖ hf hne h
  · rintro rfl
    exact gaussNormRPS_zero p F ϖ

/-- Finite nonempty sets of monomials have a graded-lex maximum. -/
theorem exists_degLex_max {S : Set (Fin k →₀ ℕ)} (hfin : S.Finite)
    (hne : S.Nonempty) :
    ∃ M ∈ S, ∀ K ∈ S,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K
        ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M := by
  classical
  set m : MonomialOrder (Fin k) := MonomialOrder.degLex with hm
  set A := hfin.toFinset with hA
  have hAne : A.Nonempty := by
    rw [hA, Set.Finite.toFinset_nonempty]
    exact hne
  set Mx := (A.image m.toSyn).max' (hAne.image _) with hMx
  have hmem : Mx ∈ A.image m.toSyn := Finset.max'_mem _ _
  obtain ⟨M, hMA, hMeq⟩ := Finset.mem_image.mp hmem
  refine ⟨M, ?_, fun K hK => ?_⟩
  · rw [hA, Set.Finite.mem_toFinset] at hMA
    exact hMA
  · rw [hMeq]
    refine Finset.le_max' _ _ (Finset.mem_image_of_mem _ ?_)
    rw [hA, Set.Finite.mem_toFinset]
    exact hK

/-- The graded-lex initial segment below `M`. -/
def degLexSeg (M : Fin k →₀ ℕ) : Type :=
  {K : Fin k →₀ ℕ // (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K
    ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M}

instance instFintypeDegLexSeg (M : Fin k →₀ ℕ) : Fintype (degLexSeg M) :=
  (finite_degLex_le M).fintype

instance instLinearOrderDegLexSeg (M : Fin k →₀ ℕ) : LinearOrder (degLexSeg M) :=
  LinearOrder.lift'
    (fun K : degLexSeg M => (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K.1)
    (fun a b h => Subtype.ext
      ((MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn.injective h))

theorem degLexSeg_lt_iff {M : Fin k →₀ ℕ} {a b : degLexSeg M} :
    a < b ↔ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn a.1
      < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn b.1 := Iff.rfl

/-- **The descent measure** (Kedlaya Lemma 3.8): the colexicographic vector of
coefficient ranks over the graded-lex segment below `M`. -/
def muMeasure {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : NNReal)
    (M : Fin k →₀ ℕ) (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :
    Colex (degLexSeg M → ℕ) :=
  toColex (fun K : degLexSeg M => coeffRank p F ϖ hρ0 hρ1 c y K.1)

/-- **The measure strictly decreases** at a reduction step. -/
theorem muMeasure_lt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {c : NNReal}
    {M : Fin k →₀ ℕ} {y y' : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    {J : Fin k →₀ ℕ}
    (hJM : (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
      ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M)
    (hJhigh : c < Valued.v ((MvPowerSeries.coeff J y : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1))
    (hfrozen : ∀ K : Fin k →₀ ℕ,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
        < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
      Valued.v (((MvPowerSeries.coeff K y' : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        - ((MvPowerSeries.coeff K y : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)) ≤ c)
    (hdrop : ((MvPowerSeries.coeff J y' : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) = 0
      ∨ degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J y'
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        < degAr p F ϖ hρ0 hρ1 ((MvPowerSeries.coeff J y
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) :
    muMeasure p F ϖ hρ0 hρ1 c M y' < muMeasure p F ϖ hρ0 hρ1 c M y := by
  refine ⟨⟨J, hJM⟩, fun Kj hKj => ?_, ?_⟩
  · exact coeffRank_eq_of_diff_le p F ϖ (hfrozen Kj.1 (degLexSeg_lt_iff.mp hKj))
  · exact coeffRank_lt_of_drop p F ϖ hJhigh hdrop

set_option maxHeartbeats 2000000 in
/-- **Kedlaya Lemma 3.8 (approximate ideal generation)**: every ideal element is,
up to an `ε`-small remainder, a combination of the finitely many Gröbner generators
with controlled coefficients. -/
theorem approx_generation {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {ε : NNReal}
    {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    {G : Finset ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    (hGH : ∀ g ∈ G, g ∈ H)
    (hG0 : ∀ g ∈ G, ((g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0))
    (hGtail : ∀ g ∈ G, ∀ K : Fin k →₀ ℕ,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn (leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
      Valued.v ((MvPowerSeries.coeff K (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
    (hGdeg : ∀ g ∈ G, ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)
        = dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))))
    (hGdom : ∀ J : Fin k →₀ ℕ, dIdx p F ϖ hρ0 hρ1 H J ≠ ⊤ →
      ∃ g ∈ G, leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ J
        ∧ dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
          = dIdx p F ϖ hρ0 hρ1 H J)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    {y₀ : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))} (hy₀H : y₀ ∈ H) :
    ∃ a : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) → ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)),
      (∀ g ∈ G, gaussNormRPS p F ϖ hρ0 hρ1 ((a g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) * gaussNormRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        ≤ gaussNormRPS p F ϖ hρ0 hρ1 (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
      ∧ gaussNormRPS p F ϖ hρ0 hρ1 (((y₀ - ∑ g ∈ G, a g * g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := by
  classical
  set B := gaussNormRPS p F ϖ hρ0 hρ1 (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) with hB
  set c := ε * B with hc
  by_cases hB0 : B = 0
  · refine ⟨fun _ => 0, fun g hg => ?_, ?_⟩
    · rw [ZeroMemClass.coe_zero, gaussNormRPS_zero, zero_mul]
      exact zero_le
    · have hsum : (∑ g ∈ G, (0 : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) * g) = 0 :=
        Finset.sum_eq_zero fun g _ => by rw [zero_mul]
      rw [hsum, sub_zero, ← hB, hB0, hc, hB0, mul_zero]
  · have hBpos : 0 < B := pos_iff_ne_zero.mpr hB0
    have hcB : c < B := by
      rw [hc]
      calc ε * B < 1 * B := by
            exact mul_lt_mul_of_pos_right hε1 hBpos
        _ = B := one_mul B
    have hc0 : 0 < c := mul_pos hε0 hBpos
    -- the graded-lex ceiling `M` of the `c`-support of `y₀`
    have hy₀res : MvPowerSeries.IsRestricted (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := y₀.2
    have hy₀0 : (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0 := by
      intro h
      exact hB0 (by rw [hB, h, gaussNormRPS_zero])
    have hfin := (isRestricted_iff_valued p F ϖ (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))).mp hy₀res c hc0
    have hlead : Valued.v ((MvPowerSeries.coeff
        (leadIdxRPS p F ϖ hρ0 hρ1 (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) = B :=
      valued_leadCoeffRPS p F ϖ hy₀res hy₀0
    have hne : {K : Fin k →₀ ℕ | c < Valued.v ((MvPowerSeries.coeff K
        (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)}.Nonempty := by
      refine ⟨leadIdxRPS p F ϖ hρ0 hρ1 (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)), ?_⟩
      rw [Set.mem_setOf_eq, hlead]
      exact hcB
    obtain ⟨M, hMmem, hMmax⟩ := exists_degLex_max hfin hne
    -- the induction
    have key : ∀ y : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)), y ∈ H → gaussNormRPS p F ϖ hρ0 hρ1 (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ B →
        (∀ K : Fin k →₀ ℕ, c < Valued.v ((MvPowerSeries.coeff K
            (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) → (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M) →
        ∃ a : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) → ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)),
          (∀ g ∈ G, gaussNormRPS p F ϖ hρ0 hρ1 ((a g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) * gaussNormRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ B)
          ∧ gaussNormRPS p F ϖ hρ0 hρ1 (((y - ∑ g ∈ G, a g * g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ c := by
      refine fun y => (InvImage.wf (fun w : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) =>
        muMeasure p F ϖ hρ0 hρ1 c M (w : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) wellFounded_lt).induction
        (C := fun y : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) => y ∈ H → gaussNormRPS p F ϖ hρ0 hρ1 (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ B →
          (∀ K : Fin k →₀ ℕ, c < Valued.v ((MvPowerSeries.coeff K
              (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) → (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M) →
          ∃ a : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) → ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)),
            (∀ g ∈ G, gaussNormRPS p F ϖ hρ0 hρ1 ((a g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) * gaussNormRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ B)
            ∧ gaussNormRPS p F ϖ hρ0 hρ1 (((y - ∑ g ∈ G, a g * g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ c) y ?_
      intro y ih hyH hyB hyL
      by_cases hsmall : gaussNormRPS p F ϖ hρ0 hρ1 (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ c
      · refine ⟨fun _ => 0, fun g hg => ?_, ?_⟩
        · rw [ZeroMemClass.coe_zero, gaussNormRPS_zero, zero_mul]
          exact zero_le
        · have hsum : (∑ g ∈ G, (0 : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) * g) = 0 :=
            Finset.sum_eq_zero fun g _ => by rw [zero_mul]
          rw [hsum, sub_zero]
          exact hsmall
      · push Not at hsmall
        have hyres : MvPowerSeries.IsRestricted (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := y.2
        have hy0 : (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0 := by
          intro h
          rw [h, gaussNormRPS_zero] at hsmall
          exact absurd hsmall (not_lt.mpr zero_le)
        obtain ⟨g, m, J, hgG, hmg, hJ, hnorm', hfrozen, hdrop⟩ :=
          groebner_reduce p F ϖ hGH hG0 hGtail hGdeg hGdom hyH hy0
        have hJhigh : c < Valued.v ((MvPowerSeries.coeff J (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
          have hval := valued_leadCoeffRPS p F ϖ hyres hy0
          rw [leadCoeffRPS] at hval
          rw [← hJ, hval]
          exact hsmall
        have hJM : (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J ≤ (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn M := hyL J hJhigh
        have hfrozen' : ∀ K : Fin k →₀ ℕ,
            (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn J
              < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
            Valued.v (((MvPowerSeries.coeff K
                ((y - m * g : ↥(restrictedMvPowerSeriesSubring k
                  ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
                  ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1))
                : hatK p F hρ0 hρ1)
              - ((MvPowerSeries.coeff K (y : MvPowerSeries (Fin k)
                ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1))
                : hatK p F hρ0 hρ1)) ≤ c := by
          intro K hK
          refine le_trans (hfrozen K hK) ?_
          rw [hc]
          exact mul_le_mul_of_nonneg_left hyB zero_le
        have hy'H : (y - m * g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) ∈ H :=
          Ideal.sub_mem H hyH (Ideal.mul_mem_left H m (hGH g hgG))
        have hdec : muMeasure p F ϖ hρ0 hρ1 c M
            (((y - m * g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            < muMeasure p F ϖ hρ0 hρ1 c M (y : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :=
          muMeasure_lt p F ϖ hJM hJhigh hfrozen' hdrop
        obtain ⟨b, hbB, hbrem⟩ := ih (y - m * g) hdec hy'H
          (le_trans hnorm' hyB)
          (support_step_subset p F ϖ hJM hyL hfrozen')
        refine ⟨Function.update b g (b g + m), fun g' hg' => ?_, ?_⟩
        · by_cases hgg : g' = g
          · subst hgg
            rw [Function.update_self]
            have hcoe : ((b g' + m : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
                = ((b g' : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) + ((m : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := rfl
            rw [hcoe]
            refine le_trans (mul_le_mul_of_nonneg_right
              (gaussNormRPS_add_le p F ϖ (b g').2 m.2) zero_le) ?_
            rw [mul_comm, nnreal_mul_max, mul_comm _ (gaussNormRPS p F ϖ hρ0 hρ1
              ((b g' : ↥(restrictedMvPowerSeriesSubring k
                ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
                ↥(ArSub p F ϖ hρ0 hρ1))),
              mul_comm _ (gaussNormRPS p F ϖ hρ0 hρ1
              ((m : ↥(restrictedMvPowerSeriesSubring k
                ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
                ↥(ArSub p F ϖ hρ0 hρ1)))]
            exact max_le (hbB g' hg') (le_trans hmg hyB)
          · have hupd : Function.update b g (b g + m) g' = b g' :=
              Function.update_of_ne hgg _ _
            rw [hupd]
            exact hbB g' hg'
        · have hsum : (∑ g' ∈ G, Function.update b g (b g + m) g' * g')
              = (∑ g' ∈ G, b g' * g') + m * g := by
            rw [← Finset.add_sum_erase G _ hgG,
              ← Finset.add_sum_erase G (fun g' => b g' * g') hgG,
              Function.update_self]
            have hrest : ∀ g' ∈ G.erase g,
                Function.update b g (b g + m) g' * g' = b g' * g' := by
              intro g' hg'
              have hupd : Function.update b g (b g + m) g' = b g' :=
                Function.update_of_ne (Finset.ne_of_mem_erase hg') _ _
              rw [hupd]
            rw [Finset.sum_congr rfl hrest]
            ring
          have hrw : ((y - ∑ g' ∈ G, Function.update b g (b g + m) g' * g'
              : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))))
              = ((y - m * g) - ∑ g' ∈ G, b g' * g' : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) := by
            rw [hsum]
            ring
          rw [hrw]
          exact hbrem
    obtain ⟨a, haB, harem⟩ := key y₀ hy₀H le_rfl (fun K hK => hMmax K hK)
    exact ⟨a, haB, harem⟩

/-- **Ultrametric series converge in `A^r`**: a sequence with vanishing value bounds
has convergent partial sums, with the expected tail estimates. -/
theorem exists_series_limit {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {u : ℕ → ↥(ArSub p F ϖ hρ0 hρ1)} {C : ℕ → NNReal}
    (hC : ∀ l, Valued.v ((u l : hatK p F hρ0 hρ1)) ≤ C l)
    (hC0 : Filter.Tendsto C Filter.atTop (nhds 0)) :
    ∃ S : ↥(ArSub p F ϖ hρ0 hρ1), ∀ (n : ℕ) (b : NNReal), 0 < b →
      (∀ l, n ≤ l → C l ≤ b) →
      Valued.v ((S : hatK p F hρ0 hρ1)
        - ∑ l ∈ Finset.range n, ((u l : hatK p F hρ0 hρ1))) ≤ b := by
  set s : ℕ → hatK p F hρ0 hρ1 :=
    fun n => ∑ l ∈ Finset.range n, ((u l : hatK p F hρ0 hρ1)) with hs
  have hsmem : ∀ n, s n ∈ ArSub p F ϖ hρ0 hρ1 := by
    intro n
    exact Subring.sum_mem _ fun l _ => (u l).2
  have hdiff : ∀ m n : ℕ, n ≤ m → ∀ b : NNReal, (∀ l, n ≤ l → C l ≤ b) →
      Valued.v (s m - s n) ≤ b := by
    intro m n hnm b hb
    have hIco : s m - s n = ∑ l ∈ Finset.Ico n m, ((u l : hatK p F hρ0 hρ1)) := by
      rw [hs, Finset.sum_Ico_eq_sub _ hnm]
    rw [hIco]
    refine Valuation.map_sum_le (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal) ?_
    intro l hl
    exact le_trans (hC l) (hb l (Finset.mem_Ico.mp hl).1)
  have hcauchy : CauchySeq s := by
    refine cauchySeq_of_valued_le p F (hρ0 := hρ0) (hρ1 := hρ1) s fun ε hε => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hC0.eventually_lt_const hε)
    refine ⟨N, fun m n hm hn => ?_⟩
    rcases le_total n m with h | h
    · exact hdiff m n h ε (fun l hl => (hN l (le_trans hn hl)).le)
    · rw [Valuation.map_sub_swap]
      exact hdiff n m h ε (fun l hl => (hN l (le_trans hm hl)).le)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hclosed : IsClosed (ArSub p F ϖ hρ0 hρ1 : Set (hatK p F hρ0 hρ1)) := by
    have hcarrier : (ArSub p F ϖ hρ0 hρ1 : Set (hatK p F hρ0 hρ1))
        = closure ((AlocToHatK p F ϖ hρ0 hρ1).range :
          Set (hatK p F hρ0 hρ1)) := rfl
    rw [hcarrier]
    exact isClosed_closure
  have hLmem : L ∈ ArSub p F ϖ hρ0 hρ1 :=
    hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall hsmem)
  refine ⟨⟨L, hLmem⟩, fun n b hb0 hb => ?_⟩
  obtain ⟨m, hmle, hmge⟩ := ((eventually_valued_sub_le_of_tendsto p F
    (hρ0 := hρ0) (hρ1 := hρ1) hL hb0).and
    (Filter.eventually_ge_atTop n)).exists
  have hsplit : (L : hatK p F hρ0 hρ1) - s n = (L - s m) + (s m - s n) := by ring
  rw [hsplit]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hdiff m n hmge b hb))
  rw [Valuation.map_sub_swap]
  exact hmle



/-- Coercion of a subring difference (small context). -/
theorem coe_RPS_sub {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (a b : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    ((a - b : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = (a : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) - (b : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := rfl

set_option maxHeartbeats 2000000 in
/-- **Ultrametric series converge in the Tate algebra** (the analytic input to
Kedlaya Lemma 3.9): coefficientwise limits of a norm-vanishing series exist, are
restricted, and satisfy the tail estimates. -/
theorem exists_rps_series_limit {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {u : ℕ → ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))} {C : ℕ → NNReal}
    (hC : ∀ l, gaussNormRPS p F ϖ hρ0 hρ1 ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ C l)
    (hC0 : Filter.Tendsto C Filter.atTop (nhds 0)) :
    ∃ U : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)), ∀ (n : ℕ) (b : NNReal), 0 < b → (∀ l, n ≤ l → C l ≤ b) →
      gaussNormRPS p F ϖ hρ0 hρ1 (((U - ∑ l ∈ Finset.range n, u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ b := by
  classical
  -- coefficientwise limits
  have hcoeff : ∀ K : Fin k →₀ ℕ, ∃ S : ↥(ArSub p F ϖ hρ0 hρ1), ∀ (n : ℕ) (b : NNReal), 0 < b →
      (∀ l, n ≤ l → C l ≤ b) →
      Valued.v ((S : hatK p F hρ0 hρ1) - ∑ l ∈ Finset.range n,
        ((MvPowerSeries.coeff K ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) ≤ b := by
    intro K
    refine exists_series_limit p F ϖ (C := C) (fun l => ?_) hC0
    exact valued_coeff_le_gaussNormRPS p F ϖ (u l).2 K |>.trans (hC l)
  choose S hS using hcoeff
  -- the candidate limit and its partial-sum comparison
  have hpartial : ∀ (n : ℕ) (K : Fin k →₀ ℕ),
      ((MvPowerSeries.coeff K ((∑ l ∈ Finset.range n, u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
      = ∑ l ∈ Finset.range n,
        ((MvPowerSeries.coeff K ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
    intro n K
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
      have hadd : ((∑ l ∈ Finset.range m, u l) + u m : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
          = ((∑ l ∈ Finset.range m, u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) + (u m : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) := rfl
      rw [hadd]
      have hcoe : (((∑ l ∈ Finset.range m, u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) + (u m : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
          : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          = ((∑ l ∈ Finset.range m, u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            + ((u m : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := rfl
      rw [hcoe, map_add, AddMemClass.coe_add]
  -- restrictedness of the limit
  set Ufun : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1) := S with hUfun
  have hres : MvPowerSeries.IsRestricted Ufun := by
    rw [isRestricted_iff_valued]
    intro t ht
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hC0.eventually_lt_const ht)
    have hsub : {K : Fin k →₀ ℕ | t < Valued.v ((MvPowerSeries.coeff K
          Ufun : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)}
        ⊆ ⋃ l ∈ Finset.range N, {K : Fin k →₀ ℕ | t < Valued.v
          ((MvPowerSeries.coeff K ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)} := by
      intro K hK
      rw [Set.mem_setOf_eq] at hK
      have hSK : ((MvPowerSeries.coeff K Ufun : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
          = ((S K : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := rfl
      rw [hSK] at hK
      have htail := hS K N t ht (fun l hl => (hN l hl).le)
      have hbig : t < Valued.v (∑ l ∈ Finset.range N,
          ((MvPowerSeries.coeff K ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)) := by
        by_contra hcon
        push Not at hcon
        have hsplit : ((S K : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
            = (((S K : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) - ∑ l ∈ Finset.range N,
                ((MvPowerSeries.coeff K ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1))
              + ∑ l ∈ Finset.range N,
                ((MvPowerSeries.coeff K ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
          ring
        rw [hsplit] at hK
        exact absurd (le_trans (Valuation.map_add _ _ _) (max_le htail hcon))
          (not_le.mpr hK)
      have hex : ∃ l ∈ Finset.range N, t < Valued.v
          ((MvPowerSeries.coeff K ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
        by_contra hcon
        push Not at hcon
        exact absurd (Valuation.map_sum_le
          (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal) hcon) (not_le.mpr hbig)
      obtain ⟨l, hlN, hl⟩ := hex
      exact Set.mem_biUnion hlN hl
    refine Set.Finite.subset (Set.Finite.biUnion (Finset.range N).finite_toSet
      fun l _ => ?_) hsub
    exact (isRestricted_iff_valued p F ϖ ((u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))).mp (u l).2 t ht
  refine ⟨⟨Ufun, hres⟩, fun n b hb0 hb => ?_⟩
  refine ciSup_le fun K => ?_
  have hcoe : ((MvPowerSeries.coeff K (((⟨Ufun, hres⟩ : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
        - ∑ l ∈ Finset.range n, u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
      = ((S K : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        - ((MvPowerSeries.coeff K ((∑ l ∈ Finset.range n, u l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
          : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) := by
    rw [coe_RPS_sub, coeff_sub_eq p F ϖ]
    rfl
  rw [hcoe, hpartial n K]
  exact hS K n b hb0 hb

/-- **Submultiplicativity of the Gauss norm**. -/
theorem gaussNormRPS_mul_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) (hg : MvPowerSeries.IsRestricted g) :
    gaussNormRPS p F ϖ hρ0 hρ1 (f * g)
      ≤ gaussNormRPS p F ϖ hρ0 hρ1 f * gaussNormRPS p F ϖ hρ0 hρ1 g := by
  refine ciSup_le fun K => ?_
  rw [MvPowerSeries.coeff_mul]
  have hcoe : ((∑ q ∈ Finset.antidiagonal K,
        MvPowerSeries.coeff q.1 f * MvPowerSeries.coeff q.2 g
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
      = ∑ q ∈ Finset.antidiagonal K,
        ((MvPowerSeries.coeff q.1 f : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1)
        * ((MvPowerSeries.coeff q.2 g : ↥(ArSub p F ϖ hρ0 hρ1))
          : hatK p F hρ0 hρ1) := by
    push_cast
    rfl
  rw [hcoe]
  refine Valuation.map_sum_le (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal) ?_
  intro q _
  rw [Valuation.map_mul]
  exact mul_le_mul (valued_coeff_le_gaussNormRPS p F ϖ hf q.1)
    (valued_coeff_le_gaussNormRPS p F ϖ hg q.2) zero_le zero_le

/-- The Gauss norm of a finite sum is bounded by the supremum of the norms. -/
theorem gaussNormRPS_finset_sum_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {ι : Type*} (s : Finset ι)
    (f : ι → ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
    (B : NNReal)
    (hf : ∀ i ∈ s, gaussNormRPS p F ϖ hρ0 hρ1
      ((f i : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
        : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ B) :
    gaussNormRPS p F ϖ hρ0 hρ1
      (((∑ i ∈ s, f i : ↥(restrictedMvPowerSeriesSubring k
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
        ↥(ArSub p F ϖ hρ0 hρ1))) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hzero : ((0 : ↥(restrictedMvPowerSeriesSubring k
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
        ↥(ArSub p F ϖ hρ0 hρ1)) = 0 := rfl
    rw [Finset.sum_empty, hzero, gaussNormRPS_zero]
    exact zero_le
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have hcoe : (((f a + ∑ i ∈ t, f i : ↥(restrictedMvPowerSeriesSubring k
          ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k)
          ↥(ArSub p F ϖ hρ0 hρ1))
        = ((f a : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
            : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          + ((∑ i ∈ t, f i : ↥(restrictedMvPowerSeriesSubring k
            ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k)
            ↥(ArSub p F ϖ hρ0 hρ1)) := rfl
    rw [hcoe]
    refine le_trans (gaussNormRPS_add_le p F ϖ (f a).2
      (∑ i ∈ t, f i).2) (max_le (hf a (Finset.mem_insert_self a t)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

/-- Swapping a finite double sum and factoring the common right factor. -/
theorem sum_range_sum_attach_mul {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (n : ℕ) (a : ℕ → ι → R) (g : ι → R) :
    (∑ l ∈ Finset.range n, ∑ i ∈ s, a l i * g i)
      = ∑ i ∈ s.attach, (∑ l ∈ Finset.range n, a l (i : ι)) * g (i : ι) := by
  rw [Finset.sum_comm,
    ← Finset.sum_attach s (fun i => ∑ l ∈ Finset.range n, a l i * g i)]
  exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

/-- The telescoping split of a combination difference. -/
theorem telescope_split {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (y : R) (P U g : ι → R) :
    y - ∑ i ∈ s, U i * g i
      = (y - ∑ i ∈ s, P i * g i) + ∑ i ∈ s, (P i - U i) * g i := by
  have h : (∑ i ∈ s, (P i - U i) * g i)
      = (∑ i ∈ s, P i * g i) - ∑ i ∈ s, U i * g i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => sub_mul _ _ _
  rw [h]
  ring

/-- Coercion of a subring sum (small context). -/
theorem coe_RPS_add {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (a b : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    ((a + b : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = (a : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) + (b : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := rfl

/-- Coercion of a subring product (small context). -/
theorem coe_RPS_mul {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (a b : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    ((a * b : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = (a : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) * (b : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := rfl

/-- Coercion of a subring negation (small context). -/
theorem coe_RPS_neg {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (a : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :
    ((-a : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = -((a : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) := rfl

set_option maxHeartbeats 8000000 in
/-- **Kedlaya Lemma 3.9**: the Gröbner generators generate the ideal. -/
theorem ideal_eq_span_groebner {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {ε : NNReal} {H : Ideal ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))} {G : Finset ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))}
    (hGH : ∀ g ∈ G, g ∈ H)
    (hG0 : ∀ g ∈ G, ((g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≠ 0))
    (hGtail : ∀ g ∈ G, ∀ K : Fin k →₀ ℕ,
      (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn
          (leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
        < (MonomialOrder.degLex : MonomialOrder (Fin k)).toSyn K →
      Valued.v ((MvPowerSeries.coeff K (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)
        ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
    (hGdeg : ∀ g ∈ G, ((degAr p F ϖ hρ0 hρ1 ((leadCoeffRPS p F ϖ hρ0 hρ1
          (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1) : ℕ∞)
        = dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))))
    (hGdom : ∀ J : Fin k →₀ ℕ, dIdx p F ϖ hρ0 hρ1 H J ≠ ⊤ →
      ∃ g ∈ G, leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ J
        ∧ dIdx p F ϖ hρ0 hρ1 H (leadIdxRPS p F ϖ hρ0 hρ1 (g : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
          = dIdx p F ϖ hρ0 hρ1 H J)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    H = Ideal.span (G : Set ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) := by
  classical
  refine le_antisymm ?_ ?_
  · -- every ideal element is a combination
    intro y₀ hy₀H
    set B := gaussNormRPS p F ϖ hρ0 hρ1 (y₀ : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) with hB
    by_cases hB0 : B = 0
    · have hy₀0 : y₀ = 0 :=
        Subtype.ext ((gaussNormRPS_eq_zero_iff p F ϖ y₀.2).mp hB0)
      rw [hy₀0]
      exact Ideal.zero_mem _
    have hBpos : 0 < B := pos_iff_ne_zero.mpr hB0
    -- one reduction round, as a function on the ideal
    have step : ∀ z : {z : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) // z ∈ H},
        ∃ (a : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) → ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) (z' : {z : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) // z ∈ H}),
          (z' : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) = (z : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) - ∑ g ∈ G, a g * g
          ∧ (∀ g ∈ G, gaussNormRPS p F ϖ hρ0 hρ1 ((a g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
              * gaussNormRPS p F ϖ hρ0 hρ1 ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            ≤ gaussNormRPS p F ϖ hρ0 hρ1 (((z : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))
          ∧ gaussNormRPS p F ϖ hρ0 hρ1 (((z' : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            ≤ ε * gaussNormRPS p F ϖ hρ0 hρ1 (((z : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := by
      rintro ⟨z, hzH⟩
      obtain ⟨a, hab, harem⟩ := approx_generation p F ϖ hGH hG0 hGtail hGdeg hGdom
        hε0 hε1 hzH
      refine ⟨a, ⟨z - ∑ g ∈ G, a g * g, ?_⟩, rfl, hab, harem⟩
      exact Ideal.sub_mem H hzH
        (Ideal.sum_mem H fun g hg => Ideal.mul_mem_left H _ (hGH g hg))
    choose α σ hσeq hαb hσn using step
    obtain ⟨Y, hY0, hYsucc⟩ : ∃ Y : ℕ → {z : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) // z ∈ H},
        Y 0 = ⟨y₀, hy₀H⟩ ∧ ∀ l, Y (l + 1) = σ (Y l) :=
      ⟨fun l => σ^[l] ⟨y₀, hy₀H⟩, rfl,
        fun l => Function.iterate_succ_apply' σ l ⟨y₀, hy₀H⟩⟩
    have hYeq : ∀ l, ((Y (l + 1) : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
        = (Y l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) - ∑ g ∈ G, α (Y l) g * g := by
      intro l
      rw [hYsucc l]
      exact hσeq (Y l)
    have hYnorm : ∀ l, gaussNormRPS p F ϖ hρ0 hρ1 (((Y l : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ ε ^ l * B := by
      intro l
      induction l with
      | zero =>
        rw [pow_zero, one_mul, hY0]
      | succ n ih =>
        rw [hYsucc n]
        refine le_trans (hσn (Y n)) ?_
        calc ε * gaussNormRPS p F ϖ hρ0 hρ1 (((Y n : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
            ≤ ε * (ε ^ n * B) := mul_le_mul_of_nonneg_left ih zero_le
          _ = ε ^ (n + 1) * B := by ring
    have hAnorm : ∀ (l : ℕ), ∀ g ∈ G, gaussNormRPS p F ϖ hρ0 hρ1 ((α (Y l) g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
        * gaussNormRPS p F ϖ hρ0 hρ1 ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ ε ^ l * B := by
      intro l g hg
      exact le_trans (hαb (Y l) g hg) (hYnorm l)
    -- telescoping
    have htel : ∀ n, (Y n : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
        = y₀ - ∑ l ∈ Finset.range n, ∑ g ∈ G, α (Y l) g * g := by
      intro n
      induction n with
      | zero =>
        rw [hY0, Finset.range_zero, Finset.sum_empty, sub_zero]
      | succ m ih =>
        rw [hYeq m, ih, Finset.sum_range_succ]
        ring
    -- the coefficient series converge
    have hgeo : Filter.Tendsto (fun l => ε ^ l * B) Filter.atTop (nhds 0) := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (zero_le : (0 : NNReal) ≤ ε) hε1).mul_const B
      rwa [zero_mul] at h1
    have hlim : ∀ g ∈ G, ∃ U : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)), ∀ (n : ℕ) (b : NNReal), 0 < b →
        (∀ l, n ≤ l → ε ^ l * B * (gaussNormRPS p F ϖ hρ0 hρ1 ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))⁻¹ ≤ b) →
        gaussNormRPS p F ϖ hρ0 hρ1 ((((U - ∑ l ∈ Finset.range n, α (Y l) g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) ≤ b := by
      intro g hg
      refine exists_rps_series_limit p F ϖ (C := fun l =>
        ε ^ l * B * (gaussNormRPS p F ϖ hρ0 hρ1 ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))⁻¹) (fun l => ?_) ?_
      · have hgpos : 0 < gaussNormRPS p F ϖ hρ0 hρ1 ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :=
          pos_iff_ne_zero.mpr (gaussNormRPS_ne_zero p F ϖ (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))).2 (hG0 g hg))
        have hcancel : ε ^ l * B * (gaussNormRPS p F ϖ hρ0 hρ1
            ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
              : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))⁻¹
            * gaussNormRPS p F ϖ hρ0 hρ1
            ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
              : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = ε ^ l * B := by
          rw [mul_assoc, inv_mul_cancel₀ hgpos.ne', mul_one]
        refine le_of_mul_le_mul_right ?_ hgpos
        rw [hcancel]
        exact hAnorm l g hg
      · have h2 := hgeo.mul_const ((gaussNormRPS p F ϖ hρ0 hρ1 ((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))⁻¹)
        rwa [zero_mul] at h2
    -- pick the limits and assemble
    have hlim' : ∀ g : {g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) // g ∈ G},
        ∃ U : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)), ∀ (n : ℕ) (b : NNReal), 0 < b →
          (∀ l, n ≤ l → ε ^ l * B * (gaussNormRPS p F ϖ hρ0 hρ1 (((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))⁻¹ ≤ b) →
          gaussNormRPS p F ϖ hρ0 hρ1 ((((U - ∑ l ∈ Finset.range n, α (Y l) (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
            : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))) ≤ b := fun g => hlim g.1 g.2
    choose U hU using hlim'
    have hgpos : ∀ g : {g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)) // g ∈ G},
        0 < gaussNormRPS p F ϖ hρ0 hρ1 (((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) := fun g =>
      pos_iff_ne_zero.mpr (gaussNormRPS_ne_zero p F ϖ (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))).2 (hG0 g.1 g.2))
    -- the candidate combination
    obtain ⟨T, hT⟩ : ∃ T : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)), T = ∑ g ∈ G.attach, U g * (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :=
      ⟨_, rfl⟩
    have hattach : ∀ l : ℕ, (∑ g ∈ G, α (Y l) g * g)
        = ∑ g ∈ G.attach, α (Y l) (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) * (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :=
      fun l => (Finset.sum_attach G (fun g => α (Y l) g * g)).symm
    have hkey : ∀ n : ℕ, gaussNormRPS p F ϖ hρ0 hρ1 (((y₀ - T : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) ≤ ε ^ n * B := by
      intro n
      obtain ⟨Rn, hRn⟩ : ∃ Rn : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)), Rn = ∑ g ∈ G.attach,
          ((∑ l ∈ Finset.range n, α (Y l) (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) - U g) * (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) :=
        ⟨_, rfl⟩
      have h1 : ∀ l ∈ Finset.range n, (∑ g ∈ G, α (Y l) g * g)
          = ∑ g ∈ G, α (Y l) g * g := fun l _ => rfl
      have hYn : (Y n : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
          = y₀ - ∑ i ∈ G.attach, (∑ l ∈ Finset.range n, α (Y l) (i : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))))
            * (i : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) := by
        rw [htel n, sum_range_sum_attach_mul G n (fun l g => α (Y l) g)
          (fun g => g)]
      have hsplit : (y₀ - T : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) = (Y n : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) + Rn := by
        rw [hYn, hRn, hT]
        exact telescope_split G.attach y₀
          (fun i => ∑ l ∈ Finset.range n, α (Y l) (i : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))))
          (fun i => U i) (fun i => (i : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))))
      rw [hsplit, coe_RPS_add]
      refine le_trans (gaussNormRPS_add_le p F ϖ (Y n : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))).2 Rn.2)
        (max_le (hYnorm n) ?_)
      rw [hRn]
      refine gaussNormRPS_finset_sum_le p F ϖ G.attach _ _ fun g _ => ?_
      rw [coe_RPS_mul]
      refine le_trans (gaussNormRPS_mul_le p F ϖ
        ((∑ l ∈ Finset.range n, α (Y l) (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) - U g).2 (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))).2) ?_
      have hUb : gaussNormRPS p F ϖ hρ0 hρ1 ((((∑ l ∈ Finset.range n, α (Y l) (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) - U g
            : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1))
          ≤ ε ^ n * B * (gaussNormRPS p F ϖ hρ0 hρ1 (((g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)))⁻¹ := by
        have h1 : ((∑ l ∈ Finset.range n, α (Y l) (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) - U g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))
            = -((U g - ∑ l ∈ Finset.range n, α (Y l) (g : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) := by
          ring
        rw [h1, coe_RPS_neg, gaussNormRPS_neg]
        refine hU g n _ (mul_pos (mul_pos (pow_pos hε0 n) hBpos)
          (inv_pos.mpr (hgpos g))) fun l hl => ?_
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ?_ zero_le) zero_le
        exact pow_le_pow_of_le_one zero_le hε1.le hl
      refine le_trans (mul_le_mul_of_nonneg_right hUb zero_le) ?_
      rw [mul_assoc, inv_mul_cancel₀ (hgpos g).ne', mul_one]
    have hzero : (y₀ - T : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))) = 0 := by
      have hnorm0 : gaussNormRPS p F ϖ hρ0 hρ1 (((y₀ - T : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) = 0 := by
        by_contra hne
        have hpos : 0 < gaussNormRPS p F ϖ hρ0 hρ1 (((y₀ - T : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1)))) : MvPowerSeries (Fin k) ↥(ArSub p F ϖ hρ0 hρ1)) :=
          pos_iff_ne_zero.mpr hne
        obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
          (hgeo.eventually_lt_const hpos)
        exact absurd (lt_of_le_of_lt (hkey n) (hn n le_rfl)) (lt_irrefl _)
      exact Subtype.ext ((gaussNormRPS_eq_zero_iff p F ϖ
        (y₀ - T : ↥(restrictedMvPowerSeriesSubring k ↥(ArSub p F ϖ hρ0 hρ1))).2).mp hnorm0)
    have hy₀T : y₀ = T := sub_eq_zero.mp hzero
    rw [hy₀T, hT]
    refine Ideal.sum_mem _ fun g _ => Ideal.mul_mem_left _ _ ?_
    exact Ideal.subset_span g.2
  · rw [Ideal.span_le]
    intro g hg
    exact hGH g (Finset.mem_coe.mp hg)

set_option maxHeartbeats 1000000 in
/-- **Kedlaya Theorem 3.2** for the campaign radius: the Tate algebra over `A^r`
in any number of variables is noetherian. -/
theorem isNoetherianRing_restrictedMvPowerSeries {k : ℕ} {ρ : NNReal}
    {hρ0 : 0 < ρ} {hρ1 : ρ < 1} :
    IsNoetherianRing ↥(restrictedMvPowerSeriesSubring k
      ↥(ArSub p F ϖ hρ0 hρ1)) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro H
  obtain ⟨G, ε, hε0, hε1, hGH, hG0, hGtail, hGdeg, hGdom⟩ :=
    exists_groebner_family p F ϖ H
  exact ⟨G, (ideal_eq_span_groebner p F ϖ hGH hG0 hGtail hGdeg hGdom
    hε0 hε1).symm⟩

/-- **`A^r` is strongly noetherian** (Kedlaya Theorem 3.2). -/
instance isStronglyNoetherian_ArSub {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} :
    IsStronglyNoetherian ↥(ArSub p F ϖ hρ0 hρ1) where
  isNoetherianRing_restricted := fun k =>
    isNoetherianRing_restrictedMvPowerSeries p F ϖ (k := k)

end FarguesFontaine

end
