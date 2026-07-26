/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

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

end FarguesFontaine

end
