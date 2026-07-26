/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.WellQuasiOrder

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

end FarguesFontaine

end
