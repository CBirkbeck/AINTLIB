/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

end FarguesFontaine

end
