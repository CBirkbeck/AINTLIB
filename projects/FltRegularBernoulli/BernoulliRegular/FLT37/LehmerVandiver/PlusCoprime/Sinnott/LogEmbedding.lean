import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Logarithmic embedding of cyclotomic-unit family elements

This file computes the logarithmic embedding of the `K⁺`-side cyclotomic-unit
family and rewrites its regulator determinant in terms of the corresponding
real cyclotomic units over `K`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField NumberField.InfinitePlace

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- For totally real `K⁺`, the multiplicity of any infinite place is `1`. -/
theorem mult_eq_one_of_maximalRealSubfield (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    mult w = 1 := by
  rw [mult]
  simp only [IsTotallyReal.isReal w, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- The logarithmic embedding of a unit over `K⁺` at a non-distinguished
infinite place is `Real.log` of its value there. -/
theorem logEmbedding_apply_maximalRealSubfield
    (u : (𝓞 (NumberField.maximalRealSubfield K))ˣ)
    (w : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    NumberField.Units.logEmbedding (NumberField.maximalRealSubfield K)
        (Additive.ofMul u) w =
      Real.log (w.val (u : NumberField.maximalRealSubfield K)) := by
  rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_component]
  rw [mult_eq_one_of_maximalRealSubfield (K := K)]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The value of a `K⁺` infinite place on a cyclotomic-family unit factors
through the corresponding infinite place of `K`. -/
theorem infinitePlace_cyclotomicUnitFamilyKplus_eq
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (w : InfinitePlace (NumberField.maximalRealSubfield K))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    w ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
        (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
        NumberField.maximalRealSubfield K) =
      ((NumberField.IsCMField.equivInfinitePlace K).symm w)
        (algebraMap (NumberField.maximalRealSubfield K) K
          ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
            (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
            NumberField.maximalRealSubfield K)) := by
  rw [NumberField.IsCMField.equivInfinitePlace_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The value of an infinite place of `K⁺` on `cyclotomicUnitFamilyKplus j`
equals the value of the corresponding place of K on `realCyclotomicUnit (j+2)`. -/
theorem infinitePlace_cyclotomicUnitFamilyKplus_eq_realCyclotomicUnit
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (w : InfinitePlace (NumberField.maximalRealSubfield K))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    w ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
        (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
        NumberField.maximalRealSubfield K) =
      ((NumberField.IsCMField.equivInfinitePlace K).symm w)
        ((FLT37.realCyclotomicUnit p K
          ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank
              (K := K)).trans
            (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
              (p := p) (K := K)))) + 2) : 𝓞 K) : K) := by
  rw [infinitePlace_cyclotomicUnitFamilyKplus_eq]
  congr 1
  have h := algebraMap_cyclotomicUnitFamilyKplus p K j hp_odd hp_three
  rw [← IsScalarTower.algebraMap_apply
    (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K]
  rw [IsScalarTower.algebraMap_apply
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) K]
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The log embedding of `cyclotomicUnitFamilyKplus j` at a place `w` of `K⁺`
equals `Real.log (w'(realCyclotomicUnit (j+2)))` where `w'` is the
corresponding place of K. -/
theorem logEmbedding_cyclotomicUnitFamilyKplus_apply
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (w : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    NumberField.Units.logEmbedding (NumberField.maximalRealSubfield K)
        (Additive.ofMul (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j)) w =
      Real.log
        (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
          ((FLT37.realCyclotomicUnit p K
            ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2) : 𝓞 K) : K)) := by
  rw [logEmbedding_apply_maximalRealSubfield (K := K)]
  congr 1
  exact infinitePlace_cyclotomicUnitFamilyKplus_eq_realCyclotomicUnit p K j w.val hp_odd hp_three

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- The log-embedding matrix of `cyclotomicUnitFamilyKplusFinRank` has
entries given by `Real.log (w' (realCyclotomicUnit (j+2)))` where `w'`
is the corresponding infinite place of `K`. -/
theorem regOfFamily_cyclotomicUnitFamilyKplus_eq_det
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      |(Matrix.of fun (i : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((FLT37.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))).det| := by
  letI : DecidableEq {w : InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := Classical.decEq _
  rw [NumberField.Units.regOfFamily_eq_det']
  congr 1
  congr 1
  funext i
  funext w
  simp only [Matrix.of_apply]
  exact logEmbedding_cyclotomicUnitFamilyKplus_apply p K
    ((NumberField.Units.equivFinRank (NumberField.maximalRealSubfield K)).symm i)
    w hp_odd hp_three

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- Multiplicativity of an infinite place applied to
`zeta_sub_one_mul_cyclotomicUnit`. -/
theorem norm_cyclotomicUnit_mul_zeta_sub_one (k : ℕ) (w : InfinitePlace K) :
    w ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) *
        w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1) =
      w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1) := by
  rw [mul_comm, ← map_mul]
  congr 1
  exact_mod_cast FLT37.zeta_sub_one_mul_cyclotomicUnit p K k

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- For `2 ≤ p`, the `K`-element `ζ - 1` is non-zero. -/
theorem zeta_sub_one_ne_zero_K (hp_two : 2 ≤ p) :
    ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1) ≠ 0 := by
  intro h
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have h_OK_zero : ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 = 0 := by
    apply h_inj
    rw [map_zero, map_sub, map_one]
    exact h
  exact (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.sub_one_ne_zero
    (by omega) h_OK_zero

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- For `k` coprime to `p` and `2 ≤ p`, `cyclotomicUnit p K k` is non-zero in
`K`. -/
theorem cyclotomicUnit_ne_zero_K
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 := by
  have hU := FLT37.isUnit_cyclotomicUnit p K k hk hp_two
  intro h
  apply hU.ne_zero
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  apply h_inj
  rw [map_zero]
  exact h

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- For `k` coprime to `p` and `2 ≤ p`, the `K`-element `ζ^k - 1` is
non-zero. -/
theorem pow_zeta_sub_one_ne_zero_K
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1) ≠
      0 := by
  intro h
  have hζ_pow_K : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k = 1 :=
    sub_eq_zero.mp h
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hζ_pow_OK : ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
    apply h_inj
    rw [map_pow, map_one]
    exact hζ_pow_K
  have hdvd : p ∣ k :=
    ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd
      k).mp hζ_pow_OK
  have hp_prime : Nat.Prime p := hp.out
  have hp_one_lt : 1 < p := hp_prime.one_lt
  have h_gcd_ge_p : p ≤ Nat.gcd k p := Nat.le_of_dvd
    (Nat.gcd_pos_of_pos_right k hp_prime.pos)
    (Nat.dvd_gcd hdvd dvd_rfl)
  rw [hk] at h_gcd_ge_p
  omega

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- The logarithm of `w (cyclotomicUnit p K k)` is the difference of the
logarithms of `w (ζ^k - 1)` and `w (ζ - 1)`. -/
theorem log_norm_cyclotomicUnit_eq_sub
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    Real.log (w ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K)) =
      Real.log
        (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1)) -
        Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1)) := by
  have h_w_cycU : w ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 := by
    refine (InfinitePlace.pos_iff.mpr ?_).ne'
    exact cyclotomicUnit_ne_zero_K p K k hk hp_two
  have h_w_zsub :
      w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1) ≠ 0 := by
    refine (InfinitePlace.pos_iff.mpr ?_).ne'
    exact zeta_sub_one_ne_zero_K p K hp_two
  have h_prod := norm_cyclotomicUnit_mul_zeta_sub_one p K k w
  have h_log_prod : Real.log (w ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K)) +
      Real.log
        (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1)) =
        Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1)) := by
    rw [← Real.log_mul h_w_cycU h_w_zsub, h_prod]
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- The logarithm of `w (realCyclotomicUnit p K k)` is twice the logarithm of
`w (cyclotomicUnit p K k)`. -/
theorem log_infinitePlace_realCyclotomicUnit
    (k : ℕ) (w : InfinitePlace K) :
    Real.log (w ((FLT37.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log (w ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K)) := by
  have h_eq : ((FLT37.realCyclotomicUnit p K k : 𝓞 K) : K) =
      ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) *
        complexConj K ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) := by
    unfold FLT37.realCyclotomicUnit
    push_cast
    rw [← coe_ringOfIntegersComplexConj]
  rw [h_eq, map_mul, infinitePlace_complexConj, ← sq, Real.log_pow]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Per-entry decomposition of the logarithm of `realCyclotomicUnit p K k` in
terms of `ζ^k - 1` and `ζ - 1`. -/
theorem log_realCyclotomicUnit_eq_sub_decomp
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    Real.log (w ((FLT37.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1)) -
        2 * Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1)) := by
  rw [log_infinitePlace_realCyclotomicUnit, log_norm_cyclotomicUnit_eq_sub p K k hk hp_two w]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Non-vanishing of `cyclotomicUnit p K k` at the `K`-place corresponding to a
`K⁺` infinite place. -/
theorem cyclotomicUnit_at_Kplus_place_ne_zero
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)
      ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 :=
  (InfinitePlace.pos_iff.mpr (cyclotomicUnit_ne_zero_K p K k hk hp_two)).ne'

set_option backward.isDefEq.respectTransparency false in
/-- Non-vanishing of `ζ - 1` at the `K`-place corresponding to a `K⁺` infinite
place. -/
theorem zeta_sub_one_at_Kplus_place_ne_zero (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1) ≠ 0 :=
  (InfinitePlace.pos_iff.mpr (zeta_sub_one_ne_zero_K p K hp_two)).ne'

set_option backward.isDefEq.respectTransparency false in
/-- Non-vanishing of `ζ^k - 1` at the `K`-place corresponding to a `K⁺`
infinite place. -/
theorem pow_zeta_sub_one_at_Kplus_place_ne_zero
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1) ≠ 0 :=
  (InfinitePlace.pos_iff.mpr (pow_zeta_sub_one_ne_zero_K p K k hk hp_two)).ne'

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- Positivity of the absolute value of `cyclotomicUnit p K k` at a `K`
infinite place. -/
theorem cyclotomicUnit_at_place_pos (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace K) :
    0 < w ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) :=
  InfinitePlace.pos_iff.mpr (cyclotomicUnit_ne_zero_K p K k hk hp_two)

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- Positivity of the absolute value of `ζ - 1` at a `K` infinite place. -/
theorem zeta_sub_one_at_place_pos (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    0 < w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1) :=
  InfinitePlace.pos_iff.mpr (zeta_sub_one_ne_zero_K p K hp_two)

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- Positivity of the absolute value of `ζ^k - 1` at a `K` infinite place. -/
theorem pow_zeta_sub_one_at_place_pos (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace K) :
    0 < w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1) :=
  InfinitePlace.pos_iff.mpr (pow_zeta_sub_one_ne_zero_K p K k hk hp_two)

set_option backward.isDefEq.respectTransparency false in
/-- The cyclotomic-unit logarithm decomposition at a `K⁺` infinite place. -/
theorem log_cyclotomicUnit_at_Kplus_place_eq_sub
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
        ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K)) =
      Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1)) -
        Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1)) :=
  log_norm_cyclotomicUnit_eq_sub p K k hk hp_two
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)

set_option backward.isDefEq.respectTransparency false in
/-- The real-cyclotomic-unit logarithm decomposition at a `K⁺` infinite
place. -/
theorem log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
        ((FLT37.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1)) -
        2 * Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1)) :=
  log_realCyclotomicUnit_eq_sub_decomp p K k hk hp_two
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit Kummer-Dirichlet determinant evaluation for the
cyclotomic-unit family over `K⁺`. -/
def KummerDirichletDeterminant (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) * NumberField.Units.regulator
      (NumberField.maximalRealSubfield K)

set_option backward.isDefEq.respectTransparency false in
/-- `KummerDirichletDeterminant` and `SinnottRegulatorIdentity` are the same
equation in the present formulation. -/
theorem sinnottRegulatorIdentity_iff_kummerDirichletDeterminant
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    KummerDirichletDeterminant p K hp_odd hp_three ↔
      SinnottRegulatorIdentity p K hp_odd hp_three :=
  Iff.rfl

end Sinnott

end FLT37

end BernoulliRegular

end
