import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem


/-!
# Logarithmic embedding of cyclotomic-unit family elements

For the K⁺-side cyclotomic-unit family, we compute the logarithmic
embedding `logEmbedding K⁺ : (𝓞 K⁺)ˣ → logSpace K⁺` explicitly.

For totally real K⁺, all infinite places are real (`mult w = 1`), so

  `logEmbedding K⁺ (family j) w = Real.log (w (family j))`

for `w : InfinitePlace K⁺` with `w ≠ w₀` (the distinguished place).

This file is **LV-SIN-A** of the Cor 8.19 / Sinnott bridge construction.
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
  simp [IsTotallyReal.isReal w]

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- The logarithmic embedding of a unit `u : (𝓞 K⁺)ˣ` at a non-distinguished
infinite place `w` is just `Real.log (w u)`, since `mult w = 1` for
totally real K⁺. -/
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
/-- For the cyclotomic-unit family element `cyclotomicUnitFamilyKplusFinRank j`,
the value of an infinite place `w` of K⁺ on this element factors through
algebraMap to K. -/
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
/-- The value of an infinite place of K⁺ on `cyclotomicUnitFamilyKplus j`
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
  -- Goal: algebraMap K⁺ K (algebraMap 𝓞 K⁺ K⁺ x) = (realCyclotomicUnit (...) : K).
  -- Use scalar tower: (𝓞 K⁺) → K⁺ → K = (𝓞 K⁺) → (𝓞 K) → K.
  have h := algebraMap_cyclotomicUnitFamilyKplus p K j hp_odd hp_three
  -- Rewrite via IsScalarTower.
  rw [← IsScalarTower.algebraMap_apply
    (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K]
  rw [IsScalarTower.algebraMap_apply
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) K]
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The log embedding of `cyclotomicUnitFamilyKplus j` at place `w` of K⁺
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

/-! ## Determinant matrix structure

The matrix `M` whose determinant equals `regOfFamily(family)`:

  `M[w, j] = logEmbedding K⁺ (family j) w`
          = `Real.log (w'_w (realCyclotomicUnit (j+2)))`

where `w'_w = (equivInfinitePlace K).symm w` is the K-side place
corresponding to `w`. The determinant of this matrix is exactly
`±regOfFamily(family)` by `regOfFamily_eq_det'` from mathlib. -/

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- The log-embedding matrix of `cyclotomicUnitFamilyKplusFinRank` has
entries given by `Real.log (w' (realCyclotomicUnit (j+2)))` where `w'`
is the K-side place. The matrix is square: rows and columns both
indexed by `{w : InfinitePlace K⁺ // w ≠ w₀}` (places of K⁺ excluding w₀).
The "row place" determines which family element via `equivFinRank.symm`. -/
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

/-! ## PF-1-helper: `cyclotomicUnit` norm at infinite places

From the geometric-series identity
`cyclotomicUnit k · (ζ - 1) = ζ^k - 1`
(shipped in `FLT37/PrimaryUnits.lean`) and the multiplicativity of
infinite places, we get
`w(cyclotomicUnit k) · w(ζ - 1) = w(ζ^k - 1)`
for any infinite place `w` of K. This is the key step for the matrix
decomposition `M = 2·A - 2·B` in PF-1-MatrixDecomp:
`log w(cyclotomicUnit k) = log w(ζ^k - 1) - log w(ζ - 1)`. -/

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **PF-1-helper.** Multiplicativity of `w` applied to
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
/-- **PF-1-helper (zeta - 1 nonzero).** For p ≥ 2 (i.e., any prime p),
the K-element `ζ - 1` is non-zero. -/
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
/-- **PF-1-helper (cyclotomicUnit nonzero in K).** For `k` coprime to
`p` and `p ≥ 2`, `cyclotomicUnit p K k` is non-zero in K.

Direct from `isUnit_cyclotomicUnit` (unit is non-zero) +
algebraMap-of-nonzero is non-zero. -/
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
/-- **PF-1-helper (ζ^k - 1 nonzero in K).** For `k` coprime to `p` and
`p ≥ 2`, `ζ^k - 1` is non-zero in K (since ζ is a primitive p-th root
of unity in K, ζ^k = 1 iff p ∣ k, contradicting coprimality).

Follows from `IsPrimitiveRoot.pow_eq_one_iff_dvd` + algebraMap. -/
theorem pow_zeta_sub_one_ne_zero_K
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1) ≠
      0 := by
  intro h
  have hζ_pow_K : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k = 1 :=
    sub_eq_zero.mp h
  -- Lift to 𝓞 K via algebraMap injective.
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hζ_pow_OK : ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
    apply h_inj
    rw [map_pow, map_one]
    exact hζ_pow_K
  -- Now apply pow_eq_one_iff_dvd
  have hdvd : p ∣ k :=
    ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd
      k).mp hζ_pow_OK
  -- Contradicts coprimality: p ∣ k + gcd(k, p) = 1 → p ∣ 1 → p = 1, contradiction.
  have hp_prime : Nat.Prime p := hp.out
  have hp_one_lt : 1 < p := hp_prime.one_lt
  have h_gcd_ge_p : p ≤ Nat.gcd k p := Nat.le_of_dvd
    (Nat.gcd_pos_of_pos_right k hp_prime.pos)
    (Nat.dvd_gcd hdvd dvd_rfl)
  rw [hk] at h_gcd_ge_p
  omega

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **PF-1-helper (log form).** From the product identity
`w(cyclotomicUnit k) · w(ζ - 1) = w(ζ^k - 1)`:
`log w(cyclotomicUnit k) = log w(ζ^k - 1) - log w(ζ - 1)`.

Requires `k.Coprime p` and `p ≥ 2` so that `cyclotomicUnit k` is a
unit (hence non-zero in K). The non-zero condition for `ζ - 1`
is shipped as `zeta_sub_one_ne_zero_K`. -/
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


/-! ## PF-1-Real: `realCyclotomicUnit` log via `cyclotomicUnit` log

`realCyclotomicUnit p K k = cyclotomicUnit p K k · σ(cyclotomicUnit p K k)`
where `σ` is complex conjugation on K (CM). For any infinite place w
of K (necessarily complex since K is CM cyclotomic of conductor p),
complex conjugation preserves the place's absolute value
(mathlib's `infinitePlace_complexConj`). Hence
`w(realCyclotomicUnit k) = w(cyclotomicUnit k)^2`, and taking log
gives the factor of 2 below. This is ticket PF-1-Real from the
`KummerDirichletDeterminant` sub-decomposition. -/

set_option backward.isDefEq.respectTransparency false in
/-- **PF-1-Real.** `Real.log (w (realCyclotomicUnit k)) =
2 · Real.log (w (cyclotomicUnit k))` for any infinite place `w` of K.

Proof: σ-symmetrization + `infinitePlace_complexConj` + `Real.log_pow`. -/
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
/-- **PF-1-MatrixDecomp (per-entry form).** Combining PF-1-Real
(`log_infinitePlace_realCyclotomicUnit`) with PF-1-helper-log
(`log_norm_cyclotomicUnit_eq_sub`):
`log w(realCyclotomicUnit k) = 2 · log w(ζ^k - 1) - 2 · log w(ζ - 1)`.

This is the per-entry form of the matrix decomposition `M = 2·A - 2·B`
for the log-embedding matrix of `cyclotomicUnitFamilyKplus`. -/
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
/-- **PF-1-helper K⁺-place.** w'(cycU k) ≠ 0 for w' = equivInfinitePlace.symm w. -/
theorem cyclotomicUnit_at_Kplus_place_ne_zero
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)
      ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 :=
  (InfinitePlace.pos_iff.mpr (cyclotomicUnit_ne_zero_K p K k hk hp_two)).ne'

set_option backward.isDefEq.respectTransparency false in
/-- **PF-1-helper K⁺-place.** w'(ζ - 1) ≠ 0. -/
theorem zeta_sub_one_at_Kplus_place_ne_zero (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1) ≠ 0 :=
  (InfinitePlace.pos_iff.mpr (zeta_sub_one_ne_zero_K p K hp_two)).ne'

set_option backward.isDefEq.respectTransparency false in
/-- **PF-1-helper K⁺-place.** w'(ζ^k - 1) ≠ 0 for k coprime to p. -/
theorem pow_zeta_sub_one_at_Kplus_place_ne_zero
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1) ≠ 0 :=
  (InfinitePlace.pos_iff.mpr (pow_zeta_sub_one_ne_zero_K p K k hk hp_two)).ne'

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **PF-1-helper.** w(cycU k) > 0 at a K-place (positivity from ne_zero). -/
theorem cyclotomicUnit_at_place_pos (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace K) :
    0 < w ((FLT37.cyclotomicUnit p K k : 𝓞 K) : K) :=
  InfinitePlace.pos_iff.mpr (cyclotomicUnit_ne_zero_K p K k hk hp_two)

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **PF-1-helper.** w(ζ - 1) > 0 at a K-place. -/
theorem zeta_sub_one_at_place_pos (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    0 < w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) - 1) :=
  InfinitePlace.pos_iff.mpr (zeta_sub_one_ne_zero_K p K hp_two)

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **PF-1-helper.** w(ζ^k - 1) > 0 at a K-place for k coprime to p. -/
theorem pow_zeta_sub_one_at_place_pos (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace K) :
    0 < w ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k - 1) :=
  InfinitePlace.pos_iff.mpr (pow_zeta_sub_one_ne_zero_K p K k hk hp_two)

set_option backward.isDefEq.respectTransparency false in
/-- **PF-1-helper K⁺-place version.** The cyclotomicUnit log
decomposition at a K⁺-place. -/
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
/-- **PF-1-MatrixDecomp at K⁺-places.** The per-entry decomposition
specialised to K⁺-places (the column index of the
`cyclotomicUnitFamilyKplusFinRank` log-embedding matrix). -/
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

/-! ## PF-1-MatrixDecomp (matrix-level, future work)

The full matrix-level decomposition `M = 2·A - 2·B` (with A k-dependent
and B column-constant of rank 1) would build on
`log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp` above, applied via
`Matrix.ext` to the matrix expression in
`regOfFamily_cyclotomicUnitFamilyKplus_eq_det`. The typeclass + nested
coercion infrastructure for the full matrix expression is involved and
left for future work; the per-entry decomposition above suffices for
the conceptual structure. -/

/-! ## Kummer-Dirichlet determinant identity (deferred analytic content)

The substantive analytic content of Sinnott's theorem reduces to a single
determinant identity. Combined with the explicit form of `regOfFamily`
above + the analytic CNF, this closes `SinnottRegulatorIdentity`. -/

set_option backward.isDefEq.respectTransparency false in
/-- **`KummerDirichletDeterminant`**: the explicit determinant evaluation.

For the matrix `M` from `regOfFamily_cyclotomicUnitFamilyKplus_eq_det`,
`|det M| = 2^((p-3)/2) · (hPlus K : ℝ) · regulator K⁺`.

The factor `2^((p-3)/2)` is the index `[C⁺ : ⟨squared cyclotomic family⟩]`:
the project's family `realCyclotomicUnit_k = c_k · σ(c_k)` is the
square of a "smaller" cyclotomic unit (under K-embedding,
`σ(realCyclotomicUnit_k) = |σ(c_k)|²`), so `⟨family⟩` has index
`2^((p-3)/2)` in the standard cyclotomic unit subgroup `C⁺`.
Combined with the Sinnott index identity `[U⁺ : C⁺] = h⁺`, the total
index is `2^((p-3)/2) · h⁺`, hence
`regOfFamily(family) = 2^((p-3)/2) · h⁺ · regulator(K⁺)`.

This is the cyclotomic case of Sinnott's class number formula. -/
def KummerDirichletDeterminant (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) * NumberField.Units.regulator
      (NumberField.maximalRealSubfield K)

set_option backward.isDefEq.respectTransparency false in
/-- **`KummerDirichletDeterminant` = `SinnottRegulatorIdentity`**: as
formulated, both Props are literally the same equation. -/
theorem sinnottRegulatorIdentity_iff_kummerDirichletDeterminant
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    KummerDirichletDeterminant p K hp_odd hp_three ↔
      SinnottRegulatorIdentity p K hp_odd hp_three :=
  Iff.rfl

end Sinnott

end FLT37

end BernoulliRegular

end
