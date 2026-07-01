module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.TraceCarry
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CoordinatePeel.CarryFreeTailEquality

/-!
# Coordinate-peel and normalized trace-carry tail products for the finite Dwork telescope.

Split from `DworkFactorization/Telescope.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

/-- If a `ℓ`-power-of-power of `x` vanishes, so does the next one: the
`ε ^ ℓ ^ (m + 1) = 0` boundary hypothesis propagates upward through `ℓ`. -/
private theorem pow_pow_ell_succ_eq_zero {M : Type*} [MonoidWithZero M]
    {x : M} {n : ℕ} (hx : x ^ ℓ ^ n = 0) : x ^ ℓ ^ (n + 1) = 0 := by
  rw [pow_succ, pow_mul, hx]
  exact zero_pow (Nat.Prime.ne_zero Fact.out)

/-- One depth-indexed coordinate peel for a Frobenius-shifted tail at the
zero boundary. -/
theorem artinHasseExp_frobenius_tail_succ_depth_eq_coeff_zero_mul_shifted_tail_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {D : ℕ} (hD : 0 < D) (N m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hzero : ε ^ (ℓ ^ (m + 1)) = 0) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
    let Z : ℕ → A := fun j =>
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
    let W : ℕ → A := fun j =>
      ∏ r ∈ Finset.Iic (D - 1),
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ (j + 1)) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
          (ℓ ^ (r + 2))
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
        ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
  let U : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
      ∏ r ∈ Finset.range D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  let Z : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      ((ε ^ (ℓ ^ j)) ^ ℓ *
        θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
  let V : ℕ → A := fun j =>
    ∏ r ∈ Finset.range D,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r)
              (c.coeff (r + 1)))))) ^
        (ℓ ^ (r + 2))
  let W : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic (D - 1),
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ (j + 1)) *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
        (ℓ ^ (r + 2))
  have hreindex :=
    F.artinHasseExp_frobenius_tail_succ_depth_eq_reindexed_tail
      N D m ε c
  have hdrop :=
    F.artinHasseExp_reindexed_tail_succ_depth_eq_range_of_zero_iterate
      N D m ε hzero c
  have hsplit :=
    F.artinHasseExp_reindexed_tail_range_depth_eq_coeff_zero_mul_shifted_tail_of_pos
      (D := D) hD N m ε c
  calc
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)))
        =
          ∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, U] using hreindex
    _ =
          ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, U] using hdrop
    _ =
          ∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j)) := by
          rfl
    _ =
          (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
            ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, cTail, Z, V, W] using hsplit

/-- Convert an accumulated non-shifted lower-depth tail into an accumulated
Frobenius-shifted root tail at the advanced parameter. -/
theorem artinHasseExp_tail_range_depth_eq_frobenius_root_tail_range_depth_pow
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let εnext : A := ε ^ ℓ
    let cRoot : WittVector ℓ k :=
      WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (εnext ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cRoot.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m + 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let εnext : A := ε ^ ℓ
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjlt : j < m := Finset.mem_range.mp hj
  have hparam : ε ^ (ℓ ^ (j + 1)) = εnext ^ (ℓ ^ j) := by
    dsimp [εnext]
    rw [← pow_mul, Nat.pow_succ]
    congr 1
    rw [Nat.mul_comm]
  have htail :=
    F.artinHasseExp_wittTeich_tail_depth_eq_frobenius_root_tail_pow
      (N := N) (D := D) (ε := εnext ^ (ℓ ^ j)) c
  have htail' :
      (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) =
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (εnext ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cRoot.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ ℓ := by
    simpa [A, θ, Eps, εnext, cRoot, hparam] using htail
  calc
    (∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ (j + 1)) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
          (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))
        =
          ((∏ r ∈ Finset.Iic D,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (εnext ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    (cRoot.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ ℓ) ^ (ℓ ^ (m - j)) := by
          rw [htail']
    _ =
          (∏ r ∈ Finset.Iic D,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (εnext ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    (cRoot.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m + 1 - j)) := by
          rw [← pow_mul, ← pow_succ', show (m - j) + 1 = m + 1 - j from by omega]

/-- At the zero boundary, the accumulated non-shifted lower-depth tail is the
next full Frobenius-shifted root tail at parameter `ε^ℓ`. -/
theorem artinHasseExp_tail_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hzero : ε ^ (ℓ ^ (m + 1)) = 0) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let εnext : A := ε ^ ℓ
    let cRoot : WittVector ℓ k :=
      WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range (m + 2),
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (εnext ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cRoot.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m + 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let εnext : A := ε ^ ℓ
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  let S : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic D,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (εnext ^ (ℓ ^ j) *
          θ (WittVector.teichmuller ℓ
            ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
              (cRoot.coeff r)) ^ ℓ)))) ^
        (ℓ ^ (r + 1))
  have hbridge :=
    F.artinHasseExp_tail_range_depth_eq_frobenius_root_tail_range_depth_pow
      N D m ε c
  have hεnext_m : εnext ^ (ℓ ^ m) = 0 := by
    dsimp [εnext]
    rw [← pow_mul, ← pow_succ']
    exact hzero
  have hεnext_succ : εnext ^ (ℓ ^ (m + 1)) = 0 := pow_pow_ell_succ_eq_zero hεnext_m
  have hEzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  have hEzero' :
      Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hEzero
  have hS_m : S m = 1 := by
    dsimp [S]
    rw [hεnext_m]
    simp [hEzero']
  have hS_succ : S (m + 1) = 1 := by
    dsimp [S]
    rw [hεnext_succ]
    simp [hEzero']
  calc
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j)))
        =
          ∏ j ∈ Finset.range m, (S j) ^ (ℓ ^ (m + 1 - j)) := by
          simpa [A, θ, Eps, εnext, cRoot, S] using hbridge
    _ =
          ∏ j ∈ Finset.range (m + 1), (S j) ^ (ℓ ^ (m + 1 - j)) := by
          symm
          rw [Finset.prod_range_succ]
          simp [hS_m]
    _ =
          ∏ j ∈ Finset.range (m + 2), (S j) ^ (ℓ ^ (m + 1 - j)) := by
          symm
          rw [show m + 2 = (m + 1) + 1 by omega]
          rw [Finset.prod_range_succ]
          simp [hS_succ]
    _ =
          ∏ j ∈ Finset.range (m + 2),
            (∏ r ∈ Finset.Iic D,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (εnext ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      (cRoot.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m + 1 - j)) := by
          rfl

/-- Convert an accumulated current-parameter non-shifted tail into an
accumulated rooted Frobenius-coordinate tail.  Unlike
`artinHasseExp_tail_range_depth_eq_frobenius_root_tail_range_depth_pow`, this
does not advance the parameter before starting the range; it is the form
needed for the remaining unshifted tail in the final telescope. -/
theorem artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_range_depth_pow
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let cRoot : WittVector ℓ k :=
      WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cRoot.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjlt : j < m := Finset.mem_range.mp hj
  have htail :=
    F.artinHasseExp_wittTeich_tail_depth_eq_frobenius_root_tail_pow
      (N := N) (D := D) (ε := ε ^ (ℓ ^ j)) c
  have hsucc : m - j = (m - 1 - j) + 1 := by
    omega
  calc
    (∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
          (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))
        =
          ((∏ r ∈ Finset.Iic D,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    (cRoot.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ ℓ) ^ (ℓ ^ (m - 1 - j)) := by
          rw [htail]
    _ =
          (∏ r ∈ Finset.Iic D,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    (cRoot.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
          rw [← pow_mul, ← pow_succ', hsucc]

/-- At the zero boundary, the accumulated current-parameter non-shifted tail
extends to the full rooted Frobenius-coordinate tail by adding the trivial
terminal factor. -/
theorem artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hzero : ε ^ (ℓ ^ m) = 0) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let cRoot : WittVector ℓ k :=
      WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) =
      ∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cRoot.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  let S : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic D,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) *
          θ (WittVector.teichmuller ℓ
            ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
              (cRoot.coeff r)) ^ ℓ)))) ^
        (ℓ ^ (r + 1))
  have hbridge :=
    F.artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_range_depth_pow
      N D m ε c
  have hEzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  have hEzero' :
      Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hEzero
  have hS_m : S m = 1 := by
    dsimp [S]
    rw [hzero]
    simp [hEzero']
  calc
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)))
        =
          ∏ j ∈ Finset.range m, (S j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, cRoot, S] using hbridge
    _ =
          ∏ j ∈ Finset.range (m + 1), (S j) ^ (ℓ ^ (m - j)) := by
          symm
          rw [Finset.prod_range_succ]
          simp [hS_m]
    _ =
          ∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic D,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      (cRoot.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
          rfl

/-- Base case for the coordinate peel: at depth zero, the Frobenius-shifted
tail consists only of the peeled zeroth-coordinate factors. -/
theorem artinHasseExp_frobenius_tail_zero_depth_eq_coeff_zero_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hzero : ε ^ (ℓ ^ (m + 1)) = 0) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Z : ℕ → A := fun j =>
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic 0,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let U : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
      ∏ r ∈ Finset.range 0,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  let Z : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      ((ε ^ (ℓ ^ j)) ^ ℓ *
        θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
  have hreindex :=
    F.artinHasseExp_frobenius_tail_succ_depth_eq_reindexed_tail
      N 0 m ε c
  have hdrop :=
    F.artinHasseExp_reindexed_tail_succ_depth_eq_range_of_zero_iterate
      N 0 m ε hzero c
  calc
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic 0,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)))
        =
          ∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, U] using hreindex
    _ =
          ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, U] using hdrop
    _ =
          ∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          simp [U, Z]

/-- Shift the carry coordinates down by one and take inverse-Frobenius roots.
This is the Witt-coordinate update after one depth peel. -/
noncomputable def coordinateTailRoot
    [ExpChar k ℓ] [PerfectRing k ℓ] (c : WittVector ℓ k) : WittVector ℓ k :=
  WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff (r + 1)))

omit [Fintype k] in
/-- Multiplication by `ℓ` has zero zeroth coordinate and tail equal to the
original Witt vector after undoing Frobenius.  This is the formal carry-shift
identity used in the finite Artin-Hasse-Witt cancellation. -/
theorem coordinateTailRoot_natCast_ell_mul
    [ExpChar k ℓ] [PerfectRing k ℓ] (c : WittVector ℓ k) :
    coordinateTailRoot ((ℓ : WittVector ℓ k) * c) = c := by
  ext r
  dsimp [coordinateTailRoot]
  rw [natCast_ell_mul_wittVector_coeff_succ (ℓ := ℓ) (k := k) c r]
  rw [← _root_.frobeniusEquiv_def (R := k) (p := ℓ) (c.coeff r)]
  exact RingEquiv.symm_apply_apply (_root_.frobeniusEquiv k ℓ) (c.coeff r)

/-- Product of all peeled zeroth-coordinate factors generated by repeatedly
peeling a finite Witt-coordinate tail. -/
noncomputable def artinHasseExpCoordinatePeelProduct
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) :
    ℕ → ℕ → (𝓞 R' ⧸ F.Q ^ (N + 1)) → WittVector ℓ k →
      (𝓞 R' ⧸ F.Q ^ (N + 1))
  | m, 0, ε, c =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      ∏ j ∈ Finset.range m,
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ) ^
          (ℓ ^ (m - j))
  | m, D + 1, ε, c =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (∏ j ∈ Finset.range m,
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ) ^
          (ℓ ^ (m - j))) *
        artinHasseExpCoordinatePeelProduct N (m + 1) D ε
          (coordinateTailRoot c)

/-- Iterating the coordinate peel eliminates a finite Frobenius-shifted
Witt-coordinate tail, leaving exactly the recursively accumulated peeled
zeroth-coordinate product. -/
theorem artinHasseExp_frobenius_tail_depth_eq_coordinatePeelProduct_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hzero : ε ^ (ℓ ^ (m + 1)) = 0) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      artinHasseExpCoordinatePeelProduct F N m D ε c := by
  classical
  dsimp only
  induction D generalizing m ε c with
  | zero =>
      simpa [artinHasseExpCoordinatePeelProduct] using
        F.artinHasseExp_frobenius_tail_zero_depth_eq_coeff_zero_of_zero_iterate
          N m ε hzero c
  | succ D ih =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
      let Z : ℕ → A := fun j =>
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
      let W : ℕ → A := fun j =>
        ∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
            (ℓ ^ (r + 2))
      let RootTail : ℕ → A := fun j =>
        ∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((coordinateTailRoot c).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))
      let RootTailShift : ℕ → A := fun j =>
        ∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ ℓ) ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((coordinateTailRoot c).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))
      have hpeel :=
        F.artinHasseExp_frobenius_tail_succ_depth_eq_coeff_zero_mul_shifted_tail_of_zero_iterate
          (D := D + 1) (hD := Nat.succ_pos D) N m ε hzero c
      have htail :=
        F.artinHasseExp_tail_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
          N D m ε hzero cTail
      have hzero_next : ε ^ (ℓ ^ ((m + 1) + 1)) = 0 := pow_pow_ell_succ_eq_zero hzero
      have hRootTailShift : ∀ j : ℕ, RootTailShift j = RootTail j := by
        intro j
        dsimp [RootTailShift, RootTail]
        refine Finset.prod_congr rfl ?_
        intro r _hr
        rw [pow_right_comm]
      have hroot_tail :
          (∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j))) =
            ∏ j ∈ Finset.range (m + 2),
              (RootTail j) ^ (ℓ ^ (m + 1 - j)) := by
        calc
          (∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j))) =
              ∏ j ∈ Finset.range (m + 2),
                (RootTailShift j) ^ (ℓ ^ (m + 1 - j)) := by
              simpa [A, θ, Eps, cTail, RootTailShift, W, coordinateTailRoot] using htail
          _ =
              ∏ j ∈ Finset.range (m + 2),
                (RootTail j) ^ (ℓ ^ (m + 1 - j)) := by
              refine Finset.prod_congr rfl ?_
              intro j _hj
              rw [hRootTailShift j]
      have hind := ih (m + 1) ε hzero_next (coordinateTailRoot c)
      calc
        (∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic (D + 1),
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε ^ (ℓ ^ j)) ^ ℓ *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      (c.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)))
            =
              (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
              simpa [A, θ, Eps, cTail, Z, W] using hpeel
        _ =
              (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                ∏ j ∈ Finset.range (m + 2),
                  (RootTail j) ^ (ℓ ^ (m + 1 - j)) := by
              rw [hroot_tail]
        _ =
              (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                artinHasseExpCoordinatePeelProduct F N (m + 1) D ε
                  (coordinateTailRoot c) := by
              rw [hind]
        _ =
              artinHasseExpCoordinatePeelProduct F N m (D + 1) ε c := by
              rfl

/-- Trace-carry peeled product written only in the chosen prime-field
coordinates.  The extra index `s` records how far the coordinate tail has been
shifted by previous peels. -/
noncomputable def artinHasseExpTraceCarryZModPeelProduct
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) :
    ℕ → ℕ → ℕ → (𝓞 R' ⧸ F.Q ^ (N + 1)) → kˣ →
      (𝓞 R' ⧸ F.Q ^ (N + 1))
  | m, 0, s, ε, y =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      ∏ j ∈ Finset.range m,
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^ ℓ) ^
          (ℓ ^ (m - j))
  | m, D + 1, s, ε, y =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (∏ j ∈ Finset.range m,
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^ ℓ) ^
          (ℓ ^ (m - j))) *
        artinHasseExpTraceCarryZModPeelProduct N (m + 1) D (s + 1) ε y

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
