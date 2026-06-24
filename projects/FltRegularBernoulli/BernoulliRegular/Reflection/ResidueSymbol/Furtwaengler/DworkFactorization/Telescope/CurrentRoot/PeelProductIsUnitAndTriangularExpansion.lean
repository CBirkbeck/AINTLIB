module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.ZModFold

/-!
# Current-root coordinate telescopes for the finite Dwork telescope.

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

/-- The recursively peeled current-root Artin-Hasse product is a unit when
the base quotient parameter is nilpotent to the working precision. -/
theorem artinHasseExpCurrentRootPeelProduct_isUnit_of_pow_succ_eq_zero
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (c : WittVector ℓ k) :
    IsUnit (artinHasseExpCurrentRootPeelProduct F N m D ε c) := by
  classical
  induction D generalizing m c with
  | zero =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      simp only [artinHasseExpCurrentRootPeelProduct]
      rw [IsUnit.prod_iff]
      intro j _hj
      have hEval :
          IsUnit ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) := by
        simpa [A, θ, Eps] using
          F.artinHasseExp_trunc_eval_pow_iterate_mul_isUnit_of_pow_succ_eq_zero
            N j ε (θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ))) hε
      exact (hEval.pow ℓ).pow (ℓ ^ (m - j))
  | succ D ih =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      simp only [artinHasseExpCurrentRootPeelProduct]
      refine IsUnit.mul ?_ ?_
      · rw [IsUnit.prod_iff]
        intro j _hj
        have hEval :
            IsUnit ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) := by
          simpa [A, θ, Eps] using
            F.artinHasseExp_trunc_eval_pow_iterate_mul_isUnit_of_pow_succ_eq_zero
              N j ε (θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ))) hε
        exact (hEval.pow ℓ).pow (ℓ ^ (m - j))
      · exact ih (m + 1) (coordinateTailRoot c)

/-- Iterating the current-root coordinate peel eliminates a finite rooted
Witt-coordinate tail, leaving the recursively accumulated peeled
zeroth-coordinate product. -/
theorem artinHasseExp_current_root_tail_depth_eq_currentRootPeelProduct_of_zero_iterate
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
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      artinHasseExpCurrentRootPeelProduct F N m D ε c := by
  classical
  dsimp only
  induction D generalizing m ε c with
  | zero =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let Z : ℕ → A := fun j =>
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
      have hEzero :
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
        simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
      have hEzero' :
          Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
        simpa [Polynomial.eval₂_eq_eval_map] using hEzero
      have hZ_m : Z m = 1 := by
        dsimp [Z]
        rw [hzero]
        simp [hEzero']
      calc
        (∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic 0,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      (c.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)))
            =
              ∏ j ∈ Finset.range (m + 1), (Z j) ^ (ℓ ^ (m - j)) := by
              refine Finset.prod_congr rfl ?_
              intro j _hj
              rw [show Finset.Iic (0 : ℕ) = ({0} : Finset ℕ) by ext r; simp]
              simp [Z]
        _ =
              ∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j)) := by
              symm
              rw [Finset.prod_range_succ]
              simp [hZ_m]
        _ =
              artinHasseExpCurrentRootPeelProduct F N m 0 ε c := by
              rfl
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
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
      let V : ℕ → A := fun j =>
        ∏ r ∈ Finset.range (D + 1),
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff (r + 1)))))) ^
            (ℓ ^ (r + 2))
      let RootTail : ℕ → A := fun j =>
        ∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((coordinateTailRoot c).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))
      have hzero_next : ε ^ (ℓ ^ (m + 1)) = 0 := by
        rw [show ℓ ^ (m + 1) = ℓ ^ m * ℓ from pow_succ ℓ m, pow_mul, hzero]
        exact zero_pow (Nat.Prime.ne_zero (Fact.out : Nat.Prime ℓ))
      have hEzero :
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
        simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
      have hEzero' :
          Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
        simpa [Polynomial.eval₂_eq_eval_map] using hEzero
      have hreindex :
          (∏ j ∈ Finset.range (m + 1),
              (∏ r ∈ Finset.Iic (D + 1),
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ j) *
                    θ (WittVector.teichmuller ℓ
                      ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                        (c.coeff r)) ^ ℓ)))) ^
                  (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
            ∏ j ∈ Finset.range (m + 1), (Z j * V j) ^ (ℓ ^ (m - j)) := by
        refine Finset.prod_congr rfl ?_
        intro j _hj
        have hinner :=
          F.artinHasseExp_wittTeich_frobenius_tail_depth_eq_coeff_zero_mul_shift
            (N := N) (D := D + 1) (ε := ε ^ (ℓ ^ j)) c
        simpa [A, θ, Eps, Z, V] using
          congrArg (fun x : A => x ^ (ℓ ^ (m - j))) hinner
      have hZ_m : Z m = 1 := by
        dsimp [Z]
        rw [hzero]
        simp [hEzero']
      have hV_m : V m = 1 := by
        dsimp [V]
        rw [hzero]
        simp [hEzero']
      have hdrop :
          (∏ j ∈ Finset.range (m + 1), (Z j * V j) ^ (ℓ ^ (m - j))) =
            ∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j)) := by
        rw [Finset.prod_range_succ]
        simp [hZ_m, hV_m]
      have hsplit :
          (∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j))) =
            (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
              ∏ j ∈ Finset.range m, (V j) ^ (ℓ ^ (m - j)) := by
        calc
          (∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j)))
              =
                ∏ j ∈ Finset.range m,
                  ((Z j) ^ (ℓ ^ (m - j)) * (V j) ^ (ℓ ^ (m - j))) := by
                refine Finset.prod_congr rfl ?_
                intro j _hj
                rw [mul_pow]
          _ =
                (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                  ∏ j ∈ Finset.range m, (V j) ^ (ℓ ^ (m - j)) := by
                rw [Finset.prod_mul_distrib]
      have hV_extend :
          (∏ j ∈ Finset.range m, (V j) ^ (ℓ ^ (m - j))) =
            ∏ j ∈ Finset.range (m + 1), (V j) ^ (ℓ ^ (m - j)) := by
        symm
        rw [Finset.prod_range_succ]
        simp [hV_m]
      have hV_root :
          (∏ j ∈ Finset.range (m + 1), (V j) ^ (ℓ ^ (m - j))) =
            ∏ j ∈ Finset.range (m + 2),
              (RootTail j) ^ (ℓ ^ (m + 1 - j)) := by
        have htail :=
          F.artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
            N D (m + 1) ε hzero_next cTail
        calc
          (∏ j ∈ Finset.range (m + 1), (V j) ^ (ℓ ^ (m - j)))
              =
                ∏ j ∈ Finset.range (m + 1),
                  (∏ r ∈ Finset.Iic D,
                    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                      (ε ^ (ℓ ^ j) *
                        θ (WittVector.teichmuller ℓ
                          (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                            (c.coeff (r + 1)))))) ^
                    (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j)) := by
                refine Finset.prod_congr rfl ?_
                intro j _hj
                dsimp [V]
                rw [Nat.range_succ_eq_Iic D]
          _ =
                ∏ j ∈ Finset.range (m + 2),
                  (RootTail j) ^ (ℓ ^ (m + 1 - j)) := by
                simpa [A, θ, Eps, cTail, RootTail, coordinateTailRoot] using htail
      have hind := ih (m + 1) ε hzero_next (coordinateTailRoot c)
      calc
        (∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic (D + 1),
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      (c.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)))
            =
              ∏ j ∈ Finset.range (m + 1), (Z j * V j) ^ (ℓ ^ (m - j)) := hreindex
        _ =
              ∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j)) := hdrop
        _ =
              (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                ∏ j ∈ Finset.range m, (V j) ^ (ℓ ^ (m - j)) := hsplit
        _ =
              (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                ∏ j ∈ Finset.range (m + 1), (V j) ^ (ℓ ^ (m - j)) := by
              rw [hV_extend]
        _ =
              (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                ∏ j ∈ Finset.range (m + 2),
                  (RootTail j) ^ (ℓ ^ (m + 1 - j)) := by
              rw [hV_root]
        _ =
              (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
                artinHasseExpCurrentRootPeelProduct F N (m + 1) D ε
                  (coordinateTailRoot c) := by
              rw [hind]
        _ =
              artinHasseExpCurrentRootPeelProduct F N m (D + 1) ε c := by
              rfl

/-- Inverse-parameter trace-carry specialization of the current-root expansion.
This is the exact triangular endpoint left by the finite Dwork fold; no
individual factor is discarded. -/
theorem traceCarry_currentRootPeelProduct_inverse_eq_triangularProduct_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) =
      ∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hzero : δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have htri :=
    F.artinHasseExp_current_root_tail_depth_eq_currentRootPeelProduct_of_zero_iterate
      N N m δ hzero (F.traceCarry y)
  calc
    artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)
        =
          ∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, Ips, πbar, δ] using htri.symm
    _ =
          ∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ (ℓ ^ j) *
                  (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          refine congrArg (fun x : A => x ^ (ℓ ^ (m - j))) ?_
          refine Finset.prod_congr rfl ?_
          intro r _hr
          have hroot :
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((F.traceCarry y).coeff r)) ^ ℓ =
                (F.traceCarry y).coeff r ^ ℓ := by
            rw [F.traceCarry_coeff_frobeniusEquiv_symm_iterate_eq_self y r r]
          rw [hroot]
          rw [← F.wittThetaModQPow_teichmuller_pow_prime N ((F.traceCarry y).coeff r)]

/-- Zero-boundary range normalization for the inverse-parameter triangular
trace-carry endpoint: the final `j = m` slice is already at parameter zero,
so it contributes `1`. -/
theorem traceCarry_triangularProduct_inverse_range_succ_eq_range_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let T : ℕ → A := fun j =>
    (∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (δ ^ (ℓ ^ j) *
          (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
        (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))
  have hzero : δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have hEzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  have hEzero' :
      Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hEzero
  have hlast : T m = 1 := by
    dsimp [T]
    rw [hzero]
    simp [hEzero']
  change (∏ j ∈ Finset.range (m + 1), T j) = ∏ j ∈ Finset.range m, T j
  rw [Finset.prod_range_succ]
  simp [hlast]

/-- Range-normalized form of
`traceCarry_currentRootPeelProduct_inverse_eq_triangularProduct_of_le`.  This
keeps the triangular exponent pattern but removes the final zero-boundary
slice. -/
theorem traceCarry_currentRootPeelProduct_inverse_eq_triangularProduct_range_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hfull :=
    F.traceCarry_currentRootPeelProduct_inverse_eq_triangularProduct_of_le N m hm y
  have hrange :=
    F.traceCarry_triangularProduct_inverse_range_succ_eq_range_of_le N m hm y
  calc
    artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)
        =
          ∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ (ℓ ^ j) *
                  (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, Ips, πbar, δ] using hfull
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ (ℓ ^ j) *
                  (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, Ips, πbar, δ] using hrange

/-- The range-normalized triangular endpoint from c5B1 has `ℓ`-th power equal
to the named full-depth trace-carry finite-character surface.  This is only a
shape bridge: all cancellation is left to the product-level telescope. -/
theorem traceCarry_triangularProduct_inverse_pow_prime_eq_finiteCharacter_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) ^ ℓ =
      artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have htri :=
    F.traceCarry_currentRootPeelProduct_inverse_eq_triangularProduct_range_of_le
      N m hm y
  have hfold :=
    F.traceCarryFiniteCharacter_inverse_eq_currentRoot_pow_prime N m y
  calc
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff r))) ^ ℓ)) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) ^ ℓ =
        (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ :=
          congrArg (fun x : A => x ^ ℓ) (by
            simpa [A, θ, Eps, Ips, πbar, δ] using htri.symm)
    _ =
        artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y := by
          simpa [A, Ips, πbar, δ] using hfold.symm

/-- The coordinate peel is the current-root peel after Frobenius-shifting the
parameter.  This identifies the two recursively accumulated peeled products
without using any root cancellation. -/
theorem artinHasseExpCoordinatePeelProduct_eq_currentRootPeelProduct_frobenius_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (c : WittVector ℓ k) :
    artinHasseExpCoordinatePeelProduct F N m D ε c =
      artinHasseExpCurrentRootPeelProduct F N m D (ε ^ ℓ) c := by
  classical
  have hparam : ∀ j : ℕ, (ε ^ (ℓ ^ j)) ^ ℓ = (ε ^ ℓ) ^ (ℓ ^ j) :=
    fun j => pow_right_comm ε (ℓ ^ j) ℓ
  induction D generalizing m c with
  | zero =>
      simp only [artinHasseExpCoordinatePeelProduct, artinHasseExpCurrentRootPeelProduct]
      refine Finset.prod_congr rfl ?_
      intro j _hj
      simp [hparam j]
  | succ D ih =>
      simp only [artinHasseExpCoordinatePeelProduct, artinHasseExpCurrentRootPeelProduct]
      congr 1
      · refine Finset.prod_congr rfl ?_
        intro j _hj
        simp [hparam j]
      · simpa using ih (m + 1) (coordinateTailRoot c)

/-- Collapse the Frobenius-shifted side of the carry-free powered comparison
using the completed finite coordinate-depth peel. -/
theorem exists_artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_coordinatePeelProduct
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : 0 < m) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
              (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) =
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, htail⟩ :=
    F.exists_artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_frobenius_tail
      N m y ε hε hzero
  have hm_succ : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hzero_peel : ε ^ (ℓ ^ ((m - 1) + 1)) = 0 := by
    simpa [hm_succ] using hzero
  have hpeel :=
    F.artinHasseExp_frobenius_tail_depth_eq_coordinatePeelProduct_of_zero_iterate
      N N (m - 1) ε hzero_peel c
  have hpeel_m :
      (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) =
        artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
    simpa [A, θ, Eps, hm_succ] using hpeel
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)))
        =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε ^ (ℓ ^ j)) ^ ℓ *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
          simpa [A, θ, Eps, zbar, t] using htail
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
          rw [hpeel_m]

/-- Non-existential coordinate-peeled comparison using the canonical
Frobenius-fixed trace carry. -/
theorem artinHasseExp_product_iterate_coordinatePeel_traceCarry
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : 0 < m) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    let c : WittVector ℓ k := F.traceCarry y
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
          (ℓ ^ m) *
        artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let c : WittVector ℓ k := F.traceCarry y
  have htail :=
    F.artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_frobenius_tail_traceCarry
      N m y ε hε hzero
  have hm_succ : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hzero_peel : ε ^ (ℓ ^ ((m - 1) + 1)) = 0 := by
    simpa [hm_succ] using hzero
  have hpeel :=
    F.artinHasseExp_frobenius_tail_depth_eq_coordinatePeelProduct_of_zero_iterate
      N N (m - 1) ε hzero_peel c
  have hpeel_m :
      (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) =
        artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
    simpa [A, θ, Eps, c, hm_succ] using hpeel
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)))
        =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε ^ (ℓ ^ j)) ^ ℓ *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
          simpa [A, θ, Eps, zbar, t, c] using htail
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
          rw [hpeel_m]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
