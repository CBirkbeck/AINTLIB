module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CoordinatePeel

/-!
# ZMod trace-carry fold and finite character endpoint for the finite Dwork telescope.

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

/-- Aligned ordinary correction product for one fixed trace-carry coordinate.
This is the `Rps` companion to the fixed-coordinate factor occurring in
`artinHasseExpTraceCarryZModPeelProductDivisible`: it has the same `j`-range,
coordinate offset, and explicitly `ℓ`-divisible exponent, but the Dwork
parameter has not yet been Frobenius-shifted. -/
noncomputable def artinHasseExpTraceCarryZModCorrectionRangeProduct
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m s : ℕ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  ∏ j ∈ Finset.range m,
    ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) *
        θ (WittVector.teichmuller ℓ
          (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^
      (ℓ * ℓ ^ (m - j))

/-- Coordinate-depth version of the aligned ordinary correction product.  This
follows the same recursive `m`/`s` update pattern as
`artinHasseExpTraceCarryZModPeelProductDivisible`, so the two products can be
folded together coordinate by coordinate in WC3c. -/
noncomputable def artinHasseExpTraceCarryZModCorrectionProduct
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) :
    ℕ → ℕ → ℕ → (𝓞 R' ⧸ F.Q ^ (N + 1)) → kˣ →
      𝓞 R' ⧸ F.Q ^ (N + 1)
  | m, 0, s, ε, y =>
      artinHasseExpTraceCarryZModCorrectionRangeProduct F N m s ε y
  | m, D + 1, s, ε, y =>
      artinHasseExpTraceCarryZModCorrectionRangeProduct F N m s ε y *
        artinHasseExpTraceCarryZModCorrectionProduct N (m + 1) D (s + 1) ε y

private theorem prod_range_succ_eq_first_mul
    {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∏ r ∈ Finset.range (n + 1), f r) =
      f 0 * ∏ r ∈ Finset.range n, f (r + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      rw [Finset.prod_range_succ]
      ac_rfl

private theorem rescaleExp_trunc_eval_zero_quotient (N : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) 0 = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  have h :=
    rescale_exp_trunc_eval₂_finset_prod_eq_sum
      ℓ (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N) N
      (0 : A) (by simp) (∅ : Finset ℕ) (fun _ => (0 : A))
  simpa [A, Rps] using h.symm

/-- Closed coordinate product matching the zero-boundary part of the ordinary
trace-carry correction.  The coordinate index is written relative to the
current recursive offset `s`; for `s = 0` and `D = N` this is the `C_j` product
from the adjusted Dwork telescope. -/
noncomputable def artinHasseExpTraceCarryZModCorrectionTeichProduct
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m D s : ℕ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  ∏ j ∈ Finset.range m,
    (∏ r ∈ Finset.range (D + 1),
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ (r + s))
              ((F.traceCarry y).coeff (r + s)))))) ^
        (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))

private theorem artinHasseExpTraceCarryZModCorrectionProduct_zero_eq_teichProduct
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    artinHasseExpTraceCarryZModCorrectionProduct F N m 0 s ε y =
      artinHasseExpTraceCarryZModCorrectionTeichProduct F N m 0 s ε y := by
  classical
  simp only [artinHasseExpTraceCarryZModCorrectionProduct,
    artinHasseExpTraceCarryZModCorrectionTeichProduct,
    artinHasseExpTraceCarryZModCorrectionRangeProduct]
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [prod_range_succ_eq_first_mul]
  simp only [Finset.range_zero, Finset.prod_empty, mul_one]
  have hcoord :
      algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s) =
        ((_root_.frobeniusEquiv k ℓ).symm ^ s) ((F.traceCarry y).coeff s) :=
    F.traceCarryCoeffZMod_frobeniusRoot_spec y s
  rw [hcoord]
  rw [pow_mul]
  simp

private theorem artinHasseExpTraceCarryZModCorrectionTeichProduct_succ_eq_range_mul_tail
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    (hzero : ε ^ (ℓ ^ m) = 0) :
    artinHasseExpTraceCarryZModCorrectionTeichProduct F N m (D + 1) s ε y =
      artinHasseExpTraceCarryZModCorrectionRangeProduct F N m s ε y *
        artinHasseExpTraceCarryZModCorrectionTeichProduct F N (m + 1) D (s + 1) ε y := by
  classical
  dsimp only [artinHasseExpTraceCarryZModCorrectionTeichProduct,
    artinHasseExpTraceCarryZModCorrectionRangeProduct]
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let X : ℕ → ℕ → A := fun j r =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) *
        θ (WittVector.teichmuller ℓ
          (((_root_.frobeniusEquiv k ℓ).symm ^ (r + s))
            ((F.traceCarry y).coeff (r + s)))))
  let X0 : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) *
        θ (WittVector.teichmuller ℓ
          (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))
  let Tail : ℕ → A := fun j =>
    ∏ r ∈ Finset.range (D + 1), X j (r + 1) ^ (ℓ ^ (r + 1))
  let ARange : ℕ → A := fun j => X0 j ^ (ℓ * ℓ ^ (m - j))
  let BTail : ℕ → A := fun j => Tail j ^ (ℓ ^ (m + 1 - j))
  let CAll : ℕ → A := fun j =>
    (∏ r ∈ Finset.range (D + 2), X j r ^ (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))
  have htail_last : BTail m = 1 := by
    have hRzero :
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) 0 = 1 := by
      simpa [A, Rps] using F.rescaleExp_trunc_eval_zero_quotient N
    have hRzero' :
        Polynomial.eval 0 (PowerSeries.trunc (N + 1) Rps) = 1 := by
      simpa [Polynomial.eval₂_eq_eval_map] using hRzero
    have hTail_m : Tail m = 1 := by
      dsimp [Tail, X]
      refine Finset.prod_eq_one ?_
      intro r _hr
      rw [hzero]
      simp [hRzero']
    dsimp [BTail]
    rw [hTail_m]
    simp
  have htail_drop :
      (∏ j ∈ Finset.range (m + 1), BTail j) =
        ∏ j ∈ Finset.range m, BTail j := by
    rw [Finset.prod_range_succ]
    simp [htail_last]
  suffices habs :
      (∏ j ∈ Finset.range m, CAll j) =
        (∏ j ∈ Finset.range m, ARange j) *
          ∏ j ∈ Finset.range (m + 1), BTail j by
    simpa [A, θ, Rps, X, X0, Tail, ARange, BTail, CAll,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using habs
  rw [htail_drop, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjlt : j < m := Finset.mem_range.mp hj
  have hcoord :
      X0 j = X j 0 := by
    dsimp [X0, X]
    have hcoeff :
        algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s) =
          ((_root_.frobeniusEquiv k ℓ).symm ^ s) ((F.traceCarry y).coeff s) :=
      F.traceCarryCoeffZMod_frobeniusRoot_spec y s
    simp [hcoeff]
  have htail_pow :
      (∏ r ∈ Finset.range (D + 1), X j (r + 1) ^ (ℓ ^ (r + 2))) =
        (Tail j) ^ ℓ := by
    dsimp [Tail]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl ?_
    intro r _hr
    rw [← pow_mul]
    have hexp : ℓ ^ (r + 2) = ℓ ^ (r + 1) * ℓ := by
      rw [show r + 2 = r + 1 + 1 by omega]
      rw [pow_succ]
    exact congrArg (fun n : ℕ => X j (r + 1) ^ n) hexp.symm
  have htail_exp :
      (Tail j ^ ℓ) ^ (ℓ ^ (m - j)) = BTail j := by
    dsimp [BTail]
    rw [← pow_mul]
    have hsub : m + 1 - j = m - j + 1 := by
      omega
    have hexp : ℓ ^ (m + 1 - j) = ℓ * ℓ ^ (m - j) := by
      rw [hsub, pow_succ, Nat.mul_comm]
    exact congrArg (fun n : ℕ => Tail j ^ n) hexp.symm
  dsimp [CAll, ARange]
  rw [prod_range_succ_eq_first_mul]
  rw [mul_pow]
  rw [hcoord, pow_mul, htail_pow, htail_exp]
  simp

theorem artinHasseExpTraceCarryZModCorrectionProduct_eq_teichProduct_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    (hzero : ε ^ (ℓ ^ m) = 0) :
    artinHasseExpTraceCarryZModCorrectionProduct F N m D s ε y =
      artinHasseExpTraceCarryZModCorrectionTeichProduct F N m D s ε y := by
  classical
  induction D generalizing m s with
  | zero =>
      exact
        F.artinHasseExpTraceCarryZModCorrectionProduct_zero_eq_teichProduct
          N m s ε y
  | succ D ih =>
      have hzero_succ : ε ^ (ℓ ^ (m + 1)) = 0 := by
        rw [show ℓ ^ (m + 1) = ℓ ^ m * ℓ by rw [pow_succ]]
        rw [pow_mul, hzero]
        exact zero_pow (ne_of_gt (Nat.Prime.pos (Fact.out : Nat.Prime ℓ)))
      have htail := ih (m + 1) (s + 1) hzero_succ
      simp only [artinHasseExpTraceCarryZModCorrectionProduct]
      rw [htail]
      exact
        (F.artinHasseExpTraceCarryZModCorrectionTeichProduct_succ_eq_range_mul_tail
          N m D s ε y hzero).symm

/-- Inverse-parameter full-depth correction product in the same `C_j` shape as
the adjusted-product telescope.  The recursive correction product has extra
coordinate-tail ranges, but those ranges are zero-boundary slices once
`δ^(ℓ^m)=0`. -/
theorem artinHasseExpTraceCarryZModCorrectionProduct_inverse_eq_teichProduct_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModCorrectionProduct F N m N 0 δ y =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((F.traceCarry y).coeff r))))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hzero : δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have hcorr :=
    F.artinHasseExpTraceCarryZModCorrectionProduct_eq_teichProduct_of_zero_iterate
      N m N 0 δ y hzero
  have hrange : Finset.range (N + 1) = Finset.Iic N := by
    ext r
    simp
  simpa [A, θ, Rps, Ips, πbar, δ,
    artinHasseExpTraceCarryZModCorrectionTeichProduct, hrange] using hcorr

/-- c5B2d assembly form: after the c5B2c adjusted-product telescope, the
`C_j` product is exactly the recursive zmod correction product. -/
theorem artinHasseExp_inverse_adjustedProduct_succ_mul_correctionProduct_eq_one_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
        artinHasseExpTraceCarryZModCorrectionProduct F N m N 0 δ y = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  have htel :=
    F.artinHasseExp_inverse_adjustedProduct_succ_traceCarry_eq_one_of_le
      N m hm y
  have hcorr :=
    F.artinHasseExpTraceCarryZModCorrectionProduct_inverse_eq_teichProduct_of_le
      N m hm y
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
        artinHasseExpTraceCarryZModCorrectionProduct F N m N 0 δ y
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
            (∏ j ∈ Finset.range m,
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                  (δ ^ (ℓ ^ j) *
                    θ (WittVector.teichmuller ℓ
                      (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                        ((F.traceCarry y).coeff r))))) ^
                  (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) := by
          rw [hcorr]
    _ = 1 := by
          simpa [A, θ, Eps, Rps, Ips, πbar, δ, zbar] using htel

/-- One-coordinate zmod trace-carry specialization of the Dwork fold.  This is
the atomic WC3c step: the aligned ordinary correction at the unshifted
parameter and the shifted Artin-Hasse factor fold to the next powered
unshifted Artin-Hasse factor. -/
theorem artinHasseExpTraceCarryZMod_oneCoordinate_correction_mul_shifted_eq_unshifted
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N q j s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hεj : (ε ^ (ℓ ^ j)) ^ (N + 1) = 0) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let x : k := algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s)
    ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) * θ (WittVector.teichmuller ℓ x))) ^ (ℓ ^ q) *
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ * θ (WittVector.teichmuller ℓ x))) ^ (ℓ ^ q) =
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) * θ (WittVector.teichmuller ℓ x))) ^ (ℓ ^ (q + 1)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let x : k := algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s)
  have hx : x ^ ℓ = x := by
    calc
      x ^ ℓ = (F.traceCarry y).coeff s ^ ℓ := by
        rw [show x = (F.traceCarry y).coeff s by
          simpa [x] using F.traceCarryCoeffZMod_spec y s]
      _ = x := by
        simpa [x] using (F.traceCarryCoeffZMod_pow_prime_spec y s).symm
  simpa [A, θ, Eps, Rps, x, hx] using
    F.artinHasseExp_wittTeich_correction_pow_mul_frobenius_eq_pow_succ
      N q (ε ^ (ℓ ^ j)) hεj x

/-- Fixed-offset range version of the zmod trace-carry Dwork fold.  Multiplying
the one-coordinate fold over the `j`-range folds the aligned `Rps` range
product and the shifted Artin-Hasse range product into the corresponding
unshifted Artin-Hasse range product. -/
theorem artinHasseExpTraceCarryZModCorrectionRange_mul_peelRange_eq_unshiftedRange
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    (hε : ∀ j : ℕ, j ∈ Finset.range m → (ε ^ (ℓ ^ j)) ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    artinHasseExpTraceCarryZModCorrectionRangeProduct F N m s ε y *
      artinHasseExpTraceCarryZModPeelProductDivisible F N m 0 s ε y =
      ∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^
          (ℓ ^ (m + 2 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  simp only [artinHasseExpTraceCarryZModCorrectionRangeProduct,
    artinHasseExpTraceCarryZModPeelProductDivisible]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjlt : j < m := Finset.mem_range.mp hj
  have hexp : ℓ * ℓ ^ (m - j) = ℓ ^ (m + 1 - j) := by
    have hsub : m + 1 - j = m - j + 1 := by
      omega
    rw [hsub, pow_succ, Nat.mul_comm]
  have hsucc : m + 1 - j + 1 = m + 2 - j := by
    omega
  have hfold :=
    F.artinHasseExpTraceCarryZMod_oneCoordinate_correction_mul_shifted_eq_unshifted
      N (m + 1 - j) j s ε (hε j hj) y
  simpa [A, θ, Eps, Rps, hexp, hsucc] using hfold

/-- Unshifted Artin-Hasse range product produced after folding the aligned
ordinary correction range against the shifted trace-carry peel range. -/
noncomputable def artinHasseExpTraceCarryZModUnshiftedRangeProduct
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m s : ℕ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  ∏ j ∈ Finset.range m,
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) *
        θ (WittVector.teichmuller ℓ
          (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^
      (ℓ ^ (m + 2 - j))

/-- Coordinate-depth product of the unshifted Artin-Hasse range products. -/
noncomputable def artinHasseExpTraceCarryZModUnshiftedProduct
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) :
    ℕ → ℕ → ℕ → (𝓞 R' ⧸ F.Q ^ (N + 1)) → kˣ →
      𝓞 R' ⧸ F.Q ^ (N + 1)
  | m, 0, s, ε, y =>
      artinHasseExpTraceCarryZModUnshiftedRangeProduct F N m s ε y
  | m, D + 1, s, ε, y =>
      artinHasseExpTraceCarryZModUnshiftedRangeProduct F N m s ε y *
        artinHasseExpTraceCarryZModUnshiftedProduct N (m + 1) D (s + 1) ε y

/-- Coordinate-depth zmod trace-carry Dwork fold.  The aligned ordinary
correction product and normalized shifted Artin-Hasse peel product fold,
coordinate by coordinate, into the recursive product of unshifted
prime-field-coordinate Artin-Hasse ranges. -/
theorem artinHasseExpTraceCarryZModCorrectionProduct_mul_peelProduct_eq_unshiftedProduct
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    (hε : ∀ j : ℕ, (ε ^ (ℓ ^ j)) ^ (N + 1) = 0) :
    artinHasseExpTraceCarryZModCorrectionProduct F N m D s ε y *
      artinHasseExpTraceCarryZModPeelProductDivisible F N m D s ε y =
      artinHasseExpTraceCarryZModUnshiftedProduct F N m D s ε y := by
  classical
  induction D generalizing m s with
  | zero =>
      have hrange :=
        F.artinHasseExpTraceCarryZModCorrectionRange_mul_peelRange_eq_unshiftedRange
          N m s ε y (fun j _hj => hε j)
      rw [artinHasseExpTraceCarryZModCorrectionProduct,
        artinHasseExpTraceCarryZModUnshiftedProduct,
        artinHasseExpTraceCarryZModUnshiftedRangeProduct]
      exact hrange
  | succ D ih =>
      let CR : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
        artinHasseExpTraceCarryZModCorrectionRangeProduct F N m s ε y
      let CT : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
        artinHasseExpTraceCarryZModCorrectionProduct F N (m + 1) D (s + 1) ε y
      let PR : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
        artinHasseExpTraceCarryZModPeelProductDivisible F N m 0 s ε y
      let PT : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
        artinHasseExpTraceCarryZModPeelProductDivisible F N (m + 1) D (s + 1) ε y
      let UR : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
        artinHasseExpTraceCarryZModUnshiftedRangeProduct F N m s ε y
      let UT : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
        artinHasseExpTraceCarryZModUnshiftedProduct F N (m + 1) D (s + 1) ε y
      have hrange : CR * PR = UR := by
        show artinHasseExpTraceCarryZModCorrectionRangeProduct F N m s ε y *
            artinHasseExpTraceCarryZModPeelProductDivisible F N m 0 s ε y =
            artinHasseExpTraceCarryZModUnshiftedRangeProduct F N m s ε y
        rw [artinHasseExpTraceCarryZModUnshiftedRangeProduct]
        exact
          F.artinHasseExpTraceCarryZModCorrectionRange_mul_peelRange_eq_unshiftedRange
            N m s ε y (fun j _hj => hε j)
      have htail : CT * PT = UT := by
        simpa [CT, PT, UT] using ih (m + 1) (s + 1)
      change (CR * CT) * (PR * PT) = UR * UT
      calc
        (CR * CT) * (PR * PT) = (CR * PR) * (CT * PT) := by
          ac_rfl
        _ = UR * UT := by
          rw [hrange, htail]

/-- Product of peeled zeroth-coordinate factors for a rooted current-parameter
Witt-coordinate tail.  This is parallel to
`artinHasseExpCoordinatePeelProduct`, but the Artin-Hasse parameter is not
advanced before the first coordinate peel. -/
noncomputable def artinHasseExpCurrentRootPeelProduct
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
          (ε ^ (ℓ ^ j) *
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
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ) ^
          (ℓ ^ (m - j))) *
        artinHasseExpCurrentRootPeelProduct N (m + 1) D ε
          (coordinateTailRoot c)

/-! ### Finite AH-Witt character surface for the current-root endpoint -/

/-- Zeroth-residue Artin-Hasse factor for a finite Witt character surface.
This is the factor that should survive after the finite AH-Witt character is
peeled to the zero boundary. -/
noncomputable def artinHasseExpFiniteWittResidueFactor
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
    (ε * θ (WittVector.teichmuller ℓ (w.coeff 0)))

/-- Finite AH-Witt current-root character surface used for the c5 endpoint.
This is deliberately a naming wrapper around the already compiled
current-root peeled product: c5A1/c5A2 will prove that this current-root
surface satisfies the finite AH-Witt residue recursion. -/
noncomputable def artinHasseExpFiniteWittCurrentRootCharacter
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m D : ℕ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  artinHasseExpCurrentRootPeelProduct F N m D ε w

/-- Finite recursive Artin-Hasse-Witt character through coordinate depth `D`.
The recursion peels the zeroth Witt coordinate and advances the Dwork
parameter by Frobenius.  This is the finite surface used in c5A1/c5A2; no
infinite Witt character is introduced. -/
noncomputable def artinHasseExpFiniteWittCharacter
    [ExpChar k ℓ] [PerfectRing k ℓ] (N D : ℕ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  Nat.rec
    (motive := fun _ =>
      (𝓞 R' ⧸ F.Q ^ (N + 1)) → WittVector ℓ k →
        𝓞 R' ⧸ F.Q ^ (N + 1))
    (fun ε w => artinHasseExpFiniteWittResidueFactor F N ε w)
    (fun _ rec ε w =>
      artinHasseExpFiniteWittResidueFactor F N ε w *
        rec (ε ^ ℓ) (coordinateTailRoot w))
    D ε w

/-- The current-root character wrapper is definitionally the existing
current-root peeled product. -/
theorem artinHasseExpFiniteWittCurrentRootCharacter_eq_currentRoot
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittCurrentRootCharacter F N m D ε w =
      artinHasseExpCurrentRootPeelProduct F N m D ε w := rfl

/-- Depth-zero equation for the finite AH-Witt character. -/
theorem artinHasseExpFiniteWittCharacter_zero
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittCharacter F N 0 ε w =
      artinHasseExpFiniteWittResidueFactor F N ε w := by
  rfl

/-- Successor peel equation for the finite AH-Witt character. -/
theorem artinHasseExpFiniteWittCharacter_succ
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittCharacter F N (D + 1) ε w =
      artinHasseExpFiniteWittResidueFactor F N ε w *
        artinHasseExpFiniteWittCharacter F N D (ε ^ ℓ)
          (coordinateTailRoot w) := by
  rfl

/-- Depth-zero equation for the finite current-root character wrapper. -/
theorem artinHasseExpFiniteWittCurrentRootCharacter_zero
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittCurrentRootCharacter F N m 0 ε w =
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      ∏ j ∈ Finset.range m,
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ ((w.coeff 0) ^ ℓ)))) ^ ℓ) ^
          (ℓ ^ (m - j)) := by
  rfl

/-- Recursive equation for the finite current-root character wrapper. -/
theorem artinHasseExpFiniteWittCurrentRootCharacter_succ
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittCurrentRootCharacter F N m (D + 1) ε w =
      (let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
       let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
       let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
       ∏ j ∈ Finset.range m,
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ ((w.coeff 0) ^ ℓ)))) ^ ℓ) ^
          (ℓ ^ (m - j))) *
        artinHasseExpFiniteWittCurrentRootCharacter F N (m + 1) D ε
          (coordinateTailRoot w) := by
  rfl

/-- The residue factor of an `ℓ`-multiple is trivial, because its zeroth Witt
coordinate is zero. -/
theorem artinHasseExpFiniteWittResidueFactor_natCast_ell_mul
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittResidueFactor F N ε
        ((ℓ : WittVector ℓ k) * w) = 1 := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  have hcoeff :
      (((ℓ : WittVector ℓ k) * w).coeff 0) = 0 :=
    natCast_ell_mul_wittVector_coeff_zero (ℓ := ℓ) (k := k) w
  have hzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  simp [artinHasseExpFiniteWittResidueFactor, A, Eps, hcoeff, hzero]

omit [Fintype k] in
/-- The zeroth coordinate of `[a] + ℓ * w` is `a`. -/
theorem wittVector_teichmuller_add_natCast_ell_mul_coeff_zero
    [ExpChar k ℓ] [PerfectRing k ℓ] (a : k) (w : WittVector ℓ k) :
    (WittVector.teichmuller ℓ a + (ℓ : WittVector ℓ k) * w).coeff 0 = a := by
  classical
  have hdisj :
      ∀ n : ℕ,
        (WittVector.teichmuller ℓ a).coeff n = 0 ∨
          ((ℓ : WittVector ℓ k) * w).coeff n = 0 := by
    intro n
    cases n with
    | zero =>
        exact Or.inr (natCast_ell_mul_wittVector_coeff_zero (ℓ := ℓ) (k := k) w)
    | succ n =>
        exact Or.inl (WittVector.teichmuller_coeff_pos ℓ a (n + 1) (Nat.succ_pos n))
  rw [WittVector.coeff_add_of_disjoint (n := 0)
    (WittVector.teichmuller ℓ a) ((ℓ : WittVector ℓ k) * w) hdisj]
  simp [natCast_ell_mul_wittVector_coeff_zero (ℓ := ℓ) (k := k) w]

omit [Fintype k] in
/-- The rooted tail of `[a] + ℓ * w` is `w`. -/
theorem coordinateTailRoot_teichmuller_add_natCast_ell_mul
    [ExpChar k ℓ] [PerfectRing k ℓ] (a : k) (w : WittVector ℓ k) :
    coordinateTailRoot (WittVector.teichmuller ℓ a + (ℓ : WittVector ℓ k) * w) = w := by
  classical
  ext r
  dsimp [coordinateTailRoot]
  have hdisj :
      ∀ n : ℕ,
        (WittVector.teichmuller ℓ a).coeff n = 0 ∨
          ((ℓ : WittVector ℓ k) * w).coeff n = 0 := by
    intro n
    cases n with
    | zero =>
        exact Or.inr (natCast_ell_mul_wittVector_coeff_zero (ℓ := ℓ) (k := k) w)
    | succ n =>
        exact Or.inl (WittVector.teichmuller_coeff_pos ℓ a (n + 1) (Nat.succ_pos n))
  rw [WittVector.coeff_add_of_disjoint (n := r + 1)
    (WittVector.teichmuller ℓ a) ((ℓ : WittVector ℓ k) * w) hdisj]
  rw [WittVector.teichmuller_coeff_pos ℓ a (r + 1) (Nat.succ_pos r)]
  rw [natCast_ell_mul_wittVector_coeff_succ (ℓ := ℓ) (k := k) w r]
  simp only [zero_add]
  rw [← _root_.frobeniusEquiv_def (R := k) (p := ℓ) (w.coeff r)]
  exact RingEquiv.symm_apply_apply (_root_.frobeniusEquiv k ℓ) (w.coeff r)

/-- The residue factor of `[a] + ℓ * w` only sees the Teichmüller coordinate
`a`. -/
theorem artinHasseExpFiniteWittResidueFactor_teichmuller_add_natCast_ell_mul
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (a : k) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittResidueFactor F N ε
        (WittVector.teichmuller ℓ a + (ℓ : WittVector ℓ k) * w) =
      artinHasseExpFiniteWittResidueFactor F N ε
        (WittVector.teichmuller ℓ a) := by
  rw [artinHasseExpFiniteWittResidueFactor]
  rw [artinHasseExpFiniteWittResidueFactor]
  rw [wittVector_teichmuller_add_natCast_ell_mul_coeff_zero
    (ℓ := ℓ) (k := k) a w]
  simp only [WittVector.teichmuller_coeff_zero]

/-- One-coordinate finite AH-Witt additivity/peel theorem.  A vector of the
form `[a] + ℓ * wTail` peels to the zeroth Teichmüller factor and continues on
`wTail` with parameter `ε^ℓ`. -/
theorem artinHasseExpFiniteWittCharacter_teichmuller_add_natCast_ell_mul_succ
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (a : k) (wTail : WittVector ℓ k) :
    artinHasseExpFiniteWittCharacter F N (D + 1) ε
        (WittVector.teichmuller ℓ a + (ℓ : WittVector ℓ k) * wTail) =
      artinHasseExpFiniteWittResidueFactor F N ε
        (WittVector.teichmuller ℓ a) *
        artinHasseExpFiniteWittCharacter F N D (ε ^ ℓ) wTail := by
  rw [artinHasseExpFiniteWittCharacter_succ]
  rw [artinHasseExpFiniteWittResidueFactor_teichmuller_add_natCast_ell_mul]
  rw [coordinateTailRoot_teichmuller_add_natCast_ell_mul]

/-- At zero parameter the finite AH-Witt residue factor is trivial. -/
theorem artinHasseExpFiniteWittResidueFactor_zero_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittResidueFactor F N
        (0 : 𝓞 R' ⧸ F.Q ^ (N + 1)) w = 1 := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  have hzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  simp [artinHasseExpFiniteWittResidueFactor, A, Eps, hzero]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
