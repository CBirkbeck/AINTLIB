module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.TraceCarry
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CoordinatePeel.CoordinatePeelInduction

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

/-- If a Witt vector is the `s`-shifted coordinate tail of the fixed trace
carry, then the generic peeled product is exactly the trace-carry peeled
product in prime-field coordinates. -/
theorem artinHasseExpCoordinatePeelProduct_eq_traceCarryZModPeelProduct_of_coeff_eq
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    {c : WittVector ℓ k}
    (hcoeff : ∀ r : ℕ, c.coeff r = (F.traceCarry y).coeff (r + s)) :
    artinHasseExpCoordinatePeelProduct F N m D ε c =
      artinHasseExpTraceCarryZModPeelProduct F N m D s ε y := by
  classical
  induction D generalizing m s c with
  | zero =>
      simp only [artinHasseExpCoordinatePeelProduct,
        artinHasseExpTraceCarryZModPeelProduct]
      refine Finset.prod_congr rfl ?_
      intro j _hj
      have hcoord :
          c.coeff 0 ^ ℓ =
            algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s) := by
        rw [hcoeff 0, zero_add]
        exact (F.traceCarryCoeffZMod_pow_prime_spec y s).symm
      rw [hcoord]
  | succ D ih =>
      simp only [artinHasseExpCoordinatePeelProduct,
        artinHasseExpTraceCarryZModPeelProduct]
      congr 1
      · refine Finset.prod_congr rfl ?_
        intro j _hj
        have hcoord :
            c.coeff 0 ^ ℓ =
              algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s) := by
          rw [hcoeff 0, zero_add]
          exact (F.traceCarryCoeffZMod_pow_prime_spec y s).symm
        rw [hcoord]
      · refine ih (m + 1) (s + 1) ?_
        intro r
        dsimp [coordinateTailRoot]
        have hroot :
            (_root_.frobeniusEquiv k ℓ).symm
                ((F.traceCarry y).coeff (r + (s + 1))) =
              (F.traceCarry y).coeff (r + (s + 1)) := by
          simpa using
            F.traceCarry_coeff_frobeniusEquiv_symm_iterate_eq_self
              y 1 (r + (s + 1))
        rw [hcoeff (r + 1)]
        have hidx : (r + 1) + s = r + (s + 1) := by omega
        rw [hidx]
        exact hroot

/-- Trace-carry specialization of the accumulated coordinate peel. -/
theorem artinHasseExpCoordinatePeelProduct_traceCarry_eq_zmodPeelProduct
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    artinHasseExpCoordinatePeelProduct F N m D ε (F.traceCarry y) =
      artinHasseExpTraceCarryZModPeelProduct F N m D 0 ε y := by
  refine
    F.artinHasseExpCoordinatePeelProduct_eq_traceCarryZModPeelProduct_of_coeff_eq
      N m D 0 ε y ?_
  intro r
  simp

/-- Coordinate-depth iteration of the trace-carry peel.  The Frobenius-shifted
tail is eliminated by induction on coordinate depth and replaced by the
accumulated product of the selected prime-field trace-carry coordinates. -/
theorem artinHasseExp_frobenius_tail_depth_traceCarry_eq_zmodPeelProduct_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hzero : ε ^ (ℓ ^ (m + 1)) = 0) (y : kˣ) :
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
                  ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      artinHasseExpTraceCarryZModPeelProduct F N m D 0 ε y := by
  classical
  dsimp only
  rw [← F.artinHasseExpCoordinatePeelProduct_traceCarry_eq_zmodPeelProduct]
  simpa using
    F.artinHasseExp_frobenius_tail_depth_eq_coordinatePeelProduct_of_zero_iterate
      N D m ε hzero (F.traceCarry y)

/-- Inverse-parameter specialization of the coordinate-depth trace-carry
peel. -/
theorem artinHasseExp_inverse_frobenius_tail_depth_traceCarry_eq_zmodPeelProduct_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (hm : N + 1 ≤ ℓ ^ (m + 1)) (y : kˣ) :
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
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((δ ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      artinHasseExpTraceCarryZModPeelProduct F N m D 0 δ y := by
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
  have hzero : δ ^ (ℓ ^ (m + 1)) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le
        N (m + 1) hm
  simpa [A, θ, Eps, Ips, πbar, δ] using
    F.artinHasseExp_frobenius_tail_depth_traceCarry_eq_zmodPeelProduct_of_zero_iterate
      N D m δ hzero y

/-- Normalized trace-carry peeled product.  This is definitionally parallel to
`artinHasseExpTraceCarryZModPeelProduct`, but each peeled coordinate factor is
written as a power whose exponent has an explicit left factor `ℓ`. -/
noncomputable def artinHasseExpTraceCarryZModPeelProductDivisible
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
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^
          (ℓ * ℓ ^ (m - j))
  | m, D + 1, s, ε, y =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^
          (ℓ * ℓ ^ (m - j))) *
        artinHasseExpTraceCarryZModPeelProductDivisible N (m + 1) D (s + 1) ε y

/-- The accumulated trace-carry peeled product has the normalized
`ℓ`-divisible exponent form needed for the next root-of-unity cancellation
step. -/
theorem artinHasseExpTraceCarryZModPeelProduct_eq_divisible
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    artinHasseExpTraceCarryZModPeelProduct F N m D s ε y =
      artinHasseExpTraceCarryZModPeelProductDivisible F N m D s ε y := by
  classical
  induction D generalizing m s with
  | zero =>
      simp only [artinHasseExpTraceCarryZModPeelProduct,
        artinHasseExpTraceCarryZModPeelProductDivisible]
      refine Finset.prod_congr rfl ?_
      intro j _hj
      rw [pow_mul]
  | succ D ih =>
      simp only [artinHasseExpTraceCarryZModPeelProduct,
        artinHasseExpTraceCarryZModPeelProductDivisible]
      congr 1
      · refine Finset.prod_congr rfl ?_
        intro j _hj
        rw [pow_mul]
      · exact ih (m + 1) (s + 1)

/-- Inverse-parameter trace-carry tail collapse with every peeled coordinate
factor normalized to an explicitly `ℓ`-divisible exponent. -/
theorem artinHasseExp_inverse_frobenius_tail_depth_traceCarry_eq_divisiblePeelProduct_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (hm : N + 1 ≤ ℓ ^ (m + 1)) (y : kˣ) :
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
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((δ ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      artinHasseExpTraceCarryZModPeelProductDivisible F N m D 0 δ y := by
  classical
  dsimp only
  rw [← F.artinHasseExpTraceCarryZModPeelProduct_eq_divisible]
  simpa using
    F.artinHasseExp_inverse_frobenius_tail_depth_traceCarry_eq_zmodPeelProduct_of_le
      N D m hm y

/-- Full-depth wrapper for the c4c carry term.  This is just the normalized
coordinate-depth trace-carry peel at `D = N`, written with the same positive
iteration index `m` used by the surrounding inverse-product telescope. -/
theorem artinHasseExp_inverse_traceCarry_fullDepth_tail_eq_divisiblePeelProduct_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm_pos : 0 < m) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
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
            ((δ ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) =
      artinHasseExpTraceCarryZModPeelProductDivisible F N (m - 1) N 0 δ y := by
  classical
  dsimp only
  have hm_succ : m - 1 + 1 = m :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  have hm' : N + 1 ≤ ℓ ^ ((m - 1) + 1) := by
    simpa [hm_succ] using hm
  simpa [hm_succ] using
    F.artinHasseExp_inverse_frobenius_tail_depth_traceCarry_eq_divisiblePeelProduct_of_le
      N N (m - 1) hm' y

/-- Conditional root-of-unity cancellation for the normalized trace-carry peel.
This lemma isolates the exact remaining mathematical input for WC3c: after
WC3b every peeled coordinate appears with an exponent `ℓ * _`, so the whole
finite product is `1` as soon as each displayed peeled base is an `ℓ`-th root
of unity. -/
theorem artinHasseExpTraceCarryZModPeelProductDivisible_eq_one_of_factor_pow_prime_eq_one
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    (hroot :
      ∀ m s j : ℕ, j ∈ Finset.range m →
        let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
        let θ : WittVector ℓ k →+* A :=
          F.toConcreteStickelbergerSetup.wittThetaModQPow N
        let Eps : PowerSeries A :=
          (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
            fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
              (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^ ℓ = 1) :
    artinHasseExpTraceCarryZModPeelProductDivisible F N m D s ε y = 1 := by
  classical
  induction D generalizing m s with
  | zero =>
      simp only [artinHasseExpTraceCarryZModPeelProductDivisible]
      refine Finset.prod_eq_one ?_
      intro j hj
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let B : A :=
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))
      have hB : B ^ ℓ = 1 := by
        simpa [A, θ, Eps, B] using hroot m s j hj
      rw [pow_mul, hB, one_pow]
  | succ D ih =>
      simp only [artinHasseExpTraceCarryZModPeelProductDivisible]
      have hprod :
          (let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
           let θ : WittVector ℓ k →+* A :=
             F.toConcreteStickelbergerSetup.wittThetaModQPow N
           let Eps : PowerSeries A :=
             (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
               fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
                 (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
           ∏ j ∈ Finset.range m,
             ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
               ((ε ^ (ℓ ^ j)) ^ ℓ *
                 θ (WittVector.teichmuller ℓ
                   (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))) ^
               (ℓ * ℓ ^ (m - j))) = 1 := by
        refine Finset.prod_eq_one ?_
        intro j hj
        let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
        let θ : WittVector ℓ k →+* A :=
          F.toConcreteStickelbergerSetup.wittThetaModQPow N
        let Eps : PowerSeries A :=
          (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
            fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
              (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        let B : A :=
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s))))
        have hB : B ^ ℓ = 1 := by
          simpa [A, θ, Eps, B] using hroot m s j hj
        rw [pow_mul, hB, one_pow]
      have htail :
          artinHasseExpTraceCarryZModPeelProductDivisible F N (m + 1) D (s + 1) ε y =
            1 :=
        ih (m + 1) (s + 1)
      simpa [hprod, htail]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
