module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.ZModFold
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CurrentRoot.TransportMultiplierAndFrobeniusFold

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

/-- c5B2e bridge: the named inverse-parameter full-depth finite character is
exactly the successor current-root endpoint.  Thus the remaining c5B2e
cancellation is precisely the product-level statement that this successor
current-root surface is `1`.
-/
theorem artinHasseExpTraceCarryZModFiniteCharacter_inverse_eq_currentRoot_succ_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
      artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have hfold :=
    F.traceCarryFiniteCharacter_inverse_eq_currentRoot_pow_prime N m y
  have hsucc :=
    F.artinHasseExpCurrentRootPeelProduct_pow_prime_eq_succ_of_zero_iterate
      N m y δ hδ hzero
  calc
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
        (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ := by
          simpa [A, Ips, πbar, δ] using hfold
    _ = artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) := by
          simpa [A, Ips, πbar, δ] using hsucc

/-- Equivalent c5B2e endpoint after the local recurrence: the inverse
full-depth finite character is `1` exactly when the successor current-root
endpoint is `1`. -/
theorem traceCarryFiniteCharacter_inverse_eq_one_iff_currentRoot_succ_eq_one_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y = 1 ↔
      artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hbridge :=
    F.artinHasseExpTraceCarryZModFiniteCharacter_inverse_eq_currentRoot_succ_of_le
      N m hm y
  constructor
  · intro hfinite
    calc
      artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) =
          artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y := by
            simpa [A, Ips, πbar, δ] using hbridge.symm
      _ = 1 := hfinite
  · intro hsucc
    calc
      artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
          artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) := by
            simpa [A, Ips, πbar, δ] using hbridge
      _ = 1 := hsucc

/-- Conditional c5B2e closer in the successor current-root form.  This is the
small final assembly once the product-level successor endpoint has been proved. -/
theorem traceCarryFiniteCharacter_inverse_target_of_currentRoot_succ_eq_one
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ)
    (hendpoint :
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Ips : PowerSeries A :=
        (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
      let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
      artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) = 1) :
    artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target F N m y := by
  classical
  intro hm
  dsimp only [artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target]
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  exact
    (F.traceCarryFiniteCharacter_inverse_eq_one_iff_currentRoot_succ_eq_one_of_le
      N m hm y).mpr (by
        simpa [A, Ips, πbar, δ] using hendpoint)

/-- The current-root endpoint itself is the accumulated current-root transport
multiplier once the terminal zero-boundary factor is evaluated. -/
theorem currentRoot_eq_transportMultiplier_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) =
      traceCarryCurrentRootTransportMultiplier F N y m δ := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have htransport :=
    F.traceCarryCurrentRootTransportMultiplier_mul_zeroBoundary_eq_currentRoot_of_zero_iterate
      N m y δ hδ hzero
  have hboundary :=
    F.artinHasseExpCurrentRootPeelProduct_inverse_zero_boundary_of_le
      N m 0 N hm (F.traceCarry y)
  calc
    artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) =
        traceCarryCurrentRootTransportMultiplier F N y m δ *
          artinHasseExpCurrentRootPeelProduct F N 0 N (δ ^ (ℓ ^ m))
            (F.traceCarry y) := by
          simpa [A, Ips, πbar, δ] using htransport.symm
    _ = traceCarryCurrentRootTransportMultiplier F N y m δ := by
          rw [show
            artinHasseExpCurrentRootPeelProduct F N 0 N (δ ^ (ℓ ^ m))
              (F.traceCarry y) = 1 by
              simpa [A, Ips, πbar, δ] using hboundary]
          simp

/-- The successor current-root endpoint is exactly the accumulated
current-root transport multiplier, because the remaining zero-boundary
current-root factor is literal `1`. -/
theorem currentRoot_succ_eq_transportMultiplier_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) =
      traceCarryCurrentRootTransportMultiplier F N y (m + 1) δ := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hm_succ : N + 1 ≤ ℓ ^ (m + 1) :=
    hm.trans (Nat.pow_le_pow_right (Fact.out : Nat.Prime ℓ).pos (Nat.le_succ m))
  simpa [A, Ips, πbar, δ] using
    F.currentRoot_eq_transportMultiplier_of_le N (m + 1) hm_succ y

/-- Equivalent c5B2e endpoint in transport-multiplier form.  The remaining
product-level cancellation is exactly that the full triangular transport
multiplier at depth `m + 1` is `1`. -/
theorem traceCarryFiniteCharacter_inverse_eq_one_iff_transportMultiplier_succ_eq_one_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y = 1 ↔
      traceCarryCurrentRootTransportMultiplier F N y (m + 1) δ = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hsucc :=
    F.currentRoot_succ_eq_transportMultiplier_of_le N m hm y
  have hiff :=
    F.traceCarryFiniteCharacter_inverse_eq_one_iff_currentRoot_succ_eq_one_of_le
      N m hm y
  constructor
  · intro hfinite
    have hcurrent := hiff.mp hfinite
    calc
      traceCarryCurrentRootTransportMultiplier F N y (m + 1) δ =
          artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) := by
            simpa [A, Ips, πbar, δ] using hsucc.symm
      _ = 1 := hcurrent
  · intro hmult
    exact hiff.mpr (by
      calc
        artinHasseExpCurrentRootPeelProduct F N (m + 1) N δ (F.traceCarry y) =
            traceCarryCurrentRootTransportMultiplier F N y (m + 1) δ := by
              simpa [A, Ips, πbar, δ] using hsucc
        _ = 1 := hmult)

/-- Equivalent c5B2e endpoint in the older powered transport-multiplier form. -/
theorem traceCarryFiniteCharacter_inverse_eq_one_iff_transportMultiplier_pow_prime_eq_one_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y = 1 ↔
      (traceCarryCurrentRootTransportMultiplier F N y m δ) ^ ℓ = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hcurrent :=
    F.currentRoot_eq_transportMultiplier_of_le N m hm y
  have hiff :=
    F.traceCarryFiniteCharacter_inverse_eq_one_iff_currentRoot_pow_prime_eq_one
      N m y
  constructor
  · intro hfinite
    have hpow := hiff.mp hfinite
    calc
      (traceCarryCurrentRootTransportMultiplier F N y m δ) ^ ℓ =
          (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ :=
            congrArg (fun x : A => x ^ ℓ) (by
              simpa [A, Ips, πbar, δ] using hcurrent.symm)
      _ = 1 := hpow
  · intro hmult
    exact hiff.mpr (by
      calc
        (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ =
            (traceCarryCurrentRootTransportMultiplier F N y m δ) ^ ℓ :=
              congrArg (fun x : A => x ^ ℓ) (by
                simpa [A, Ips, πbar, δ] using hcurrent)
        _ = 1 := hmult)

/-- Cancellation form of the inverse-parameter transition.  If the two
successive peeled current-root products are identified, the powered
Frobenius theta product is `1` in the quotient. -/
theorem artinHasseExp_inverse_product_pow_eq_one_of_currentRootPeel_eq_next_traceCarry_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm_pos : 0 < m) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ)
    (hpeel :
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Ips : PowerSeries A :=
        (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
      let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
      let c : WittVector ℓ k := F.traceCarry y
      artinHasseExpCurrentRootPeelProduct F N m N δ c =
        artinHasseExpCurrentRootPeelProduct F N (m - 1) N (δ ^ ℓ) c) :
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
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) = 1 := by
  classical
  dsimp only
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
  let c : WittVector ℓ k := F.traceCarry y
  let P : A :=
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m)
  let U : A := artinHasseExpCurrentRootPeelProduct F N m N δ c
  let V : A := artinHasseExpCurrentRootPeelProduct F N (m - 1) N (δ ^ ℓ) c
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have htransition : P * U = V := by
    simpa [A, Eps, Ips, πbar, δ, zbar, c, P, U, V] using
      F.artinHasseExp_inverse_product_pow_mul_currentRootPeel_eq_next_traceCarry_of_le
        N m hm_pos hm y
  have hpeel' : U = V := by
    simpa [A, Ips, πbar, δ, c, U, V] using hpeel
  have hUunit : IsUnit U := by
    simpa [A, Ips, πbar, δ, c, U] using
      F.artinHasseExpCurrentRootPeelProduct_isUnit_of_pow_succ_eq_zero
        N m N δ hδ c
  have hPU : P * U = 1 * U := by
    rw [htransition, ← hpeel']
    simp
  have hP : P = 1 := hUunit.mul_right_cancel hPU
  simpa [A, Eps, Ips, πbar, δ, zbar, P] using hP

/-- Actual inverse-parameter version of the coordinate-peeled carry-free
comparison.  At the Dwork inverse parameter the powered base side is `1`, so
the remaining powered product is measured exactly by the peeled coordinate
product and the unshifted Witt tail. -/
theorem exists_artinHasseExp_inverse_mul_tail_eq_coordinatePeelProduct_of_le
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
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    ∃ c : WittVector ℓ k,
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
              (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) =
        artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
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
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hδzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  obtain ⟨c, hcmp⟩ :=
    F.exists_artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_coordinatePeelProduct
      N m hm_pos y δ hδ hδzero
  have hbase :=
    F.artinHasseExp_inverse_base_trace_pow_prime_iterate_eq_one_of_pos
      N m hm_pos y
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)))
        =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
          simpa [A, θ, Eps, Ips, πbar, δ, zbar, t] using hcmp
    _ =
          artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
          rw [show (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ t) ^
              (ℓ ^ m) = 1 by
            simpa [A, Eps, Ips, πbar, δ, t] using hbase]
          simp

/-- Rooted-current-tail form of the inverse-parameter coordinate comparison.
The unshifted tail on the product side is converted to the rooted
Frobenius-coordinate shape, while the right side remains the already peeled
coordinate product. -/
theorem exists_artinHasseExp_inverse_mul_rootTail_eq_coordinatePeelProduct_of_le
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
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    ∃ c : WittVector ℓ k,
      let cRoot : WittVector ℓ k :=
        WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        (∏ j ∈ Finset.range (m + 1),
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    (cRoot.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
        artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
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
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  obtain ⟨c, hcmp⟩ :=
    F.exists_artinHasseExp_inverse_mul_tail_eq_coordinatePeelProduct_of_le
      N m hm_pos hm y
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  have hδzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have htail :=
    F.artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
      N N m δ hδzero c
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cRoot.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)))
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            (∏ j ∈ Finset.range m,
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (δ ^ (ℓ ^ j) *
                    θ (WittVector.teichmuller ℓ
                      (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
                  (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) := by
          rw [htail]
    _ =
          artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
          simpa [A, θ, Eps, Ips, πbar, δ, zbar] using hcmp

/-- Fully peeled product form of the inverse-parameter comparison.  The
rooted current tail in
`exists_artinHasseExp_inverse_mul_rootTail_eq_coordinatePeelProduct_of_le`
is eliminated by the current-root coordinate telescope, leaving only the
powered Frobenius product and two explicit peeled coordinate products. -/
theorem exists_artinHasseExp_inverse_pow_mul_currentRootPeel_eq_coordinatePeelProduct_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm_pos : 0 < m) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
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
    ∃ c : WittVector ℓ k,
      let cRoot : WittVector ℓ k :=
        WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        artinHasseExpCurrentRootPeelProduct F N m N δ cRoot =
        artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
  classical
  dsimp only
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
  obtain ⟨c, hcmp⟩ :=
    F.exists_artinHasseExp_inverse_mul_rootTail_eq_coordinatePeelProduct_of_le
      N m hm_pos hm y
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  have hδzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have hroot :=
    F.artinHasseExp_current_root_tail_depth_eq_currentRootPeelProduct_of_zero_iterate
      N N m δ hδzero cRoot
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      artinHasseExpCurrentRootPeelProduct F N m N δ cRoot
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            (∏ j ∈ Finset.range (m + 1),
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (δ ^ (ℓ ^ j) *
                    F.toConcreteStickelbergerSetup.wittThetaModQPow N
                      (WittVector.teichmuller ℓ
                        ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                          (cRoot.coeff r)) ^ ℓ)))) ^
                  (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) := by
          rw [hroot]
    _ =
          artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
          simpa [A, Eps, Ips, πbar, δ, zbar, cRoot] using hcmp

/-- Transition form of the fully peeled inverse-parameter comparison.  The
right side is rewritten as the same current-root peeled product at the
Frobenius-shifted parameter `δ^ℓ`. -/
theorem exists_artinHasseExp_inverse_pow_mul_currentRootPeel_eq_currentRootPeel_frobenius_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm_pos : 0 < m) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
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
    ∃ c : WittVector ℓ k,
      let cRoot : WittVector ℓ k :=
        WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        artinHasseExpCurrentRootPeelProduct F N m N δ cRoot =
        artinHasseExpCurrentRootPeelProduct F N (m - 1) N (δ ^ ℓ) c := by
  classical
  dsimp only
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
  obtain ⟨c, hcmp⟩ :=
    F.exists_artinHasseExp_inverse_pow_mul_currentRootPeel_eq_coordinatePeelProduct_of_le
      N m hm_pos hm y
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      artinHasseExpCurrentRootPeelProduct F N m N δ
        (WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r)))
        =
          artinHasseExpCoordinatePeelProduct F N (m - 1) N δ c := by
          simpa [A, Eps, Ips, πbar, δ, zbar] using hcmp
    _ =
          artinHasseExpCurrentRootPeelProduct F N (m - 1) N (δ ^ ℓ) c := by
          rw [F.artinHasseExpCoordinatePeelProduct_eq_currentRootPeelProduct_frobenius_parameter]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
