module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.ZModFold
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CurrentRoot.PeelProductIsUnitAndTriangularExpansion

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

/-- Parameter-general transition form of the carry-free powered comparison.
After converting the unshifted tail to rooted-current shape, the equation
relates a current-root peeled product at `ε` to the corresponding current-root
peeled product at `ε^ℓ`, with the powered base side still visible. -/
theorem exists_artinHasseExp_product_iterate_currentRootPeel_transition_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : 0 < m) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      let cRoot : WittVector ℓ k :=
        WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        artinHasseExpCurrentRootPeelProduct F N m N ε cRoot =
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c := by
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
  obtain ⟨c, hcmp⟩ :=
    F.exists_artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_coordinatePeelProduct
      N m hm y ε hε hzero
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  have htail :=
    F.artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
      N N m ε hzero c
  have hroot :=
    F.artinHasseExp_current_root_tail_depth_eq_currentRootPeelProduct_of_zero_iterate
      N N m ε hzero cRoot
  have hcoord :
      artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c =
        artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c := by
    rw [F.artinHasseExpCoordinatePeelProduct_eq_currentRootPeelProduct_frobenius_parameter]
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      artinHasseExpCurrentRootPeelProduct F N m N ε cRoot
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            (∏ j ∈ Finset.range (m + 1),
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ j) *
                    θ (WittVector.teichmuller ℓ
                      ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                        (cRoot.coeff r)) ^ ℓ)))) ^
                  (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) := by
          rw [hroot]
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            (∏ j ∈ Finset.range m,
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ j) *
                    θ (WittVector.teichmuller ℓ
                      (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
                  (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) := by
          rw [← htail]
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
          simpa [A, θ, Eps, zbar, t] using hcmp
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c := by
          rw [hcoord]

/-- Chainable parameter-general transition for the canonical trace carry.
The Frobenius root on the current side has been removed using
`traceCarry_root_eq_self`, so the same carry appears on both sides. -/
theorem artinHasseExp_product_iterate_currentRootPeel_transition_traceCarry_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : 0 < m) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
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
      artinHasseExpCurrentRootPeelProduct F N m N ε c =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
          (ℓ ^ m) *
        artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c := by
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
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  have hcRoot : cRoot = c := by
    simpa [c, cRoot] using F.traceCarry_root_eq_self y
  have hcmp :=
    F.artinHasseExp_product_iterate_coordinatePeel_traceCarry
      N m hm y ε hε hzero
  have htail :=
    F.artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
      N N m ε hzero c
  have hroot :=
    F.artinHasseExp_current_root_tail_depth_eq_currentRootPeelProduct_of_zero_iterate
      N N m ε hzero cRoot
  have hcoord :
      artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c =
        artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c := by
    rw [F.artinHasseExpCoordinatePeelProduct_eq_currentRootPeelProduct_frobenius_parameter]
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      artinHasseExpCurrentRootPeelProduct F N m N ε c
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            artinHasseExpCurrentRootPeelProduct F N m N ε cRoot := by
          rw [hcRoot]
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            (∏ j ∈ Finset.range (m + 1),
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ j) *
                    θ (WittVector.teichmuller ℓ
                      ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                        (cRoot.coeff r)) ^ ℓ)))) ^
                  (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) := by
          rw [hroot]
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            (∏ j ∈ Finset.range m,
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ j) *
                    θ (WittVector.teichmuller ℓ
                      (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
                  (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))) := by
          rw [← htail]
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c := by
          simpa [A, θ, Eps, zbar, t, c] using hcmp
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) *
          artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c := by
          rw [hcoord]

/-- Product-level current-root transport with the accumulated trace-carry
correction as multiplier.  This is the non-circular form of the WC3c endpoint:
the carry correction transports the Frobenius-shifted current-root endpoint
back to the unshifted one. -/
theorem traceCarryIterCorrection_mul_currentRootPeelProduct_frobenius_eq_currentRootPeelProduct
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm_pos : 0 < m) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let c : WittVector ℓ k := F.traceCarry y
    F.artinHasseExpTraceCarryIterCorrection N y ε m *
        artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c =
      artinHasseExpCurrentRootPeelProduct F N m N ε c := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let c : WittVector ℓ k := F.traceCarry y
  let cRoot : WittVector ℓ k :=
    WittVector.mk ℓ (fun r => (_root_.frobeniusEquiv k ℓ).symm (c.coeff r))
  have hcRoot : cRoot = c := by
    simpa [c, cRoot] using F.traceCarry_root_eq_self y
  have hpred_succ : m - 1 + 1 = m :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  have hzero_shift : (ε ^ ℓ) ^ (ℓ ^ (m - 1)) = 0 := by
    have hpow : (ε ^ ℓ) ^ (ℓ ^ (m - 1)) = ε ^ (ℓ ^ m) := by
      rw [← pow_mul]
      congr 1
      calc
        ℓ * ℓ ^ (m - 1) = ℓ ^ (m - 1) * ℓ := by
          rw [Nat.mul_comm]
        _ = ℓ ^ ((m - 1) + 1) := by
          rw [pow_succ]
        _ = ℓ ^ m := by
          rw [hpred_succ]
    rw [hpow, hzero]
  have hcarry :=
    F.traceCarryIterCorrection_mul_teichmuller_frobenius_tail_eq_tail_traceCarry
      N m y ε hε
  have hshift :=
    F.artinHasseExp_current_root_tail_depth_eq_currentRootPeelProduct_of_zero_iterate
      N N (m - 1) (ε ^ ℓ) hzero_shift c
  have htail :=
    F.artinHasseExp_tail_current_range_depth_eq_frobenius_root_tail_succ_depth_of_zero_iterate
      N N m ε hzero c
  have hcurrent :=
    F.artinHasseExp_current_root_tail_depth_eq_currentRootPeelProduct_of_zero_iterate
      N N m ε hzero cRoot
  calc
    F.artinHasseExpTraceCarryIterCorrection N y ε m *
        artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c
        =
          F.artinHasseExpTraceCarryIterCorrection N y ε m *
            (∏ j ∈ Finset.range m,
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  ((ε ^ (ℓ ^ j)) ^ ℓ *
                    θ (WittVector.teichmuller ℓ
                      ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                        ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
                  (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) := by
          rw [← hshift]
          refine congrArg (fun x : A => F.artinHasseExpTraceCarryIterCorrection N y ε m * x) ?_
          refine Finset.prod_congr ?_ ?_
          · ext j
            simp [hpred_succ]
          · intro j hj
            refine congrArg (fun x : A => x ^ (ℓ ^ (m - 1 - j))) ?_
            refine Finset.prod_congr rfl ?_
            intro r hr
            have hparam : (ε ^ ℓ) ^ (ℓ ^ j) = (ε ^ (ℓ ^ j)) ^ ℓ := by
              rw [← pow_mul, ← pow_mul]
              congr 1
              exact Nat.mul_comm ℓ (ℓ ^ j)
            rw [hparam]
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      ((F.traceCarry y).coeff r))))) ^
                (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)) := by
          simpa [A, θ, Eps] using hcarry
    _ =
          ∏ j ∈ Finset.range (m + 1),
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      (cRoot.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, c, cRoot] using htail
    _ =
          artinHasseExpCurrentRootPeelProduct F N m N ε c := by
          rw [hcurrent]
          rw [hcRoot]

/-- Accumulated multiplier obtained by iterating the product-level
trace-carry transport from `ε` to `ε^(ℓ^m)`. -/
noncomputable def traceCarryCurrentRootTransportMultiplier
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (F : FullTeichStickelbergerSetup ℓ p k K R') (N : ℕ) (y : kˣ) :
    ℕ → (𝓞 R' ⧸ F.Q ^ (N + 1)) → 𝓞 R' ⧸ F.Q ^ (N + 1)
  | 0, _ => 1
  | m + 1, ε =>
      F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1) *
        traceCarryCurrentRootTransportMultiplier F N y m (ε ^ ℓ)

/-- Bundled product-level transport from the zero-boundary current-root
endpoint to the original current-root endpoint.  The remaining c5 task is to
show that the multiplier in this statement has `ℓ`-th power `1`. -/
theorem traceCarryCurrentRootTransportMultiplier_mul_zeroBoundary_eq_currentRoot_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let c : WittVector ℓ k := F.traceCarry y
    traceCarryCurrentRootTransportMultiplier F N y m ε *
        artinHasseExpCurrentRootPeelProduct F N 0 N (ε ^ (ℓ ^ m)) c =
      artinHasseExpCurrentRootPeelProduct F N m N ε c := by
  classical
  dsimp only
  induction m generalizing ε with
  | zero =>
      simp [traceCarryCurrentRootTransportMultiplier]
  | succ m ih =>
      let c : WittVector ℓ k := F.traceCarry y
      have hε_shift : (ε ^ ℓ) ^ (N + 1) = 0 := by
        simpa using
          F.parameter_pow_iterate_pow_succ_eq_zero N 1 ε hε
      have hboundary : (ε ^ ℓ) ^ (ℓ ^ m) = ε ^ (ℓ ^ (m + 1)) := by
        rw [← pow_mul]
        congr 1
        calc
          ℓ * ℓ ^ m = ℓ ^ m * ℓ := by
            rw [Nat.mul_comm]
          _ = ℓ ^ (m + 1) := by
            rw [pow_succ]
      have hzero_shift : (ε ^ ℓ) ^ (ℓ ^ m) = 0 := by
        rw [hboundary, hzero]
      have htail := ih (ε ^ ℓ) hε_shift hzero_shift
      have hstep :=
        F.traceCarryIterCorrection_mul_currentRootPeelProduct_frobenius_eq_currentRootPeelProduct
          N (m + 1) (Nat.succ_pos m) y ε hε hzero
      calc
        traceCarryCurrentRootTransportMultiplier F N y (m + 1) ε *
            artinHasseExpCurrentRootPeelProduct F N 0 N (ε ^ (ℓ ^ (m + 1))) c
            =
              (F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1) *
                  traceCarryCurrentRootTransportMultiplier F N y m (ε ^ ℓ)) *
                artinHasseExpCurrentRootPeelProduct F N 0 N ((ε ^ ℓ) ^ (ℓ ^ m)) c := by
              rw [← hboundary]
              simp [traceCarryCurrentRootTransportMultiplier]
        _ =
              F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1) *
                (traceCarryCurrentRootTransportMultiplier F N y m (ε ^ ℓ) *
                  artinHasseExpCurrentRootPeelProduct F N 0 N ((ε ^ ℓ) ^ (ℓ ^ m)) c) := by
              ring
        _ =
              F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1) *
                artinHasseExpCurrentRootPeelProduct F N m N (ε ^ ℓ) c := by
              rw [htail]
        _ =
              artinHasseExpCurrentRootPeelProduct F N (m + 1) N ε c := by
              simpa [c] using hstep

/-- Powered transport conditional on the accumulated multiplier being
`ℓ`-torsion.  This is the exact non-circular final shape needed by c5. -/
theorem currentRoot_transport_to_zeroBoundary_pow_prime_of_transportMultiplier_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0)
    (hmult :
      (traceCarryCurrentRootTransportMultiplier F N y m ε) ^ ℓ = 1) :
    let c : WittVector ℓ k := F.traceCarry y
    (artinHasseExpCurrentRootPeelProduct F N m N ε c) ^ ℓ =
      (artinHasseExpCurrentRootPeelProduct F N 0 N (ε ^ (ℓ ^ m)) c) ^ ℓ := by
  classical
  dsimp only
  let c : WittVector ℓ k := F.traceCarry y
  have htransport :=
    F.traceCarryCurrentRootTransportMultiplier_mul_zeroBoundary_eq_currentRoot_of_zero_iterate
      N m y ε hε hzero
  calc
    (artinHasseExpCurrentRootPeelProduct F N m N ε c) ^ ℓ =
        (traceCarryCurrentRootTransportMultiplier F N y m ε *
          artinHasseExpCurrentRootPeelProduct F N 0 N (ε ^ (ℓ ^ m)) c) ^ ℓ := by
        rw [← htransport]
    _ =
        (traceCarryCurrentRootTransportMultiplier F N y m ε) ^ ℓ *
          (artinHasseExpCurrentRootPeelProduct F N 0 N (ε ^ (ℓ ^ m)) c) ^ ℓ := by
        rw [mul_pow]
    _ =
        (artinHasseExpCurrentRootPeelProduct F N 0 N (ε ^ (ℓ ^ m)) c) ^ ℓ := by
        rw [hmult]
        simp

/-- Conditional WC3c closure from the single remaining product-level torsion
statement for the accumulated current-root transport multiplier. -/
theorem traceCarryFiniteCharacter_inverse_target_of_transportMultiplier_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ)
    (hm : N + 1 ≤ ℓ ^ m)
    (hmult :
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Ips : PowerSeries A :=
        (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
      let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
      (traceCarryCurrentRootTransportMultiplier F N y m δ) ^ ℓ = 1) :
    artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target F N m y := by
  classical
  refine
    F.traceCarryFiniteCharacter_inverse_target_of_currentRoot_transport_to_zero_boundary
      N m y hm ?_
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
  exact
    F.currentRoot_transport_to_zeroBoundary_pow_prime_of_transportMultiplier_pow_prime
      N m y δ hδ hzero (by
        simpa [A, Ips, πbar, δ] using hmult)

/-- Actual inverse-parameter transition for the canonical trace carry.  The
normalized base side has positive `ℓ`-power equal to `1`, so the
Frobenius-parameter transition becomes an equality between the powered
theta product with the current rooted peel and the next rooted peel. -/
theorem artinHasseExp_inverse_product_pow_mul_currentRootPeel_eq_next_traceCarry_of_le
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
    let c : WittVector ℓ k := F.traceCarry y
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      artinHasseExpCurrentRootPeelProduct F N m N δ c =
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
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let c : WittVector ℓ k := F.traceCarry y
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  have htransition :=
    F.artinHasseExp_product_iterate_currentRootPeel_transition_traceCarry_of_zero_iterate
      N m hm_pos y δ hδ hzero
  have hbase :
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ t) ^
          (ℓ ^ m) = 1 := by
    simpa [A, Eps, Ips, πbar, δ, t] using
      F.artinHasseExp_inverse_base_trace_pow_prime_iterate_eq_one_of_pos
        N m hm_pos y
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
      artinHasseExpCurrentRootPeelProduct F N m N δ c
        =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ t) ^
              (ℓ ^ m) *
            artinHasseExpCurrentRootPeelProduct F N (m - 1) N (δ ^ ℓ) c := by
          simpa [A, Eps, Ips, πbar, δ, zbar, t, c] using htransition
    _ = artinHasseExpCurrentRootPeelProduct F N (m - 1) N (δ ^ ℓ) c := by
          rw [hbase]
          simp

/-- At the actual inverse-series parameter, the normalized full-depth
trace-carry peel is exactly the next current-root boundary term.  This is the
product-level identification between the Frobenius-shifted peeled tail and the
current-root telescope at the advanced parameter `δ^ℓ`.
-/
theorem traceCarryDivisiblePeel_eq_currentRoot_frobenius_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm_pos : 0 < m) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    artinHasseExpTraceCarryZModPeelProductDivisible F N (m - 1) N 0 ε y =
      artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ)
        (F.traceCarry y) := by
  classical
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
  let Ppow : A :=
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m)
  let Tail0 : A :=
    ∏ j ∈ Finset.range m,
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
          (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))
  let Tail : A := artinHasseExpTraceCarryZModPeelProductDivisible F N (m - 1) N 0 ε y
  let FrobTail : A :=
    ∏ j ∈ Finset.range m,
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
          (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))
  let Coord : A := artinHasseExpCoordinatePeelProduct F N (m - 1) N ε c
  let CurrentShift : A := artinHasseExpCurrentRootPeelProduct F N (m - 1) N (ε ^ ℓ) c
  let B : A :=
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m)
  have hm_succ : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  have hzero_peel : ε ^ (ℓ ^ ((m - 1) + 1)) = 0 := by
    simpa [hm_succ] using hzero
  have hpeel :
      FrobTail = Tail := by
    calc
      FrobTail = artinHasseExpTraceCarryZModPeelProduct F N (m - 1) N 0 ε y := by
        simpa [A, θ, Eps, c, FrobTail, hm_succ] using
          F.artinHasseExp_frobenius_tail_depth_traceCarry_eq_zmodPeelProduct_of_zero_iterate
            N N (m - 1) ε hzero_peel y
      _ = Tail := by
        rw [F.artinHasseExpTraceCarryZModPeelProduct_eq_divisible]
  have hfrob :
      Ppow * Tail0 = B * FrobTail := by
    simpa [A, θ, Eps, zbar, t, c, Ppow, Tail0, FrobTail, B] using
      F.artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_frobenius_tail_traceCarry
        N m y ε hε hzero
  have hcoord :
      Ppow * Tail0 = B * Coord := by
    simpa [A, θ, Eps, zbar, t, c, Ppow, Tail0, Coord, B] using
      F.artinHasseExp_product_iterate_coordinatePeel_traceCarry
        N m hm_pos y ε hε hzero
  have hEvalUnit :
      IsUnit ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) := by
    simpa [A, Eps] using
      F.artinHasseExp_trunc_eval_pow_iterate_mul_isUnit_of_pow_succ_eq_zero
        N 0 ε (1 : A) hε
  have hBunit : IsUnit B :=
    (hEvalUnit.pow t).pow (ℓ ^ m)
  have hBCancel : B * Tail = B * Coord := by
    calc
      B * Tail = B * FrobTail := by rw [← hpeel]
      _ = Ppow * Tail0 := hfrob.symm
      _ = B * Coord := hcoord
  have htailCoord : Tail = Coord :=
    hBunit.mul_left_cancel hBCancel
  calc
    Tail = Coord := htailCoord
    _ = CurrentShift := by
          simpa [Coord, CurrentShift] using
            (F.artinHasseExpCoordinatePeelProduct_eq_currentRootPeelProduct_frobenius_parameter
              N (m - 1) N ε c)

/-- At the actual inverse-series parameter, the normalized full-depth
trace-carry peel is exactly the next current-root boundary term.  This is the
product-level identification between the Frobenius-shifted peeled tail and the
current-root telescope at the advanced parameter `δ^ℓ`.
-/
theorem traceCarryDivisiblePeel_inverse_eq_currentRoot_frobenius_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm_pos : 0 < m) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModPeelProductDivisible F N (m - 1) N 0 δ y =
      artinHasseExpCurrentRootPeelProduct F N (m - 1) N (δ ^ ℓ)
        (F.traceCarry y) := by
  classical
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
  simpa [A, Ips, πbar, δ] using
    F.traceCarryDivisiblePeel_eq_currentRoot_frobenius_of_zero_iterate
      N m hm_pos y δ hδ hzero

/-- Parameter-general current-root fold: the recursive zmod correction product
multiplied by the Frobenius-shifted current-root surface at the next
parameter is exactly the `ℓ`-th power of the present current-root endpoint.
This is the parameter-general local fold underlying the final triangular
cancellation.
-/
theorem artinHasseExpTraceCarryZModCorrection_mul_currentRoot_shifted_eq_currentRoot_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    artinHasseExpTraceCarryZModCorrectionProduct F N m N 0 ε y *
      artinHasseExpCurrentRootPeelProduct F N m N (ε ^ ℓ)
        (F.traceCarry y) =
      (artinHasseExpCurrentRootPeelProduct F N m N ε (F.traceCarry y)) ^ ℓ := by
  have hε_iter : ∀ j : ℕ, (ε ^ (ℓ ^ j)) ^ (N + 1) = 0 := fun j =>
    F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε
  have hzero_succ : ε ^ (ℓ ^ (m + 1)) = 0 := by
    have hexp : ℓ ^ (m + 1) = ℓ ^ m * ℓ := by
      rw [pow_succ]
    calc
      ε ^ (ℓ ^ (m + 1)) = ε ^ (ℓ ^ m * ℓ) := by
        rw [hexp]
      _ = (ε ^ (ℓ ^ m)) ^ ℓ := by
        rw [pow_mul]
      _ = 0 := by
        rw [hzero]
        exact zero_pow (Fact.out : Nat.Prime ℓ).ne_zero
  have hfold :=
    F.artinHasseExpTraceCarryZModCorrection_mul_peel_eq_currentRoot_pow_prime
      N m N 0 ε y hε_iter
  have hpeel :
      artinHasseExpCurrentRootPeelProduct F N m N (ε ^ ℓ) (F.traceCarry y) =
        artinHasseExpTraceCarryZModPeelProductDivisible F N m N 0 ε y := by
    simpa using
      (F.traceCarryDivisiblePeel_eq_currentRoot_frobenius_of_zero_iterate
        N (m + 1) (Nat.succ_pos _) y ε hε hzero_succ).symm
  have hmk :
      (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + 0)) = F.traceCarry y := by
    ext r
    simp
  calc
    artinHasseExpTraceCarryZModCorrectionProduct F N m N 0 ε y *
        artinHasseExpCurrentRootPeelProduct F N m N (ε ^ ℓ)
          (F.traceCarry y)
        = artinHasseExpTraceCarryZModCorrectionProduct F N m N 0 ε y *
            artinHasseExpTraceCarryZModPeelProductDivisible F N m N 0 ε y := by
            rw [hpeel]
    _ =
        (artinHasseExpCurrentRootPeelProduct F N m N ε (F.traceCarry y)) ^ ℓ := by
          rw [hmk] at hfold
          exact hfold

/-- Parameter-general c5B2 recurrence: once the full-depth current-root
surface is folded against the same-parameter adjusted-product telescope, its
`ℓ`-th power is exactly the next current-root endpoint at the same base
parameter.  This is the diagonal `U/C/P/B` cancellation at one fixed
parameter, before specializing to the inverse boundary. -/
theorem artinHasseExpCurrentRootPeelProduct_pow_prime_eq_succ_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    (artinHasseExpCurrentRootPeelProduct F N m N ε (F.traceCarry y)) ^ ℓ =
      artinHasseExpCurrentRootPeelProduct F N (m + 1) N ε (F.traceCarry y) := by
  classical
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
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let P : A :=
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε * zbar ^ (ℓ ^ (i : ℕ)))
  let Prod : A := P ^ (ℓ ^ (m + 1))
  let B : A := (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
    (ℓ ^ (m + 1))
  let Corr : A := artinHasseExpTraceCarryZModCorrectionProduct F N m N 0 ε y
  let Shift : A :=
    artinHasseExpCurrentRootPeelProduct F N m N (ε ^ ℓ) (F.traceCarry y)
  let Curr : A := artinHasseExpCurrentRootPeelProduct F N m N ε (F.traceCarry y)
  let Next : A :=
    artinHasseExpCurrentRootPeelProduct F N (m + 1) N ε (F.traceCarry y)
  have hzero_succ : ε ^ (ℓ ^ (m + 1)) = 0 := by
    have hexp : ℓ ^ (m + 1) = ℓ ^ m * ℓ := by
      rw [pow_succ]
    calc
      ε ^ (ℓ ^ (m + 1)) = ε ^ (ℓ ^ m * ℓ) := by
        rw [hexp]
      _ = (ε ^ (ℓ ^ m)) ^ ℓ := by
        rw [pow_mul]
      _ = 0 := by
        rw [hzero]
        exact zero_pow (Nat.Prime.ne_zero (Fact.out : Nat.Prime ℓ))
  have hfold :=
    F.artinHasseExpTraceCarryZModCorrection_mul_currentRoot_shifted_eq_currentRoot_pow_prime
      N m y ε hε hzero
  have hcorr :=
    F.artinHasseExpTraceCarryZModCorrectionProduct_eq_teichProduct_of_zero_iterate
      N m N 0 ε y hzero
  have hadj :=
    F.artinHasseExp_adjustedProduct_succ_mul_traceCarryTeichProduct_eq_base
      N m y ε hε hzero
  have htrans :=
    F.artinHasseExp_product_iterate_currentRootPeel_transition_traceCarry_of_zero_iterate
      N (m + 1) (Nat.succ_pos _) y ε hε hzero_succ
  have hrange : Finset.range (N + 1) = Finset.Iic N := by
    ext r
    simp
  have hprodCorr : Prod * Corr = B := by
    have hcorr' :
        Corr =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      ((F.traceCarry y).coeff r))))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j)) := by
      simpa [A, θ, Rps, Corr, hrange,
        artinHasseExpTraceCarryZModCorrectionTeichProduct] using hcorr
    calc
      Prod * Corr
          = Prod *
              (∏ j ∈ Finset.range m,
                (∏ r ∈ Finset.Iic N,
                  ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                    (ε ^ (ℓ ^ j) *
                      θ (WittVector.teichmuller ℓ
                        (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                          ((F.traceCarry y).coeff r))))) ^
                    (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) := by
            rw [hcorr']
      _ = B := by
            simpa [A, θ, Eps, Rps, zbar, t, P, Prod, B] using hadj
  have hprodNext : Prod * Next = B * Shift := by
    simpa [A, Eps, zbar, t, P, Prod, B, Shift, Next] using htrans
  have hPunit : IsUnit P := by
    dsimp [P]
    rw [IsUnit.prod_iff]
    intro i hi
    simpa [A, Eps, zbar] using
      F.artinHasseExp_trunc_eval_pow_iterate_mul_isUnit_of_pow_succ_eq_zero
        N 0 ε (zbar ^ (ℓ ^ (i : ℕ))) hε
  have hProdUnit : IsUnit Prod := hPunit.pow (ℓ ^ (m + 1))
  have hEq : Prod * (Curr ^ ℓ) = Prod * Next := by
    calc
      Prod * (Curr ^ ℓ) = Prod * (Corr * Shift) := by
        rw [hfold]
      _ = (Prod * Corr) * Shift := by
        ac_rfl
      _ = B * Shift := by
        rw [hprodCorr]
      _ = Prod * Next := by
        rw [hprodNext]
  exact hProdUnit.mul_left_cancel hEq

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
