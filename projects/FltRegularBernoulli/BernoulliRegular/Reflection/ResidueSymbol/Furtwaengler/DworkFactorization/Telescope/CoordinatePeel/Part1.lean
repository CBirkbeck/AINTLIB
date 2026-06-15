module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.TraceCarry

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

/-- Parameter-general carry-free tail form of the zero-boundary powered
comparison.  The accumulated carry is replaced by the explicit Artin-Hasse
coordinate tail, while keeping the powered base factor visible. -/
theorem exists_artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_frobenius_tail
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
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
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε ^ (ℓ ^ j)) ^ ℓ *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
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
  let P : A :=
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m)
  let B : A :=
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m)
  let C : A := F.artinHasseExpTraceCarryIterCorrection N y ε m
  obtain ⟨c, htail⟩ :=
    F.exists_traceCarryIterCorrection_mul_teichmuller_frobenius_tail_eq_tail
      N m y ε hε
  let Tail : A :=
    ∏ j ∈ Finset.range m,
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
          (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))
  let FrobTail : A :=
    ∏ j ∈ Finset.range m,
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
          (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))
  have htail' : C * FrobTail = Tail := by
    simpa [A, θ, Eps, C, Tail, FrobTail] using htail
  have hprod : P * C = B := by
    simpa [A, Eps, zbar, t, P, B, C] using
      F.artinHasseExp_product_pow_prime_iterate_mul_traceCarry_eq_base_pow_prime_iterate
        N m y ε hε hzero
  refine ⟨c, ?_⟩
  change P * Tail = B * FrobTail
  calc
    P * Tail = P * (C * FrobTail) := by rw [htail']
    _ = (P * C) * FrobTail := by ring
    _ = B * FrobTail := by rw [hprod]

/-- Non-existential parameter-general carry-free tail comparison using the
fixed Witt carry `traceCarry`. -/
theorem artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_frobenius_tail_traceCarry
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
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
        ∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((ε ^ (ℓ ^ j)) ^ ℓ *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
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
  let P : A :=
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m)
  let B : A :=
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m)
  let C : A := F.artinHasseExpTraceCarryIterCorrection N y ε m
  let Tail : A :=
    ∏ j ∈ Finset.range m,
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
          (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))
  let FrobTail : A :=
    ∏ j ∈ Finset.range m,
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
          (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))
  have htail' : C * FrobTail = Tail := by
    simpa [A, θ, Eps, C, Tail, FrobTail, c] using
      F.traceCarryIterCorrection_mul_teichmuller_frobenius_tail_eq_tail_traceCarry
        N m y ε hε
  have hprod : P * C = B := by
    simpa [A, Eps, zbar, t, P, B, C] using
      F.artinHasseExp_product_pow_prime_iterate_mul_traceCarry_eq_base_pow_prime_iterate
        N m y ε hε hzero
  change P * Tail = B * FrobTail
  calc
    P * Tail = P * (C * FrobTail) := by rw [htail']
    _ = (P * C) * FrobTail := by ring
    _ = B * FrobTail := by rw [hprod]

/-- Reindexed parameter-general carry-free tail comparison.  The
Frobenius-shifted tail on the right is rewritten by separating the zeroth
Witt coordinate and shifting the remaining coordinates down. -/
theorem exists_artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_reindexed_tail
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
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
          ∏ j ∈ Finset.range m,
            (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε ^ (ℓ ^ j)) ^ ℓ *
                  θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
              ∏ r ∈ Finset.range N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  ((ε ^ (ℓ ^ j)) ^ ℓ *
                    θ (WittVector.teichmuller ℓ
                      (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                        (c.coeff (r + 1)))))) ^
                  (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)) := by
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
  let P : A :=
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m)
  let B : A :=
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m)
  let Tail : A :=
    ∏ j ∈ Finset.range m,
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
          (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j))
  let S : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ
            ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
        (ℓ ^ (r + 1))
  let U : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
      ∏ r ∈ Finset.range N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  have htail' :
      P * Tail =
        B * ∏ j ∈ Finset.range m, (S j) ^ (ℓ ^ (m - 1 - j)) := by
    simpa [A, θ, Eps, zbar, t, P, B, Tail, S] using htail
  have hreindex : ∀ j : ℕ, S j = U j := by
    intro j
    simpa [A, θ, Eps, S, U] using
      F.artinHasseExp_wittTeich_frobenius_tail_eq_coeff_zero_mul_shift
        (N := N) (ε := (ε ^ (ℓ ^ j)) ^ ℓ) c
  refine ⟨c, ?_⟩
  change
    P * Tail =
      B * ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - 1 - j))
  calc
    P * Tail =
        B * ∏ j ∈ Finset.range m, (S j) ^ (ℓ ^ (m - 1 - j)) := htail'
    _ =
        B * ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - 1 - j)) := by
        congr 1
        refine Finset.prod_congr rfl ?_
        intro j _hj
        rw [hreindex j]

/-- Parameter-general boundary cleanup for the reindexed tail: the last shifted
iterate is trivial once the parameter has reached the zero boundary. -/
theorem artinHasseExp_reindexed_tail_succ_eq_range_of_zero_iterate
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
    let U : ℕ → A := fun j =>
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
        ∏ r ∈ Finset.range N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff (r + 1)))))) ^
            (ℓ ^ (r + 2))
    (∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - j)) := by
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
      ∏ r ∈ Finset.range N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  have hεzero : (ε ^ (ℓ ^ m)) ^ ℓ = 0 := by
    have hpow : (ε ^ (ℓ ^ m)) ^ ℓ = ε ^ (ℓ ^ (m + 1)) := by
      rw [← pow_mul, Nat.pow_succ]
    rw [hpow, hzero]
  have hEzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  have hEzero' :
      Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hEzero
  have hlast : U m = 1 := by
    dsimp [U]
    rw [hεzero]
    simp [hEzero']
  change (∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - j))
  rw [Finset.prod_range_succ]
  simp [hlast]

/-- Parameter-general coefficient shift for the nonzero-coordinate part of the
reindexed tail. -/
theorem artinHasseExp_reindexed_shifted_range_eq_tail_of_pos
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {N : ℕ} (hN : 0 < N) (m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.range N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff (r + 1)))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic (N - 1),
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cTail.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j)) := by
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
  refine Finset.prod_congr rfl ?_
  intro j _hj
  congr 1
  have hNpred : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
  rw [← Nat.range_succ_eq_Iic (N - 1), hNpred]
  refine Finset.prod_congr rfl ?_
  intro r _hr
  have hpow : (ε ^ (ℓ ^ j)) ^ ℓ = ε ^ (ℓ ^ (j + 1)) := by
    rw [← pow_mul, Nat.pow_succ]
  rw [hpow]
  simp

/-- Parameter-general split of the reindexed tail into the peeled zeroth
coordinate and the shifted lower-depth tail. -/
theorem artinHasseExp_reindexed_tail_range_eq_coeff_zero_mul_shifted_tail_of_pos
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {N : ℕ} (hN : 0 < N) (m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (c : WittVector ℓ k) :
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
    let V : ℕ → A := fun j =>
      ∏ r ∈ Finset.range N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
    let W : ℕ → A := fun j =>
      ∏ r ∈ Finset.Iic (N - 1),
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ (j + 1)) *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
          (ℓ ^ (r + 2))
    (∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j))) =
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
  let Z : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      ((ε ^ (ℓ ^ j)) ^ ℓ *
        θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
  let V : ℕ → A := fun j =>
    ∏ r ∈ Finset.range N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r)
              (c.coeff (r + 1)))))) ^
        (ℓ ^ (r + 2))
  let W : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic (N - 1),
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ (j + 1)) *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
        (ℓ ^ (r + 2))
  have hshift :
      (∏ j ∈ Finset.range m, (V j) ^ (ℓ ^ (m - j))) =
        ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
    simpa [A, θ, Eps, cTail, V, W] using
      F.artinHasseExp_reindexed_shifted_range_eq_tail_of_pos
        (N := N) hN m ε c
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
    _ =
          (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
            ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
          rw [hshift]

/-- Depth-indexed boundary cleanup for the reindexed tail.  The coordinate
depth is independent of the quotient precision. -/
theorem artinHasseExp_reindexed_tail_succ_depth_eq_range_of_zero_iterate
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
    (∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - j)) := by
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
      ∏ r ∈ Finset.range D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  have hεzero : (ε ^ (ℓ ^ m)) ^ ℓ = 0 := by
    have hpow : (ε ^ (ℓ ^ m)) ^ ℓ = ε ^ (ℓ ^ (m + 1)) := by
      rw [← pow_mul, Nat.pow_succ]
    rw [hpow, hzero]
  have hEzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  have hEzero' :
      Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hEzero
  have hlast : U m = 1 := by
    dsimp [U]
    rw [hεzero]
    simp [hEzero']
  change (∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - j))
  rw [Finset.prod_range_succ]
  simp [hlast]

/-- Depth-indexed coefficient shift for the nonzero-coordinate part of the
reindexed tail. -/
theorem artinHasseExp_reindexed_shifted_range_depth_eq_tail_of_pos
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {D : ℕ} (hD : 0 < D) (N m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.range D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff (r + 1)))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic (D - 1),
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (cTail.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j)) := by
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
  refine Finset.prod_congr rfl ?_
  intro j _hj
  congr 1
  have hDpred : D - 1 + 1 = D := Nat.sub_add_cancel (Nat.succ_le_of_lt hD)
  rw [← Nat.range_succ_eq_Iic (D - 1), hDpred]
  refine Finset.prod_congr rfl ?_
  intro r _hr
  have hpow : (ε ^ (ℓ ^ j)) ^ ℓ = ε ^ (ℓ ^ (j + 1)) := by
    rw [← pow_mul, Nat.pow_succ]
  rw [hpow]
  simp

/-- Depth-indexed split of the reindexed tail into the peeled zeroth coordinate
and the shifted lower-depth tail. -/
theorem artinHasseExp_reindexed_tail_range_depth_eq_coeff_zero_mul_shifted_tail_of_pos
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {D : ℕ} (hD : 0 < D) (N m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (c : WittVector ℓ k) :
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
    (∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j))) =
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
  have hshift :
      (∏ j ∈ Finset.range m, (V j) ^ (ℓ ^ (m - j))) =
        ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
    simpa [A, θ, Eps, cTail, V, W] using
      F.artinHasseExp_reindexed_shifted_range_depth_eq_tail_of_pos
        (D := D) hD N m ε c
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
    _ =
          (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
            ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
          rw [hshift]

/-- Depth-indexed reindexing of the accumulated Frobenius-shifted tail. -/
theorem artinHasseExp_frobenius_tail_succ_depth_eq_reindexed_tail
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (c : WittVector ℓ k) :
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
        ∏ r ∈ Finset.range D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff (r + 1)))))) ^
            (ℓ ^ (r + 2))
    (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic D,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j)) := by
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
      ∏ r ∈ Finset.range D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  refine Finset.prod_congr rfl ?_
  intro j _hj
  have hinner :=
    F.artinHasseExp_wittTeich_frobenius_tail_depth_eq_coeff_zero_mul_shift
      (N := N) (D := D) (ε := (ε ^ (ℓ ^ j)) ^ ℓ) c
  simpa [A, θ, Eps, U] using congrArg (fun x : A => x ^ (ℓ ^ (m - j))) hinner

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
