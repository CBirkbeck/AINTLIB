module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CurrentRoot

/-!
# Inverse-parameter peel and precision compatibility lemmas for the finite Dwork telescope.

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

/-- One recursive peel of the parameter-general carry-free comparison.  At a
positive coordinate depth, the reindexed tail is reduced to the peeled zeroth
coordinate and the same lower-depth tail for shifted Witt coefficients. -/
theorem exists_artinHasseExp_product_pow_prime_iterate_peel_tail_of_zero_iterate
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {N : ℕ} (hN : 0 < N) (m : ℕ) (y : kˣ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ (m + 1)) = 0) :
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
      let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
      let Z : ℕ → A := fun j =>
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
      let W : ℕ → A := fun j =>
        ∏ r ∈ Finset.Iic (N - 1),
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
            (ℓ ^ (r + 2))
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
        (∏ j ∈ Finset.range (m + 1),
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
              (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))) =
        ((((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ (m + 1))) *
          ((∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
            ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j))) := by
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
  obtain ⟨c, hreindex⟩ :=
    F.exists_artinHasseExp_product_pow_prime_iterate_mul_tail_eq_base_mul_reindexed_tail
      N (m + 1) y ε hε hzero
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
  have hdrop :=
    F.artinHasseExp_reindexed_tail_succ_eq_range_of_zero_iterate
      N m ε hzero c
  have hsplit :=
    F.artinHasseExp_reindexed_tail_range_eq_coeff_zero_mul_shifted_tail_of_pos
      (N := N) hN m ε c
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
      (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j)))
        =
          ((((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
              (ℓ ^ (m + 1))) *
            ∏ j ∈ Finset.range (m + 1), (Z j * V j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, zbar, t, Z, V] using hreindex
    _ =
          ((((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
              (ℓ ^ (m + 1))) *
            ∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j)) := by
          rw [hdrop]
    _ =
          ((((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
              (ℓ ^ (m + 1))) *
            ((∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
              ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j))) := by
          rw [hsplit]

/-- Carry-free tail form of the zero-boundary powered comparison.  The
accumulated carry is replaced by the explicit Artin-Hasse coordinate tail
coming from the Witt carry. -/
theorem exists_artinHasseExp_inverse_product_pow_prime_iterate_mul_tail_eq_frobenius_tail_of_le
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
        ∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((δ ^ (ℓ ^ j)) ^ ℓ *
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  obtain ⟨c, htail⟩ :=
    F.exists_traceCarryIterCorrection_mul_teichmuller_frobenius_tail_eq_tail
      N m y δ hδ
  have hprod :=
    F.artinHasseExp_inverse_product_pow_prime_iterate_mul_traceCarry_eq_one_of_le
      N m hm_pos hm y
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
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            (F.artinHasseExpTraceCarryIterCorrection N y δ m *
              (∏ j ∈ Finset.range m,
                (∏ r ∈ Finset.Iic N,
                  ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                    ((δ ^ (ℓ ^ j)) ^ ℓ *
                      θ (WittVector.teichmuller ℓ
                        ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                          (c.coeff r)) ^ ℓ)))) ^
                    (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)))) := by
          rw [htail]
    _ =
          ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
              F.artinHasseExpTraceCarryIterCorrection N y δ m) *
            (∏ j ∈ Finset.range m,
              (∏ r ∈ Finset.Iic N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  ((δ ^ (ℓ ^ j)) ^ ℓ *
                    θ (WittVector.teichmuller ℓ
                      ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
                  (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) := by
          ring
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((δ ^ (ℓ ^ j)) ^ ℓ *
                  θ (WittVector.teichmuller ℓ
                    ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
          rw [hprod]
          simp

/-- Reindexed form of the carry-free tail comparison.  The Frobenius-shifted
tail on the right is rewritten by peeling off the zeroth Witt coordinate and
shifting every remaining carry coordinate down by one index. -/
theorem exists_artinHasseExp_inverse_product_pow_prime_iterate_mul_tail_eq_reindexed_tail_of_le
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
        ∏ j ∈ Finset.range m,
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((δ ^ (ℓ ^ j)) ^ ℓ *
                θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
            ∏ r ∈ Finset.range N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((δ ^ (ℓ ^ j)) ^ ℓ *
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  obtain ⟨c, htail⟩ :=
    F.exists_artinHasseExp_inverse_product_pow_prime_iterate_mul_tail_eq_frobenius_tail_of_le
      N m hm_pos hm y
  let S : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ
            ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
        (ℓ ^ (r + 1))
  let U : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
      ∏ r ∈ Finset.range N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((δ ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  have hreindex : ∀ j : ℕ, S j = U j := by
    intro j
    simpa [A, θ, Eps, S, U] using
      F.artinHasseExp_wittTeich_frobenius_tail_eq_coeff_zero_mul_shift
        (N := N) (ε := (δ ^ (ℓ ^ j)) ^ ℓ) c
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
          ∏ j ∈ Finset.range m, (S j) ^ (ℓ ^ (m - 1 - j)) := by
          simpa [A, θ, Eps, Ips, πbar, δ, zbar, S] using htail
    _ =
          ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - 1 - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          rw [hreindex j]
    _ =
          ∏ j ∈ Finset.range m,
            (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((δ ^ (ℓ ^ j)) ^ ℓ *
                  θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
              ∏ r ∈ Finset.range N,
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  ((δ ^ (ℓ ^ j)) ^ ℓ *
                    θ (WittVector.teichmuller ℓ
                      (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                        (c.coeff (r + 1)))))) ^
                  (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)) := by
          rfl

/-- In the reindexed tail, the last shifted iterate is trivial once the
inverse-series parameter has reached the zero boundary. -/
theorem artinHasseExp_inverse_reindexed_tail_succ_eq_range_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ (m + 1)) (c : WittVector ℓ k) :
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
    let U : ℕ → A := fun j =>
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((δ ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
        ∏ r ∈ Finset.range N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((δ ^ (ℓ ^ j)) ^ ℓ *
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let U : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ *
      ∏ r ∈ Finset.range N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((δ ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
  have hδzero : (δ ^ (ℓ ^ m)) ^ ℓ = 0 := by
    have hzero :
        δ ^ (ℓ ^ (m + 1)) = 0 := by
      simpa [A, Ips, πbar, δ] using
        F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le
          N (m + 1) hm
    have hpow : (δ ^ (ℓ ^ m)) ^ ℓ = δ ^ (ℓ ^ (m + 1)) := by
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
    rw [hδzero]
    simp [hEzero']
  change (∏ j ∈ Finset.range (m + 1), (U j) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m, (U j) ^ (ℓ ^ (m - j))
  rw [Finset.prod_range_succ]
  simp [hlast]

/-- The nonzero-coordinate part of the reindexed tail is the same tail for
the Witt vector with shifted coefficients, with the Dwork parameter advanced
by one Frobenius step. -/
theorem artinHasseExp_inverse_reindexed_shifted_range_eq_tail_of_pos
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {N : ℕ} (hN : 0 < N) (m : ℕ) (c : WittVector ℓ k) :
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
    let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
    (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.range N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((δ ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  (c.coeff (r + 1)))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic (N - 1),
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ (j + 1)) *
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
  refine Finset.prod_congr rfl ?_
  intro j _hj
  congr 1
  have hNpred : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
  rw [← Nat.range_succ_eq_Iic (N - 1), hNpred]
  refine Finset.prod_congr rfl ?_
  intro r _hr
  have hpow : (δ ^ (ℓ ^ j)) ^ ℓ = δ ^ (ℓ ^ (j + 1)) := by
    rw [← pow_mul, Nat.pow_succ]
  rw [hpow]
  simp [δ, πbar, Ips]

/-- Split the reindexed tail into the peeled zeroth-coordinate factor and the
lower-depth tail attached to the shifted Witt coefficients. -/
theorem artinHasseExp_inverse_reindexed_tail_range_eq_coeff_zero_mul_shifted_tail_of_pos
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {N : ℕ} (hN : 0 < N) (m : ℕ) (c : WittVector ℓ k) :
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
    let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
    let Z : ℕ → A := fun j =>
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
    let V : ℕ → A := fun j =>
      ∏ r ∈ Finset.range N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((δ ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                (c.coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
    let W : ℕ → A := fun j =>
      ∏ r ∈ Finset.Iic (N - 1),
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ ^ (ℓ ^ (j + 1)) *
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
  let Z : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      ((δ ^ (ℓ ^ j)) ^ ℓ *
        θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
  let V : ℕ → A := fun j =>
    ∏ r ∈ Finset.range N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r)
              (c.coeff (r + 1)))))) ^
        (ℓ ^ (r + 2))
  let W : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic (N - 1),
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (δ ^ (ℓ ^ (j + 1)) *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
        (ℓ ^ (r + 2))
  have hshift :
      (∏ j ∈ Finset.range m, (V j) ^ (ℓ ^ (m - j))) =
        ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
    simpa [A, θ, Eps, Ips, πbar, δ, cTail, V, W] using
      F.artinHasseExp_inverse_reindexed_shifted_range_eq_tail_of_pos
        (N := N) hN m c
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

/-- Trace-carry specialization of one positive-depth peel.  The peeled
zeroth-coordinate factor is already displayed as an `ℓ`-th power, and the
shifted lower tail is rewritten using the fixed prime-field coordinates
`traceCarryCoeffZMod y (r + 1)`, without introducing a new carry. -/
theorem artinHasseExp_inverse_traceCarry_reindexed_tail_range_eq_zmod_peel_of_pos
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {N : ℕ} (hN : 0 < N) (m : ℕ) (y : kˣ) :
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
    let Zraw : ℕ → A := fun j =>
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ (((F.traceCarry y).coeff 0) ^ ℓ)))) ^ ℓ
    let Vraw : ℕ → A := fun j =>
      ∏ r ∈ Finset.range N,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((δ ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff (r + 1)))))) ^
          (ℓ ^ (r + 2))
    let Z : ℕ → A := fun j =>
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ
            (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y 0))))) ^ ℓ
    let W : ℕ → A := fun j =>
      ∏ r ∈ Finset.Iic (N - 1),
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ ^ (ℓ ^ (j + 1)) *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y (r + 1)))))) ^
          (ℓ ^ (r + 2))
    (∏ j ∈ Finset.range m, (Zraw j * Vraw j) ^ (ℓ ^ (m - j))) =
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let Zraw : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      ((δ ^ (ℓ ^ j)) ^ ℓ *
        θ (WittVector.teichmuller ℓ (((F.traceCarry y).coeff 0) ^ ℓ)))) ^ ℓ
  let Vraw : ℕ → A := fun j =>
    ∏ r ∈ Finset.range N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((δ ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r)
              ((F.traceCarry y).coeff (r + 1)))))) ^
        (ℓ ^ (r + 2))
  let Wraw : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic (N - 1),
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (δ ^ (ℓ ^ (j + 1)) *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r)
              ((F.traceCarry y).coeff (r + 1)))))) ^
        (ℓ ^ (r + 2))
  let Z : ℕ → A := fun j =>
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      ((δ ^ (ℓ ^ j)) ^ ℓ *
        θ (WittVector.teichmuller ℓ
          (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y 0))))) ^ ℓ
  let W : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic (N - 1),
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (δ ^ (ℓ ^ (j + 1)) *
          θ (WittVector.teichmuller ℓ
            (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y (r + 1)))))) ^
        (ℓ ^ (r + 2))
  have hsplit :
      (∏ j ∈ Finset.range m, (Zraw j * Vraw j) ^ (ℓ ^ (m - j))) =
        (∏ j ∈ Finset.range m, (Zraw j) ^ (ℓ ^ (m - j))) *
          ∏ j ∈ Finset.range m, (Wraw j) ^ (ℓ ^ (m - j)) := by
    simpa [A, θ, Eps, Ips, πbar, δ, Zraw, Vraw, Wraw] using
      F.artinHasseExp_inverse_reindexed_tail_range_eq_coeff_zero_mul_shifted_tail_of_pos
        (N := N) hN m (F.traceCarry y)
  have hZ : ∀ j : ℕ, Zraw j = Z j := by
    intro j
    dsimp [Zraw, Z]
    rw [← F.traceCarryCoeffZMod_pow_prime_spec y 0]
  have hW : ∀ j : ℕ, Wraw j = W j := by
    intro j
    dsimp [Wraw, W]
    refine Finset.prod_congr rfl ?_
    intro r _hr
    have hfactor :=
      F.artinHasseExp_traceCarry_shifted_coord_factor_eq_zmod
        N (δ ^ (ℓ ^ (j + 1))) y r r 1
    simpa [A, θ, Eps] using
      congrArg (fun x : A => x ^ (ℓ ^ (r + 2))) hfactor
  have hZprod :
      (∏ j ∈ Finset.range m, (Zraw j) ^ (ℓ ^ (m - j))) =
        ∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j)) := by
    refine Finset.prod_congr rfl ?_
    intro j _hj
    rw [hZ j]
  have hWprod :
      (∏ j ∈ Finset.range m, (Wraw j) ^ (ℓ ^ (m - j))) =
        ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
    refine Finset.prod_congr rfl ?_
    intro j _hj
    rw [hW j]
  calc
    (∏ j ∈ Finset.range m, (Zraw j * Vraw j) ^ (ℓ ^ (m - j)))
        =
          (∏ j ∈ Finset.range m, (Zraw j) ^ (ℓ ^ (m - j))) *
            ∏ j ∈ Finset.range m, (Wraw j) ^ (ℓ ^ (m - j)) := hsplit
    _ =
          (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
            ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
          rw [hZprod, hWprod]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
