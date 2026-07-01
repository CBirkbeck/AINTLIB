module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CoordinatePeel
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.ZModFold.FiniteCharacterFold

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

/-- Diagnostic conditional: the positive-index `ℓ * traceCarry` current-root
endpoint follows from a coordinatewise current-root factor root statement.
This hypothesis is not expected to be the right c5 route; individual factors
need not be `ℓ`-torsion before the product-level Dwork telescope cancels. -/
theorem artinHasseExpCurrentRootPeelProduct_natCast_ell_mul_inverse_endpoint_pow_prime_eq_one
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (hm_pos : 0 < m) (y : kˣ)
    (hroot :
      ∀ m s j : ℕ, j ∈ Finset.range m →
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
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ ^ (ℓ ^ j) *
            (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff s))) ^ ℓ)) ^ ℓ = 1) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    (artinHasseExpCurrentRootPeelProduct F N (m - 1) (N + 1) δ
      ((ℓ : WittVector ℓ k) * F.traceCarry y)) ^ ℓ = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hdrop :
      artinHasseExpCurrentRootPeelProduct F N (m - 1) (N + 1) δ
          ((ℓ : WittVector ℓ k) * F.traceCarry y) =
        artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) := by
    have h :=
      F.artinHasseExpCurrentRootPeelProduct_natCast_ell_mul_succ
        N (m - 1) N δ (F.traceCarry y)
    simpa [Nat.sub_add_cancel hm_pos] using h
  have htail :
      artinHasseExpCurrentRootPeelProduct F N m N δ
          (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + 0)) = 1 := by
    refine
      F.artinHasseExpCurrentRootPeelProduct_traceCarry_tail_eq_one_of_factor_pow_prime_eq_one
        N m N 0 δ y ?_
    intro m' s j hj
    simpa [A, Ips, πbar, δ] using hroot m' s j hj
  have hmk :
      (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + 0)) = F.traceCarry y := by
    ext r
    simp
  have hcurrent :
      artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) = 1 := by
    rw [← hmk]
    exact htail
  rw [hdrop, hcurrent]
  simp

/-- Diagnostic conditional closure of the named WC3c target from coordinatewise
prime-field root-of-unity facts.  This is useful for sanity-checking the
current-root expansion, but it should not be used as the main c5 plan:
the scalar factor-root hypothesis is too strong before the finite Dwork product
telescope has been applied. -/
theorem traceCarryFiniteCharacter_inverse_target_of_traceCarry_factor_roots
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ)
    (hroot :
      ∀ m s j : ℕ, j ∈ Finset.range m →
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
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ ^ (ℓ ^ j) *
            (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff s))) ^ ℓ)) ^ ℓ = 1) :
    artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target F N m y := by
  classical
  refine
    F.traceCarryFiniteCharacter_inverse_target_of_currentRoot_pow_prime_eq_one
      N m y ?_
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have htail :
      artinHasseExpCurrentRootPeelProduct F N m N δ
          (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + 0)) = 1 := by
    refine
      F.artinHasseExpCurrentRootPeelProduct_traceCarry_tail_eq_one_of_factor_pow_prime_eq_one
        N m N 0 δ y ?_
    intro m' s j hj
    simpa [A, Ips, πbar, δ] using hroot m' s j hj
  have hmk :
      (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + 0)) = F.traceCarry y := by
    ext r
    simp
  have hcurrent :
      artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) = 1 := by
    rw [← hmk]
    exact htail
  rw [hcurrent]
  simp

/-- Conditional closure of the WC3c target from the same endpoint rewritten
as the finite character of the actual `ℓ * traceCarry y` Witt vector. -/
theorem traceCarryFiniteCharacter_inverse_target_of_natCast_ell_mul_endpoint_eq_one
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (hm_pos : 0 < m) (y : kˣ)
    (hendpoint :
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Ips : PowerSeries A :=
        (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
      let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
      (artinHasseExpCurrentRootPeelProduct F N (m - 1) (N + 1) δ
        ((ℓ : WittVector ℓ k) * F.traceCarry y)) ^ ℓ = 1) :
    artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target F N m y := by
  classical
  intro _hm
  dsimp only [artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target]
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hfold :=
    F.traceCarryFiniteCharacter_inverse_eq_natCast_ell_mul_currentRoot_pow_prime
      N m hm_pos y
  calc
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
        (artinHasseExpCurrentRootPeelProduct F N (m - 1) (N + 1) δ
          ((ℓ : WittVector ℓ k) * F.traceCarry y)) ^ ℓ := by
          simpa [A, Ips, πbar, δ] using hfold
    _ = 1 := by
          simpa [A, Ips, πbar, δ] using hendpoint

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
