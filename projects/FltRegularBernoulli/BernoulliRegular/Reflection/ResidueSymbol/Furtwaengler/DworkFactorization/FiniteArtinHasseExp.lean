module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLog

/-!
# Finite Artin-Hasse exponential coordinates

This file defines the principal-unit coordinate `E_N(x) - 1` of the truncated
Artin-Hasse exponential in `𝓞 R' / Q^(N+1)`.  The coefficient representatives
are the existing precision-indexed Artin-Hasse coefficients
`dworkCoeffArtinHasseAtTo`.
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

/-- The finite Artin-Hasse exponential evaluation `E_N(x)` lifted to
`𝓞 R'`, using the precision-indexed Artin-Hasse coefficient representatives. -/
noncomputable def finiteArtinHasseExp (N : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  dworkThetaTrunc (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N) N 1

/-- The principal-unit coordinate `E_N(x) - 1` lifted to `𝓞 R'`. -/
noncomputable def finiteArtinHasseExpCoord (N : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  F.finiteArtinHasseExp N x - 1

@[simp] theorem finiteArtinHasseExpCoord_add_one (N : ℕ) (x : 𝓞 R') :
    F.finiteArtinHasseExpCoord N x + 1 = F.finiteArtinHasseExp N x := by
  simp [finiteArtinHasseExpCoord]

theorem finiteArtinHasseExpCoord_eq_positive_sum (N : ℕ) (x : 𝓞 R') :
    F.finiteArtinHasseExpCoord N x =
      ∑ n ∈ Finset.range N,
        dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N (n + 1) := by
  simp [finiteArtinHasseExpCoord, finiteArtinHasseExp, dworkThetaTrunc,
    Finset.sum_range_succ']

/-- If `x ∈ Q`, then the Artin-Hasse exponential coordinate lies in `Q`. -/
theorem finiteArtinHasseExpCoord_mem_Q (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseExpCoord N x ∈ F.Q := by
  classical
  rw [F.finiteArtinHasseExpCoord_eq_positive_sum]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  have hcoeff :
      dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N (n + 1) ∈
        F.Q ^ (n + 1) :=
    dworkCoeffArtinHasseAtTo_mem_Q_pow F.toConcreteStickelbergerSetup hx N (n + 1)
  have hle : F.Q ^ (n + 1) ≤ F.Q := by
    simpa using
      (Ideal.pow_le_pow_right (Nat.succ_pos n) : F.Q ^ (n + 1) ≤ F.Q ^ 1)
  exact hle hcoeff

/-- Quotient form of the finite Artin-Hasse exponential evaluation. -/
theorem quotient_mk_finiteArtinHasseExp_eq_trunc_eval (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExp N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) := by
  dsimp only
  simpa [finiteArtinHasseExp] using
    F.toConcreteStickelbergerSetup.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
      x 1 N

/-- Quotient form of the Artin-Hasse principal-unit coordinate `E_N(x) - 1`. -/
theorem quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval_sub_one
    (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) - 1 := by
  dsimp only
  rw [finiteArtinHasseExpCoord, map_sub,
    F.quotient_mk_finiteArtinHasseExp_eq_trunc_eval]
  simp

/-- Adding back the removed constant term recovers the truncated
Artin-Hasse evaluation in the quotient. -/
theorem one_add_quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval
    (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) := by
  dsimp only
  rw [F.quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval_sub_one]
  ring

theorem quotient_mk_finiteArtinHasseExpCoord_mem_map_Q
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) F.Q :=
  Ideal.mem_map_of_mem _ (F.finiteArtinHasseExpCoord_mem_Q N hx)

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
