module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CurrentRoot
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.InversePeel.FrobeniusReindexedTail

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

/-- One recursive peel of the carry-free powered comparison.  At positive
coordinate depth, the reindexed tail is reduced to the peeled zeroth
coordinate and the same tail for the shifted Witt coefficients. -/
theorem exists_artinHasseExp_inverse_product_pow_prime_iterate_peel_tail_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {N : ℕ} (hN : 0 < N) (m : ℕ) (hm : N + 1 ≤ ℓ ^ (m + 1)) (y : kˣ) :
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
      let cTail : WittVector ℓ k := WittVector.mk ℓ (fun r => c.coeff (r + 1))
      let Z : ℕ → A := fun j =>
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((δ ^ (ℓ ^ j)) ^ ℓ *
            θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ
      let W : ℕ → A := fun j =>
        ∏ r ∈ Finset.Iic (N - 1),
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ (j + 1)) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (cTail.coeff r))))) ^
            (ℓ ^ (r + 2))
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
        (∏ j ∈ Finset.range (m + 1),
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
              (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j))) =
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
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  obtain ⟨c, hreindex⟩ :=
    F.exists_artinHasseExp_inverse_product_pow_prime_iterate_mul_tail_eq_reindexed_tail_of_le
      N (m + 1) (Nat.succ_pos m) hm y
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
  have hdrop :=
    F.artinHasseExp_inverse_reindexed_tail_succ_eq_range_of_le N m hm c
  have hsplit :=
    F.artinHasseExp_inverse_reindexed_tail_range_eq_coeff_zero_mul_shifted_tail_of_pos
      (N := N) hN m c
  refine ⟨c, ?_⟩
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
      (∏ j ∈ Finset.range (m + 1),
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - j)))
        =
          ∏ j ∈ Finset.range (m + 1), (Z j * V j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, Ips, πbar, δ, zbar, Z, V] using hreindex
    _ =
          ∏ j ∈ Finset.range m, (Z j * V j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, Ips, πbar, δ, Z, V] using hdrop
    _ =
          (∏ j ∈ Finset.range m, (Z j) ^ (ℓ ^ (m - j))) *
            ∏ j ∈ Finset.range m, (W j) ^ (ℓ ^ (m - j)) := by
          simpa [A, θ, Eps, Ips, πbar, δ, cTail, Z, V, W] using hsplit

/-- The actual inverse-series Dwork parameter is compatible under precision
reduction. -/
theorem artinHasseExp_inverse_parameter_factor_eq
    {M N : ℕ} (hMN : M ≤ N) :
    let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
    let φ : AN →+* AM :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    let IpsN : PowerSeries AN :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let IpsM : PowerSeries AM :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
    let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
    let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
    let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
    φ δN = δM := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
  let φ : AN →+* AM :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  let hI : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpInverseSeries ℓ) :=
    artinHasseExpInverseSeries_isRIntegral ℓ
  let IpsN : PowerSeries AN := hI.mapTo (S0.rIntegralRatToQuotient N)
  let IpsM : PowerSeries AM := hI.mapTo (S0.rIntegralRatToQuotient M)
  let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
  let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
  let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
  let γN : 𝓞 R' := artinHasseDworkParameterApproxTo S0 N
  let γM : 𝓞 R' := artinHasseDworkParameterApproxTo S0 M
  have hδN :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) γN = δN := by
    simpa [S0, AN, IpsN, πN, δN, γN] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S0 N
  have hδM :
      Ideal.Quotient.mk (F.Q ^ (M + 1)) γM = δM := by
    simpa [S0, AM, IpsM, πM, δM, γM] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S0 M
  calc
    φ δN =
        φ (Ideal.Quotient.mk (F.Q ^ (N + 1)) γN) := by
          rw [hδN]
    _ = Ideal.Quotient.mk (F.Q ^ (M + 1)) γM :=
          quotient_mk_artinHasseDworkParameterApproxTo_factor_eq S0 hMN
    _ = δM := hδM

/-- Precision reduction is compatible with the normalized base value
`E(δ)^trace` at the actual inverse-series parameter. -/
theorem artinHasseExp_inverse_base_trace_factor_eq
    {M N : ℕ} (hMN : M ≤ N) (y : kˣ) :
    let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
    let φ : AN →+* AM :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    let EpsN : PowerSeries AN :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let EpsM : PowerSeries AM :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
    let IpsN : PowerSeries AN :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let IpsM : PowerSeries AM :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
    let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
    let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
    let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    φ (((PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN) δN) ^ t) =
      ((PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM) δM) ^ t := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
  let φ : AN →+* AM :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let EpsN : PowerSeries AN := hE.mapTo (S0.rIntegralRatToQuotient N)
  let EpsM : PowerSeries AM := hE.mapTo (S0.rIntegralRatToQuotient M)
  let hI : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpInverseSeries ℓ) :=
    artinHasseExpInverseSeries_isRIntegral ℓ
  let IpsN : PowerSeries AN := hI.mapTo (S0.rIntegralRatToQuotient N)
  let IpsM : PowerSeries AM := hI.mapTo (S0.rIntegralRatToQuotient M)
  let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
  let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
  let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hδ : φ δN = δM := by
    simpa [S0, AN, AM, φ, IpsN, IpsM, πN, πM, δN, δM] using
      F.artinHasseExp_inverse_parameter_factor_eq hMN
  have hδMnil :
      δM ^ (M + 1) = 0 := by
    simpa [S0, AM, IpsM, πM, δM] using
      S0.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero M
  have heval :
      φ ((PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN) δN) =
        (PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM) δM := by
    simpa [S0, AN, AM, φ, EpsN, EpsM] using
      S0.isRIntegralPS_trunc_eval₂_factor_eq hE hMN δN δM hδ hδMnil
  calc
    φ (((PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN) δN) ^ t)
        =
          (φ ((PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN) δN)) ^ t := by
          rw [map_pow]
    _ = ((PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM) δM) ^ t := by
          rw [heval]

/-- Precision reduction is compatible with the actual inverse-parameter
Frobenius Artin-Hasse product. -/
theorem artinHasseExp_inverse_frobenius_product_factor_eq
    {M N : ℕ} (hMN : M ≤ N) (y : kˣ) :
    let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
    let φ : AN →+* AM :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    let EpsN : PowerSeries AN :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let EpsM : PowerSeries AM :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
    let IpsN : PowerSeries AN :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let IpsM : PowerSeries AM :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
    let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
    let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
    let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
    let zN : AN :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let zM : AM :=
      Ideal.Quotient.mk (F.Q ^ (M + 1)) (F.teichUnitFullVal (F.traceScale * y))
    φ (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN)
          (δN * zN ^ (ℓ ^ (i : ℕ)))) =
      ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM)
          (δM * zM ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
  let φ : AN →+* AM :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let EpsN : PowerSeries AN := hE.mapTo (S0.rIntegralRatToQuotient N)
  let EpsM : PowerSeries AM := hE.mapTo (S0.rIntegralRatToQuotient M)
  let hI : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpInverseSeries ℓ) :=
    artinHasseExpInverseSeries_isRIntegral ℓ
  let IpsN : PowerSeries AN := hI.mapTo (S0.rIntegralRatToQuotient N)
  let IpsM : PowerSeries AM := hI.mapTo (S0.rIntegralRatToQuotient M)
  let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
  let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
  let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
  let zN : AN :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let zM : AM :=
    Ideal.Quotient.mk (F.Q ^ (M + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let γN : 𝓞 R' := artinHasseDworkParameterApproxTo S0 N
  let γM : 𝓞 R' := artinHasseDworkParameterApproxTo S0 M
  have hδN :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) γN = δN := by
    simpa [S0, AN, IpsN, πN, δN, γN] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S0 N
  have hδM :
      Ideal.Quotient.mk (F.Q ^ (M + 1)) γM = δM := by
    simpa [S0, AM, IpsM, πM, δM, γM] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S0 M
  have hδ : φ δN = δM := by
    calc
      φ δN =
          φ (Ideal.Quotient.mk (F.Q ^ (N + 1)) γN) := by
            rw [hδN]
      _ = Ideal.Quotient.mk (F.Q ^ (M + 1)) γM :=
            quotient_mk_artinHasseDworkParameterApproxTo_factor_eq S0 hMN
      _ = δM := hδM
  rw [map_prod]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  let argN : AN := δN * zN ^ (ℓ ^ (i : ℕ))
  let argM : AM := δM * zM ^ (ℓ ^ (i : ℕ))
  have hz : φ zN = zM := by
    dsimp [φ, zN, zM]
    exact Ideal.Quotient.factor_mk
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
      (F.teichUnitFullVal (F.traceScale * y))
  have harg : φ argN = argM := by
    calc
      φ argN = φ (δN * zN ^ (ℓ ^ (i : ℕ))) := rfl
      _ = φ δN * φ (zN ^ (ℓ ^ (i : ℕ))) := map_mul φ δN (zN ^ (ℓ ^ (i : ℕ)))
      _ = δM * zM ^ (ℓ ^ (i : ℕ)) := by rw [hδ, map_pow, hz]
      _ = argM := rfl
  have harg_nil : argM ^ (M + 1) = 0 := by
    have hδMnil :
        δM ^ (M + 1) = 0 := by
      simpa [S0, AM, IpsM, πM, δM] using
        S0.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero M
    dsimp [argM]
    rw [mul_pow, hδMnil, zero_mul]
  simpa [S0, AN, AM, φ, EpsN, EpsM, IpsN, IpsM, πN, πM, δN, δM, zN, zM,
    argN, argM] using
    S0.isRIntegralPS_trunc_eval₂_factor_eq hE hMN argN argM harg harg_nil

/-- The remaining inverse-parameter splitting difference is compatible under
precision reduction. -/
theorem artinHasseExp_inverse_splitting_difference_factor_eq
    {M N : ℕ} (hMN : M ≤ N) (y : kˣ) :
    let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
    let φ : AN →+* AM :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    let EpsN : PowerSeries AN :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let EpsM : PowerSeries AM :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
    let IpsN : PowerSeries AN :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let IpsM : PowerSeries AM :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
    let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
    let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
    let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
    let zN : AN :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let zM : AM :=
      Ideal.Quotient.mk (F.Q ^ (M + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    φ ((((PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN) δN) ^ t) -
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN)
            (δN * zN ^ (ℓ ^ (i : ℕ)))) =
      (((PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM) δM) ^ t) -
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM)
            (δM * zM ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let AM : Type _ := 𝓞 R' ⧸ F.Q ^ (M + 1)
  let φ : AN →+* AM :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let EpsN : PowerSeries AN := hE.mapTo
    (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let EpsM : PowerSeries AM := hE.mapTo
    (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
  let hI : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpInverseSeries ℓ) :=
    artinHasseExpInverseSeries_isRIntegral ℓ
  let IpsN : PowerSeries AN := hI.mapTo
    (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let IpsM : PowerSeries AM := hI.mapTo
    (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient M)
  let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let πM : AM := Ideal.Quotient.mk (F.Q ^ (M + 1)) F.π
  let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
  let δM : AM := (PowerSeries.trunc (M + 1) IpsM).eval₂ (RingHom.id AM) πM
  let zN : AN :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let zM : AM :=
    Ideal.Quotient.mk (F.Q ^ (M + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hbase :
      φ (((PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN) δN) ^ t) =
        ((PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM) δM) ^ t := by
    simpa [AN, AM, φ, EpsN, EpsM, IpsN, IpsM, πN, πM, δN, δM, t] using
      F.artinHasseExp_inverse_base_trace_factor_eq hMN y
  have hprod :
      φ (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN)
            (δN * zN ^ (ℓ ^ (i : ℕ)))) =
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (M + 1) EpsM).eval₂ (RingHom.id AM)
            (δM * zM ^ (ℓ ^ (i : ℕ))) := by
    simpa [AN, AM, φ, EpsN, EpsM, IpsN, IpsM, πN, πM, δN, δM, zN, zM] using
      F.artinHasseExp_inverse_frobenius_product_factor_eq hMN y
  rw [map_sub, hbase, hprod]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
