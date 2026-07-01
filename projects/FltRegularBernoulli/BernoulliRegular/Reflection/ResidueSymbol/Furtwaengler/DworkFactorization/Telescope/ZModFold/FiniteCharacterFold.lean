module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.CoordinatePeel
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.ZModFold.ZModTraceCarryFold

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

/-- At zero parameter the whole finite AH-Witt character is trivial. -/
theorem artinHasseExpFiniteWittCharacter_zero_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D : ℕ) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittCharacter F N D
        (0 : 𝓞 R' ⧸ F.Q ^ (N + 1)) w = 1 := by
  classical
  induction D generalizing w with
  | zero =>
      simpa [artinHasseExpFiniteWittCharacter_zero] using
        F.artinHasseExpFiniteWittResidueFactor_zero_parameter N w
  | succ D ih =>
      rw [artinHasseExpFiniteWittCharacter_succ]
      rw [F.artinHasseExpFiniteWittResidueFactor_zero_parameter N w]
      rw [zero_pow (Nat.Prime.ne_zero (Fact.out : Nat.Prime ℓ))]
      rw [ih]
      simp

/-- If the first Frobenius-shifted parameter is zero, the finite AH-Witt
character is just its zeroth residue factor. -/
theorem artinHasseExpFiniteWittCharacter_eq_residueFactor_of_pow_prime_eq_zero
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k)
    (hε : ε ^ ℓ = 0) :
    artinHasseExpFiniteWittCharacter F N (D + 1) ε w =
      artinHasseExpFiniteWittResidueFactor F N ε w := by
  rw [artinHasseExpFiniteWittCharacter_succ]
  rw [hε]
  rw [F.artinHasseExpFiniteWittCharacter_zero_parameter N D]
  simp

/-- Inverse-parameter zero boundary for the finite AH-Witt character.  This is
the c5A2 tail-kill statement: after enough Frobenius iterations of
`δ = E_N^{-1}(π)`, every finite Witt tail evaluates to `1`. -/
theorem artinHasseExpFiniteWittCharacter_inverse_zero_boundary_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (hm : N + 1 ≤ ℓ ^ m) (w : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpFiniteWittCharacter F N D (δ ^ (ℓ ^ m)) w = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hδ : δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  rw [hδ]
  exact F.artinHasseExpFiniteWittCharacter_zero_parameter N D w

/-- One-step inverse-parameter residue formula after the next Frobenius shift
has reached the zero boundary. -/
theorem artinHasseExpFiniteWittCharacter_inverse_eq_residueFactor_of_next_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (hm : N + 1 ≤ ℓ ^ (m + 1)) (w : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpFiniteWittCharacter F N (D + 1) (δ ^ (ℓ ^ m)) w =
      artinHasseExpFiniteWittResidueFactor F N (δ ^ (ℓ ^ m)) w := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hpow : (δ ^ (ℓ ^ m)) ^ ℓ = 0 := by
    have hsucc : δ ^ (ℓ ^ (m + 1)) = 0 := by
      simpa [A, Ips, πbar, δ] using
        F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N (m + 1) hm
    rw [← pow_mul]
    rw [show ℓ ^ m * ℓ = ℓ ^ (m + 1) by rw [pow_succ]]
    exact hsucc
  exact
    F.artinHasseExpFiniteWittCharacter_eq_residueFactor_of_pow_prime_eq_zero
      N D (δ ^ (ℓ ^ m)) w hpow

/-- A current-root peel product for an `ℓ`-multiple drops its zero residue
coordinate and continues with the original Witt vector as the tail. -/
theorem artinHasseExpCurrentRootPeelProduct_natCast_ell_mul_succ
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (c : WittVector ℓ k) :
    artinHasseExpCurrentRootPeelProduct F N m (D + 1) ε
        ((ℓ : WittVector ℓ k) * c) =
      artinHasseExpCurrentRootPeelProduct F N (m + 1) D ε c := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  have hcoeff0 :
      (((ℓ : WittVector ℓ k) * c).coeff 0) = 0 :=
    natCast_ell_mul_wittVector_coeff_zero (ℓ := ℓ) (k := k) c
  have htail :
      coordinateTailRoot ((ℓ : WittVector ℓ k) * c) = c :=
    coordinateTailRoot_natCast_ell_mul (ℓ := ℓ) (k := k) c
  have hEzero :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
    simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
  have hEzero' :
      Polynomial.eval 0 (PowerSeries.trunc (N + 1) Eps) = 1 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hEzero
  have hconst :
      ((PowerSeries.trunc (N + 1) Eps).coeff 0) = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact hEzero'
  have hfirst :
      (∏ j ∈ Finset.range m,
        (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              ((((ℓ : WittVector ℓ k) * c).coeff 0) ^ ℓ)))) ^ ℓ) ^
          (ℓ ^ (m - j))) = (1 : A) := by
    refine Finset.prod_eq_one ?_
    intro j _hj
    rw [hcoeff0]
    have hℓ_ne : ℓ ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime ℓ)
    simp [hconst, zero_pow hℓ_ne]
  simp only [artinHasseExpCurrentRootPeelProduct]
  rw [hfirst, htail]
  simp

/-- The finite current-root character wrapper for an `ℓ`-multiple drops the
zero residue and continues with the original Witt vector as tail. -/
theorem artinHasseExpFiniteWittCurrentRootCharacter_natCast_ell_mul_succ
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (w : WittVector ℓ k) :
    artinHasseExpFiniteWittCurrentRootCharacter F N m (D + 1) ε
        ((ℓ : WittVector ℓ k) * w) =
      artinHasseExpFiniteWittCurrentRootCharacter F N (m + 1) D ε w := by
  simpa [artinHasseExpFiniteWittCurrentRootCharacter] using
    F.artinHasseExpCurrentRootPeelProduct_natCast_ell_mul_succ N m D ε w

/-- Conversely, at a positive iteration index a current-root product for `c`
is the tail of the current-root product for the `ℓ`-multiple of `c`. -/
theorem artinHasseExpCurrentRootPeelProduct_eq_natCast_ell_mul_pred
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (c : WittVector ℓ k)
    (hm : 0 < m) :
    artinHasseExpCurrentRootPeelProduct F N m D ε c =
      artinHasseExpCurrentRootPeelProduct F N (m - 1) (D + 1) ε
        ((ℓ : WittVector ℓ k) * c) := by
  have hshift :=
    F.artinHasseExpCurrentRootPeelProduct_natCast_ell_mul_succ
      N (m - 1) D ε c
  symm
  simpa [Nat.sub_add_cancel hm] using hshift

/-- At zero parameter every finite current-root peel product is trivial. -/
theorem artinHasseExpCurrentRootPeelProduct_zero_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D : ℕ) (c : WittVector ℓ k) :
    artinHasseExpCurrentRootPeelProduct F N m D
        (0 : 𝓞 R' ⧸ F.Q ^ (N + 1)) c = 1 := by
  classical
  induction D generalizing m c with
  | zero =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      have hEzero :
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
        simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
      simp only [artinHasseExpCurrentRootPeelProduct]
      refine Finset.prod_eq_one ?_
      intro j _hj
      have hpow_ne : ℓ ^ j ≠ 0 :=
        pow_ne_zero j (Nat.Prime.ne_zero (Fact.out : Nat.Prime ℓ))
      rw [zero_pow hpow_ne]
      rw [zero_mul]
      rw [show (PowerSeries.trunc (N + 1)
          (DieudonneDwork.IsRIntegralPS.mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
            (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
              fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n))).eval₂
            (RingHom.id A) 0 = 1 by
        simpa [A, Eps] using hEzero]
      simp
  | succ D ih =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      have hEzero :
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
        simpa [A, Eps] using F.artinHasseExp_trunc_eval_zero N
      have hfirst :
          (∏ j ∈ Finset.range m,
            (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((0 : A) ^ (ℓ ^ j) *
                F.toConcreteStickelbergerSetup.wittThetaModQPow N
                  (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ) ^
              (ℓ ^ (m - j))) = (1 : A) := by
        refine Finset.prod_eq_one ?_
        intro j _hj
        have hpow_ne : ℓ ^ j ≠ 0 :=
          pow_ne_zero j (Nat.Prime.ne_zero (Fact.out : Nat.Prime ℓ))
        rw [zero_pow hpow_ne]
        rw [zero_mul]
        rw [hEzero]
        simp
      simp only [artinHasseExpCurrentRootPeelProduct]
      rw [hfirst, ih]
      simp

/-- Actual inverse-parameter zero-boundary specialization for current-root
peel products.  After sufficiently many Frobenius iterations, the inverse
Artin-Hasse parameter is literally zero in the finite quotient, so the
literal-zero endpoint applies unchanged. -/
theorem artinHasseExpCurrentRootPeelProduct_inverse_zero_boundary_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m m₀ D : ℕ) (hm : N + 1 ≤ ℓ ^ m) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpCurrentRootPeelProduct F N m₀ D (δ ^ (ℓ ^ m)) c = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hzero : δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  rw [hzero]
  exact F.artinHasseExpCurrentRootPeelProduct_zero_parameter N m₀ D c

/-- Powered form of
`artinHasseExpCurrentRootPeelProduct_inverse_zero_boundary_of_le`, matching
the `ℓ`-power endpoints used by the finite trace-carry character fold. -/
theorem artinHasseExpCurrentRootPeelProduct_inverse_zero_boundary_pow_prime_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m m₀ D : ℕ) (hm : N + 1 ≤ ℓ ^ m) (c : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    (artinHasseExpCurrentRootPeelProduct F N m₀ D (δ ^ (ℓ ^ m)) c) ^ ℓ = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  rw [F.artinHasseExpCurrentRootPeelProduct_inverse_zero_boundary_of_le
    N m m₀ D hm c]
  simp

/-- Coordinatewise root-of-unity kill for the current-root peel of a shifted
trace-carry tail.  This is the finite product reduction used by the WC3c
endpoint: once every displayed prime-field coordinate factor has `ℓ`-th power
`1`, the whole current-root product is `1`. -/
theorem artinHasseExpCurrentRootPeelProduct_traceCarry_tail_eq_one_of_factor_pow_prime_eq_one
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
          (ε ^ (ℓ ^ j) *
            (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff s))) ^ ℓ)) ^ ℓ = 1) :
    artinHasseExpCurrentRootPeelProduct F N m D ε
        (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s)) = 1 := by
  classical
  induction D generalizing m s with
  | zero =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      simp only [artinHasseExpCurrentRootPeelProduct]
      refine Finset.prod_eq_one ?_
      intro j hj
      let B : A :=
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            θ (WittVector.teichmuller ℓ
              (((WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s)).coeff 0) ^ ℓ)))
      have hB : B ^ ℓ = 1 := by
        have hBroot := hroot m s j hj
        dsimp only at hBroot
        rw [F.wittThetaModQPow_teichmuller_pow_prime N ((F.traceCarry y).coeff s)] at hBroot
        simpa [A, θ, Eps, B] using hBroot
      calc
        (B ^ ℓ) ^ (ℓ ^ (m - j)) = 1 ^ (ℓ ^ (m - j)) := by
          rw [hB]
        _ = 1 := by
          simp
  | succ D ih =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Eps : PowerSeries A :=
        (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let c : WittVector ℓ k :=
        WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s)
      let cTail : WittVector ℓ k :=
        WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + (s + 1))
      have htailVec : coordinateTailRoot c = cTail := by
        ext r
        dsimp [coordinateTailRoot, c, cTail]
        have hrootCoord :
            (_root_.frobeniusEquiv k ℓ).symm
                ((F.traceCarry y).coeff (r + (s + 1))) =
              (F.traceCarry y).coeff (r + (s + 1)) := by
          simpa using
            F.traceCarry_coeff_frobeniusEquiv_symm_iterate_eq_self
              y 1 (r + (s + 1))
        have hidx : r + 1 + s = r + (s + 1) := by
          omega
        rw [hidx]
        exact hrootCoord
      have hfirst :
          (∏ j ∈ Finset.range m,
            (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  ((c.coeff 0) ^ ℓ)))) ^ ℓ) ^
              (ℓ ^ (m - j))) = (1 : A) := by
        refine Finset.prod_eq_one ?_
        intro j hj
        let B : A :=
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                ((c.coeff 0) ^ ℓ)))
        have hB : B ^ ℓ = 1 := by
          have hBroot := hroot m s j hj
          dsimp only at hBroot
          rw [F.wittThetaModQPow_teichmuller_pow_prime N ((F.traceCarry y).coeff s)] at hBroot
          simpa [A, θ, Eps, B, c] using hBroot
        calc
          (B ^ ℓ) ^ (ℓ ^ (m - j)) = 1 ^ (ℓ ^ (m - j)) := by
            rw [hB]
          _ = 1 := by
            simp
      have htail :
          artinHasseExpCurrentRootPeelProduct F N (m + 1) D ε cTail = 1 :=
        ih (m + 1) (s + 1)
      simp only [artinHasseExpCurrentRootPeelProduct]
      change
        (∏ j ∈ Finset.range m,
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ ((c.coeff 0) ^ ℓ)))) ^ ℓ) ^
            (ℓ ^ (m - j))) *
          artinHasseExpCurrentRootPeelProduct F N (m + 1) D ε
            (coordinateTailRoot c) = 1
      rw [hfirst, htailVec, htail]
      simp

/-- Fixed-coordinate current-root range attached to the `s`-th trace-carry
coordinate. -/
noncomputable def artinHasseExpTraceCarryCurrentRootRangeProduct
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
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) *
        (θ (WittVector.teichmuller ℓ ((F.traceCarry y).coeff s))) ^ ℓ)) ^ ℓ) ^
      (ℓ ^ (m - j))

/-- Fixed-coordinate cleanup: the unshifted trace-carry range product is the
`ℓ`-th power of the corresponding current-root range. -/
theorem artinHasseExpTraceCarryZModUnshiftedRangeProduct_eq_currentRootRange_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    artinHasseExpTraceCarryZModUnshiftedRangeProduct F N m s ε y =
      (artinHasseExpTraceCarryCurrentRootRangeProduct F N m s ε y) ^ ℓ := by
  classical
  simp only [artinHasseExpTraceCarryZModUnshiftedRangeProduct,
    artinHasseExpTraceCarryCurrentRootRangeProduct]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjlt : j < m := Finset.mem_range.mp hj
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  have hcoord :
      algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y s) =
        (F.traceCarry y).coeff s ^ ℓ :=
    F.traceCarryCoeffZMod_pow_prime_spec y s
  have hexp : ℓ ^ (m + 2 - j) = ℓ * (ℓ ^ (m - j) * ℓ) := by
    have hsub : m + 2 - j = m - j + 2 := by
      omega
    rw [hsub, pow_add, pow_two]
    ring
  rw [hcoord]
  rw [← F.wittThetaModQPow_teichmuller_pow_prime N ((F.traceCarry y).coeff s)]
  rw [← pow_mul, ← pow_mul, ← Nat.mul_assoc]
  rw [hexp]
  rw [Nat.mul_assoc]

/-- The unshifted trace-carry product is the `ℓ`-th power of the existing
current-root peeled product for the corresponding tail of `traceCarry y`.
This is the endpoint cleanup after the coordinate-depth fold: no shifted
Artin-Hasse endpoint remains, only a current-root product to be killed in the
next step. -/
theorem artinHasseExpTraceCarryZModUnshiftedProduct_eq_currentRootPeelProduct_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    artinHasseExpTraceCarryZModUnshiftedProduct F N m D s ε y =
      (artinHasseExpCurrentRootPeelProduct F N m D ε
        (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s))) ^ ℓ := by
  classical
  induction D generalizing m s with
  | zero =>
      have hcoord :
          (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s)).coeff 0 =
            (F.traceCarry y).coeff s := by
        simp
      rw [show artinHasseExpTraceCarryZModUnshiftedProduct F N m 0 s ε y =
          artinHasseExpTraceCarryZModUnshiftedRangeProduct F N m s ε y from rfl,
        F.artinHasseExpTraceCarryZModUnshiftedRangeProduct_eq_currentRootRange_pow_prime
          N m s ε y]
      simp only [artinHasseExpCurrentRootPeelProduct,
        artinHasseExpTraceCarryCurrentRootRangeProduct, hcoord]
      refine congrArg (· ^ ℓ) (Finset.prod_congr rfl ?_)
      intro j _hj
      rw [F.wittThetaModQPow_teichmuller_pow_prime N ((F.traceCarry y).coeff s)]
  | succ D ih =>
      let c : WittVector ℓ k :=
        WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s)
      let cTail : WittVector ℓ k :=
        WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + (s + 1))
      have htailVec : coordinateTailRoot c = cTail := by
        ext r
        dsimp [coordinateTailRoot, c, cTail]
        have hroot :
            (_root_.frobeniusEquiv k ℓ).symm
                ((F.traceCarry y).coeff (r + (s + 1))) =
              (F.traceCarry y).coeff (r + (s + 1)) := by
          simpa using
            F.traceCarry_coeff_frobeniusEquiv_symm_iterate_eq_self
              y 1 (r + (s + 1))
        have hidx : r + 1 + s = r + (s + 1) := by
          omega
        rw [hidx]
        exact hroot
      simp only [artinHasseExpTraceCarryZModUnshiftedProduct,
        artinHasseExpCurrentRootPeelProduct]
      rw [mul_pow]
      have hrange :
          artinHasseExpTraceCarryZModUnshiftedRangeProduct F N m s ε y =
            (artinHasseExpTraceCarryCurrentRootRangeProduct F N m s ε y) ^ ℓ := by
        simpa [c] using
          F.artinHasseExpTraceCarryZModUnshiftedRangeProduct_eq_currentRootRange_pow_prime
            N m s ε y
      have htail :
          artinHasseExpTraceCarryZModUnshiftedProduct F N (m + 1) D (s + 1) ε y =
            (artinHasseExpCurrentRootPeelProduct F N (m + 1) D ε (coordinateTailRoot c)) ^ ℓ := by
        simpa [cTail, htailVec] using ih (m + 1) (s + 1)
      rw [hrange, htail]
      simp [c, artinHasseExpTraceCarryCurrentRootRangeProduct]

/-- Combined WC3c fold endpoint: the aligned ordinary correction product and
the normalized shifted trace-carry peel fold to the `ℓ`-th power of the
current-root peeled product.  This is the strongest local product-level
statement available before inserting the inverse-parameter telescope. -/
theorem artinHasseExpTraceCarryZModCorrection_mul_peel_eq_currentRoot_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    (hε : ∀ j : ℕ, (ε ^ (ℓ ^ j)) ^ (N + 1) = 0) :
    artinHasseExpTraceCarryZModCorrectionProduct F N m D s ε y *
      artinHasseExpTraceCarryZModPeelProductDivisible F N m D s ε y =
      (artinHasseExpCurrentRootPeelProduct F N m D ε
        (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s))) ^ ℓ := by
  rw [F.artinHasseExpTraceCarryZModCorrectionProduct_mul_peelProduct_eq_unshiftedProduct
    N m D s ε y hε]
  rw [F.artinHasseExpTraceCarryZModUnshiftedProduct_eq_currentRootPeelProduct_pow_prime]

/-- The finite trace-carry Artin-Hasse-Witt character surface used in WC3c:
the aligned ordinary correction product paired with the normalized shifted
trace-carry peel.  This is only a naming wrapper; the content is supplied by
the fold lemmas above. -/
noncomputable def artinHasseExpTraceCarryZModFiniteCharacter
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m D s : ℕ)
    (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  artinHasseExpTraceCarryZModCorrectionProduct F N m D s ε y *
    artinHasseExpTraceCarryZModPeelProductDivisible F N m D s ε y

/-- Fold endpoint for the named finite trace-carry character surface. -/
theorem artinHasseExpTraceCarryZModFiniteCharacter_eq_currentRoot_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ)
    (hε : ∀ j : ℕ, (ε ^ (ℓ ^ j)) ^ (N + 1) = 0) :
    artinHasseExpTraceCarryZModFiniteCharacter F N m D s ε y =
      (artinHasseExpCurrentRootPeelProduct F N m D ε
        (WittVector.mk ℓ fun r => (F.traceCarry y).coeff (r + s))) ^ ℓ := by
  simpa [artinHasseExpTraceCarryZModFiniteCharacter] using
    F.artinHasseExpTraceCarryZModCorrection_mul_peel_eq_currentRoot_pow_prime
      N m D s ε y hε

/-- Target proposition for the remaining WC3c endpoint kill.  It deliberately
states only the full-depth inverse-parameter trace-carry character needed
later, rather than a general Artin-Hasse-Witt homomorphism theorem. -/
def artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ) : Prop :=
  N + 1 ≤ ℓ ^ m →
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y = 1

/-- Inverse-parameter specialization of the named finite character surface.
This is the exact c1 target reduced to the current-root endpoint; the
remaining WC3c work is to kill that endpoint. -/
theorem artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_eq_currentRoot_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
      (artinHasseExpCurrentRootPeelProduct F N m N δ
        (WittVector.mk ℓ fun r => (F.traceCarry y).coeff r)) ^ ℓ := by
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
  have hδ_iter :
      ∀ j : ℕ, (δ ^ (ℓ ^ j)) ^ (N + 1) = 0 := fun j =>
    F.parameter_pow_iterate_pow_succ_eq_zero N j δ hδ
  simpa [A, Ips, πbar, δ] using
    F.artinHasseExpTraceCarryZModFiniteCharacter_eq_currentRoot_pow_prime
      N m N 0 δ y hδ_iter

/-- Same inverse-parameter finite-character endpoint, normalized to the
canonical `traceCarry y` rather than an extensionally equal `WittVector.mk`. -/
theorem traceCarryFiniteCharacter_inverse_eq_currentRoot_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
      (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hmk :
      (WittVector.mk ℓ fun r => (F.traceCarry y).coeff r) = F.traceCarry y := by
    ext r
    rfl
  simpa [A, Ips, πbar, δ, hmk] using
    F.artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_eq_currentRoot_pow_prime
      N m y

/-- The inverse full-depth finite-character equation is equivalent to the
current-root c5B2 endpoint equality. -/
theorem
  traceCarryFiniteCharacter_inverse_eq_one_iff_currentRoot_pow_prime_eq_one
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y = 1 ↔
      (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hfold :=
    F.traceCarryFiniteCharacter_inverse_eq_currentRoot_pow_prime N m y
  constructor
  · intro hfinite
    calc
      (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ =
          artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y := by
            simpa [A, Ips, πbar, δ] using hfold.symm
      _ = 1 := hfinite
  · intro hcurrent
    calc
      artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
          (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ := by
            simpa [A, Ips, πbar, δ] using hfold
      _ = 1 := hcurrent

/-- c5B2 endpoint extracted from the named inverse full-depth finite-character
target. -/
theorem traceCarryCurrentRootPeelProduct_inverse_pow_prime_eq_one_of_target
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ)
    (htarget :
      artinHasseExpTraceCarryZModFiniteCharacter_inverse_fullDepth_target F N m y) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  exact
    (F.traceCarryFiniteCharacter_inverse_eq_one_iff_currentRoot_pow_prime_eq_one
      N m y).mp (by
        simpa [A, Ips, πbar, δ] using htarget hm)

/-- Positive-index inverse endpoint rewritten as the current-root product for
the actual `ℓ * traceCarry y` Witt vector.  This is the product-level bridge
from the c1-c4 fold to the `ℓ`-multiple residue kill. -/
theorem traceCarryFiniteCharacter_inverse_eq_natCast_ell_mul_currentRoot_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (hm : 0 < m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
      (artinHasseExpCurrentRootPeelProduct F N (m - 1) (N + 1) δ
        ((ℓ : WittVector ℓ k) * F.traceCarry y)) ^ ℓ := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hfold :=
    F.traceCarryFiniteCharacter_inverse_eq_currentRoot_pow_prime N m y
  have hshift :
      artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y) =
        artinHasseExpCurrentRootPeelProduct F N (m - 1) (N + 1) δ
          ((ℓ : WittVector ℓ k) * F.traceCarry y) :=
    F.artinHasseExpCurrentRootPeelProduct_eq_natCast_ell_mul_pred
        N m N δ (F.traceCarry y) hm
  calc
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
        (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ := by
          simpa [A, Ips, πbar, δ] using hfold
    _ =
        (artinHasseExpCurrentRootPeelProduct F N (m - 1) (N + 1) δ
          ((ℓ : WittVector ℓ k) * F.traceCarry y)) ^ ℓ := by
          rw [hshift]

/-- Conditional closure of the named WC3c target from the current-root endpoint
kill.  This isolates the only remaining mathematical input after c1-c4. -/
theorem traceCarryFiniteCharacter_inverse_target_of_currentRoot_pow_prime_eq_one
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ)
    (hendpoint :
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Ips : PowerSeries A :=
        (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
      let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
      (artinHasseExpCurrentRootPeelProduct F N m N δ
        (F.traceCarry y)) ^ ℓ = 1) :
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
    F.traceCarryFiniteCharacter_inverse_eq_currentRoot_pow_prime
      N m y
  calc
    artinHasseExpTraceCarryZModFiniteCharacter F N m N 0 δ y =
        (artinHasseExpCurrentRootPeelProduct F N m N δ (F.traceCarry y)) ^ ℓ := by
          simpa [A, Ips, πbar, δ] using hfold
    _ = 1 := by
          simpa [A, Ips, πbar, δ] using hendpoint

/-- Closure of the named WC3c target from a transport of the current-root
endpoint to the actual zero boundary `δ^(ℓ^m)`.  This isolates the remaining
c5 work as the transport equality; the zero-boundary cleanup itself is handled
by `artinHasseExpCurrentRootPeelProduct_inverse_zero_boundary_pow_prime_of_le`. -/
theorem traceCarryFiniteCharacter_inverse_target_of_currentRoot_transport_to_zero_boundary
    [ExpChar k ℓ] [PerfectRing k ℓ] (N m : ℕ) (y : kˣ)
    (hm : N + 1 ≤ ℓ ^ m)
    (htransport :
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Ips : PowerSeries A :=
        (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
      let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
      (artinHasseExpCurrentRootPeelProduct F N m N δ
        (F.traceCarry y)) ^ ℓ =
      (artinHasseExpCurrentRootPeelProduct F N 0 N (δ ^ (ℓ ^ m))
        (F.traceCarry y)) ^ ℓ) :
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
  have hboundary :=
    F.artinHasseExpCurrentRootPeelProduct_inverse_zero_boundary_pow_prime_of_le
      N m 0 N hm (F.traceCarry y)
  calc
    (artinHasseExpCurrentRootPeelProduct F N m N δ
        (F.traceCarry y)) ^ ℓ =
        (artinHasseExpCurrentRootPeelProduct F N 0 N (δ ^ (ℓ ^ m))
          (F.traceCarry y)) ^ ℓ := by
          simpa [A, Ips, πbar, δ] using htransport
    _ = 1 := by
          simpa [A, Ips, πbar, δ] using hboundary

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
