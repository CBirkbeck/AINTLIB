module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteArtinHasseFormal
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteArtinHasseLog
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogHomogeneous
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogProducts

/-!
# Homogeneous expansion of the finite Artin-Hasse logarithm input

This file records the one-variable homogeneous polynomial whose value at `1`
is the finite Artin-Hasse principal-unit coordinate `E_N(x) - 1`. It then
expands `finiteLog N (E_N(x) - 1)` as the localized finite-log evaluator
applied to the homogeneous coefficients of powers of that polynomial.
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

/-- Homogeneous bookkeeping polynomial for the finite Artin-Hasse
principal-unit coordinate. Its coefficient in formal degree `n` is the
`Q^n`-integral representative of the `n`-th Artin-Hasse term. -/
noncomputable def finiteArtinHasseExpCoordPoly (N : ℕ) (x : 𝓞 R') :
    Polynomial (𝓞 R') :=
  ∑ n ∈ Finset.range N,
    Polynomial.monomial (n + 1)
      (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N (n + 1))

theorem finiteArtinHasseExpCoordPoly_eval_one (N : ℕ) (x : 𝓞 R') :
    (F.finiteArtinHasseExpCoordPoly N x).eval 1 =
      F.finiteArtinHasseExpCoord N x := by
  rw [F.finiteArtinHasseExpCoord_eq_positive_sum]
  simp [finiteArtinHasseExpCoordPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem finiteArtinHasseExpCoordPoly_coeff_mem_Q_pow
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (d : ℕ) :
    (F.finiteArtinHasseExpCoordPoly N x).coeff d ∈ F.Q ^ d := by
  classical
  rw [finiteArtinHasseExpCoordPoly, Polynomial.finsetSum_coeff]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  by_cases hnd : n + 1 = d
  · subst d
    simpa [Polynomial.coeff_monomial] using
      dworkCoeffArtinHasseAtTo_mem_Q_pow F.toConcreteStickelbergerSetup hx N (n + 1)
  · simp [Polynomial.coeff_monomial, hnd]

theorem finiteArtinHasseExpCoordPoly_coeff_zero (N : ℕ) (x : 𝓞 R') :
    (F.finiteArtinHasseExpCoordPoly N x).coeff 0 = 0 := by
  classical
  simp [finiteArtinHasseExpCoordPoly, Polynomial.coeff_monomial]

theorem finiteArtinHasseExpCoordPoly_coeff_eq_of_pos_le
    (N d : ℕ) (x : 𝓞 R') (hd0 : d ≠ 0) (hdN : d ≤ N) :
    (F.finiteArtinHasseExpCoordPoly N x).coeff d =
      dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N d := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdmem : d - 1 ∈ Finset.range N := Finset.mem_range.mpr (by lia)
  rw [finiteArtinHasseExpCoordPoly, Polynomial.finsetSum_coeff]
  calc
    (∑ n ∈ Finset.range N,
        ((Polynomial.monomial (n + 1))
          (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N (n + 1))
            ).coeff d)
        =
      ((Polynomial.monomial ((d - 1) + 1))
        (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N
          ((d - 1) + 1))).coeff d := by
        refine Finset.sum_eq_single_of_mem (d - 1) hdmem ?_
        intro n _hn hne
        have hne_degree : n + 1 ≠ d := fun h =>
          hne (by lia)
        simp [Polynomial.coeff_monomial, hne_degree]
    _ = dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N d := by
        simp [Nat.sub_add_cancel hdpos]

theorem finiteArtinHasseExpCoordPoly_coeff_sub_coeff_mem_Q_pow
    (N M d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (hNM : N ≤ M) :
    (F.finiteArtinHasseExpCoordPoly N x).coeff d -
        (F.finiteArtinHasseExpCoordPoly M x).coeff d ∈
      F.Q ^ (if d ≤ N then N + 1 + d else d) := by
  classical
  by_cases hdN : d ≤ N
  · rw [if_pos hdN]
    by_cases hd0 : d = 0
    · subst d
      simp [F.finiteArtinHasseExpCoordPoly_coeff_zero]
    · have hdM : d ≤ M := hdN.trans hNM
      let S := F.toConcreteStickelbergerSetup
      let c : ℚ := (PowerSeries.coeff (R := ℚ) d) (artinHasseExpSeries ℓ)
      have hNcoeff :
          (F.finiteArtinHasseExpCoordPoly N x).coeff d =
            dworkCoeffArtinHasseAtTo S x N d := by
        simpa [S] using F.finiteArtinHasseExpCoordPoly_coeff_eq_of_pos_le N d x hd0 hdN
      have hMcoeff :
          (F.finiteArtinHasseExpCoordPoly M x).coeff d =
            dworkCoeffArtinHasseAtTo S x M d := by
        simpa [S] using F.finiteArtinHasseExpCoordPoly_coeff_eq_of_pos_le M d x hd0 hdM
      have hN :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S x N d -
              (c.num : 𝓞 R') * x ^ d ∈ F.Q ^ (N + 1 + d) := by
        simpa [S, c] using
          dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ_add
            S hx N d
      have hMhigh :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S x M d -
              (c.num : 𝓞 R') * x ^ d ∈ F.Q ^ (M + 1 + d) := by
        simpa [S, c] using
          dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ_add
            S hx M d
      have hM :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S x M d -
              (c.num : 𝓞 R') * x ^ d ∈ F.Q ^ (N + 1 + d) :=
        Ideal.pow_le_pow_right (by lia) hMhigh
      have hden_mul :
          (c.den : 𝓞 R') *
              ((F.finiteArtinHasseExpCoordPoly N x).coeff d -
                (F.finiteArtinHasseExpCoordPoly M x).coeff d) ∈
            F.Q ^ (N + 1 + d) := by
        have hsub := (F.Q ^ (N + 1 + d)).sub_mem hN hM
        rw [hNcoeff, hMcoeff]
        convert hsub using 1
        ring
      have hden_not_mem : (c.den : 𝓞 R') ∉ F.Q :=
        S.natCast_not_mem_Q_of_coprime_ell
          (show c.den.Coprime ℓ from
            artinHasseExpSeries_coeff_isRIntegral ℓ d)
      rcases Ideal.IsPrime.mul_mem_pow F.Q hden_mul with hden | hdiff
      · exact False.elim (hden_not_mem hden)
      · exact hdiff
  · rw [if_neg hdN]
    have hNmem :
        (F.finiteArtinHasseExpCoordPoly N x).coeff d ∈ F.Q ^ d :=
      F.finiteArtinHasseExpCoordPoly_coeff_mem_Q_pow N hx d
    have hMmem :
        (F.finiteArtinHasseExpCoordPoly M x).coeff d ∈ F.Q ^ d :=
      F.finiteArtinHasseExpCoordPoly_coeff_mem_Q_pow M hx d
    exact (F.Q ^ d).sub_mem hNmem hMmem

/-- The quotient power series represented by the homogeneous coordinate
polynomial: formally this is `E_ell(x T) - 1`, but with the Artin-Hasse
coefficients interpreted through the local quotient map. -/
noncomputable def finiteArtinHasseExpCoordQuotientSeries (N : ℕ) (x : 𝓞 R') :
    PowerSeries (𝓞 R' ⧸ F.Q ^ (N + 1)) :=
  PowerSeries.mk fun d =>
    (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
        (((show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)) - 1) *
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ d)

@[simp] theorem coeff_finiteArtinHasseExpCoordQuotientSeries
    (N d : ℕ) (x : 𝓞 R') :
    (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
        (F.finiteArtinHasseExpCoordQuotientSeries N x) =
      (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
        (((show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
            fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
              (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)) - 1) *
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ d) := by
  simp [finiteArtinHasseExpCoordQuotientSeries]

theorem quotient_mk_finiteArtinHasseExpCoordPoly_coeff_eq
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        ((F.finiteArtinHasseExpCoordPoly N x).coeff d) =
      (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
        (F.finiteArtinHasseExpCoordQuotientSeries N x) := by
  classical
  let A : Type w := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let QN : Ideal (𝓞 R') := F.Q ^ (N + 1)
  let S := F.toConcreteStickelbergerSetup
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S.rIntegralRatToQuotient N)
  by_cases hd0 : d = 0
  · subst d
    have hconst :
        (PowerSeries.coeff (R := A) 0) (Eps - 1) = 0 := by
      have hcoeff0 :
          (⟨(PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ), hE 0⟩ :
              DieudonneDwork.rIntegralRatSubring ℓ) = 1 := by
        ext
        simp [artinHasseExpSeries_constantCoeff]
      have hmap0 :
          S.rIntegralRatToQuotientVal N
              (⟨(PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ), hE 0⟩ :
                DieudonneDwork.rIntegralRatSubring ℓ) = 1 := by
        have hmap0' :
            S.rIntegralRatToQuotient N
                (⟨(PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ), hE 0⟩ :
                  DieudonneDwork.rIntegralRatSubring ℓ) = 1 := by
          rw [hcoeff0]
          exact map_one (S.rIntegralRatToQuotient N)
        simpa [ConcreteStickelbergerSetup.rIntegralRatToQuotient_apply] using hmap0'
      have hcoeff_Eps0 : (PowerSeries.coeff (R := A) 0) Eps = 1 := by
        change (PowerSeries.coeff (R := A) 0)
            (hE.mapTo (S.rIntegralRatToQuotient N)) = 1
        rw [DieudonneDwork.IsRIntegralPS.coeff_mapTo]
        exact hmap0
      have hconst_Eps : PowerSeries.constantCoeff Eps = 1 := by
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff_Eps0
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hconst_Eps]
    rw [F.finiteArtinHasseExpCoordPoly_coeff_zero]
    rw [F.coeff_finiteArtinHasseExpCoordQuotientSeries]
    change (0 : A) =
      (PowerSeries.coeff (R := A) 0) (Eps - 1) * Ideal.Quotient.mk QN (x ^ 0)
    rw [hconst]
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    by_cases hdN : d ≤ N
    · have hdmem : d - 1 ∈ Finset.range N :=
        Finset.mem_range.mpr (by lia)
      have hcoeff_poly :
          (F.finiteArtinHasseExpCoordPoly N x).coeff d =
            dworkCoeffArtinHasseAtTo S x N d := by
        rw [finiteArtinHasseExpCoordPoly, Polynomial.finsetSum_coeff]
        calc
          (∑ n ∈ Finset.range N,
              ((Polynomial.monomial (n + 1))
                (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N (n + 1))
                  ).coeff d)
              =
            ((Polynomial.monomial ((d - 1) + 1))
              (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N
                ((d - 1) + 1))).coeff d := by
              refine Finset.sum_eq_single_of_mem (d - 1) hdmem ?_
              intro n hn hne
              have hne_degree : n + 1 ≠ d := fun h =>
                hne (by lia)
              simp [Polynomial.coeff_monomial, hne_degree]
          _ = dworkCoeffArtinHasseAtTo S x N d := by
              simp [Nat.sub_add_cancel hdpos, S]
      have hcoeff_E :
          (PowerSeries.coeff (R := A) d) (Eps - 1) =
            S.rIntegralRatToQuotient N
              (⟨(PowerSeries.coeff (R := ℚ) d) (artinHasseExpSeries ℓ), hE d⟩ :
                DieudonneDwork.rIntegralRatSubring ℓ) := by
        have hcoeff_Eps :
            (PowerSeries.coeff (R := A) d) Eps =
              S.rIntegralRatToQuotient N
                (⟨(PowerSeries.coeff (R := ℚ) d) (artinHasseExpSeries ℓ), hE d⟩ :
                  DieudonneDwork.rIntegralRatSubring ℓ) := by
          change (PowerSeries.coeff (R := A) d)
              (hE.mapTo (S.rIntegralRatToQuotient N)) =
            S.rIntegralRatToQuotient N
              (⟨(PowerSeries.coeff (R := ℚ) d) (artinHasseExpSeries ℓ), hE d⟩ :
                DieudonneDwork.rIntegralRatSubring ℓ)
          rw [DieudonneDwork.IsRIntegralPS.coeff_mapTo]
        simp [hcoeff_Eps, hd0]
      calc
        Ideal.Quotient.mk QN ((F.finiteArtinHasseExpCoordPoly N x).coeff d)
            =
          Ideal.Quotient.mk QN (dworkCoeffArtinHasseAtTo S x N d) := by
            rw [hcoeff_poly]
        _ =
          S.rIntegralRatToQuotient N
              (⟨(PowerSeries.coeff (R := ℚ) d) (artinHasseExpSeries ℓ), hE d⟩ :
                DieudonneDwork.rIntegralRatSubring ℓ) *
            Ideal.Quotient.mk QN (x ^ d) := by
            simpa [S, QN, hE] using
              quotient_mk_dworkCoeffArtinHasseAtTo_eq_rIntegralRatToQuotient_mul_gamma_pow
                S x N d
        _ =
          (PowerSeries.coeff (R := A) d)
            (F.finiteArtinHasseExpCoordQuotientSeries N x) := by
            rw [F.coeff_finiteArtinHasseExpCoordQuotientSeries]
            change
              S.rIntegralRatToQuotient N
                    (⟨(PowerSeries.coeff (R := ℚ) d) (artinHasseExpSeries ℓ), hE d⟩ :
                      DieudonneDwork.rIntegralRatSubring ℓ) *
                  Ideal.Quotient.mk QN (x ^ d) =
                (PowerSeries.coeff (R := A) d) (Eps - 1) *
                  Ideal.Quotient.mk QN (x ^ d)
            rw [hcoeff_E]
    · have hNd : N + 1 ≤ d := by lia
      have hcoeff_poly :
          (F.finiteArtinHasseExpCoordPoly N x).coeff d = 0 := by
        rw [finiteArtinHasseExpCoordPoly, Polynomial.finsetSum_coeff]
        refine Finset.sum_eq_zero ?_
        intro n hn
        have hnlt : n < N := Finset.mem_range.mp hn
        have hne_degree : n + 1 ≠ d := by lia
        simp [Polynomial.coeff_monomial, hne_degree]
      have hxpow : x ^ d ∈ F.Q ^ (N + 1) :=
        Ideal.pow_le_pow_right hNd (Ideal.pow_mem_pow hx d)
      have hmk_xpow : Ideal.Quotient.mk QN (x ^ d) = (0 : A) :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [QN] using hxpow)
      rw [hcoeff_poly]
      rw [F.coeff_finiteArtinHasseExpCoordQuotientSeries]
      change (0 : A) =
        (PowerSeries.coeff (R := A) d) (Eps - 1) * Ideal.Quotient.mk QN (x ^ d)
      rw [hmk_xpow, mul_zero]

theorem quotient_mk_finiteArtinHasseExpCoordPoly_pow_coeff_eq
    (N n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d) =
      (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
        ((F.finiteArtinHasseExpCoordQuotientSeries N x) ^ n) := by
  classical
  let A : Type w := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let QN : Ideal (𝓞 R') := F.Q ^ (N + 1)
  let P : Polynomial (𝓞 R') := F.finiteArtinHasseExpCoordPoly N x
  let φ : 𝓞 R' →+* A := Ideal.Quotient.mk QN
  have hseries :
      ((P.map φ : Polynomial A) : PowerSeries A) =
        F.finiteArtinHasseExpCoordQuotientSeries N x := by
    ext d
    rw [Polynomial.coeff_coe, Polynomial.coeff_map]
    change Ideal.Quotient.mk (F.Q ^ (N + 1))
        ((F.finiteArtinHasseExpCoordPoly N x).coeff d) =
      (PowerSeries.coeff (R := A) d) (F.finiteArtinHasseExpCoordQuotientSeries N x)
    exact quotient_mk_finiteArtinHasseExpCoordPoly_coeff_eq (F := F) N d hx
  calc
    Ideal.Quotient.mk QN ((P ^ n).coeff d)
        = ((P.map φ) ^ n).coeff d := by
          rw [← Polynomial.map_pow, Polynomial.coeff_map]
    _ =
      (PowerSeries.coeff (R := A) d) (((P.map φ : Polynomial A) : PowerSeries A) ^ n) := by
        rw [← Polynomial.coe_pow, Polynomial.coeff_coe]
    _ =
      (PowerSeries.coeff (R := A) d)
        ((F.finiteArtinHasseExpCoordQuotientSeries N x) ^ n) := by
        rw [hseries]

theorem finiteArtinHasseExpCoordQuotientSeries_eq_rescale
    (N : ℕ) (x : 𝓞 R') :
    F.finiteArtinHasseExpCoordQuotientSeries N x =
      PowerSeries.rescale (Ideal.Quotient.mk (F.Q ^ (N + 1)) x)
        ((((show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
            fun m => artinHasseExpSeries_coeff_isRIntegral ℓ m).mapTo
              (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)) - 1)) := by
  ext d
  rw [F.coeff_finiteArtinHasseExpCoordQuotientSeries, PowerSeries.coeff_rescale]
  simp [map_pow]
  ring

theorem coeff_finiteArtinHasseExpCoordQuotientSeries_pow
    (N n d : ℕ) (x : 𝓞 R') :
    (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
        ((F.finiteArtinHasseExpCoordQuotientSeries N x) ^ n) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ d) *
        (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
          (((((show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
              fun m => artinHasseExpSeries_coeff_isRIntegral ℓ m).mapTo
                (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)) - 1) ^ n)) := by
  let A : Type w := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let QN : Ideal (𝓞 R') := F.Q ^ (N + 1)
  let xbar : A := Ideal.Quotient.mk QN x
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun m => artinHasseExpSeries_coeff_isRIntegral ℓ m).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  calc
    (PowerSeries.coeff (R := A) d)
        ((F.finiteArtinHasseExpCoordQuotientSeries N x) ^ n)
        =
      (PowerSeries.coeff (R := A) d) ((PowerSeries.rescale xbar (Eps - 1)) ^ n) := by
        rw [F.finiteArtinHasseExpCoordQuotientSeries_eq_rescale]
    _ =
      (PowerSeries.coeff (R := A) d) (PowerSeries.rescale xbar ((Eps - 1) ^ n)) := by
        rw [(map_pow (PowerSeries.rescale xbar) (Eps - 1) n).symm]
    _ =
      xbar ^ d * (PowerSeries.coeff (R := A) d) ((Eps - 1) ^ n) := by
        rw [PowerSeries.coeff_rescale]
    _ =
      Ideal.Quotient.mk QN (x ^ d) *
        (PowerSeries.coeff (R := A) d) ((Eps - 1) ^ n) := by
        simp [xbar, QN]

theorem rIntegralRatToQuotient_factorialWeightedLogCoeff
    (N d n : ℕ) :
    F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N
        (FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) =
      ((d.factorial / n : ℕ) : 𝓞 R' ⧸ F.Q ^ (N + 1)) *
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
            (((((show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
                fun m => artinHasseExpSeries_coeff_isRIntegral ℓ m).mapTo
                  (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)) - 1) ^ n)) := by
  let S := F.toConcreteStickelbergerSetup
  let φ := S.rIntegralRatToQuotient N
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun m => artinHasseExpSeries_coeff_isRIntegral ℓ m
  let hA : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ - 1) :=
    hE.sub (DieudonneDwork.IsRIntegralPS.one ℓ)
  have hAps :
      hA.mapTo φ =
        hE.mapTo φ - (1 : PowerSeries (𝓞 R' ⧸ F.Q ^ (N + 1))) := by
    simpa [hA, hE, φ, S] using
      DieudonneDwork.IsRIntegralPS.mapTo_sub φ hE (DieudonneDwork.IsRIntegralPS.one ℓ)
  have hcoeff :
      φ (⟨(PowerSeries.coeff (R := ℚ) d) ((artinHasseExpSeries ℓ - 1) ^ n),
          hA.pow n d⟩ : DieudonneDwork.rIntegralRatSubring ℓ) =
        (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
          ((hE.mapTo φ - 1) ^ n) := by
    calc
      φ (⟨(PowerSeries.coeff (R := ℚ) d) ((artinHasseExpSeries ℓ - 1) ^ n),
          hA.pow n d⟩ : DieudonneDwork.rIntegralRatSubring ℓ)
          =
        (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d) ((hA.pow n).mapTo φ) := by
          rw [DieudonneDwork.IsRIntegralPS.coeff_mapTo]
      _ =
        (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d) ((hA.mapTo φ) ^ n) := by
          rw [DieudonneDwork.IsRIntegralPS.mapTo_pow]
      _ =
        (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d) ((hE.mapTo φ - 1) ^ n) := by
          rw [hAps]
  calc
    S.rIntegralRatToQuotient N
        (FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n)
        =
      ((d.factorial / n : ℕ) : 𝓞 R' ⧸ F.Q ^ (N + 1)) *
          ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          φ (⟨(PowerSeries.coeff (R := ℚ) d) ((artinHasseExpSeries ℓ - 1) ^ n),
            hA.pow n d⟩ : DieudonneDwork.rIntegralRatSubring ℓ) := by
        change φ (FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) =
          ((d.factorial / n : ℕ) : 𝓞 R' ⧸ F.Q ^ (N + 1)) *
            ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
              φ (⟨(PowerSeries.coeff (R := ℚ) d) ((artinHasseExpSeries ℓ - 1) ^ n),
                hA.pow n d⟩ : DieudonneDwork.rIntegralRatSubring ℓ)
        simp [FiniteArtinHasseFormal.factorialWeightedLogCoeff, map_mul, map_pow]
    _ =
      ((d.factorial / n : ℕ) : 𝓞 R' ⧸ F.Q ^ (N + 1)) *
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (PowerSeries.coeff (R := 𝓞 R' ⧸ F.Q ^ (N + 1)) d)
            ((hE.mapTo φ - 1) ^ n) := by
        rw [hcoeff]

theorem finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (n d : ℕ) :
    ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d ∈ F.Q ^ d := by
  induction n generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp
      · simp [Polynomial.coeff_one, hd]
  | succ n ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using Finset.mem_antidiagonal.mp ha
      have hleft :
          ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff a.1 ∈ F.Q ^ a.1 :=
        ih a.1
      have hright : (F.finiteArtinHasseExpCoordPoly N x).coeff a.2 ∈ F.Q ^ a.2 :=
        F.finiteArtinHasseExpCoordPoly_coeff_mem_Q_pow N hx a.2
      have hmul :
          ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff a.1 *
              (F.finiteArtinHasseExpCoordPoly N x).coeff a.2 ∈
            F.Q ^ (a.1 + a.2) := by
        simpa [pow_add] using Ideal.mul_mem_mul hleft hright
      simpa [hsum] using hmul

theorem finiteArtinHasseExpCoordPoly_pow_coeff_eq_zero_of_lt
    (N : ℕ) (x : 𝓞 R') {n d : ℕ} (hdn : d < n) :
    ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d = 0 := by
  induction n generalizing d with
  | zero =>
      lia
  | succ n ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      refine Finset.sum_eq_zero ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using Finset.mem_antidiagonal.mp ha
      by_cases ha_lt : a.1 < n
      · rw [ih ha_lt, zero_mul]
      · have hb_zero : a.2 = 0 := by lia
        rw [hb_zero, F.finiteArtinHasseExpCoordPoly_coeff_zero, mul_zero]

theorem finiteArtinHasseExpCoordPoly_pow_le_of_mem_support
    (N : ℕ) (x : 𝓞 R') {n d : ℕ}
    (hd : d ∈ ((F.finiteArtinHasseExpCoordPoly N x) ^ n).support) :
    n ≤ d := by
  by_contra hnd
  exact (Polynomial.mem_support_iff.mp hd)
    (F.finiteArtinHasseExpCoordPoly_pow_coeff_eq_zero_of_lt N x
      (Nat.lt_of_not_ge hnd))

theorem finiteArtinHasseExpCoordPoly_pow_coeff_sub_coeff_mem_Q_pow
    (N M n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (hNM : N ≤ M) :
    ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d -
        ((F.finiteArtinHasseExpCoordPoly M x) ^ n).coeff d ∈
      F.Q ^ (if d < N + n then N + 1 + d else d) := by
  classical
  induction n generalizing d with
  | zero =>
      simp
  | succ n ih =>
      let PN : Polynomial (𝓞 R') := F.finiteArtinHasseExpCoordPoly N x
      let PM : Polynomial (𝓞 R') := F.finiteArtinHasseExpCoordPoly M x
      rw [pow_succ, pow_succ, Polynomial.coeff_mul, Polynomial.coeff_mul]
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using Finset.mem_antidiagonal.mp ha
      by_cases ha2z : a.2 = 0
      · simp [ha2z, F.finiteArtinHasseExpCoordPoly_coeff_zero]
      · have ha2pos : 0 < a.2 := Nat.pos_of_ne_zero ha2z
        have hPN₂ : PN.coeff a.2 ∈ F.Q ^ a.2 := by
          simpa [PN] using F.finiteArtinHasseExpCoordPoly_coeff_mem_Q_pow N hx a.2
        have hPMpow₁ :
            (PM ^ n).coeff a.1 ∈ F.Q ^ a.1 := by
          simpa [PM] using F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow M hx n a.1
        have hdiff₁ :
            (PN ^ n).coeff a.1 - (PM ^ n).coeff a.1 ∈
              F.Q ^ (if a.1 < N + n then N + 1 + a.1 else a.1) := by
          simpa [PN, PM] using ih a.1
        have hmul₁ :
            ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 ∈
              F.Q ^ ((if a.1 < N + n then N + 1 + a.1 else a.1) + a.2) := by
          simpa [pow_add] using Ideal.mul_mem_mul hdiff₁ hPN₂
        have hterm₁ :
            ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 ∈
              F.Q ^ (if d < N + (n + 1) then N + 1 + d else d) := by
          refine Ideal.pow_le_pow_right ?_ hmul₁
          by_cases hdsmall : d < N + (n + 1)
          · have ha1small : a.1 < N + n := by lia
            rw [if_pos hdsmall, if_pos ha1small]
            lia
          · rw [if_neg hdsmall]
            by_cases ha1small : a.1 < N + n
            · rw [if_pos ha1small]
              lia
            · rw [if_neg ha1small]
              lia
        have hterm₂ :
            (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) ∈
              F.Q ^ (if d < N + (n + 1) then N + 1 + d else d) := by
          by_cases ha1lt : a.1 < n
          · have hzero : (PM ^ n).coeff a.1 = 0 := by
              simpa [PM] using
                F.finiteArtinHasseExpCoordPoly_pow_coeff_eq_zero_of_lt M x ha1lt
            rw [hzero, zero_mul]
            exact zero_mem _
          · have hna1 : n ≤ a.1 := Nat.le_of_not_gt ha1lt
            have hdiff₂ :
                PN.coeff a.2 - PM.coeff a.2 ∈
                  F.Q ^ (if a.2 ≤ N then N + 1 + a.2 else a.2) := by
              simpa [PN, PM] using
                F.finiteArtinHasseExpCoordPoly_coeff_sub_coeff_mem_Q_pow N M a.2 hx hNM
            have hmul₂ :
                (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) ∈
                  F.Q ^ (a.1 + (if a.2 ≤ N then N + 1 + a.2 else a.2)) := by
              simpa [pow_add] using Ideal.mul_mem_mul hPMpow₁ hdiff₂
            refine Ideal.pow_le_pow_right ?_ hmul₂
            by_cases hdsmall : d < N + (n + 1)
            · have ha2N : a.2 ≤ N := by lia
              rw [if_pos hdsmall, if_pos ha2N]
              lia
            · rw [if_neg hdsmall]
              by_cases ha2N : a.2 ≤ N
              · rw [if_pos ha2N]
                lia
              · rw [if_neg ha2N]
                lia
        rw [show
            (PN ^ n).coeff a.1 * PN.coeff a.2 -
                (PM ^ n).coeff a.1 * PM.coeff a.2 =
              ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 +
                (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) by ring]
        exact (F.Q ^ (if d < N + (n + 1) then N + 1 + d else d)).add_mem
          hterm₁ hterm₂

/-- Unsigned homogeneous finite-log term attached to the degree-`d`
coefficient of `(E_N(x)-1)^n`. -/
noncomputable def finiteArtinHasseExpCoordLogHomogeneousCore
    (N n d : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  if hn : n = 0 then 0 else
    if hnd : n ≤ d then
      F.finiteLogNatDivEvalAtDegree N n d hn
        (((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d)
        (F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx n d)
        (by
          have h :=
            Nat.factorization_mul_pred_le_pred
              (ell := ℓ) (n := n) (Fact.out : Nat.Prime ℓ) hn
          lia)
    else 0

/-- Signed homogeneous finite-log term attached to the degree-`d`
coefficient of `(E_N(x)-1)^n`. -/
noncomputable def finiteArtinHasseExpCoordLogHomogeneousTerm
    (N n d : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
    F.finiteArtinHasseExpCoordLogHomogeneousCore N n d x hx

/-- The Artin-Hasse denominator exponent is bounded by the ambient degree. -/
theorem finiteArtinHasse_den_exponent_le {n d : ℕ} (hn : n ≠ 0) (hnd : n ≤ d) :
    n.factorization ℓ * (ℓ - 1) ≤ d := by
  have h := Nat.factorization_mul_pred_le_pred
    (ell := ℓ) (n := n) (Fact.out : Nat.Prime ℓ) hn
  lia

theorem finiteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval
    (N n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (hn : n ≠ 0) (hnd : n ≤ d) :
    F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx =
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        F.finiteLogNatDivEvalAtDegree N n d hn
          (((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d)
          (F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx n d)
          (finiteArtinHasse_den_exponent_le (ℓ := ℓ) hn hnd) := by
  simp [finiteArtinHasseExpCoordLogHomogeneousTerm,
    finiteArtinHasseExpCoordLogHomogeneousCore, hn, hnd]

theorem finiteArtinHasseExpCoord_signed_pow_coeff_mem_Q_pow
    (N n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    ((-1 : 𝓞 R') ^ (n + 1)) *
        ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d ∈ F.Q ^ d :=
  Ideal.mul_mem_left _ _ (F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx n d)

/-- Signed numerator of the homogeneous finite-log contribution before quotienting. -/
def finiteArtinHasseExpCoordLogHomogeneousNumerator
    (N n d : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  ((-1 : 𝓞 R') ^ (n + 1)) *
    ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d

theorem finiteArtinHasseExpCoordLogHomogeneousNumerator_mem_Q_pow
    (N n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x ∈ F.Q ^ d :=
  F.finiteArtinHasseExpCoord_signed_pow_coeff_mem_Q_pow N n d hx

theorem quotient_mk_finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : 𝓞 R') *
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ d) *
        F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N
          (∑ n ∈ Finset.Icc 1 d, FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) := by
  classical
  let A : Type w := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let QN : Ideal (𝓞 R') := F.Q ^ (N + 1)
  let S := F.toConcreteStickelbergerSetup
  let φ := S.rIntegralRatToQuotient N
  let xbar_d : A := Ideal.Quotient.mk QN (x ^ d)
  have hterm : ∀ n ∈ Finset.Icc 1 d,
      Ideal.Quotient.mk QN
          (((d.factorial / n : ℕ) : 𝓞 R') *
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x) =
        xbar_d * φ (FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) := by
    intro n _hn
    calc
      Ideal.Quotient.mk QN
          (((d.factorial / n : ℕ) : 𝓞 R') *
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x)
          =
        ((d.factorial / n : ℕ) : A) *
          ((-1 : A) ^ (n + 1)) *
            (PowerSeries.coeff (R := A) d)
              ((F.finiteArtinHasseExpCoordQuotientSeries N x) ^ n) := by
          simp [QN, A, finiteArtinHasseExpCoordLogHomogeneousNumerator,
            F.quotient_mk_finiteArtinHasseExpCoordPoly_pow_coeff_eq N n d hx,
            map_mul, map_pow]
          ring
      _ =
        xbar_d * φ (FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) := by
          rw [F.coeff_finiteArtinHasseExpCoordQuotientSeries_pow N n d x]
          rw [F.rIntegralRatToQuotient_factorialWeightedLogCoeff N d n]
          simp [xbar_d, QN, A, S]
          ring
  calc
    Ideal.Quotient.mk QN
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : 𝓞 R') *
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x)
        =
      ∑ n ∈ Finset.Icc 1 d,
        Ideal.Quotient.mk QN
          (((d.factorial / n : ℕ) : 𝓞 R') *
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x) := by
        rw [map_sum]
    _ =
      ∑ n ∈ Finset.Icc 1 d,
        xbar_d * φ (FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact hterm n hn
    _ =
      xbar_d *
        ∑ n ∈ Finset.Icc 1 d,
          φ (FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) := by
        rw [← Finset.mul_sum]
    _ =
          Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ d) *
        F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N
          (∑ n ∈ Finset.Icc 1 d, FiniteArtinHasseFormal.factorialWeightedLogCoeff ℓ d n) := by
        rw [map_sum]

theorem finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_Q_pow
    (N M n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (hNM : N ≤ M)
    (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    (((d.factorial / n : ℕ) : 𝓞 R') *
        (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
          F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x)) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + (N + 1)) := by
  classical
  let s : ℕ := n.factorization ℓ * (ℓ - 1)
  let u : ℕ := if d < N + n then N + 1 + d else d
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
  have hs_le_pred : s ≤ n - 1 := by
    simpa [s] using
      Nat.factorization_mul_pred_le_pred
        (ell := ℓ) (n := n) (Fact.out : Nat.Prime ℓ) hn0
  have hs_le_d : s ≤ d := by lia
  have hu : N + 1 + s ≤ u := by
    by_cases hdsmall : d < N + n
    · dsimp [u]
      rw [if_pos hdsmall]
      lia
    · dsimp [u]
      rw [if_neg hdsmall]
      lia
  have hpowdiff :
      ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d -
          ((F.finiteArtinHasseExpCoordPoly M x) ^ n).coeff d ∈ F.Q ^ u := by
    simpa [u] using
      F.finiteArtinHasseExpCoordPoly_pow_coeff_sub_coeff_mem_Q_pow
        N M n d hx hNM
  have hnumdiff :
      F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
          F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x ∈ F.Q ^ u := by
    have hmul :
        ((-1 : 𝓞 R') ^ (n + 1)) *
            (((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d -
              ((F.finiteArtinHasseExpCoordPoly M x) ^ n).coeff d) ∈ F.Q ^ u :=
      Ideal.mul_mem_left _ _ hpowdiff
    simpa [finiteArtinHasseExpCoordLogHomogeneousNumerator, sub_eq_add_neg, mul_add,
      mul_neg] using hmul
  have hweighted :
      (((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x)) ∈
        F.Q ^ ((d.factorial / n).factorization ℓ * (ℓ - 1) + u) :=
    F.natCast_mul_mem_Q_pow_factorization_mul_pred_add
      (c := d.factorial / n) hnumdiff
  have hdiv : n ∣ d.factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero hn0) hnd
  have hmul_div : d.factorial / n * n = d.factorial := Nat.div_mul_cancel hdiv
  have hdiv_ne : d.factorial / n ≠ 0 := by
    intro hzero
    have hfac0 : d.factorial = 0 := by
      simpa [hzero] using hmul_div.symm
    exact Nat.factorial_ne_zero d hfac0
  have hfac :
      d.factorial.factorization ℓ =
        (d.factorial / n).factorization ℓ + n.factorization ℓ := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f ℓ)
      (Nat.factorization_mul hdiv_ne hn0)
    simpa [hmul_div] using h
  have htarget :
      d.factorial.factorization ℓ * (ℓ - 1) + (N + 1) ≤
        (d.factorial / n).factorization ℓ * (ℓ - 1) + u := by
    rw [hfac, Nat.add_mul]
    lia
  exact Ideal.pow_le_pow_right htarget hweighted

theorem finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_highPrecision_mem_Q_pow
    (N n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    (((d.factorial / n : ℕ) : 𝓞 R') *
        (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
          F.finiteArtinHasseExpCoordLogHomogeneousNumerator
            (N + d.factorial.factorization ℓ * (ℓ - 1)) n d x)) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + (N + 1)) :=
  F.finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_Q_pow
    N (N + d.factorial.factorization ℓ * (ℓ - 1)) n d hx
    (Nat.le_add_right N (d.factorial.factorization ℓ * (ℓ - 1))) hn1 hnd

theorem finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_mem_Q_pow_of_not_pow
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hd : ¬ ∃ r : ℕ, d = ℓ ^ r) :
    (∑ n ∈ Finset.Icc 1 d,
      ((d.factorial / n : ℕ) : 𝓞 R') *
        F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + (N + 1)) := by
  classical
  let D : ℕ := d.factorial.factorization ℓ * (ℓ - 1)
  let M : ℕ := D + N
  let I : Ideal (𝓞 R') := F.Q ^ (D + (N + 1))
  have hNM : N ≤ M := by lia
  have hdiff :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x)) ∈ I := by
    refine Ideal.sum_mem _ ?_
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
    simpa [I, D] using
      F.finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_Q_pow
        N M n d hx hNM hn1 hnd
  have hsumM_M :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x) ∈
        F.Q ^ (M + 1) := by
    have hq :=
      F.quotient_mk_finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
        M d hx
    rw [FiniteArtinHasseFormal.sum_factorialWeightedLogCoeff_eq_zero_of_not_pow ℓ d hd] at hq
    rw [map_zero, mul_zero] at hq
    have hq_zero :
        Ideal.Quotient.mk (F.Q ^ (M + 1))
          (∑ n ∈ Finset.Icc 1 d,
            ((d.factorial / n : ℕ) : 𝓞 R') *
              F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x) = 0 := by
      simpa using hq
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq_zero
  have hsumM : (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x) ∈ I := by
    simpa [I, M, D, Nat.add_assoc] using hsumM_M
  have hsplit :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x) =
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x)) +
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  rw [hsplit]
  exact I.add_mem hdiff hsumM

theorem finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_pow_mem_Q_pow
    (N r : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    (∑ n ∈ Finset.Icc 1 (ℓ ^ r),
      (((ℓ ^ r).factorial / n : ℕ) : 𝓞 R') *
        (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n (ℓ ^ r) x -
          if n = ℓ ^ r then x ^ (ℓ ^ r) else 0)) ∈
      F.Q ^ ((ℓ ^ r).factorial.factorization ℓ * (ℓ - 1) + (N + 1)) := by
  classical
  let d : ℕ := ℓ ^ r
  let D : ℕ := d.factorial.factorization ℓ * (ℓ - 1)
  let M : ℕ := D + N
  let I : Ideal (𝓞 R') := F.Q ^ (D + (N + 1))
  let target : ℕ → 𝓞 R' := fun n => if n = d then x ^ d else 0
  have hd_ne : d ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime ℓ).ne_zero
  have hd_mem : d ∈ Finset.Icc 1 d :=
    Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd_ne), le_rfl⟩
  have hNM : N ≤ M := by lia
  have hdiff :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x)) ∈ I := by
    refine Ideal.sum_mem _ ?_
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
    simpa [I, D] using
      F.finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_Q_pow
        N M n d hx hNM hn1 hnd
  have hsumM_eq :
      Ideal.Quotient.mk (F.Q ^ (M + 1))
          (∑ n ∈ Finset.Icc 1 d,
            ((d.factorial / n : ℕ) : 𝓞 R') *
              F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x) =
        Ideal.Quotient.mk (F.Q ^ (M + 1))
          (((d.factorial / d : ℕ) : 𝓞 R') * x ^ d) := by
    have hq :=
      F.quotient_mk_finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
        M d hx
    rw [show d = ℓ ^ r by rfl] at hq
    rw [FiniteArtinHasseFormal.sum_factorialWeightedLogCoeff_eq_factorial_div_pow ℓ r] at hq
    simpa [d, map_mul, mul_comm, mul_left_comm, mul_assoc] using hq
  have htarget_sum :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') * target n) =
        ((d.factorial / d : ℕ) : 𝓞 R') * x ^ d := by
    calc
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') * target n)
          =
        ((d.factorial / d : ℕ) : 𝓞 R') * target d := by
          refine Finset.sum_eq_single (s := Finset.Icc 1 d) (a := d)
            (f := fun n => ((d.factorial / n : ℕ) : 𝓞 R') * target n) ?main ?not_mem
          · intro n hn hne
            have hne' : n ≠ d := fun h =>
              hne h
            simp [target, hne']
          · intro hd_not
            exact False.elim (hd_not hd_mem)
      _ = ((d.factorial / d : ℕ) : 𝓞 R') * x ^ d := by
          simp [target]
  have hsumM_sub_M :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x - target n)) ∈
        F.Q ^ (M + 1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hsplit :
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : 𝓞 R') *
            (F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x - target n)) =
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : 𝓞 R') *
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x) -
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : 𝓞 R') * target n) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro n _hn
      ring
    rw [hsplit, map_sub, hsumM_eq, htarget_sum]
    simp
  have hsumM_sub : (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x - target n)) ∈ I := by
    simpa [I, M, D, Nat.add_assoc] using hsumM_sub_M
  have hsplit :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x - target n)) =
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x -
            F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x)) +
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator M n d x - target n)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  have hmain : (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x - target n)) ∈ I := by
    rw [hsplit]
    exact I.add_mem hdiff hsumM_sub
  simpa [d, I, D, target] using hmain

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
