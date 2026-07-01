module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope

/-!
# Low-precision Dwork splitting endpoints

Split from `DworkFactorization.lean`.
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

/-- The natural-number trace lift and the sum of Teichmüller Frobenius
conjugates have the same residue. -/
theorem traceNatCast_sub_teichFrobeniusSum_mem_Q (y : kˣ) :
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
        𝓞 R') -
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈ F.Q := by
  rw [F.toConcreteStickelbergerSetup.mem_Q_iff_residueMap_eq_zero, map_sub]
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  have hleft :
      F.residueMap
          ((((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
            𝓞 R')) =
        algebraMap (ZMod ℓ) k
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) := by
    rw [map_natCast]
    have h :=
      congrArg (algebraMap (ZMod ℓ) k)
        (ZMod.natCast_zmod_val
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))))
    rwa [map_natCast] at h
  have hright :
      F.residueMap
          (∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) =
        ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          ((F.traceScale : k) * (y : k)) ^ (ℓ ^ (i : ℕ)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _hi => ?_
    rw [map_pow, F.residueMap_teichUnitFullVal]
    rfl
  have htrace :
      algebraMap (ZMod ℓ) k
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) =
        ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          ((F.traceScale : k) * (y : k)) ^ (ℓ ^ (i : ℕ)) := by
    have hrange :
        algebraMap (ZMod ℓ) k
            (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) =
          ∑ i ∈ Finset.range F.toConcreteStickelbergerSetup.f,
            ((F.traceScale : k) * (y : k)) ^ (ℓ ^ i) := by
      simpa [traceSum] using
        F.toTraceFormStickelbergerSetup.algebraMap_trace_pow_eq_traceSum_pow_setup
          ((F.traceScale : k) * (y : k)) 1
    rw [← Fin.sum_univ_eq_sum_range] at hrange
    simpa using hrange
  rw [hleft, hright, htrace]
  simp

/-- For odd residue characteristic, the rational prime `ℓ` is already in
`Q^2`. -/
theorem natCast_ell_mem_Q_sq (hℓ : 2 < ℓ) :
    (ℓ : 𝓞 R') ∈ F.Q ^ 2 := by
  exact Ideal.pow_le_pow_right (by omega : 2 ≤ ℓ - 1)
    F.toTraceFormStickelbergerSetup.natCast_ell_mem_Q_pow_pred

/-- The natural-number lift of the trace is Frobenius-fixed modulo `Q^2`. -/
theorem traceNatCast_pow_ell_sub_self_mem_Q_sq (hℓ : 2 < ℓ) (y : kˣ) :
    let traceLift : 𝓞 R' :=
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
        𝓞 R')
    traceLift ^ ℓ - traceLift ∈ F.Q ^ 2 := by
  dsimp only
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have ht_le : t ≤ t ^ ℓ := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · exact le_self_pow (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero ht0))
        (Fact.out : Nat.Prime ℓ).ne_zero
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  have hzero : ((t ^ ℓ - t : ℕ) : ZMod ℓ) = 0 := by
    rw [Nat.cast_sub ht_le, Nat.cast_pow, ZMod.pow_card, sub_self]
  have hdvd_pow : ℓ ^ 1 ∣ t ^ ℓ - t := by
    simpa using (ZMod.natCast_eq_zero_iff (t ^ ℓ - t) ℓ).mp hzero
  have hmem_high :
      ((t ^ ℓ - t : ℕ) : 𝓞 R') ∈ F.Q ^ (1 * (ℓ - 1)) := by
    simpa using
      F.toTraceFormStickelbergerSetup.natCast_mem_Q_pow_mul_pred_of_ell_pow_dvd
        (c := t ^ ℓ - t) (m := 1) hdvd_pow
  have hmem_sq : ((t ^ ℓ - t : ℕ) : 𝓞 R') ∈ F.Q ^ 2 :=
    Ideal.pow_le_pow_right (by omega : 2 ≤ 1 * (ℓ - 1)) hmem_high
  simpa [t, Nat.cast_sub ht_le, Nat.cast_pow] using hmem_sq

/-- The Teichmüller Frobenius trace sum is Frobenius-fixed modulo `Q^2`. -/
theorem teichFrobeniusSum_pow_ell_sub_self_mem_Q_sq (hℓ : 2 < ℓ) (y : kˣ) :
    (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ^ ℓ -
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
        F.Q ^ 2 := by
  classical
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let f : ℕ := F.toConcreteStickelbergerSetup.f
  let u : Fin f → 𝓞 R' := fun i => z ^ (ℓ ^ (i : ℕ))
  have hellI : (ℓ : 𝓞 R') ∈ F.Q ^ 2 :=
    F.natCast_ell_mem_Q_sq hℓ
  have hfresh :
      (∑ i ∈ (Finset.univ : Finset (Fin f)), u i) ^ ℓ -
          (∑ i ∈ (Finset.univ : Finset (Fin f)), u i ^ ℓ) ∈ F.Q ^ 2 :=
    finset_sum_pow_prime_sub_sum_pow_mem_sq
      (I := F.Q) (s := (Finset.univ : Finset (Fin f)))
      (Fact.out : Nat.Prime ℓ) hellI u
  have hcard_pow : z ^ (ℓ ^ f) = z := by
    have hcard_pos : 0 < Fintype.card k := Fintype.card_pos
    have hcard : z ^ Fintype.card k = z := by
      rw [show Fintype.card k = (Fintype.card k - 1) + 1 by omega, pow_succ]
      simpa [z] using
        congrArg (fun a : 𝓞 R' => a * z)
          (F.teichUnitFullVal_pow_card_sub_one (F.traceScale * y))
    rw [← F.toConcreteStickelbergerSetup.card_k_eq]
    exact hcard
  have hleft_range :
      (∑ i : Fin f, u i ^ ℓ) =
        ∑ i ∈ Finset.range f, z ^ (ℓ ^ (i + 1)) := by
    simpa [u, pow_mul, pow_succ] using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ => z ^ (ℓ ^ (i + 1))) f)
  have hright_range :
      (∑ i : Fin f, u i) =
        ∑ i ∈ Finset.range f, z ^ (ℓ ^ i) := by
    simpa [u] using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ => z ^ (ℓ ^ i)) f)
  have hsum_pow : (∑ i : Fin f, u i ^ ℓ) = ∑ i : Fin f, u i := by
    rw [hleft_range, hright_range]
    exact sum_range_pow_shift_eq_of_pow_period z ℓ f hcard_pow
  rw [show (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) =
        ∑ i : Fin f, u i by rfl]
  simpa [hsum_pow] using hfresh

/-- The natural-number trace lift and the sum of Teichmüller Frobenius
conjugates agree modulo `Q^2` in odd residue characteristic. -/
theorem traceNatCast_sub_teichFrobeniusSum_mem_Q_sq (hℓ : 2 < ℓ) (y : kˣ) :
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
        𝓞 R') -
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈ F.Q ^ 2 := by
  let traceLift : 𝓞 R' :=
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
      𝓞 R')
  let teichSum : 𝓞 R' :=
    ∑ i : Fin F.toConcreteStickelbergerSetup.f,
      (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hQ : traceLift - teichSum ∈ F.Q := by
    simpa [traceLift, teichSum] using F.traceNatCast_sub_teichFrobeniusSum_mem_Q y
  have htrace : traceLift ^ ℓ - traceLift ∈ F.Q ^ 2 := by
    simpa [traceLift] using F.traceNatCast_pow_ell_sub_self_mem_Q_sq hℓ y
  have hteich : teichSum ^ ℓ - teichSum ∈ F.Q ^ 2 := by
    simpa [teichSum] using F.teichFrobeniusSum_pow_ell_sub_self_mem_Q_sq hℓ y
  exact
    sub_mem_sq_of_sub_mem_of_pow_prime_sub_self
      (I := F.Q) (Fact.out : Nat.Prime ℓ) (F.natCast_ell_mem_Q_sq hℓ)
      hQ htrace hteich

/-- Equality in the quotient by `Q^2` from a lifted congruence. -/
theorem quotient_mk_Q_sq_eq_of_sub_mem {x y : 𝓞 R'} (hxy : x - y ∈ F.Q ^ 2) :
    Ideal.Quotient.mk (F.Q ^ 2) x = Ideal.Quotient.mk (F.Q ^ 2) y := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hxy

/-- Concrete second-order trace comparison for the precision-2 Artin-Hasse
Dwork parameter. -/
theorem psiTraceBinomialApprox_two_sub_artinHasseSecondOrderTeichExpansion_approx_mem_Q_cubed
    (hℓ : 2 < ℓ) (y : kˣ) :
    psiTraceBinomialApprox F 2 y -
        artinHasseSecondOrderTeichExpansion F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup 2) y ∈
      F.Q ^ 3 := by
  classical
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S0 2
  let c₂ : 𝓞 R' := dworkCoeffArtinHasseAtTo S0 γ 2 2
  let tNat : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let t : 𝓞 R' := (tNat : ℕ)
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  let S : 𝓞 R' := ∑ i : Fin F.toConcreteStickelbergerSetup.f, u i
  let U₂ : 𝓞 R' := ∑ i : Fin F.toConcreteStickelbergerSetup.f, u i ^ 2
  let P : 𝓞 R' :=
    ∑ i : Fin F.toConcreteStickelbergerSetup.f,
      u i * ∑ j ∈ Finset.univ.filter (fun j => j < i), u j
  let C : 𝓞 R' := (Nat.choose tNat 2 : 𝓞 R')
  have hγQ : γ ∈ F.Q := by
    simpa [γ, S0] using artinHasseDworkParameterApproxTo_mem_Q S0 2
  have hγπ : γ - F.π ∈ F.Q ^ 2 := by
    simpa [γ, S0] using
      artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos S0
        (N := 2) (by norm_num : 0 < 2)
  have htraceQ : t - S ∈ F.Q := by
    simpa [t, tNat, S, u] using F.traceNatCast_sub_teichFrobeniusSum_mem_Q y
  have htraceQsq : t - S ∈ F.Q ^ 2 := by
    simpa [t, tNat, S, u] using F.traceNatCast_sub_teichFrobeniusSum_mem_Q_sq hℓ y
  have hchoose : (2 : 𝓞 R') * C = t * (t - 1) := by
    simpa [C, t, tNat] using two_mul_nat_choose_two_cast (A := 𝓞 R') tNat
  have hsquare : S ^ 2 = U₂ + (2 : 𝓞 R') * P := by
    simpa [S, U₂, P, u] using
      fin_sum_sq_eq_sum_sq_add_two_lower F.toConcreteStickelbergerSetup.f u
  have hpsi :
      psiTraceBinomialApprox F 2 y =
        1 + F.π * t + F.π ^ 2 * C := by
    simp [psiTraceBinomialApprox, t, tNat, C, Finset.sum_range_succ, pow_succ]
  have hexp :
      artinHasseSecondOrderTeichExpansion F γ y =
        1 + F.π * S + ((γ - F.π) * S + c₂ * U₂) + F.π ^ 2 * P := by
    simpa [S0, γ, c₂, u, S, U₂, P] using
      F.artinHasseSecondOrderTeichExpansion_eq_collected γ y
  have htwo_eq :
      (2 : 𝓞 R') *
          (psiTraceBinomialApprox F 2 y - artinHasseSecondOrderTeichExpansion F γ y) =
        (2 : 𝓞 R') * F.π * (t - S) -
          (((2 : 𝓞 R') * (γ - F.π) + F.π ^ 2) * S) -
          (((2 : 𝓞 R') * c₂ - F.π ^ 2) * U₂) +
          F.π ^ 2 * (S + t * (t - 1) - U₂ - (2 : 𝓞 R') * P) := by
    rw [hpsi, hexp, ← hchoose]
    ring
  have hterm₁ : (2 : 𝓞 R') * F.π * (t - S) ∈ F.Q ^ 3 := by
    have hπ : F.π ∈ F.Q ^ 1 := by
      simpa using F.π_mem_Q
    have hπtrace3 : F.π * (t - S) ∈ F.Q ^ 3 := by
      simpa using mul_mem_ideal_pow_add (I := F.Q) hπ htraceQsq
    simpa [mul_assoc] using Ideal.mul_mem_left (F.Q ^ 3) (2 : 𝓞 R') hπtrace3
  have hterm₂ :
      ((2 : 𝓞 R') * (γ - F.π) + F.π ^ 2) * S ∈ F.Q ^ 3 := by
    have hγcorr :
        (2 : 𝓞 R') * (γ - F.π) + F.π ^ 2 ∈ F.Q ^ 3 := by
      simpa [γ, S0] using
        two_mul_artinHasseDworkParameterApproxTo_two_sub_pi_add_pi_sq_mem_Q_cubed
          S0 hℓ
    exact Ideal.mul_mem_right _ _ hγcorr
  have hγsqπ : γ ^ 2 - F.π ^ 2 ∈ F.Q ^ 3 := by
    have hplus_one : γ + F.π ∈ F.Q ^ 1 := by
      simpa using F.Q.add_mem hγQ F.π_mem_Q
    have hprod : (γ - F.π) * (γ + F.π) ∈ F.Q ^ (2 + 1) :=
      mul_mem_ideal_pow_add (I := F.Q) hγπ hplus_one
    convert hprod using 1
    ring
  have hcoeffcorr : (2 : 𝓞 R') * c₂ - F.π ^ 2 ∈ F.Q ^ 3 := by
    have hcγ : (2 : 𝓞 R') * c₂ - γ ^ 2 ∈ F.Q ^ 3 := by
      simpa [c₂, γ, S0] using
        two_mul_dworkCoeffArtinHasseAtTo_two_sub_gamma_sq_mem_Q_cubed S0 γ hℓ
    rw [show (2 : 𝓞 R') * c₂ - F.π ^ 2 =
        ((2 : 𝓞 R') * c₂ - γ ^ 2) + (γ ^ 2 - F.π ^ 2) by ring]
    exact (F.Q ^ 3).add_mem hcγ hγsqπ
  have hterm₃ : ((2 : 𝓞 R') * c₂ - F.π ^ 2) * U₂ ∈ F.Q ^ 3 :=
    Ideal.mul_mem_right _ _ hcoeffcorr
  have hbracket_eq :
      S + t * (t - 1) - U₂ - (2 : 𝓞 R') * P =
        (t - S) * (t + S - 1) := by
    rw [show S + t * (t - 1) - U₂ - (2 : 𝓞 R') * P =
        S + t * (t - 1) - (U₂ + (2 : 𝓞 R') * P) by ring, ← hsquare]
    ring
  have hbracketQ :
      S + t * (t - 1) - U₂ - (2 : 𝓞 R') * P ∈ F.Q := by
    rw [hbracket_eq]
    exact Ideal.mul_mem_right _ _ htraceQ
  have hterm₄ :
      F.π ^ 2 * (S + t * (t - 1) - U₂ - (2 : 𝓞 R') * P) ∈ F.Q ^ 3 := by
    have hπ₂ : F.π ^ 2 ∈ F.Q ^ 2 :=
      Ideal.pow_mem_pow F.π_mem_Q 2
    have hbracket_one :
        S + t * (t - 1) - U₂ - (2 : 𝓞 R') * P ∈ F.Q ^ 1 := by
      simpa using hbracketQ
    simpa using mul_mem_ideal_pow_add (I := F.Q) hπ₂ hbracket_one
  have htwo_mem :
      (2 : 𝓞 R') *
          (psiTraceBinomialApprox F 2 y - artinHasseSecondOrderTeichExpansion F γ y) ∈
        F.Q ^ 3 := by
    rw [htwo_eq]
    exact (F.Q ^ 3).add_mem
      ((F.Q ^ 3).sub_mem ((F.Q ^ 3).sub_mem hterm₁ hterm₂) hterm₃)
      hterm₄
  have hinv₂ :
      (2 : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S0 2 2 - 1 ∈ F.Q ^ 3 := by
    let c : ℚ := (PowerSeries.coeff (R := ℚ) 2) (artinHasseExpSeries ℓ)
    have hc : c = (1 : ℚ) / (Nat.factorial 2 : ℚ) := by
      simpa [c] using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ
    have hden : c.den = 2 := by
      rw [hc]
      norm_num
    simpa [S0, c, hden] using dworkCoeffArtinHasseDenInvTo_spec S0 2 2
  have hmain : psiTraceBinomialApprox F 2 y -
        artinHasseSecondOrderTeichExpansion F γ y ∈ F.Q ^ 3 :=
    mem_of_mul_mem_of_mul_inv_sub_one_mem
      (I := F.Q ^ 3) (a := (2 : 𝓞 R'))
      (v := dworkCoeffArtinHasseDenInvTo S0 2 2) htwo_mem hinv₂
  simpa [γ, S0] using hmain

/-- Precision-2 Dwork splitting for the Artin-Hasse parameter approximation,
in theta-product form. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_two_approx_mem_Q_cubed
    (hℓ : 2 < ℓ) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup 2) 2 y ∈
      F.Q ^ 3 := by
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S0 2
  have hγ : γ ∈ F.Q := by
    simpa [γ, S0] using artinHasseDworkParameterApproxTo_mem_Q S0 2
  have hγπ : γ - F.π ∈ F.Q ^ 2 := by
    simpa [γ, S0] using
      artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos S0
        (N := 2) (by norm_num : 0 < 2)
  have htrace :
      psiTraceBinomialApprox F 2 y - artinHasseSecondOrderTeichExpansion F γ y ∈
        F.Q ^ 3 := by
    simpa [γ, S0] using
      F.psiTraceBinomialApprox_two_sub_artinHasseSecondOrderTeichExpansion_approx_mem_Q_cubed
        hℓ y
  simpa [γ, S0] using
    F.psiInt_sub_artinHasseThetaTruncProductAtTo_two_mem_Q_cubed_of_trace
      hγ hγπ y htrace

/-- Precision-2 Dwork splitting for the Artin-Hasse parameter approximation,
in the final `multiIndexLE` form. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAtTo_two_approx_mem_Q_cubed
    (hℓ : 2 < ℓ) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseDworkMultiIndexSumAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup 2) 2 y ∈
      F.Q ^ 3 := by
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S0 2
  have hγ : γ ∈ F.Q := by
    simpa [γ, S0] using artinHasseDworkParameterApproxTo_mem_Q S0 2
  have htheta :
      F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ 2 y ∈ F.Q ^ 3 := by
    simpa [γ, S0] using
      F.psiInt_sub_artinHasseThetaTruncProductAtTo_two_approx_mem_Q_cubed hℓ y
  simpa [γ, S0] using
    F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_mem_Q_pow_succ_of_theta hγ 2 y htheta

/-- First-order binomial expansion of the trace-form additive character. -/
theorem psiInt_sub_one_add_pi_traceNatCast_mem_Q_sq (y : kˣ) :
    F.psiInt (y : k) -
        (1 + F.π *
          (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
            𝓞 R')) ∈ F.Q ^ 2 := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) = F.zeta_ell_int ^ t := by
    simpa [t] using
      F.toTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace (y : k)
  have hzeta : F.zeta_ell_int = 1 + F.π := by
    rw [F.hπ]
    ring
  have htrunc := one_add_pow_sub_choose_sum_mem_pow (I := F.Q) F.π_mem_Q t 1
  have hsum :
      (∑ n ∈ Finset.range (1 + 1),
          F.π ^ n * (Nat.choose t n : 𝓞 R')) =
        1 + F.π * (t : 𝓞 R') := by
    simp [Finset.sum_range_succ]
  rw [hsum] at htrunc
  simpa [hpsi, hzeta, t] using htrunc

/-- First-order additive-character expansion with the trace rewritten as the
Teichmüller Frobenius sum. -/
theorem psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq (y : kˣ) :
    F.psiInt (y : k) -
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let traceLift : 𝓞 R' :=
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
      𝓞 R')
  let teichSum : 𝓞 R' :=
    ∑ i : Fin F.toConcreteStickelbergerSetup.f,
      (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hpsi : F.psiInt (y : k) - (1 + F.π * traceLift) ∈ F.Q ^ 2 := by
    simpa [traceLift] using F.psiInt_sub_one_add_pi_traceNatCast_mem_Q_sq y
  have htrace : traceLift - teichSum ∈ F.Q := by
    simpa [traceLift, teichSum] using F.traceNatCast_sub_teichFrobeniusSum_mem_Q y
  have htrace_sq : F.π * (traceLift - teichSum) ∈ F.Q ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul F.π_mem_Q htrace
  rw [show F.psiInt (y : k) - (1 + F.π * teichSum) =
      (F.psiInt (y : k) - (1 + F.π * traceLift)) +
        F.π * (traceLift - teichSum) by ring]
  exact (F.Q ^ 2).add_mem hpsi htrace_sq

/-- First-order binomial expansion of the trace-form root in its explicit
`(1 + π)^trace` form. -/
theorem one_add_pi_pow_traceNatCast_sub_linearTrace_mem_Q_sq (y : kˣ) :
    (1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val -
        (1 + F.π *
          (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
            𝓞 R')) ∈ F.Q ^ 2 := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) = (1 + F.π) ^ t := by
    have hzeta : F.zeta_ell_int = 1 + F.π := by
      rw [F.hπ]
      ring
    simpa [t, hzeta] using
      F.toTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace (y : k)
  simpa [t, hpsi] using F.psiInt_sub_one_add_pi_traceNatCast_mem_Q_sq y

/-- Quotient form of the first-order trace-root expansion modulo `Q^2`. -/
theorem quotient_mk_one_add_pi_pow_traceNatCast_eq_linearTrace_mod_Q_sq (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ 2)
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) =
      Ideal.Quotient.mk (F.Q ^ 2)
        (1 + F.π *
          (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
            𝓞 R')) :=
  F.quotient_mk_Q_sq_eq_of_sub_mem
    (F.one_add_pi_pow_traceNatCast_sub_linearTrace_mem_Q_sq y)

/-- First-order trace-root expansion with the trace rewritten as the
Teichmüller Frobenius sum. -/
theorem one_add_pi_pow_traceNatCast_sub_linearTeichSum_mem_Q_sq (y : kˣ) :
    (1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val -
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) = (1 + F.π) ^ t := by
    have hzeta : F.zeta_ell_int = 1 + F.π := by
      rw [F.hπ]
      ring
    simpa [t, hzeta] using
      F.toTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace (y : k)
  simpa [t, hpsi] using F.psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq y

/-- First nontrivial Dwork splitting congruence, modulo `Q^2`. -/
theorem psiInt_sub_artinHasseThetaTruncProduct_one_mem_Q_sq (y : kˣ) :
    F.psiInt (y : k) - artinHasseThetaTruncProduct F 1 y ∈ F.Q ^ 2 := by
  let linear : 𝓞 R' :=
    1 + F.π *
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hpsi : F.psiInt (y : k) - linear ∈ F.Q ^ 2 := by
    simpa [linear] using F.psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq y
  have htheta : artinHasseThetaTruncProduct F 1 y - linear ∈ F.Q ^ 2 := by
    simpa [linear] using F.artinHasseThetaTruncProduct_one_sub_linearTeichSum_mem_Q_sq y
  have hlinear_theta : linear - artinHasseThetaTruncProduct F 1 y ∈ F.Q ^ 2 := by
    simpa [sub_eq_add_neg] using (F.Q ^ 2).neg_mem htheta
  exact sub_mem_trans (F.Q ^ 2) hpsi hlinear_theta

/-- First nontrivial parameterized Dwork splitting congruence, modulo `Q^2`. -/
theorem psiInt_sub_artinHasseThetaTruncProductAt_one_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    F.psiInt (y : k) - artinHasseThetaTruncProductAt F γ 1 y ∈ F.Q ^ 2 := by
  let linear : 𝓞 R' :=
    1 + F.π *
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hpsi : F.psiInt (y : k) - linear ∈ F.Q ^ 2 := by
    simpa [linear] using F.psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq y
  have htheta : artinHasseThetaTruncProductAt F γ 1 y - linear ∈ F.Q ^ 2 := by
    simpa [linear] using
      F.artinHasseThetaTruncProductAt_one_sub_linearTeichSum_mem_Q_sq hγ hγπ y
  have hlinear_theta : linear - artinHasseThetaTruncProductAt F γ 1 y ∈ F.Q ^ 2 := by
    simpa [sub_eq_add_neg] using (F.Q ^ 2).neg_mem htheta
  exact sub_mem_trans (F.Q ^ 2) hpsi hlinear_theta

/-- First nontrivial precision-indexed parameterized Dwork splitting
congruence, modulo `Q^2`. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_one_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ 1 y ∈ F.Q ^ 2 := by
  let linear : 𝓞 R' :=
    1 + F.π *
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hpsi : F.psiInt (y : k) - linear ∈ F.Q ^ 2 := by
    simpa [linear] using F.psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq y
  have htheta : artinHasseThetaTruncProductAtTo F γ 1 y - linear ∈ F.Q ^ 2 := by
    simpa [linear] using
      F.artinHasseThetaTruncProductAtTo_one_sub_linearTeichSum_mem_Q_sq hγ hγπ y
  have hlinear_theta : linear - artinHasseThetaTruncProductAtTo F γ 1 y ∈ F.Q ^ 2 := by
    simpa [sub_eq_add_neg] using (F.Q ^ 2).neg_mem htheta
  exact sub_mem_trans (F.Q ^ 2) hpsi hlinear_theta

/-- Any positive precision-indexed parameterized theta product satisfies the
first-order Dwork splitting congruence modulo `Q^2`. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_mem_Q_sq_of_one_le
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ N y ∈ F.Q ^ 2 := by
  let linear : 𝓞 R' :=
    1 + F.π *
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hpsi : F.psiInt (y : k) - linear ∈ F.Q ^ 2 := by
    simpa [linear] using F.psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq y
  have htheta : artinHasseThetaTruncProductAtTo F γ N y - linear ∈ F.Q ^ 2 := by
    simpa [linear] using
      F.artinHasseThetaTruncProductAtTo_sub_linearTeichSum_mem_Q_sq_of_one_le
        hγ hγπ hN y
  have hlinear_theta : linear - artinHasseThetaTruncProductAtTo F γ N y ∈ F.Q ^ 2 := by
    simpa [sub_eq_add_neg] using (F.Q ^ 2).neg_mem htheta
  exact sub_mem_trans (F.Q ^ 2) hpsi hlinear_theta

/-- First-order product comparison for the Dwork approximation parameter,
modulo `Q^2`. -/
theorem artinHasseThetaTruncProductAtTo_approx_sub_linearTeichSum_mem_Q_sq_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y -
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S0 N
  have hγ : γ ∈ F.Q := by
    simpa [γ, S0] using artinHasseDworkParameterApproxTo_mem_Q S0 N
  have hγπ : γ - F.π ∈ F.Q ^ 2 := by
    have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    simpa [γ, S0] using
      artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos S0 (N := N) hNpos
  simpa [γ, S0] using
    F.artinHasseThetaTruncProductAtTo_sub_linearTeichSum_mem_Q_sq_of_one_le
      hγ hγπ hN y

/-- Quotient form of the first-order product comparison for the Dwork
approximation parameter. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_linearTeichSum_mod_Q_sq
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ 2)
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y) =
      Ideal.Quotient.mk (F.Q ^ 2)
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) :=
  F.quotient_mk_Q_sq_eq_of_sub_mem
    (F.artinHasseThetaTruncProductAtTo_approx_sub_linearTeichSum_mem_Q_sq_of_one_le
      hN y)

/-- The approximating Artin-Hasse product and the trace-form root have the
same image modulo `Q^2`; equivalently, their quotient starts in `1 + Q^2`. -/
theorem artinHasseThetaTruncProductAtTo_approx_sub_one_add_pi_pow_traceNatCast_mem_Q_sq
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y -
        (1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val ∈
      F.Q ^ 2 := by
  let linear : 𝓞 R' :=
    1 + F.π *
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hprod :
      artinHasseThetaTruncProductAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y -
          linear ∈ F.Q ^ 2 := by
    simpa [linear] using
      F.artinHasseThetaTruncProductAtTo_approx_sub_linearTeichSum_mem_Q_sq_of_one_le
        hN y
  have hroot :
      (1 + F.π) ^
            (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val -
          linear ∈ F.Q ^ 2 := by
    simpa [linear] using F.one_add_pi_pow_traceNatCast_sub_linearTeichSum_mem_Q_sq y
  have hlinear_root :
      linear -
          (1 + F.π) ^
            (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val ∈
        F.Q ^ 2 := by
    simpa [sub_eq_add_neg] using (F.Q ^ 2).neg_mem hroot
  exact sub_mem_trans (F.Q ^ 2) hprod hlinear_root

/-- Quotient form of the first-order product/root comparison modulo `Q^2`. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_one_add_pi_pow_traceNatCast_mod_Q_sq
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ 2)
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y) =
      Ideal.Quotient.mk (F.Q ^ 2)
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) :=
  F.quotient_mk_Q_sq_eq_of_sub_mem
    (F.artinHasseThetaTruncProductAtTo_approx_sub_one_add_pi_pow_traceNatCast_mem_Q_sq
      hN y)

/-- Base-order Dwork splitting: modulo `Q`, both the additive character and
the zero-th Artin-Hasse theta product are congruent to `1`. -/
theorem psiInt_sub_artinHasseThetaTruncProduct_zero_mem_Q (y : kˣ) :
    F.psiInt (y : k) - artinHasseThetaTruncProduct F 0 y ∈ F.Q := by
  have hpsi : F.psiInt (y : k) - 1 ∈ F.Q :=
    F.toConcreteStickelbergerSetup.psiInt_sub_one_mem_Q (y : k)
  have hprod_one :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          artinHasseThetaFactor F 0 y i) - (∏ _i : Fin F.toConcreteStickelbergerSetup.f,
          (1 : 𝓞 R')) ∈ F.Q := by
    simpa using
      fin_prod_sub_prod_mem_pow (I := F.Q)
        (fun i : Fin F.toConcreteStickelbergerSetup.f =>
          artinHasseThetaFactor F 0 y i)
        (fun _i : Fin F.toConcreteStickelbergerSetup.f => (1 : 𝓞 R')) 1
        (fun i =>
          by
            simpa [artinHasseThetaFactor] using
              F.toConcreteStickelbergerSetup.dworkThetaTrunc_artinHasse_zero_sub_one_mem_Q
                ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
  have hprod : artinHasseThetaTruncProduct F 0 y - 1 ∈ F.Q := by
    rw [artinHasseThetaTruncProduct_eq_prod_factor]
    simpa using hprod_one
  rw [show F.psiInt (y : k) - artinHasseThetaTruncProduct F 0 y =
      (F.psiInt (y : k) - 1) -
        (artinHasseThetaTruncProduct F 0 y - 1) by ring]
  exact F.Q.sub_mem hpsi hprod

/-- Base-order parameterized Dwork splitting. -/
theorem psiInt_sub_artinHasseThetaTruncProductAt_zero_mem_Q (γ : 𝓞 R') (y : kˣ) :
    F.psiInt (y : k) - artinHasseThetaTruncProductAt F γ 0 y ∈ F.Q := by
  have hpsi : F.psiInt (y : k) - 1 ∈ F.Q :=
    F.toConcreteStickelbergerSetup.psiInt_sub_one_mem_Q (y : k)
  have hprod_one :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          artinHasseThetaFactorAt F γ 0 y i) - (∏ _i : Fin F.toConcreteStickelbergerSetup.f,
          (1 : 𝓞 R')) ∈ F.Q := by
    simpa using
      fin_prod_sub_prod_mem_pow (I := F.Q)
        (fun i : Fin F.toConcreteStickelbergerSetup.f =>
          artinHasseThetaFactorAt F γ 0 y i)
        (fun _i : Fin F.toConcreteStickelbergerSetup.f => (1 : 𝓞 R')) 1
        (fun i =>
          by
            simp [artinHasseThetaFactorAt, dworkThetaTrunc])
  have hprod : artinHasseThetaTruncProductAt F γ 0 y - 1 ∈ F.Q := by
    simpa [artinHasseThetaTruncProductAt, artinHasseThetaFactorAt,
      dworkThetaFrobeniusProduct] using hprod_one
  rw [show F.psiInt (y : k) - artinHasseThetaTruncProductAt F γ 0 y =
      (F.psiInt (y : k) - 1) -
        (artinHasseThetaTruncProductAt F γ 0 y - 1) by ring]
  exact F.Q.sub_mem hpsi hprod

/-- Base-order precision-indexed parameterized Dwork splitting. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_zero_mem_Q
    (γ : 𝓞 R') (y : kˣ) :
    F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ 0 y ∈ F.Q := by
  have hpsi : F.psiInt (y : k) - 1 ∈ F.Q :=
    F.toConcreteStickelbergerSetup.psiInt_sub_one_mem_Q (y : k)
  have hprod_one :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          artinHasseThetaFactorAtTo F γ 0 y i) -
          (∏ _i : Fin F.toConcreteStickelbergerSetup.f, (1 : 𝓞 R')) ∈ F.Q := by
    simpa using
      fin_prod_sub_prod_mem_pow (I := F.Q)
        (fun i : Fin F.toConcreteStickelbergerSetup.f =>
          artinHasseThetaFactorAtTo F γ 0 y i)
        (fun _i : Fin F.toConcreteStickelbergerSetup.f => (1 : 𝓞 R')) 1
        (fun i =>
          by
            simp [artinHasseThetaFactorAtTo, dworkThetaTrunc])
  have hprod : artinHasseThetaTruncProductAtTo F γ 0 y - 1 ∈ F.Q := by
    simpa [artinHasseThetaTruncProductAtTo, artinHasseThetaFactorAtTo,
      dworkThetaFrobeniusProduct] using hprod_one
  rw [show F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ 0 y =
      (F.psiInt (y : k) - 1) -
        (artinHasseThetaTruncProductAtTo F γ 0 y - 1) by ring]
  exact F.Q.sub_mem hpsi hprod

/-- Base-order Dwork factorization in the final `multiIndexLE` form. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSum_zero_mem_Q (y : kˣ) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSum F 0 y ∈ F.Q := by
  simpa using
    F.psiInt_sub_artinHasseDworkMultiIndexSum_mem_Q_pow_succ_of_theta 0 y
      (by simpa using F.psiInt_sub_artinHasseThetaTruncProduct_zero_mem_Q y)

/-- First-order Dwork factorization in the final `multiIndexLE` form. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSum_one_mem_Q_sq (y : kˣ) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSum F 1 y ∈ F.Q ^ 2 := by
  simpa using
    F.psiInt_sub_artinHasseDworkMultiIndexSum_mem_Q_pow_succ_of_theta 1 y
      (F.psiInt_sub_artinHasseThetaTruncProduct_one_mem_Q_sq y)

/-- Base-order parameterized Dwork factorization in the final `multiIndexLE`
form. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAt_zero_mem_Q
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (y : kˣ) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSumAt F γ 0 y ∈ F.Q := by
  simpa using
    F.psiInt_sub_artinHasseDworkMultiIndexSumAt_mem_Q_pow_succ_of_theta hγ 0 y
      (by simpa using F.psiInt_sub_artinHasseThetaTruncProductAt_zero_mem_Q γ y)

/-- First-order parameterized Dwork factorization in the final `multiIndexLE`
form. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAt_one_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSumAt F γ 1 y ∈ F.Q ^ 2 := by
  simpa using
    F.psiInt_sub_artinHasseDworkMultiIndexSumAt_mem_Q_pow_succ_of_theta hγ 1 y
      (F.psiInt_sub_artinHasseThetaTruncProductAt_one_mem_Q_sq hγ hγπ y)

/-- Base-order precision-indexed parameterized Dwork factorization in the
final `multiIndexLE` form. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAtTo_zero_mem_Q
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (y : kˣ) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSumAtTo F γ 0 y ∈ F.Q := by
  simpa using
    F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_mem_Q_pow_succ_of_theta hγ 0 y
      (by simpa using F.psiInt_sub_artinHasseThetaTruncProductAtTo_zero_mem_Q γ y)

/-- First-order precision-indexed parameterized Dwork factorization in the
final `multiIndexLE` form. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAtTo_one_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSumAtTo F γ 1 y ∈ F.Q ^ 2 := by
  simpa using
    F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_mem_Q_pow_succ_of_theta hγ 1 y
      (F.psiInt_sub_artinHasseThetaTruncProductAtTo_one_mem_Q_sq hγ hγπ y)

/-- The precision-indexed Artin-Hasse approximation now satisfies the Dwork
factorization through precision `N = 2`. This packages the completed
low-order part separately from the still-open all-precision splitting
identity. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAtTo_approx_mem_Q_pow_succ_of_le_two
    (hℓ : 2 < ℓ) {N : ℕ} (hN : N ≤ 2) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseDworkMultiIndexSumAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) := by
  interval_cases N
  · have hγ : artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup 0 ∈ F.Q :=
      artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup 0
    simpa using
      F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_zero_mem_Q hγ y
  · have hγ : artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup 1 ∈ F.Q :=
      artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup 1
    have hγπ :
        artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup 1 - F.π ∈
          F.Q ^ 2 := by
      simpa using
        artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos
          F.toConcreteStickelbergerSetup (N := 1) (by norm_num : 0 < 1)
    simpa using
      F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_one_mem_Q_sq hγ hγπ y
  · simpa using
      F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_two_approx_mem_Q_cubed hℓ y

/-- Every higher-precision corrected theta product has the already-proved
precision-2 congruence as its reduction.  Thus the remaining all-order
problem starts in `Q^3`, not merely in `Q`. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_cubed_of_two_le
    (hℓ : 2 < ℓ) {N : ℕ} (hN : 2 ≤ N) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ 3 := by
  classical
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let AN : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let A2 : Type _ := 𝓞 R' ⧸ F.Q ^ (2 + 1)
  let φ : AN →+* A2 :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hN))
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let EpsN : PowerSeries AN := hE.mapTo (S0.rIntegralRatToQuotient N)
  let Eps2 : PowerSeries A2 := hE.mapTo (S0.rIntegralRatToQuotient 2)
  let hI : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpInverseSeries ℓ) :=
    artinHasseExpInverseSeries_isRIntegral ℓ
  let IpsN : PowerSeries AN := hI.mapTo (S0.rIntegralRatToQuotient N)
  let Ips2 : PowerSeries A2 := hI.mapTo (S0.rIntegralRatToQuotient 2)
  let πN : AN := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let π2 : A2 := Ideal.Quotient.mk (F.Q ^ (2 + 1)) F.π
  let δN : AN := (PowerSeries.trunc (N + 1) IpsN).eval₂ (RingHom.id AN) πN
  let δ2 : A2 := (PowerSeries.trunc (2 + 1) Ips2).eval₂ (RingHom.id A2) π2
  let zN : AN :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let z2 : A2 :=
    Ideal.Quotient.mk (F.Q ^ (2 + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let thetaN : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo S0 N) N y
  let prodN : AN :=
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) EpsN).eval₂ (RingHom.id AN)
        (δN * zN ^ (ℓ ^ (i : ℕ)))
  let prod2 : A2 :=
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (2 + 1) Eps2).eval₂ (RingHom.id A2)
        (δ2 * z2 ^ (ℓ ^ (i : ℕ)))
  let base2 : A2 := ((PowerSeries.trunc (2 + 1) Eps2).eval₂ (RingHom.id A2) δ2) ^ t
  have hlow :
      base2 = prod2 := by
    simpa [S0, A2, Eps2, Ips2, π2, δ2, z2, t, base2, prod2, hE] using
      (F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_base_pow
        2 y).1
        (F.psiInt_sub_artinHasseThetaTruncProductAtTo_two_approx_mem_Q_cubed hℓ y)
  have hpsi2 :
      Ideal.Quotient.mk (F.Q ^ (2 + 1)) (F.psiInt (y : k)) = base2 := by
    have hnorm :
        (PowerSeries.trunc (2 + 1) Eps2).eval₂ (RingHom.id A2) δ2 =
          1 + π2 := by
      simpa [S0, A2, Eps2, Ips2, π2, δ2] using
        S0.artinHasseExp_trunc_eval_inverse_trunc_eval_eq_one_add_pi 2
    calc
      Ideal.Quotient.mk (F.Q ^ (2 + 1)) (F.psiInt (y : k))
          =
            (1 + π2) ^ t := by
              simpa [π2, t, A2] using F.quotient_mk_psiInt_eq_one_add_pi_pow_trace 2 y
      _ = base2 := by
              rw [← hnorm]
  have hthetaN_N :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) thetaN = prodN := by
    simpa [S0, AN, EpsN, IpsN, πN, δN, zN, thetaN, prodN, hE] using
      F.quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
        N y
  have hprod_factor : φ prodN = prod2 := by
    simpa [S0, AN, A2, φ, EpsN, Eps2, IpsN, Ips2, πN, π2, δN, δ2, zN, z2,
      prodN, prod2] using
      F.artinHasseExp_inverse_frobenius_product_factor_eq (M := 2) (N := N) hN y
  have htheta2 :
      Ideal.Quotient.mk (F.Q ^ (2 + 1)) thetaN = prod2 := by
    calc
      Ideal.Quotient.mk (F.Q ^ (2 + 1)) thetaN =
          φ (Ideal.Quotient.mk (F.Q ^ (N + 1)) thetaN) :=
            (Ideal.Quotient.factor_mk
              (Ideal.pow_le_pow_right (Nat.succ_le_succ hN)) thetaN).symm
      _ = φ prodN := by rw [hthetaN_N]
      _ = prod2 := hprod_factor
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpsi2, htheta2, hlow, sub_self]

/-- Multi-index version of
`psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_cubed_of_two_le`. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAtTo_approx_mem_Q_cubed_of_two_le
    (hℓ : 2 < ℓ) {N : ℕ} (hN : 2 ≤ N) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseDworkMultiIndexSumAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ 3 := by
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S0 N
  have htheta :
      F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ N y ∈ F.Q ^ 3 := by
    simpa [S0, γ] using
      F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_cubed_of_two_le
        hℓ hN y
  have hγ : γ ∈ F.Q := by
    simpa [S0, γ] using artinHasseDworkParameterApproxTo_mem_Q S0 N
  have hproduct :
      artinHasseThetaTruncProductAtTo F γ N y -
          artinHasseDworkMultiIndexSumAtTo F γ N y ∈ F.Q ^ 3 :=
    Ideal.pow_le_pow_right (by omega : 3 ≤ N + 1)
      (by
        simpa [artinHasseDworkMultiIndexSumAtTo] using
          F.artinHasseThetaTruncProductAtTo_sub_multiIndexSumAtTo_mem_Q_pow_succ
            hγ N y)
  simpa [S0, γ] using sub_mem_trans (F.Q ^ 3) htheta hproduct

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
