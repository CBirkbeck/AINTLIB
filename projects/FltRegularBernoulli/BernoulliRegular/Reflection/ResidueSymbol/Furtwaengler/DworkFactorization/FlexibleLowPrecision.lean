module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteArtinHasseHomogeneous

/-!
# Low-precision flexible Dwork inputs

This file ports the first-order `Q^2` comparisons used by the finite-log
product argument to the conductor-flexible full-Teich setup.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

/-- The precision-indexed linear Artin-Hasse coefficient is congruent to `π`
modulo `Q^2` as soon as `γ ≡ π mod Q^2`. -/
theorem dworkCoeffArtinHasseAtTo_one_sub_pi_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) :
    S.dworkCoeffArtinHasseAtTo γ N 1 - S.π ∈ S.Q ^ 2 := by
  have hℓ : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
  simpa using S.dworkCoeffArtinHasseAtTo_lt_ell_leading hγ hγπ N 1 hN hℓ

/-- Any positive precision-indexed parameterized Artin-Hasse theta truncation
has the same first-order reduction modulo `Q^2`. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_one_add_pi_mul_mod_sq_of_one_le
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (u : 𝓞 R') :
    Ideal.Quotient.mk (S.Q ^ 2)
        (dworkThetaTrunc (S.dworkCoeffArtinHasseAtTo γ N) N u) =
      Ideal.Quotient.mk (S.Q ^ 2) (1 + S.π * u) := by
  classical
  let coeff : ℕ → 𝓞 R' := S.dworkCoeffArtinHasseAtTo γ N
  have h0mem : 0 ∈ Finset.range (N + 1) := by simp
  have h1lt : 1 < N + 1 := Nat.lt_succ_of_le hN
  have h1mem : 1 ∈ Finset.range (N + 1) \ {0} := by
    simp [h1lt]
  have hcoeff₁ : coeff 1 - S.π ∈ S.Q ^ 2 :=
    S.dworkCoeffArtinHasseAtTo_one_sub_pi_mem_Q_sq hγ hγπ hN
  have hlinear :
      Ideal.Quotient.mk (S.Q ^ 2) (coeff 1 * u) =
        Ideal.Quotient.mk (S.Q ^ 2) (S.π * u) := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have hmul : (coeff 1 - S.π) * u ∈ S.Q ^ 2 :=
      Ideal.mul_mem_right _ _ hcoeff₁
    convert hmul using 1
    ring
  have htail :
      (∑ n ∈ (Finset.range (N + 1) \ {0}) \ {1},
          Ideal.Quotient.mk (S.Q ^ 2) (coeff n * u ^ n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn_ne1 : n ≠ 1 := by
      simpa using (Finset.mem_sdiff.mp hn).2
    have hn_mem0 : n ∈ Finset.range (N + 1) \ {0} :=
      (Finset.mem_sdiff.mp hn).1
    have hn_ne0 : n ≠ 0 := by
      simpa using (Finset.mem_sdiff.mp hn_mem0).2
    have hn2 : 2 ≤ n := by omega
    have hcoeff₂ : coeff n ∈ S.Q ^ 2 :=
      Ideal.pow_le_pow_right hn2
        (S.dworkCoeffArtinHasseAtTo_mem_Q_pow hγ N n)
    have hterm : coeff n * u ^ n ∈ S.Q ^ 2 :=
      Ideal.mul_mem_right _ _ hcoeff₂
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hterm
  calc
    Ideal.Quotient.mk (S.Q ^ 2)
        (dworkThetaTrunc (S.dworkCoeffArtinHasseAtTo γ N) N u)
        = ∑ n ∈ Finset.range (N + 1),
            Ideal.Quotient.mk (S.Q ^ 2) (coeff n * u ^ n) := by
            simp [dworkThetaTrunc, coeff, map_sum]
    _ =
        Ideal.Quotient.mk (S.Q ^ 2) (coeff 0 * u ^ 0) +
          (Ideal.Quotient.mk (S.Q ^ 2) (coeff 1 * u ^ 1) +
            ∑ n ∈ (Finset.range (N + 1) \ {0}) \ {1},
              Ideal.Quotient.mk (S.Q ^ 2) (coeff n * u ^ n)) := by
            simp only [Finset.sdiff_singleton_eq_erase] at h0mem h1mem ⊢
            rw [← Finset.add_sum_erase _ _ h0mem, ← Finset.add_sum_erase _ _ h1mem]
    _ = Ideal.Quotient.mk (S.Q ^ 2) (1 + S.π * u) := by
            rw [htail]
            simp only [pow_zero, pow_one, mul_one, add_zero]
            rw [hlinear]
            simp [coeff]

/-- Subtraction-form first-order reduction of every positive
precision-indexed parameterized Artin-Hasse theta truncation. -/
theorem dworkThetaTrunc_artinHasseAtTo_sub_one_add_pi_mul_mem_Q_sq_of_one_le
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (u : 𝓞 R') :
    dworkThetaTrunc (S.dworkCoeffArtinHasseAtTo γ N) N u - (1 + S.π * u) ∈
      S.Q ^ 2 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk (S.Q ^ 2)
      (dworkThetaTrunc (S.dworkCoeffArtinHasseAtTo γ N) N u - (1 + S.π * u)) = 0
  rw [map_sub,
    S.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_one_add_pi_mul_mod_sq_of_one_le
      hγ hγπ hN u]
  simp

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- The natural-number trace lift and the sum of Teichmuller Frobenius
conjugates have the same residue. -/
theorem traceNatCast_sub_teichFrobeniusSum_mem_Q (y : kˣ) :
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
        𝓞 R') -
      (∑ i : Fin F.concrete.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈ F.Q := by
  change
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
        𝓞 R') -
      (∑ i : Fin F.concrete.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈ F.concrete.Q
  rw [F.concrete.mem_Q_iff_residueMap_eq_zero, map_sub]
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  have hleft :
      F.concrete.residueMap
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
      F.concrete.residueMap
          (∑ i : Fin F.concrete.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) =
        ∑ i : Fin F.concrete.f,
          ((F.traceScale : k) * (y : k)) ^ (ℓ ^ (i : ℕ)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _hi => ?_
    have hbase :
        F.concrete.residueMap (F.teichUnitFullVal (F.traceScale * y)) =
          ((F.traceScale : k) * (y : k)) := by
      have h := F.residueMap_teichUnitFullVal (F.traceScale * y)
      rwa [Units.val_mul] at h
    rw [map_pow, hbase]
  have htrace :
      algebraMap (ZMod ℓ) k
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) =
        ∑ i : Fin F.concrete.f,
          ((F.traceScale : k) * (y : k)) ^ (ℓ ^ (i : ℕ)) := by
    have hfin : Module.finrank (ZMod ℓ) k = F.concrete.f := by
      have hpow : ℓ ^ Module.finrank (ZMod ℓ) k = ℓ ^ F.concrete.f := by
        rw [FiniteField.pow_finrank_eq_card, F.concrete.card_k]
      exact Nat.pow_right_injective (Fact.out : Nat.Prime ℓ).one_lt hpow
    have hrange :
        algebraMap (ZMod ℓ) k
            (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) =
          ∑ i ∈ Finset.range F.concrete.f,
            ((F.traceScale : k) * (y : k)) ^ (ℓ ^ i) := by
      simpa [traceSum] using
        algebraMap_trace_pow_eq_traceSum_pow
          (K := ZMod ℓ) (L := k) (ℓ := ℓ) (f := F.concrete.f)
          (Nat.card_zmod ℓ) hfin ((F.traceScale : k) * (y : k)) 1
    rw [← Fin.sum_univ_eq_sum_range] at hrange
    simpa using hrange
  rw [hleft, hright, htrace]
  simp

/-- Equality in the quotient by `Q^2` from a lifted congruence. -/
theorem quotient_mk_Q_sq_eq_of_sub_mem {x y : 𝓞 R'} (hxy : x - y ∈ F.Q ^ 2) :
    Ideal.Quotient.mk (F.Q ^ 2) x = Ideal.Quotient.mk (F.Q ^ 2) y := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hxy

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
      F.toConductorFlexibleTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace
        (y : k)
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
Teichmuller Frobenius sum. -/
theorem psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq (y : kˣ) :
    F.psiInt (y : k) -
        (1 + F.π *
          ∑ i : Fin F.concrete.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let traceLift : 𝓞 R' :=
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
      𝓞 R')
  let teichSum : 𝓞 R' :=
    ∑ i : Fin F.concrete.f,
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
      F.toConductorFlexibleTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace
        (y : k)
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
Teichmuller Frobenius sum. -/
theorem one_add_pi_pow_traceNatCast_sub_linearTeichSum_mem_Q_sq (y : kˣ) :
    (1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val -
        (1 + F.π *
          ∑ i : Fin F.concrete.f,
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
      F.toConductorFlexibleTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace
        (y : k)
  simpa [t, hpsi] using F.psiInt_sub_one_add_pi_teichFrobeniusSum_mem_Q_sq y

/-- Precision-indexed theta product linearization modulo `Q^2`. -/
theorem artinHasseThetaTruncProductAtTo_sub_linearTeichSum_mem_Q_sq_of_one_le
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo γ N y -
        (1 + F.π *
          ∑ i : Fin F.concrete.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let S0 : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' := F.concrete
  let u : Fin F.concrete.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hfactor :
      (∏ i : Fin F.concrete.f,
          dworkThetaTrunc (S0.dworkCoeffArtinHasseAtTo γ N) N (u i)) -
          (∏ i : Fin F.concrete.f, (1 + F.π * u i)) ∈
        F.Q ^ 2 :=
    fin_prod_sub_prod_mem_pow (I := F.Q)
      (fun i : Fin F.concrete.f =>
        dworkThetaTrunc (S0.dworkCoeffArtinHasseAtTo γ N) N (u i))
      (fun i : Fin F.concrete.f => (1 + F.π * u i)) 2
      (fun i =>
        by
          have hi :=
            S0.dworkThetaTrunc_artinHasseAtTo_sub_one_add_pi_mul_mem_Q_sq_of_one_le
              hγ hγπ hN (u i)
          exact hi)
  have hlinear :
      (∏ i : Fin F.concrete.f, (1 + F.π * u i)) -
          (1 + F.π * ∑ i : Fin F.concrete.f, u i) ∈ F.Q ^ 2 :=
    fin_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
      (I := F.Q) F.π_mem_Q u
  simpa [artinHasseThetaTruncProductAtTo, dworkThetaFrobeniusProduct, u, S0]
    using sub_mem_trans (F.Q ^ 2) hfactor hlinear

/-- First-order product comparison for the Dwork approximation parameter,
modulo `Q^2`. -/
theorem artinHasseThetaTruncProductAtTo_approx_sub_linearTeichSum_mem_Q_sq_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo (F.concrete.artinHasseDworkParameterApproxTo N) N y -
        (1 + F.π *
          ∑ i : Fin F.concrete.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let γ : 𝓞 R' := F.concrete.artinHasseDworkParameterApproxTo N
  have hγ : γ ∈ F.Q :=
    F.concrete.artinHasseDworkParameterApproxTo_mem_Q N
  have hγπ : γ - F.π ∈ F.Q ^ 2 := by
    have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    exact
      F.concrete.artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos
        (N := N) hNpos
  simpa [γ] using
    F.artinHasseThetaTruncProductAtTo_sub_linearTeichSum_mem_Q_sq_of_one_le
      hγ hγπ hN y

/-- Quotient form of the first-order product comparison for the Dwork
approximation parameter. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_linearTeichSum_mod_Q_sq
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ 2)
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y) =
      Ideal.Quotient.mk (F.Q ^ 2)
        (1 + F.π *
          ∑ i : Fin F.concrete.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) :=
  F.quotient_mk_Q_sq_eq_of_sub_mem
    (F.artinHasseThetaTruncProductAtTo_approx_sub_linearTeichSum_mem_Q_sq_of_one_le
      hN y)

/-- The approximating Artin-Hasse product and the trace-form root have the
same image modulo `Q^2`. -/
theorem artinHasseThetaTruncProductAtTo_approx_sub_one_add_pi_pow_traceNatCast_mem_Q_sq
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y -
        (1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val ∈
      F.Q ^ 2 := by
  let linear : 𝓞 R' :=
    1 + F.π *
      ∑ i : Fin F.concrete.f,
        (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hprod :
      F.artinHasseThetaTruncProductAtTo
            (F.concrete.artinHasseDworkParameterApproxTo N) N y -
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
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y) =
      Ideal.Quotient.mk (F.Q ^ 2)
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) :=
  F.quotient_mk_Q_sq_eq_of_sub_mem
    (F.artinHasseThetaTruncProductAtTo_approx_sub_one_add_pi_pow_traceNatCast_mem_Q_sq
      hN y)

/-- Principal-unit coordinate for the inverse of the trace-form target root. -/
def traceRootInverseCoord (y : kˣ) : 𝓞 R' :=
  finiteLogPowCoord
    (ℓ - (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) F.π

theorem traceRootInverseCoord_mem_Q (y : kˣ) :
    F.traceRootInverseCoord y ∈ F.Q :=
  F.finiteLogPowCoord_mem_Q F.π_mem_Q _

/-- The trace-root coordinate and `traceRootInverseCoord` multiply to the
trivial principal-unit coordinate. -/
theorem finiteLogProductCoord_one_add_pi_pow_traceNatCast_sub_one_traceRootInverseCoord_eq_zero
    (y : kˣ) :
    finiteLogProductCoord
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.traceRootInverseCoord y) =
      0 := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  have htlt : t < ℓ := by
    simpa [t] using
      ZMod.val_lt (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k)))
  have hsum : t + (ℓ - t) = ℓ := Nat.add_sub_of_le (Nat.le_of_lt htlt)
  have hpow_ell : (1 + F.π) ^ ℓ = (1 : 𝓞 R') := by
    have hzeta : (1 : 𝓞 R') + F.π = F.zeta_ell_int := by
      rw [F.hπ]
      ring
    rw [hzeta]
    exact F.concrete.zeta_ell_int_isPrimitiveRoot.pow_eq_one
  have hprod :
      (1 + F.π) ^ t * (1 + F.π) ^ (ℓ - t) = (1 : 𝓞 R') := by
    rw [← pow_add, hsum, hpow_ell]
  calc
    finiteLogProductCoord
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.traceRootInverseCoord y)
        =
      (1 + F.π) ^ t * (1 + F.π) ^ (ℓ - t) - 1 := by
        simp [traceRootInverseCoord, finiteLogPowCoord, finiteLogProductCoord, t]
        ring
    _ = 0 := by
        rw [hprod]
        ring

/-- The integral inverse coordinate represents the inverse of the trace-form
target root. -/
theorem one_add_pi_pow_traceNatCast_mul_one_add_traceRootInverseCoord_eq_one
    (y : kˣ) :
    (1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val *
        (1 + F.traceRootInverseCoord y) =
      1 := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hcoord :
      finiteLogProductCoord ((1 + F.π) ^ t - 1) (F.traceRootInverseCoord y) = 0 := by
    simpa [t] using
      F.finiteLogProductCoord_one_add_pi_pow_traceNatCast_sub_one_traceRootInverseCoord_eq_zero
        y
  have hcoord_eq :
      finiteLogProductCoord ((1 + F.π) ^ t - 1) (F.traceRootInverseCoord y) =
        (1 + F.π) ^ t * (1 + F.traceRootInverseCoord y) - 1 := by
    unfold finiteLogProductCoord
    ring
  rw [hcoord_eq] at hcoord
  simpa [t] using sub_eq_zero.mp hcoord

/-- For positive precision, the normalized Dwork-product/root ratio coordinate
starts in `Q^2`, by the first-order product/root comparison. -/
theorem dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_sq_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y *
        (1 + F.traceRootInverseCoord y) - 1 ∈
      F.Q ^ 2 := by
  let P : 𝓞 R' :=
    F.artinHasseThetaTruncProductAtTo
      (F.concrete.artinHasseDworkParameterApproxTo N) N y
  let R : 𝓞 R' :=
    (1 + F.π) ^
      (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let invCoord : 𝓞 R' := F.traceRootInverseCoord y
  have hPR : P - R ∈ F.Q ^ 2 := by
    simpa [P, R] using
      F.artinHasseThetaTruncProductAtTo_approx_sub_one_add_pi_pow_traceNatCast_mem_Q_sq
        hN y
  have hRinv : R * (1 + invCoord) = 1 := by
    simpa [R, invCoord] using
      F.one_add_pi_pow_traceNatCast_mul_one_add_traceRootInverseCoord_eq_one y
  have heq : P * (1 + invCoord) - 1 = (P - R) * (1 + invCoord) := by
    calc
      P * (1 + invCoord) - 1 = P * (1 + invCoord) - R * (1 + invCoord) := by
        rw [hRinv]
      _ = (P - R) * (1 + invCoord) := by
        ring
  rw [heq]
  exact Ideal.mul_mem_right (1 + invCoord) (F.Q ^ 2) hPR

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
