module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteArtinHasseHomogeneous
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogInjectivity
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.LowPrecision
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.Basic

/-!
# Finite logarithm of the Dwork product

This file assembles the already-proved finite-log product law, the
one-variable Artin-Hasse logarithm identity, and Frobenius orbit-sum
invariance to compute the finite logarithm of the Dwork theta product.
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

/-- Evaluating the parameterized Artin-Hasse theta truncation at `u` is the
same lifted polynomial as evaluating the finite Artin-Hasse exponential at
`γ * u`. -/
theorem dworkThetaTrunc_artinHasseAtTo_eq_finiteArtinHasseExp_mul
    (N : ℕ) (γ u : 𝓞 R') :
    dworkThetaTrunc
        (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ N) N u =
      F.finiteArtinHasseExp N (γ * u) := by
  classical
  unfold finiteArtinHasseExp dworkThetaTrunc
  refine Finset.sum_congr rfl ?_
  intro n _hn
  cases n with
  | zero =>
      simp
  | succ m =>
      simp [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, mul_pow,
        mul_comm, mul_left_comm, mul_assoc]

/-- The precision-indexed theta product is the finite product of the
corresponding finite Artin-Hasse exponential evaluations. -/
theorem artinHasseThetaTruncProductAtTo_eq_prod_finiteArtinHasseExp
    (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F γ N y =
      ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        F.finiteArtinHasseExp N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) := by
  classical
  simp [artinHasseThetaTruncProductAtTo, dworkThetaFrobeniusProduct,
    F.dworkThetaTrunc_artinHasseAtTo_eq_finiteArtinHasseExp_mul]

/-- The coordinate of the precision-indexed theta product is the finite-log
finset-product coordinate of its Artin-Hasse factor coordinates. -/
theorem artinHasseThetaTruncProductAtTo_sub_one_eq_finsetProductCoord
    (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F γ N y - 1 =
      finiteLogFinsetProductCoord Finset.univ (fun i : Fin F.toConcreteStickelbergerSetup.f ↦
        F.finiteArtinHasseExpCoord N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  rw [F.artinHasseThetaTruncProductAtTo_eq_prod_finiteArtinHasseExp]
  unfold finiteLogFinsetProductCoord
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _hi
  rw [← F.finiteArtinHasseExpCoord_add_one]
  ring

/-- The theta-product coordinate lies in `Q` when the Artin-Hasse parameter
does. -/
theorem artinHasseThetaTruncProductAtTo_sub_one_mem_Q
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F γ N y - 1 ∈ F.Q := by
  classical
  let x : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i ↦
    F.finiteArtinHasseExpCoord N
      (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
  have hx : ∀ i ∈ Finset.univ, x i ∈ F.Q := fun i _hi ↦
    F.finiteArtinHasseExpCoord_mem_Q N
      (Ideal.mul_mem_right _ _ hγ)
  have hcoord : finiteLogFinsetProductCoord Finset.univ x ∈ F.Q :=
    F.finiteLogFinsetProductCoord_mem_Q hx
  simpa [x, F.artinHasseThetaTruncProductAtTo_sub_one_eq_finsetProductCoord γ N y]
    using hcoord

/-- The `r`-th Artin-Hasse logarithm term is homogeneous with respect to
right multiplication of the argument. -/
theorem finiteArtinHasseLogTerm_mul_right
    (N r : ℕ) {x y : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseLogTerm N r (x * y) (Ideal.mul_mem_right y F.Q hx) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (y ^ (ℓ ^ r)) *
        F.finiteArtinHasseLogTerm N r x hx := by
  classical
  have hz :
      x ^ (ℓ ^ r) ∈
        F.Q ^ ((ℓ ^ r).factorization ℓ * (ℓ - 1) +
          finiteArtinHasseLogTermOrder (ℓ := ℓ) r) := by
    simpa [pow_factorization_mul_pred_add_finiteArtinHasseLogTermOrder (ℓ := ℓ) r]
      using Ideal.pow_mem_pow hx (ℓ ^ r)
  have hyz :
      y ^ (ℓ ^ r) * x ^ (ℓ ^ r) ∈
        F.Q ^ ((ℓ ^ r).factorization ℓ * (ℓ - 1) +
          finiteArtinHasseLogTermOrder (ℓ := ℓ) r) :=
    Ideal.mul_mem_left _ _ hz
  have hpow : (x * y) ^ (ℓ ^ r) = y ^ (ℓ ^ r) * x ^ (ℓ ^ r) := by
    rw [mul_pow]
    ring
  have hmul :=
    F.finiteLogNatDivEval_mul_left
      (N := N) (n := ℓ ^ r) (s := finiteArtinHasseLogTermOrder (ℓ := ℓ) r)
      (pow_ne_zero r (Fact.out : Nat.Prime ℓ).ne_zero) (y ^ (ℓ ^ r)) hz hyz
  simpa [finiteArtinHasseLogTerm, hpow, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Summing Artin-Hasse logarithms over the Frobenius orbit factors out the
orbit sum. -/
theorem sum_finiteArtinHasseLog_teichFrobenius_eq_sum_mul
    (N : ℕ) {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (y : kˣ) :
    (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        F.finiteArtinHasseLog N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ)) =
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N γ hγ := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  have hterm :
      ∀ (i : Fin F.toConcreteStickelbergerSetup.f) (r : ℕ),
        F.finiteArtinHasseLogTerm N r (γ * z ^ (ℓ ^ (i : ℕ)))
            (Ideal.mul_mem_right _ _ hγ) =
          zbar ^ (ℓ ^ ((i : ℕ) + r)) * F.finiteArtinHasseLogTerm N r γ hγ := by
    intro i r
    have hmul := F.finiteArtinHasseLogTerm_mul_right N r (x := γ)
      (y := z ^ (ℓ ^ (i : ℕ))) hγ
    have hpow :
        Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((z ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ r)) =
          zbar ^ (ℓ ^ ((i : ℕ) + r)) := by
      calc
        Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((z ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ r))
            = zbar ^ (ℓ ^ (i : ℕ) * ℓ ^ r) := by
            simp [zbar, z, map_pow, pow_mul]
        _ = zbar ^ (ℓ ^ ((i : ℕ) + r)) := by
            congr 1
            rw [pow_add]
    rw [hmul, hpow]
  calc
    (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        F.finiteArtinHasseLog N (γ * z ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ))
        =
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        ∑ r ∈ Finset.range (N + 1),
          zbar ^ (ℓ ^ ((i : ℕ) + r)) * F.finiteArtinHasseLogTerm N r γ hγ := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [finiteArtinHasseLog]
        refine Finset.sum_congr rfl ?_
        intro r _hr
        exact hterm i r
    _ =
      ∑ r ∈ Finset.range (N + 1),
        ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ ((i : ℕ) + r)) * F.finiteArtinHasseLogTerm N r γ hγ := by
        rw [Finset.sum_comm]
    _ =
      ∑ r ∈ Finset.range (N + 1),
        (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) *
          F.finiteArtinHasseLogTerm N r γ hγ := by
        refine Finset.sum_congr rfl ?_
        intro r _hr
        simpa [A, z, zbar] using
          F.teichFrobeniusSum_shift_iterate_mul_eq N r y
            (F.finiteArtinHasseLogTerm N r γ hγ)
    _ =
      (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) *
        F.finiteArtinHasseLog N γ hγ := by
        rw [finiteArtinHasseLog, Finset.mul_sum]

/-- The finite logarithm of a precision-indexed Dwork product is the sum of
the finite Artin-Hasse logarithms of its factors. -/
theorem finiteLog_artinHasseThetaTruncProductAtTo_sub_one_eq_sum_finiteArtinHasseLog
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ) :
    F.finiteLog N (artinHasseThetaTruncProductAtTo F γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) =
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        F.finiteArtinHasseLog N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ) := by
  classical
  let x : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i ↦
    F.finiteArtinHasseExpCoord N
      (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
  have hx : ∀ i ∈ Finset.univ, x i ∈ F.Q := fun i _hi ↦
    F.finiteArtinHasseExpCoord_mem_Q N
      (Ideal.mul_mem_right _ _ hγ)
  have hprod :
      artinHasseThetaTruncProductAtTo F γ N y - 1 -
          finiteLogFinsetProductCoord Finset.univ x ∈ F.Q ^ (N + 1) := by
    rw [F.artinHasseThetaTruncProductAtTo_sub_one_eq_finsetProductCoord]
    simp [x]
  have hlog :=
    F.finiteLog_eq_sum_of_sub_finsetProductCoord_mem
      (N := N) (s := Finset.univ) (x := x)
      hx (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) hprod
  have hlog' :
      F.finiteLog N (artinHasseThetaTruncProductAtTo F γ N y - 1)
          (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) =
        ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          F.finiteLog N
            (F.finiteArtinHasseExpCoord N
              (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
            (F.finiteArtinHasseExpCoord_mem_Q N (Ideal.mul_mem_right _ _ hγ)) := by
    rw [Finset.attach_eq_univ] at hlog
    have hsum :
        (∑ a : {i // i ∈ (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f))},
            F.finiteLog N (x a.1) (hx a.1 a.2)) =
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            F.finiteLog N (x i) (hx i (Finset.mem_univ i)) :=
      (Finset.sum_subtype
          (s := (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
          (p := fun i : Fin F.toConcreteStickelbergerSetup.f ↦
            i ∈ (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
          (fun _ ↦ Iff.rfl)
          (fun i ↦ F.finiteLog N (x i) (hx i (Finset.mem_univ i)))).symm
    rw [hsum] at hlog
    simpa only [x, Finset.mem_univ, true_implies] using hlog
  calc
    F.finiteLog N (artinHasseThetaTruncProductAtTo F γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y)
        =
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        F.finiteLog N
          (F.finiteArtinHasseExpCoord N
            (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
          (F.finiteArtinHasseExpCoord_mem_Q N (Ideal.mul_mem_right _ _ hγ)) := hlog'
    _ =
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        F.finiteArtinHasseLog N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact F.finiteLog_finiteArtinHasseExpCoord_factor_eq_finiteArtinHasseLog
          N _ _

/-- Finite-log computation for the precision-indexed Dwork product. -/
theorem finiteLog_artinHasseThetaTruncProductAtTo_sub_one_eq_sum_mul
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ) :
    F.finiteLog N (artinHasseThetaTruncProductAtTo F γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) =
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N γ hγ := by
  calc
    F.finiteLog N (artinHasseThetaTruncProductAtTo F γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y)
        =
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        F.finiteArtinHasseLog N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ) :=
        F.finiteLog_artinHasseThetaTruncProductAtTo_sub_one_eq_sum_finiteArtinHasseLog
          hγ N y
    _ =
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N γ hγ :=
        F.sum_finiteArtinHasseLog_teichFrobenius_eq_sum_mul N hγ y

/-- The corrected Dwork product coordinate lies in `Q`. -/
theorem artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y - 1 ∈
      F.Q :=
  F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q
    (by
      simpa using
        artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)
    N y

/-- REF-Ke1: the finite logarithm of the corrected Dwork product is the
Frobenius orbit sum times the inverse-parameter Artin-Hasse logarithm. -/
theorem finiteLog_artinHasseThetaTruncProductAtTo_approx_sub_one_eq_sum_mul
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y - 1)
        (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y) =
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
          (by
            simpa using
              artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) :=
  F.finiteLog_artinHasseThetaTruncProductAtTo_sub_one_eq_sum_mul
    (by
      simpa using
        artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)
    N y

/-- The trace-form root coordinate `(1 + π)^Trace - 1` is a principal-unit
coordinate. -/
theorem one_add_pi_pow_traceNatCast_sub_one_mem_Q (y : kˣ) :
    (1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1 ∈
      F.Q := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  simpa [t, finiteLogPowCoord] using F.finiteLogPowCoord_mem_Q F.π_mem_Q t

/-- The finite logarithm of the trace-form root coordinate is the trace
natural-number lift times `Log_N(1 + π)`. -/
theorem finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteLog_pi
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) =
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteLog N F.π F.π_mem_Q := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  simpa [t, finiteLogPowCoord, nsmul_eq_mul] using
    F.finiteLog_powCoord N t F.π_mem_Q

/-- REF-Ke2: the finite logarithm of the trace-form root coordinate is the
trace natural-number lift times the inverse-parameter Artin-Hasse logarithm. -/
theorem finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) =
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
          (by
            simpa using
              artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) := by
  rw [F.finiteArtinHasseLog_inverseParameter_eq_finiteLog_pi' N]
  exact F.finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteLog_pi N y

/-- `ψ(a) - 1` is exactly the trace-form root coordinate, hence it has the
same finite logarithm.  This is the form suited for the final ratio. -/
theorem finiteLog_psiInt_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
    (N : ℕ) (y : kˣ) :
    F.finiteLog N (F.psiInt (y : k) - 1)
        (F.toConcreteStickelbergerSetup.psiInt_sub_one_mem_Q (y : k)) =
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
          (by
            simpa using
              artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) - 1 = (1 + F.π) ^ t - 1 := by
    have hψpow :
        F.psiInt (y : k) = F.zeta_ell_int ^ t := by
      simpa [t] using
        F.toTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace (y : k)
    have hzeta : F.zeta_ell_int = 1 + F.π := by
      rw [F.hπ]
      ring
    rw [hψpow, hzeta]
  have hsub :
      (F.psiInt (y : k) - 1) - ((1 + F.π) ^ t - 1) ∈ F.Q ^ (N + 1) := by
    rw [hpsi]
    simp
  calc
    F.finiteLog N (F.psiInt (y : k) - 1)
        (F.toConcreteStickelbergerSetup.psiInt_sub_one_mem_Q (y : k))
        =
      F.finiteLog N ((1 + F.π) ^ t - 1)
        (by simpa [t] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) :=
        F.finiteLog_eq_of_sub_mem
          (F.toConcreteStickelbergerSetup.psiInt_sub_one_mem_Q (y : k))
          (by simpa [t] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y)
          hsub
    _ =
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
          (by
            simpa using
              artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) := by
        simpa [t] using
          F.finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
            N y

/-- The trace-carry error in the Dwork-product finite logarithm is killed by
the `ℓ`-torsion relation on the inverse-parameter Artin-Hasse logarithm. -/
theorem teichFrobeniusSum_sub_traceNatCast_mul_finiteArtinHasseLog_eq_zero
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
        (t : A)) *
      F.finiteArtinHasseLog N
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
        (by
          simpa using
            artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) =
      0 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let hN : A :=
    F.finiteArtinHasseLog N
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
      (by
        simpa using
          artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)
  have hcarry :=
    F.teichFrobeniusSum_sub_traceNatCast_mul_eq_natCast_ell_mul_wittTheta_neg_traceCarry
      N y hN
  calc
    ((∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
        (t : A)) * hN =
      ((ℓ : A) * hN) * θ (-F.traceCarry y) := by
        simpa [A, θ, zbar, t, hN] using hcarry
    _ = 0 := by
        rw [F.finiteArtinHasseLog_inverseParameter_natCast_ell_mul_eq_zero' N]
        simp

/-- REF-Ke3 scalar core: the finite logarithms of the Dwork product and the
trace-form target root agree. -/
theorem finiteLog_dworkProductApprox_sub_one_eq_finiteLog_traceRoot_sub_one
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y - 1)
        (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y) =
      F.finiteLog N
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let S : A := ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let hN : A :=
    F.finiteArtinHasseLog N
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
      (by
        simpa using
          artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)
  have hcarry0 :
      (S - (t : A)) * hN = 0 := by
    simpa [A, zbar, S, t, hN] using
      F.teichFrobeniusSum_sub_traceNatCast_mul_finiteArtinHasseLog_eq_zero N y
  have hS : S * hN = (t : A) * hN := by
    have hsub : S * hN - (t : A) * hN = 0 := by
      calc
        S * hN - (t : A) * hN = (S - (t : A)) * hN := by
          ring
        _ = 0 := hcarry0
    exact sub_eq_zero.mp hsub
  calc
    F.finiteLog N
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y - 1)
        (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
        = S * hN := by
          simpa [A, zbar, S, hN] using
            F.finiteLog_artinHasseThetaTruncProductAtTo_approx_sub_one_eq_sum_mul
              N y
    _ = (t : A) * hN := hS
    _ =
      F.finiteLog N
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) := by
        simpa [A, t, hN] using
          (F.finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
            N y).symm

/-- Principal-unit coordinate for the inverse of the trace-form target root.
Since the target root is `(1 + π)^t` with `t < ℓ`, its inverse is represented
integrally by `(1 + π)^(ℓ - t)`. -/
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
    exact F.toConcreteStickelbergerSetup.zeta_ell_int_isPrimitiveRoot.pow_eq_one
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

/-- The integral inverse coordinate really represents the inverse of the
trace-form target root. -/
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
      F.finiteLogProductCoord_one_add_pi_pow_traceNatCast_sub_one_traceRootInverseCoord_eq_zero y
  have hcoord_eq :
      finiteLogProductCoord ((1 + F.π) ^ t - 1) (F.traceRootInverseCoord y) =
        (1 + F.π) ^ t * (1 + F.traceRootInverseCoord y) - 1 := by
    unfold finiteLogProductCoord
    ring
  rw [hcoord_eq] at hcoord
  simpa [t] using sub_eq_zero.mp hcoord

/-- The finite logarithm of the trace-root inverse coordinate is the negative
of the target-root logarithm. -/
theorem finiteLog_traceRootInverseCoord_eq_neg_traceNatCast_mul_finiteArtinHasseLog
    (N : ℕ) (y : kˣ) :
    F.finiteLog N (F.traceRootInverseCoord y) (F.traceRootInverseCoord_mem_Q y) =
      -(((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
          (by
            simpa using
              artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hneg :=
    F.finiteLog_eq_neg_of_productCoord_eq_zero
      (N := N)
      (x := (1 + F.π) ^ t - 1)
      (y := F.traceRootInverseCoord y)
      (by simpa [t] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y)
      (F.traceRootInverseCoord_mem_Q y)
      (by
        simpa [t] using
          F.finiteLogProductCoord_one_add_pi_pow_traceNatCast_sub_one_traceRootInverseCoord_eq_zero
            y)
  calc
    F.finiteLog N (F.traceRootInverseCoord y) (F.traceRootInverseCoord_mem_Q y)
        =
      -F.finiteLog N ((1 + F.π) ^ t - 1)
        (by simpa [t] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) := hneg
    _ =
      -(((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
          (by
            simpa using
              artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) := by
        simpa [t] using
          congrArg Neg.neg
            (F.finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
              N y)

/-- REF-Ke3: the finite logarithm of the normalized Dwork-product/root ratio
is zero.  The ratio coordinate is written as a product coordinate with the
explicit integral inverse `traceRootInverseCoord`. -/
theorem finiteLog_artinHasseThetaTruncProductAtTo_approx_traceRootRatioCoord_eq_zero
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (finiteLogProductCoord
          (artinHasseThetaTruncProductAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y - 1)
          (F.traceRootInverseCoord y))
        (F.finiteLogProductCoord_mem_Q
          (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
          (F.traceRootInverseCoord_mem_Q y)) =
      0 := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let S : A := ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let hN : A :=
    F.finiteArtinHasseLog N
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
      (by
        simpa using
          artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)
  have hcarry0 :
      (S - (t : A)) * hN = 0 := by
    simpa [A, zbar, S, t, hN] using
      F.teichFrobeniusSum_sub_traceNatCast_mul_finiteArtinHasseLog_eq_zero N y
  calc
    F.finiteLog N
        (finiteLogProductCoord
          (artinHasseThetaTruncProductAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y - 1)
          (F.traceRootInverseCoord y))
        (F.finiteLogProductCoord_mem_Q
          (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
          (F.traceRootInverseCoord_mem_Q y))
        =
      F.finiteLog N
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y - 1)
        (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y) +
        F.finiteLog N (F.traceRootInverseCoord y) (F.traceRootInverseCoord_mem_Q y) :=
        F.finiteLog_add_add_mul N
          (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
          (F.traceRootInverseCoord_mem_Q y)
    _ = S * hN + -((t : A) * hN) := by
        rw [F.finiteLog_artinHasseThetaTruncProductAtTo_approx_sub_one_eq_sum_mul]
        rw [F.finiteLog_traceRootInverseCoord_eq_neg_traceNatCast_mul_finiteArtinHasseLog]
        simp [A, zbar, S, t, hN]
    _ = 0 := by
        calc
          S * hN + -((t : A) * hN) = (S - (t : A)) * hN := by
            ring
          _ = 0 := hcarry0

/-- The multiplicative Dwork-product/root ratio coordinate lies in `Q`. -/
theorem dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q
    (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y *
        (1 + F.traceRootInverseCoord y) - 1 ∈
      F.Q := by
  let P : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y
  let invCoord : 𝓞 R' := F.traceRootInverseCoord y
  have hcoord :
      finiteLogProductCoord (P - 1) invCoord ∈ F.Q :=
    F.finiteLogProductCoord_mem_Q
      (by
        simpa [P] using F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
      (by
        simpa [invCoord] using F.traceRootInverseCoord_mem_Q y)
  have heq : P * (1 + invCoord) - 1 = finiteLogProductCoord (P - 1) invCoord := by
    unfold finiteLogProductCoord
    ring
  simpa [P, invCoord, heq] using hcoord

/-- REF-Ke3 in multiplicative ratio form: the finite logarithm of
`P_N(a) * ((1 + π)^Trace(a).val)⁻¹` is zero, with the inverse represented by
`traceRootInverseCoord`. -/
theorem finiteLog_dworkProductApprox_mul_traceRootInverse_sub_one_eq_zero
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (artinHasseThetaTruncProductAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y *
          (1 + F.traceRootInverseCoord y) - 1)
        (F.dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q N y) =
      0 := by
  let P : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y
  let invCoord : 𝓞 R' := F.traceRootInverseCoord y
  have heq : P * (1 + invCoord) - 1 = finiteLogProductCoord (P - 1) invCoord := by
    unfold finiteLogProductCoord
    ring
  calc
    F.finiteLog N (P * (1 + invCoord) - 1)
        (by
          simpa [P, invCoord] using
            F.dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q N y)
        =
      F.finiteLog N (finiteLogProductCoord (P - 1) invCoord)
        (F.finiteLogProductCoord_mem_Q
          (by
            simpa [P] using F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
          (by
            simpa [invCoord] using F.traceRootInverseCoord_mem_Q y)) :=
        F.finiteLog_eq_of_sub_mem _ _
          (by
            rw [heq]
            simp)
    _ = 0 := by
        simpa [P, invCoord] using
          F.finiteLog_artinHasseThetaTruncProductAtTo_approx_traceRootRatioCoord_eq_zero
            N y

/-- For positive precision, the normalized Dwork-product/root ratio coordinate
starts in `Q^2`, by the first-order product/root comparison. -/
theorem dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_sq_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y *
        (1 + F.traceRootInverseCoord y) - 1 ∈
      F.Q ^ 2 := by
  let P : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y
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

/-- For positive precision, finite-log injectivity upgrades the normalized
ratio coordinate from `Q^2` to `Q^(N+1)`. -/
theorem dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_pow_succ_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y *
        (1 + F.traceRootInverseCoord y) - 1 ∈
      F.Q ^ (N + 1) := by
  let ratio : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y *
        (1 + F.traceRootInverseCoord y) - 1
  have hratio2 : ratio ∈ F.Q ^ 2 := by
    simpa [ratio] using
      F.dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_sq_of_one_le hN y
  have hlog :
      F.finiteLog N ratio (F.Q.pow_le_self (by decide) hratio2) = 0 := by
    simpa [ratio] using
      F.finiteLog_dworkProductApprox_mul_traceRootInverse_sub_one_eq_zero N y
  exact F.finiteLog_mem_Q_pow_succ_of_mem_Q_sq_of_eq_zero' hratio2 hlog

/-- Positive-precision quotient identity for the corrected Dwork product:
`P_N(a)` equals the trace-form target root modulo `Q^(N+1)`. -/
theorem quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y) =
      Ideal.Quotient.mk (F.Q ^ (N + 1))
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) := by
  let P : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y
  let R : 𝓞 R' :=
    (1 + F.π) ^
      (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let invCoord : 𝓞 R' := F.traceRootInverseCoord y
  have hratio :
      P * (1 + invCoord) - 1 ∈ F.Q ^ (N + 1) := by
    simpa [P, invCoord] using
      F.dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_pow_succ_of_one_le hN y
  have hRinv : R * (1 + invCoord) = 1 := by
    simpa [R, invCoord] using
      F.one_add_pi_pow_traceNatCast_mul_one_add_traceRootInverseCoord_eq_one y
  have hdiff : P - R ∈ F.Q ^ (N + 1) := by
    have hmul : R * (P * (1 + invCoord) - 1) ∈ F.Q ^ (N + 1) :=
      (F.Q ^ (N + 1)).mul_mem_left R hratio
    have heq : P - R = R * (P * (1 + invCoord) - 1) := by
      calc
        P - R = P * (R * (1 + invCoord)) - R := by
          rw [hRinv]
          ring
        _ = R * (P * (1 + invCoord) - 1) := by
          ring
    simpa [heq] using hmul
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  simpa [P, R] using hdiff

/-- REF-Ke4: quotient identity for the corrected Dwork product at every
precision.  The `N = 0` case is the basic `Q`-congruence; positive precision
uses the REF-Ke3 finite-log-zero ratio and injectivity on `1 + Q^2`. -/
theorem quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast
    (N : ℕ) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y) =
      Ideal.Quotient.mk (F.Q ^ (N + 1))
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) := by
  by_cases hN : 1 ≤ N
  · exact F.quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast_of_one_le hN y
  · have hN0 : N = 0 := by omega
    subst N
    let P : 𝓞 R' :=
      artinHasseThetaTruncProductAtTo F
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup 0) 0 y
    let R : 𝓞 R' :=
      (1 + F.π) ^
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    have hP : P - 1 ∈ F.Q := by
      simpa [P] using F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q 0 y
    have hR : R - 1 ∈ F.Q := by
      simpa [R] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y
    have hdiffQ : P - R ∈ F.Q := by
      have hsub : (P - 1) - (R - 1) ∈ F.Q := F.Q.sub_mem hP hR
      have heq : P - R = (P - 1) - (R - 1) := by
        ring
      rw [heq]
      exact hsub
    have hdiff : P - R ∈ F.Q ^ (0 + 1) := by
      simpa using hdiffQ
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    simpa [P, R] using hdiff

/-- REF-Ke4 packaged in the named product-identity form used by the final
quotient-to-membership reduction. -/
theorem artinHasseApproxDworkOneAddPiProductIdentity_of_finiteLog
    (N : ℕ) (y : kˣ) :
    F.artinHasseApproxDworkOneAddPiProductIdentity N y := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let P : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y
  let R : 𝓞 R' := (1 + F.π) ^ t
  let target : A :=
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
  have hquot :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) P =
        Ideal.Quotient.mk (F.Q ^ (N + 1)) R := by
    simpa [P, R, t] using
      F.quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast N y
  have hprod :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) P = target := by
    simpa [P, target, Eps, Ips, πbar, A] using
      F.quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
        N y
  have hroot :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) R = (1 + πbar) ^ t := by
    simp [R, πbar, t]
  have hidentity : (1 + πbar) ^ t = target := by
    calc
      (1 + πbar) ^ t = Ideal.Quotient.mk (F.Q ^ (N + 1)) R := hroot.symm
      _ = Ideal.Quotient.mk (F.Q ^ (N + 1)) P := hquot.symm
      _ = target := hprod
  simpa [artinHasseApproxDworkOneAddPiProductIdentity, A, Eps, Ips, πbar, t,
    target] using hidentity

/-- REF-Ke5: the finite-log quotient identity closes the all-order Dwork
membership theorem for the Artin-Hasse theta approximation. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ
    (N : ℕ) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) :=
  F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_of_oneAddPiProductIdentity
    (F.artinHasseApproxDworkOneAddPiProductIdentity_of_finiteLog N y)

/-- REF-Kf1: exact full-Teich Dwork setup from the Artin-Hasse inverse
parameter, with no remaining Dwork splitting premise. -/
noncomputable def toFullTeichDworkSetupArtinHasseApproxToOfFiniteLog :
    FullTeichDworkSetup ℓ p k K R' :=
  F.toFullTeichDworkSetupArtinHasseApproxToOfTheta
    (fun N y ↦ F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ N y)

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
