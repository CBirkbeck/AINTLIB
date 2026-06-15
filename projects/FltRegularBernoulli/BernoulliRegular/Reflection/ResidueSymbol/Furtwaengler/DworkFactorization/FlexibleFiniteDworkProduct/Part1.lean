module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLogInjectivity
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleLowPrecision
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleTraceCarry

/-!
# Flexible finite logarithm of the Dwork product

This file assembles the conductor-flexible finite-log product law, the
one-variable Artin-Hasse logarithm identity, and Frobenius orbit-sum
invariance to prove the flexible Dwork membership theorem from the named
Artin-Hasse product identity.
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

omit [Algebra (ZMod ℓ) k] in
/-- The integral additive character is congruent to `1` modulo the selected
prime `Q`. -/
theorem psiInt_sub_one_mem_Q (x : k) : S.psiInt x - 1 ∈ S.Q := by
  change S.zeta_ell_int ^ S.psiExponent x - 1 ∈ S.Q
  exact zeta_pow_sub_one_mem_of_natCast_mem S.zeta_ell_int_isPrimitiveRoot
    S.hQ (S.psiExponent x)

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- Teichmuller lifts are fixed by the `ℓ ^ f` Frobenius power attached to the
flexible residue field cardinality. -/
theorem teichUnitFullVal_pow_ell_f_eq_self (x : kˣ) :
    F.teichUnitFullVal x ^ (ℓ ^ F.concrete.f) = F.teichUnitFullVal x := by
  let z : 𝓞 R' := F.teichUnitFullVal x
  have hcard_pos : 0 < Fintype.card k := Fintype.card_pos
  have hcard : z ^ Fintype.card k = z := by
    rw [show Fintype.card k = (Fintype.card k - 1) + 1 by omega]
    rw [pow_succ]
    have hunit := F.teichUnitFullVal_pow_card_sub_one x
    simpa [z] using congrArg (fun a : 𝓞 R' => a * z) hunit
  rw [← F.concrete.card_k]
  exact hcard

/-- The Teichmuller Frobenius trace sum is unchanged by any cyclic shift of
the Frobenius orbit. -/
theorem teichFrobeniusSum_shift_iterate_eq
    (N m : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∑ i : Fin F.concrete.f,
        zbar ^ (ℓ ^ ((i : ℕ) + m))) =
      ∑ i : Fin F.concrete.f,
        zbar ^ (ℓ ^ (i : ℕ)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let f : ℕ := F.concrete.f
  let g : ℕ → A := fun n => zbar ^ (ℓ ^ n)
  have hzperiod : zbar ^ (ℓ ^ f) = zbar := by
    simpa [z, zbar, f, map_pow] using
      congrArg (Ideal.Quotient.mk (F.Q ^ (N + 1)))
        (F.teichUnitFullVal_pow_ell_f_eq_self (F.traceScale * y))
  have hperiod : ∀ n : ℕ, g (n + f) = g n := by
    intro n
    have hpow_nf : ℓ ^ (n + f) = ℓ ^ f * ℓ ^ n := by
      rw [pow_add, Nat.mul_comm]
    calc
      g (n + f) = zbar ^ (ℓ ^ f * ℓ ^ n) := by
        simp [g, hpow_nf]
      _ = (zbar ^ (ℓ ^ f)) ^ (ℓ ^ n) := by
        rw [← pow_mul]
      _ = g n := by
        rw [hzperiod]
  have hshift := sum_range_shift_iterate_eq_of_period g f m hperiod
  have hleft :
      (∑ i : Fin f, zbar ^ (ℓ ^ ((i : ℕ) + m))) =
        ∑ i ∈ Finset.range f, g (i + m) :=
    (Finset.sum_range (f := fun i : ℕ => zbar ^ (ℓ ^ (i + m)))).symm
  have hright :
      (∑ i : Fin f, zbar ^ (ℓ ^ (i : ℕ))) =
        ∑ i ∈ Finset.range f, g i :=
    (Finset.sum_range (f := fun i : ℕ => zbar ^ (ℓ ^ i))).symm
  rw [show F.concrete.f = f from rfl]
  rw [hleft, hright]
  exact hshift

/-- Scalar-right form of `teichFrobeniusSum_shift_iterate_eq`, matching the
inner sums after factoring an Artin-Hasse logarithm term. -/
theorem teichFrobeniusSum_shift_iterate_mul_eq
    (N m : ℕ) (y : kˣ) (h : 𝓞 R' ⧸ F.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∑ i : Fin F.concrete.f,
        zbar ^ (ℓ ^ ((i : ℕ) + m)) * h) =
      (∑ i : Fin F.concrete.f,
        zbar ^ (ℓ ^ (i : ℕ))) * h := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  calc
    (∑ i : Fin F.concrete.f,
        zbar ^ (ℓ ^ ((i : ℕ) + m)) * h)
        =
          (∑ i : Fin F.concrete.f,
            zbar ^ (ℓ ^ ((i : ℕ) + m))) * h := by
          rw [Finset.sum_mul]
    _ =
          (∑ i : Fin F.concrete.f,
            zbar ^ (ℓ ^ (i : ℕ))) * h := by
          rw [F.teichFrobeniusSum_shift_iterate_eq N m y]

/-- Evaluating the parameterized Artin-Hasse theta truncation at `u` is the
same lifted polynomial as evaluating the finite Artin-Hasse exponential at
`γ * u`. -/
theorem dworkThetaTrunc_artinHasseAtTo_eq_finiteArtinHasseExp_mul
    (N : ℕ) (γ u : 𝓞 R') :
    dworkThetaTrunc (F.concrete.dworkCoeffArtinHasseAtTo γ N) N u =
      F.finiteArtinHasseExp N (γ * u) := by
  classical
  unfold finiteArtinHasseExp dworkThetaTrunc
  refine Finset.sum_congr rfl ?_
  intro n _hn
  cases n with
  | zero =>
      simp
  | succ m =>
      simp [ConductorFlexibleConcreteStickelbergerSetup.dworkCoeffArtinHasseAtTo,
        ConductorFlexibleConcreteStickelbergerSetup.dworkCoeffArtinHasseAtRawTo, mul_pow,
        mul_comm, mul_left_comm, mul_assoc]

/-- The precision-indexed theta product is the finite product of the
corresponding finite Artin-Hasse exponential evaluations. -/
theorem artinHasseThetaTruncProductAtTo_eq_prod_finiteArtinHasseExp
    (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo γ N y =
      ∏ i : Fin F.concrete.f,
        F.finiteArtinHasseExp N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) := by
  classical
  simp [artinHasseThetaTruncProductAtTo, dworkThetaFrobeniusProduct,
    F.dworkThetaTrunc_artinHasseAtTo_eq_finiteArtinHasseExp_mul]

/-- The coordinate of the precision-indexed theta product is the finite-log
finset-product coordinate of its Artin-Hasse factor coordinates. -/
theorem artinHasseThetaTruncProductAtTo_sub_one_eq_finsetProductCoord
    (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo γ N y - 1 =
      finiteLogFinsetProductCoord Finset.univ (fun i : Fin F.concrete.f =>
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
    F.artinHasseThetaTruncProductAtTo γ N y - 1 ∈ F.Q := by
  classical
  let x : Fin F.concrete.f → 𝓞 R' := fun i =>
    F.finiteArtinHasseExpCoord N
      (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
  have hx : ∀ i ∈ Finset.univ, x i ∈ F.Q := fun i _hi =>
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
    (∑ i : Fin F.concrete.f,
        F.finiteArtinHasseLog N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ)) =
      (∑ i : Fin F.concrete.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N γ hγ := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  have hterm :
      ∀ (i : Fin F.concrete.f) (r : ℕ),
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
    (∑ i : Fin F.concrete.f,
        F.finiteArtinHasseLog N (γ * z ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ))
        =
      ∑ i : Fin F.concrete.f,
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
        ∑ i : Fin F.concrete.f,
          zbar ^ (ℓ ^ ((i : ℕ) + r)) * F.finiteArtinHasseLogTerm N r γ hγ := by
        rw [Finset.sum_comm]
    _ =
      ∑ r ∈ Finset.range (N + 1),
        (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) *
          F.finiteArtinHasseLogTerm N r γ hγ := by
        refine Finset.sum_congr rfl ?_
        intro r _hr
        simpa [A, z, zbar] using
          F.teichFrobeniusSum_shift_iterate_mul_eq N r y
            (F.finiteArtinHasseLogTerm N r γ hγ)
    _ =
      (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) *
        F.finiteArtinHasseLog N γ hγ := by
        rw [finiteArtinHasseLog, Finset.mul_sum]

/-- The finite logarithm of a precision-indexed Dwork product is the sum of
the finite Artin-Hasse logarithms of its factors. -/
theorem finiteLog_artinHasseThetaTruncProductAtTo_sub_one_eq_sum_finiteArtinHasseLog
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ) :
    F.finiteLog N (F.artinHasseThetaTruncProductAtTo γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) =
      ∑ i : Fin F.concrete.f,
        F.finiteArtinHasseLog N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ) := by
  classical
  let x : Fin F.concrete.f → 𝓞 R' := fun i =>
    F.finiteArtinHasseExpCoord N
      (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
  have hx : ∀ i ∈ Finset.univ, x i ∈ F.Q := fun i _hi =>
    F.finiteArtinHasseExpCoord_mem_Q N
      (Ideal.mul_mem_right _ _ hγ)
  have hprod :
      F.artinHasseThetaTruncProductAtTo γ N y - 1 -
          finiteLogFinsetProductCoord Finset.univ x ∈ F.Q ^ (N + 1) := by
    rw [F.artinHasseThetaTruncProductAtTo_sub_one_eq_finsetProductCoord]
    simp [x]
  have hlog :=
    F.finiteLog_eq_sum_of_sub_finsetProductCoord_mem
      (N := N) (s := Finset.univ) (x := x)
      hx (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) hprod
  have hlog' :
      F.finiteLog N (F.artinHasseThetaTruncProductAtTo γ N y - 1)
          (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) =
        ∑ i : Fin F.concrete.f,
          F.finiteLog N
            (F.finiteArtinHasseExpCoord N
              (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
            (F.finiteArtinHasseExpCoord_mem_Q N (Ideal.mul_mem_right _ _ hγ)) := by
    rw [Finset.attach_eq_univ] at hlog
    have hsum :
        (∑ a : {i // i ∈ (Finset.univ : Finset (Fin F.concrete.f))},
            F.finiteLog N (x a.1) (hx a.1 a.2)) =
          ∑ i : Fin F.concrete.f,
            F.finiteLog N (x i) (hx i (Finset.mem_univ i)) :=
      (Finset.sum_subtype
          (s := (Finset.univ : Finset (Fin F.concrete.f)))
          (p := fun i : Fin F.concrete.f =>
            i ∈ (Finset.univ : Finset (Fin F.concrete.f)))
          (fun _ => Iff.rfl)
          (fun i => F.finiteLog N (x i) (hx i (Finset.mem_univ i)))).symm
    rw [hsum] at hlog
    simpa only [x, Finset.mem_univ, true_implies] using hlog
  calc
    F.finiteLog N (F.artinHasseThetaTruncProductAtTo γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y)
        =
      ∑ i : Fin F.concrete.f,
        F.finiteLog N
          (F.finiteArtinHasseExpCoord N
            (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
          (F.finiteArtinHasseExpCoord_mem_Q N (Ideal.mul_mem_right _ _ hγ)) := hlog'
    _ =
      ∑ i : Fin F.concrete.f,
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
    F.finiteLog N (F.artinHasseThetaTruncProductAtTo γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y) =
      (∑ i : Fin F.concrete.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N γ hγ := by
  calc
    F.finiteLog N (F.artinHasseThetaTruncProductAtTo γ N y - 1)
        (F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q hγ N y)
        =
      ∑ i : Fin F.concrete.f,
        F.finiteArtinHasseLog N
          (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
          (Ideal.mul_mem_right _ _ hγ) :=
        F.finiteLog_artinHasseThetaTruncProductAtTo_sub_one_eq_sum_finiteArtinHasseLog
          hγ N y
    _ =
      (∑ i : Fin F.concrete.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N γ hγ :=
        F.sum_finiteArtinHasseLog_teichFrobenius_eq_sum_mul N hγ y

/-- The corrected Dwork product coordinate lies in `Q`. -/
theorem artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q (N : ℕ) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo
        (F.concrete.artinHasseDworkParameterApproxTo N) N y - 1 ∈ F.Q :=
  F.artinHasseThetaTruncProductAtTo_sub_one_mem_Q
    (by
      exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N)
    N y

/-- The finite logarithm of the corrected Dwork product is the Frobenius orbit
sum times the inverse-parameter Artin-Hasse logarithm. -/
theorem finiteLog_artinHasseThetaTruncProductAtTo_approx_sub_one_eq_sum_mul
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y - 1)
        (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y) =
      (∑ i : Fin F.concrete.f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) *
        F.finiteArtinHasseLog N
          (F.concrete.artinHasseDworkParameterApproxTo N)
          (by
            exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N) :=
  F.finiteLog_artinHasseThetaTruncProductAtTo_sub_one_eq_sum_mul
    (by
      exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N)
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

/-- The finite logarithm of the trace-form root coordinate is the trace
natural-number lift times the inverse-parameter Artin-Hasse logarithm. -/
theorem finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) =
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (F.concrete.artinHasseDworkParameterApproxTo N)
          (by
            exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N) := by
  rw [F.finiteArtinHasseLog_inverseParameter_eq_finiteLog_pi' N]
  exact F.finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteLog_pi N y

/-- `ψ(a) - 1` is exactly the trace-form root coordinate, hence it has the
same finite logarithm. -/
theorem finiteLog_psiInt_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
    (N : ℕ) (y : kˣ) :
    F.finiteLog N (F.psiInt (y : k) - 1)
        (F.concrete.psiInt_sub_one_mem_Q (y : k)) =
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (F.concrete.artinHasseDworkParameterApproxTo N)
          (by
            exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N) := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) - 1 = (1 + F.π) ^ t - 1 := by
    have hψpow :
        F.psiInt (y : k) = F.zeta_ell_int ^ t := by
      simpa [t] using
        F.toConductorFlexibleTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace
          (y : k)
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
        (F.concrete.psiInt_sub_one_mem_Q (y : k))
        =
      F.finiteLog N ((1 + F.π) ^ t - 1)
        (by simpa [t] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) :=
        F.finiteLog_eq_of_sub_mem
          (F.concrete.psiInt_sub_one_mem_Q (y : k))
          (by simpa [t] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y)
          hsub
    _ =
      (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (F.concrete.artinHasseDworkParameterApproxTo N)
          (by
            exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N) := by
        simpa [t] using
          F.finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
            N y

/-- Scalar core: the finite logarithms of the Dwork product and the trace-form
target root agree. -/
theorem finiteLog_dworkProductApprox_sub_one_eq_finiteLog_traceRoot_sub_one
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y - 1)
        (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y) =
      F.finiteLog N
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val - 1)
        (F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y) := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let S : A := ∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let hN : A :=
    F.finiteArtinHasseLog N
      (F.concrete.artinHasseDworkParameterApproxTo N)
      (by
        exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N)
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
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y - 1)
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

/-- The finite logarithm of the trace-root inverse coordinate is the negative
of the target-root logarithm. -/
theorem finiteLog_traceRootInverseCoord_eq_neg_traceNatCast_mul_finiteArtinHasseLog
    (N : ℕ) (y : kˣ) :
    F.finiteLog N (F.traceRootInverseCoord y) (F.traceRootInverseCoord_mem_Q y) =
      -(((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (F.concrete.artinHasseDworkParameterApproxTo N)
          (by
            exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N) := by
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
          (F.concrete.artinHasseDworkParameterApproxTo N)
          (by
            exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N) := by
        simpa [t] using
          congrArg Neg.neg
            (F.finiteLog_one_add_pi_pow_traceNatCast_sub_one_eq_traceNatCast_mul_finiteArtinHasseLog
              N y)

/-- The finite logarithm of the normalized Dwork-product/root ratio is zero. -/
theorem finiteLog_artinHasseThetaTruncProductAtTo_approx_traceRootRatioCoord_eq_zero
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (finiteLogProductCoord
          (F.artinHasseThetaTruncProductAtTo
            (F.concrete.artinHasseDworkParameterApproxTo N) N y - 1)
          (F.traceRootInverseCoord y))
        (F.finiteLogProductCoord_mem_Q
          (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
          (F.traceRootInverseCoord_mem_Q y)) =
      0 := by
  classical
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let S : A := ∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let hN : A :=
    F.finiteArtinHasseLog N
      (F.concrete.artinHasseDworkParameterApproxTo N)
      (by
        exact F.concrete.artinHasseDworkParameterApproxTo_mem_Q N)
  have hcarry0 :
      (S - (t : A)) * hN = 0 := by
    simpa [A, zbar, S, t, hN] using
      F.teichFrobeniusSum_sub_traceNatCast_mul_finiteArtinHasseLog_eq_zero N y
  calc
    F.finiteLog N
        (finiteLogProductCoord
          (F.artinHasseThetaTruncProductAtTo
            (F.concrete.artinHasseDworkParameterApproxTo N) N y - 1)
          (F.traceRootInverseCoord y))
        (F.finiteLogProductCoord_mem_Q
          (F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q N y)
          (F.traceRootInverseCoord_mem_Q y))
        =
      F.finiteLog N
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y - 1)
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
    F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y *
        (1 + F.traceRootInverseCoord y) - 1 ∈ F.Q := by
  let P : 𝓞 R' :=
    F.artinHasseThetaTruncProductAtTo
      (F.concrete.artinHasseDworkParameterApproxTo N) N y
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

/-- Multiplicative ratio form: the finite logarithm of
`P_N(a) * ((1 + π)^Trace(a).val)⁻¹` is zero, with the inverse represented by
`traceRootInverseCoord`. -/
theorem finiteLog_dworkProductApprox_mul_traceRootInverse_sub_one_eq_zero
    (N : ℕ) (y : kˣ) :
    F.finiteLog N
        (F.artinHasseThetaTruncProductAtTo
            (F.concrete.artinHasseDworkParameterApproxTo N) N y *
          (1 + F.traceRootInverseCoord y) - 1)
        (F.dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q N y) =
      0 := by
  let P : 𝓞 R' :=
    F.artinHasseThetaTruncProductAtTo
      (F.concrete.artinHasseDworkParameterApproxTo N) N y
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

/-- For positive precision, finite-log injectivity upgrades the normalized
ratio coordinate from `Q^2` to `Q^(N+1)`. -/
theorem dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_pow_succ_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y *
        (1 + F.traceRootInverseCoord y) - 1 ∈
      F.Q ^ (N + 1) := by
  let ratio : 𝓞 R' :=
    F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y *
        (1 + F.traceRootInverseCoord y) - 1
  have hratio2 : ratio ∈ F.Q ^ 2 := by
    simpa [ratio] using
      F.dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_sq_of_one_le hN y
  have hlog :
      F.finiteLog N ratio (F.Q.pow_le_self (by decide) hratio2) = 0 := by
    simpa [ratio] using
      F.finiteLog_dworkProductApprox_mul_traceRootInverse_sub_one_eq_zero N y
  exact F.finiteLog_mem_Q_pow_succ_of_mem_Q_sq_of_eq_zero' hratio2 hlog

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
