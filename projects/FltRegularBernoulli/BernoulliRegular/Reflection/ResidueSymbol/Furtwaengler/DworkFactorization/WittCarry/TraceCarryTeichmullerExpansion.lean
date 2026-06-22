module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.WittCarry.TraceCarryDef

/-!
# Witt carry comparison for Dwork factorization

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

/-- Natural-representative form of `traceCarryCoeffZMod_spec`. -/
theorem traceCarryCoeffNat_spec
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (r : ℕ) :
    algebraMap (ZMod ℓ) k ((F.traceCarryCoeffNat y r : ℕ) : ZMod ℓ) =
      (F.traceCarry y).coeff r := by
  rw [F.traceCarryCoeffNat_cast_zmod y r]
  exact F.traceCarryCoeffZMod_spec y r

/-- Natural-representative form for the Frobenius-rooted coordinate used by the
telescoping product. -/
theorem traceCarryCoeffNat_frobeniusRoot_spec
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (r : ℕ) :
    algebraMap (ZMod ℓ) k ((F.traceCarryCoeffNat y r : ℕ) : ZMod ℓ) =
      ((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r) := by
  rw [F.traceCarryCoeffNat_cast_zmod y r]
  exact F.traceCarryCoeffZMod_frobeniusRoot_spec y r

/-- The Artin-Hasse factor at a Frobenius-rooted trace-carry coordinate can be
rewritten using the chosen `ZMod ℓ` coordinate. -/
theorem artinHasseWittTeichFactor_traceCarry_coord_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (r : ℕ) :
    F.artinHasseWittTeichFactor N ε
        (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r)) =
      F.artinHasseWittTeichFactor N ε
        (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r)) := by
  rw [← F.traceCarryCoeffZMod_frobeniusRoot_spec y r]

/-- Expanded factor version of
`artinHasseWittTeichFactor_traceCarry_coord_eq_zmod`, matching the factors that
occur inside the finite telescoping product. -/
theorem artinHasseExp_traceCarry_coord_factor_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (r : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r)))) =
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r)))) := by
  dsimp only
  rw [← F.traceCarryCoeffZMod_frobeniusRoot_spec y r]

/-- Product form of the prime-field coordinate reduction for trace-carry
Artin-Hasse factors.  The exponent family is arbitrary so the lemma can be
used by whichever finite truncation/telescoping shape is needed downstream. -/
theorem artinHasseExp_traceCarry_coord_product_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (e : ℕ → ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff r))))) ^ e r) =
      ∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^ e r := by
  classical
  dsimp only
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [F.artinHasseExp_traceCarry_coord_factor_eq_zmod N ε y r]

/-- Shifted-coordinate version of
`artinHasseExp_traceCarry_coord_factor_eq_zmod`.  This is the local rewrite
needed after peeling a coordinate tail: the inverse-Frobenius iterate index and
the trace-carry coordinate index may differ. -/
theorem artinHasseExp_traceCarry_shifted_coord_factor_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (n r s : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ n)
              ((F.traceCarry y).coeff (r + s))))) =
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y (r + s))))) := by
  dsimp only
  rw [← F.traceCarryCoeffZMod_frobeniusRoot_iterate_spec y n (r + s)]

/-- Product form of the shifted trace-carry coordinate rewrite over an initial
segment.  The coordinate index is `r + s`, while the inverse-Frobenius iterate
is the local tail index `r`. -/
theorem artinHasseExp_traceCarry_shifted_coord_product_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (e : ℕ → ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff (r + s)))))) ^ e r) =
      ∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y (r + s)))))) ^
          e r := by
  classical
  dsimp only
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [F.artinHasseExp_traceCarry_shifted_coord_factor_eq_zmod N ε y r r s]

/-- Range-indexed product form of the shifted trace-carry coordinate rewrite,
matching the nonzero-coordinate tail products created by one peel step. -/
theorem artinHasseExp_traceCarry_shifted_coord_range_product_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D s : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (e : ℕ → ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (∏ r ∈ Finset.range D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff (r + s)))))) ^ e r) =
      ∏ r ∈ Finset.range D,
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y (r + s)))))) ^
          e r := by
  classical
  dsimp only
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [F.artinHasseExp_traceCarry_shifted_coord_factor_eq_zmod N ε y r r s]

/-- Ordinary correction factor version of
`artinHasseExp_traceCarry_coord_factor_eq_zmod`.  This is the `Rps` analogue
needed before the carry telescope is converted to Artin-Hasse factors. -/
theorem rescaleExp_traceCarry_coord_factor_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (r : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r)))) := by
  dsimp only
  rw [← F.traceCarryCoeffZMod_frobeniusRoot_spec y r]

/-- Product form of the prime-field coordinate reduction for trace-carry
ordinary correction factors.  The exponent family is arbitrary, matching the
Artin-Hasse factor rewrite and the accumulated carry-product shapes used in
the telescope. -/
theorem rescaleExp_traceCarry_coord_product_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N D : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (e : ℕ → ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff r))))) ^ e r) =
      ∏ r ∈ Finset.Iic D,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^ e r := by
  classical
  dsimp only
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [F.rescaleExp_traceCarry_coord_factor_eq_zmod N ε y r]

/-- Non-existential form of the trace-carry equation in
`𝓞 R' / Q^(N+1)`, using the fixed Witt carry `traceCarry`. -/
theorem traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_traceCarry
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (t : A) -
        (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
      (ℓ : A) * θ (F.traceCarry y) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let a : ZMod ℓ := Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))
  let traceK : k := algebraMap (ZMod ℓ) k a
  let t : ℕ := a.val
  let W : WittVector ℓ k :=
    ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
      F.toConcreteStickelbergerSetup.f
      (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))
  let traceTeich : WittVector ℓ k := WittVector.teichmuller ℓ traceK
  have hTraceTeich :
      θ traceTeich =
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) := by
    simpa [θ, traceTeich, traceK] using F.wittThetaModQPow_teichmuller N traceK
  have hW :
      θ W =
        ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)) := by
    have h :=
      F.wittThetaModQPow_wittFrobeniusTrace_teichmuller_unit
        N F.toConcreteStickelbergerSetup.f (F.traceScale * y)
    simpa [θ, W, z, zbar, map_sum, map_pow] using h
  have hNatW :
      (((t : ℕ) : WittVector ℓ k) - traceTeich) =
        (ℓ : WittVector ℓ k) * F.traceNatCarry y := by
    simpa [t, a, traceTeich, traceK] using F.traceNatCarry_spec y
  have hTraceW :
      W - traceTeich =
        (ℓ : WittVector ℓ k) * F.traceFrobeniusCarry y := by
    simpa [W, traceTeich, traceK] using F.traceFrobeniusCarry_spec y
  have hNatTheta :
      (t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) =
        (ℓ : A) * θ (F.traceNatCarry y) := by
    calc
      (t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)
          = θ (((t : ℕ) : WittVector ℓ k)) - θ traceTeich := by
              rw [map_natCast, hTraceTeich]
      _ = θ ((((t : ℕ) : WittVector ℓ k)) - traceTeich) := by
              rw [map_sub]
      _ = θ ((ℓ : WittVector ℓ k) * F.traceNatCarry y) := by
              rw [hNatW]
      _ = (ℓ : A) * θ (F.traceNatCarry y) := by
              rw [map_mul, map_natCast]
  have hTraceTheta :
      (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
          Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) =
        (ℓ : A) * θ (F.traceFrobeniusCarry y) := by
    calc
      (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
          Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)
          = θ W - θ traceTeich := by
              rw [hW, hTraceTeich]
      _ = θ (W - traceTeich) := by
              rw [map_sub]
      _ = θ ((ℓ : WittVector ℓ k) * F.traceFrobeniusCarry y) := by
              rw [hTraceW]
      _ = (ℓ : A) * θ (F.traceFrobeniusCarry y) := by
              rw [map_mul, map_natCast]
  calc
    (t : A) -
        (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
        =
          ((t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)) -
            ((∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
              Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)) := by
          ring
    _ = (ℓ : A) * θ (F.traceNatCarry y) -
        (ℓ : A) * θ (F.traceFrobeniusCarry y) := by
          rw [hNatTheta, hTraceTheta]
    _ = (ℓ : A) * θ (F.traceCarry y) := by
          rw [traceCarry, map_sub]
          ring

/-- Sign-oriented form of the trace-carry equation: the Teichmüller
Frobenius trace sum minus the ordinary trace lift is an `ℓ`-multiple. -/
theorem teichFrobeniusSum_sub_traceNatCast_eq_natCast_ell_mul_wittTheta_neg_traceCarry
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
        (t : A) =
      (ℓ : A) * θ (-F.traceCarry y) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hsub :=
    F.traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_traceCarry
      N y
  calc
    (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
        (t : A)
        =
          -((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) := by
          ring
    _ = -((ℓ : A) * θ (F.traceCarry y)) := by
          rw [hsub]
    _ = (ℓ : A) * θ (-F.traceCarry y) := by
          rw [map_neg]
          ring

/-- Existential quotient form of trace-carry divisibility by the scalar `ℓ`. -/
theorem exists_teichFrobeniusSum_sub_traceNatCast_eq_natCast_ell_mul
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : A,
      (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
          (t : A) =
        (ℓ : A) * c := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  refine ⟨θ (-F.traceCarry y), ?_⟩
  exact
    F.teichFrobeniusSum_sub_traceNatCast_eq_natCast_ell_mul_wittTheta_neg_traceCarry
      N y

/-- Product form for the logarithmic trace-carry error.  If a downstream
logarithmic term `h` is killed by multiplication by `ℓ`, then the whole
trace-carry error is killed. -/
theorem teichFrobeniusSum_sub_traceNatCast_mul_eq_natCast_ell_mul_wittTheta_neg_traceCarry
    (N : ℕ) (y : kˣ) (h : 𝓞 R' ⧸ F.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
        (t : A)) * h =
      ((ℓ : A) * h) * θ (-F.traceCarry y) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  rw [F.teichFrobeniusSum_sub_traceNatCast_eq_natCast_ell_mul_wittTheta_neg_traceCarry
    N y]
  ring

/-- Quotient form of
`wittFrobeniusTrace_teichmuller_traceScale_mul_add_natCast_ell_mul_traceCarry`:
after applying the Fontaine-style Witt map, the Frobenius trace term plus the
`ℓ`-multiple carry term is the natural trace lift. -/
theorem wittThetaModQPow_wittFrobeniusTrace_add_natCast_ell_mul_traceCarry_eq_traceNatCast
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let W : WittVector ℓ k :=
      ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
        F.toConcreteStickelbergerSetup.f
        (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    θ W + (ℓ : A) * θ (F.traceCarry y) = (t : A) := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let W : WittVector ℓ k :=
    ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
      F.toConcreteStickelbergerSetup.f
      (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  calc
    θ W + (ℓ : A) * θ (F.traceCarry y)
        = θ (W + (ℓ : WittVector ℓ k) * F.traceCarry y) := by
            rw [map_add, map_mul, map_natCast]
    _ = θ (((t : ℕ) : WittVector ℓ k)) := by
            rw [F.wittFrobeniusTrace_teichmuller_traceScale_mul_add_natCast_ell_mul_traceCarry]
    _ = (t : A) := by
            rw [map_natCast]

/-- Concrete quotient form of the needed additive identity: the finite
Teichmüller Frobenius sum plus the `ℓ`-multiple trace-carry contribution is
the natural trace lift. -/
theorem teichFrobeniusSum_add_natCast_ell_mul_wittTheta_traceCarry_eq_traceNatCast
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) +
        (ℓ : A) * θ (F.traceCarry y) =
      (t : A) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hsub :=
    F.traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_traceCarry
      N y
  calc
    (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) +
        (ℓ : A) * θ (F.traceCarry y)
        =
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) +
            ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) := by
            rw [hsub]
    _ = (t : A) := by
            ring

/-- In the quotient `𝓞 R' / Q^(N+1)`, the difference between the ordinary
trace lift and the Teichmüller Frobenius trace sum is an `ℓ`-multiple coming
from a Witt-vector carry. -/
theorem exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        (ℓ : A) * θ c := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let a : ZMod ℓ := Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))
  let traceK : k := algebraMap (ZMod ℓ) k a
  let t : ℕ := a.val
  let W : WittVector ℓ k :=
    ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
      F.toConcreteStickelbergerSetup.f
      (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))
  let traceTeich : WittVector ℓ k := WittVector.teichmuller ℓ traceK
  obtain ⟨cNat, hcNat⟩ :=
    ConcreteStickelbergerSetup.natCast_zmod_val_sub_teichmuller_dvd_prime
      (ℓ := ℓ) (k := k) a
  obtain ⟨cTrace, hcTrace⟩ :=
    F.wittFrobeniusTrace_teichmuller_traceScale_mul_sub_teichmuller_trace_dvd_prime y
  have hTraceTeich :
      θ traceTeich =
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) := by
    simpa [θ, traceTeich, traceK] using F.wittThetaModQPow_teichmuller N traceK
  have hW :
      θ W =
        ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)) := by
    have h :=
      F.wittThetaModQPow_wittFrobeniusTrace_teichmuller_unit
        N F.toConcreteStickelbergerSetup.f (F.traceScale * y)
    simpa [θ, W, z, zbar, map_sum, map_pow] using h
  have hNatTheta :
      (t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) =
        (ℓ : A) * θ cNat := by
    calc
      (t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)
          = θ (((t : ℕ) : WittVector ℓ k)) - θ traceTeich := by
              rw [map_natCast, hTraceTeich]
      _ = θ ((((t : ℕ) : WittVector ℓ k)) - traceTeich) := by
              rw [map_sub]
      _ = θ ((ℓ : WittVector ℓ k) * cNat) := by
              rw [show (((t : ℕ) : WittVector ℓ k) - traceTeich) =
                ((a.val : ℕ) : WittVector ℓ k) -
                  WittVector.teichmuller ℓ (algebraMap (ZMod ℓ) k a) by
                  rfl, hcNat]
      _ = (ℓ : A) * θ cNat := by
              rw [map_mul, map_natCast]
  have hTraceTheta :
      (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
          Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) =
        (ℓ : A) * θ cTrace := by
    calc
      (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
          Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)
          = θ W - θ traceTeich := by
              rw [hW, hTraceTeich]
      _ = θ (W - traceTeich) := by
              rw [map_sub]
      _ = θ ((ℓ : WittVector ℓ k) * cTrace) := by
              rw [show W - traceTeich =
                ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
                    F.toConcreteStickelbergerSetup.f
                    (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k))) -
                  WittVector.teichmuller ℓ
                    (algebraMap (ZMod ℓ) k
                      (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k)))) by
                  rfl, hcTrace]
      _ = (ℓ : A) * θ cTrace := by
              rw [map_mul, map_natCast]
  refine ⟨cNat - cTrace, ?_⟩
  calc
    (t : A) -
        (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
        =
          ((t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)) -
            ((∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) -
              Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)) := by
          ring
    _ = (ℓ : A) * θ cNat - (ℓ : A) * θ cTrace := by
          rw [hNatTheta, hTraceTheta]
    _ = (ℓ : A) * θ (cNat - cTrace) := by
          rw [map_sub]
          ring

/-- The explicit trace carry can be written in finite Teichmüller-coordinate
form through the target precision. This is the concrete version of
`exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta`:
the remaining Witt carry is expanded by its Teichmüller series, and the
`ℓ^(N+1)` tail is killed in `𝓞 R' / Q^(N+1)`. -/
theorem exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_series
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        (ℓ : A) *
          ∑ j ∈ Finset.Iic N,
            (ℓ : A) ^ j *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta N y
  have hseries :
      θ c =
        ∑ j ∈ Finset.Iic N,
          (ℓ : A) ^ j *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))) := by
    simpa [A, θ] using
      F.toConcreteStickelbergerSetup.wittThetaModQPow_eq_sum_teichmuller_series N c
  refine ⟨c, ?_⟩
  calc
    (t : A) -
        (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
        = (ℓ : A) * θ c := hc
    _ =
        (ℓ : A) *
          ∑ j ∈ Finset.Iic N,
            (ℓ : A) ^ j *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))) := by
          rw [hseries]

/-- The ordinary correction factor at the trace carry is the finite product
of the ordinary correction factors attached to the Teichmüller coordinates
of the Witt carry. -/
theorem exists_traceCarry_correction_eq_teichmuller_series_product
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * ((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
        ∏ j ∈ Finset.Iic N,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ((ℓ : A) ^ (j + 1) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_series N y
  let u : ℕ → A := fun j =>
    (ℓ : A) ^ (j + 1) *
      θ (WittVector.teichmuller ℓ
        (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j)))
  have hsum :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        ∑ j ∈ Finset.Iic N, u j := by
    calc
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
          =
            (ℓ : A) *
              ∑ j ∈ Finset.Iic N,
                (ℓ : A) ^ j *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))) := hc
      _ =
            ∑ j ∈ Finset.Iic N, u j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              simp [u, pow_succ]
              ring
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hprod :=
    rescale_exp_trunc_eval₂_finset_prod_eq_sum
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := δ)
      hδ
      (s := Finset.Iic N)
      (u := u)
  refine ⟨c, ?_⟩
  rw [hsum]
  simpa [A, θ, Ips, Rps, πbar, δ, zbar, t, u] using hprod.symm

/-- Power form of `exists_traceCarry_correction_eq_teichmuller_series_product`:
each Teichmüller-coordinate correction in the carry product is an explicit
`ℓ^(j+1)`-st power. -/
theorem exists_traceCarry_correction_eq_teichmuller_series_product_powers
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * ((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
        ∏ j ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) ^
            (ℓ ^ (j + 1)) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceCarry_correction_eq_teichmuller_series_product N y
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  refine ⟨c, ?_⟩
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          ∏ j ∈ Finset.Iic N,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * ((ℓ : A) ^ (j + 1) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) := hc
    _ =
          ∏ j ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) ^
              (ℓ ^ (j + 1)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          simpa [A, θ, Ips, Rps, πbar, δ, zbar, t, mul_assoc, mul_left_comm,
            mul_comm] using
            (rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
              (r := ℓ)
              (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
              (N := N)
              (δ := δ)
              hδ
              (x := θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))
              (t := ℓ ^ (j + 1)))

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
