module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.TraceCarry.Part1

/-!
# Trace-carry correction iteration for the finite Dwork telescope.

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

/-- Successor formula for the accumulated product-side correction: one more
Dwork step contributes the ordinary-exponential correction at the
Teichmüller Frobenius trace sum. -/
theorem artinHasseExpFrobeniusProductIterCorrection_succ_eq
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    F.artinHasseExpFrobeniusProductIterCorrection N y ε (m + 1) =
      (F.artinHasseExpFrobeniusProductIterCorrection N y ε m) ^ ℓ *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) *
            ∑ i : Fin F.toConcreteStickelbergerSetup.f,
              zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  have hεm : (ε ^ (ℓ ^ m)) ^ (N + 1) = 0 :=
    F.parameter_pow_iterate_pow_succ_eq_zero N m ε hε
  have hcollapse_shift :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ ((i : ℕ) + m)))) =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) *
            ∑ i : Fin F.toConcreteStickelbergerSetup.f,
              zbar ^ (ℓ ^ ((i : ℕ) + m))) := by
    have hprod :=
      rescale_exp_trunc_eval₂_finset_prod_eq_sum
        (r := ℓ)
        (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        (N := N)
        (δ := ε ^ (ℓ ^ m))
        hεm
        (s := (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
        (u := fun i : Fin F.toConcreteStickelbergerSetup.f =>
          zbar ^ (ℓ ^ ((i : ℕ) + m)))
    simpa [A, Rps, zbar] using hprod
  have hshift :
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ ((i : ℕ) + m))) =
        ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ (i : ℕ)) := by
    simpa [A, zbar] using F.teichFrobeniusSum_shift_iterate_eq N m y
  calc
    F.artinHasseExpFrobeniusProductIterCorrection N y ε (m + 1)
        =
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (S0.artinHasseExpIterCorrection N
                (ε * zbar ^ (ℓ ^ (i : ℕ))) m) ^ ℓ *
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m)) := by
          rfl
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (S0.artinHasseExpIterCorrection N
              (ε * zbar ^ (ℓ ^ (i : ℕ))) m) ^ ℓ) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m)) := by
          rw [Finset.prod_mul_distrib]
    _ =
          (F.artinHasseExpFrobeniusProductIterCorrection N y ε m) ^ ℓ *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ ((i : ℕ) + m))) := by
          congr 1
          · rw [Finset.prod_pow]
            rfl
          · refine Finset.prod_congr rfl ?_
            intro i _hi
            have hpow :
                (zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m) =
                  zbar ^ (ℓ ^ ((i : ℕ) + m)) := by
              have hpow_im : ℓ ^ (i : ℕ) * ℓ ^ m = ℓ ^ ((i : ℕ) + m) := by
                rw [pow_add]
              exact (pow_mul zbar (ℓ ^ (i : ℕ)) (ℓ ^ m)).symm.trans
                (congrArg (fun n : ℕ => zbar ^ n) hpow_im)
            rw [mul_pow, hpow]
    _ =
          (F.artinHasseExpFrobeniusProductIterCorrection N y ε m) ^ ℓ *
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) *
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ ((i : ℕ) + m))) := by
          rw [hcollapse_shift]
    _ =
          (F.artinHasseExpFrobeniusProductIterCorrection N y ε m) ^ ℓ *
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) *
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hshift]

/-- Successor formula for the accumulated base-side correction. -/
theorem artinHasseExpBaseIterCorrectionTrace_succ_eq
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε (m + 1)) ^ t =
      ((F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t) ^ ℓ *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) * (t : A)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hεm : (ε ^ (ℓ ^ m)) ^ (N + 1) = 0 :=
    F.parameter_pow_iterate_pow_succ_eq_zero N m ε hε
  have hcorr :=
    F.artinHasseExp_trace_nat_correction_eq_base_correction_pow_of_parameter
      N y (ε ^ (ℓ ^ m)) hεm
  calc
    (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε (m + 1)) ^ t
        =
          ((F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ ℓ *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t := by
          rfl
    _ =
          ((F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ ℓ) ^ t *
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t := by
          rw [mul_pow]
    _ =
          ((F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t) ^ ℓ *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m) * (t : A)) := by
          rw [← hcorr]
          ring

/-- Closed product form for the accumulated product-side correction in the
finite Dwork telescope. -/
theorem artinHasseExpFrobeniusProductIterCorrection_eq_prod
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    F.artinHasseExpFrobeniusProductIterCorrection N y ε m =
      ∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            ∑ i : Fin F.toConcreteStickelbergerSetup.f,
              zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let a : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) *
        ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ (i : ℕ)))
  change F.artinHasseExpFrobeniusProductIterCorrection N y ε m =
    ∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))
  induction m with
  | zero =>
      simp [artinHasseExpFrobeniusProductIterCorrection,
        ConcreteStickelbergerSetup.artinHasseExpIterCorrection]
  | succ m ih =>
      have hsucc :=
        F.artinHasseExpFrobeniusProductIterCorrection_succ_eq N m y ε hε
      have hpowprod :
          (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))) ^ ℓ =
            ∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - j)) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl ?_
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hexp : ℓ ^ (m - 1 - j) * ℓ = ℓ ^ (m - j) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [← pow_mul, hexp]
      calc
        F.artinHasseExpFrobeniusProductIterCorrection N y ε (m + 1)
            =
              (F.artinHasseExpFrobeniusProductIterCorrection N y ε m) ^ ℓ *
                a m := by
              simpa [A, Rps, zbar, a] using hsucc
        _ =
              (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))) ^ ℓ * a m := by
              rw [ih]
        _ =
              (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - j))) * a m := by
              rw [hpowprod]
        _ =
              ∏ j ∈ Finset.range (m + 1), a j ^ (ℓ ^ (m - j)) := by
              rw [Finset.prod_range_succ]
              simp

/-- Closed product form for the accumulated base-side correction in the
finite Dwork telescope. -/
theorem artinHasseExpBaseIterCorrectionTrace_eq_prod
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t =
      ∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) * (t : A))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let a : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) * (t : A))
  change (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t =
    ∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))
  induction m with
  | zero =>
      simp [ConcreteStickelbergerSetup.artinHasseExpIterCorrection]
  | succ m ih =>
      have hsucc :=
        F.artinHasseExpBaseIterCorrectionTrace_succ_eq N m y ε hε
      have hpowprod :
          (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))) ^ ℓ =
            ∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - j)) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl ?_
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hexp : ℓ ^ (m - 1 - j) * ℓ = ℓ ^ (m - j) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [← pow_mul, hexp]
      calc
        (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε (m + 1)) ^ t
            =
              ((F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t) ^ ℓ *
                a m := by
              simpa [A, Rps, t, a] using hsucc
        _ =
              (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))) ^ ℓ * a m := by
              rw [ih]
        _ =
              (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - j))) * a m := by
              rw [hpowprod]
        _ =
              ∏ j ∈ Finset.range (m + 1), a j ^ (ℓ ^ (m - j)) := by
              rw [Finset.prod_range_succ]
              simp

/-- Closed product comparison for the accumulated correction factors.  At
each Frobenius iterate this is just the additive law for the ordinary
Artin-Hasse correction series, applied to
`sum_i zbar^(ℓ^i)` and the complementary trace-carry term. -/
theorem artinHasseExp_correctionProducts_mul_traceCarryProducts_eq_baseProducts
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            ∑ i : Fin F.toConcreteStickelbergerSetup.f,
              zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m - 1 - j))) *
      (∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))))) ^ (ℓ ^ (m - 1 - j))) =
      ∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) * (t : A))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let s : A :=
    ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))
  let a : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) * s)
  let b : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) * ((t : A) - s))
  let c : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) * (t : A))
  change (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))) *
      (∏ j ∈ Finset.range m, b j ^ (ℓ ^ (m - 1 - j))) =
    ∏ j ∈ Finset.range m, c j ^ (ℓ ^ (m - 1 - j))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j _hj
  have hεj : (ε ^ (ℓ ^ j)) ^ (N + 1) = 0 :=
    F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε
  have hstep : a j * b j = c j := by
    simpa [A, Rps, zbar, t, s, a, b, c] using
      (rescale_exp_trunc_eval₂_mul_sub
        (r := ℓ)
        (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        (N := N)
        (δ := ε ^ (ℓ ^ j))
        (x := s)
        (y := (t : A))
        hεj)
  rw [← mul_pow, hstep]

/-- The accumulated product-side correction times the accumulated trace-carry
correction equals the accumulated base-side correction. This is the exact
finite correction comparison left by the telescope. -/
theorem artinHasseExp_iterCorrection_mul_traceCarryIterCorrection_eq_base
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
        F.artinHasseExpTraceCarryIterCorrection N y ε m =
      (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val := by
  classical
  induction m with
  | zero =>
      simp [artinHasseExpFrobeniusProductIterCorrection,
        artinHasseExpTraceCarryIterCorrection,
        ConcreteStickelbergerSetup.artinHasseExpIterCorrection]
  | succ m ih =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Rps : PowerSeries A :=
        (rescale_exp_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let zbar : A :=
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
      let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
      have hprod :=
        F.artinHasseExpFrobeniusProductIterCorrection_succ_eq N m y ε hε
      have hbase :=
        F.artinHasseExpBaseIterCorrectionTrace_succ_eq N m y ε hε
      have hεm : (ε ^ (ℓ ^ m)) ^ (N + 1) = 0 :=
        F.parameter_pow_iterate_pow_succ_eq_zero N m ε hε
      have hcarry :=
        F.artinHasseExp_trace_sum_correction_mul_trace_carry_eq_trace_nat_correction_of_parameter
          N y (ε ^ (ℓ ^ m)) hεm
      calc
        F.artinHasseExpFrobeniusProductIterCorrection N y ε (m + 1) *
            F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1)
            =
              ((F.artinHasseExpFrobeniusProductIterCorrection N y ε m) ^ ℓ *
                (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ m) *
                    ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                      zbar ^ (ℓ ^ (i : ℕ)))) *
              ((F.artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ *
                (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ m) *
                    ((t : A) -
                      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                        zbar ^ (ℓ ^ (i : ℕ))))) := by
              rw [hprod]
              rfl
        _ =
              ((F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
                F.artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ) *
                ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ m) *
                    ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                      zbar ^ (ℓ ^ (i : ℕ))) *
                (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ m) *
                    ((t : A) -
                      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                        zbar ^ (ℓ ^ (i : ℕ))))) := by
              rw [mul_pow]
              ring
        _ =
              (((F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^
                t) ^ ℓ) *
                (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                  (ε ^ (ℓ ^ m) * (t : A)) := by
              rw [ih]
              rw [hcarry]
        _ =
              (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε (m + 1)) ^
                t := by
              rw [hbase]

/-- Finite `m`-step comparison before taking the zero boundary.  The
accumulated trace carry converts the powered product/base comparison at
`ε` into the product/base comparison at the remaining parameter
`ε^(ℓ^m)`. -/
theorem artinHasseExp_product_pow_prime_iterate_mul_traceCarry_mul_base_iterate_eq
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        F.artinHasseExpTraceCarryIterCorrection N y ε m *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m))) ^ t =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
          (ℓ ^ m) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hprod :=
    F.artinHasseExp_frobenius_product_pow_prime_iterate_eq_iterCorrection_mul
      N m y ε hε
  have hbase :=
    F.artinHasseExp_base_trace_pow_prime_iterate_eq_iterCorrection_mul
      N m y ε hε
  have hcmp :=
    F.artinHasseExp_iterCorrection_mul_traceCarryIterCorrection_eq_base
      N m y ε hε
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        F.artinHasseExpTraceCarryIterCorrection N y ε m *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m))) ^ t
        =
          (F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ)))) *
            F.artinHasseExpTraceCarryIterCorrection N y ε m *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t := by
          rw [hprod]
    _ =
          (F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
              F.artinHasseExpTraceCarryIterCorrection N y ε m) *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
          ring
    _ =
          (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hcmp]
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
              (ℓ ^ m) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hbase]

/-- Product-form adjusted Dwork telescope with the trace-carry correction
expanded as the Teichmüller-coordinate product.  This is the standalone
`P/C/B` telescope needed before relating back to current-root products. -/
theorem artinHasseExp_adjustedProduct_mul_traceCarryTeichProduct_mul_base_eq
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    ((F.traceCarry y).coeff r))))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m))) ^ t =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
          (ℓ ^ m) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hcmp :=
    F.artinHasseExp_product_pow_prime_iterate_mul_traceCarry_mul_base_iterate_eq
      N m y ε hε
  have hcorr :=
    F.traceCarryIterCorrection_eq_teichmuller_series_product_powers_traceCarry
      N m y ε hε
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    ((F.traceCarry y).coeff r))))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m))) ^ t =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
            F.artinHasseExpTraceCarryIterCorrection N y ε m *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t := by
          rw [← hcorr]
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
              (ℓ ^ m) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
          simpa [A, Eps, zbar, t] using hcmp

private theorem prod_range_pow_prime_pred_sub_eq_sub
    {A : Type*} [CommMonoid A] (q m : ℕ) (C : ℕ → A) :
    (∏ j ∈ Finset.range m, C j ^ (q ^ (m - 1 - j))) ^ q =
      ∏ j ∈ Finset.range m, C j ^ (q ^ (m - j)) := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [← pow_mul]
  congr 1
  have hjlt : j < m := Finset.mem_range.mp hj
  have hsub : m - j = m - 1 - j + 1 := by
    omega
  rw [hsub, pow_succ]

/-- Zero-boundary powered comparison between the Frobenius product and the
base value, with the accumulated trace-carry correction explicitly present. -/
theorem artinHasseExp_product_pow_prime_iterate_mul_traceCarry_eq_base_pow_prime_iterate
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        F.artinHasseExpTraceCarryIterCorrection N y ε m =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
        (ℓ ^ m) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hprod :=
    F.artinHasseExp_frobenius_product_pow_prime_iterate_eq_iterCorrection_of_zero_iterate
      N m y ε hε hzero
  have hbase :=
    F.artinHasseExp_base_trace_pow_prime_iterate_eq_iterCorrection_of_zero_iterate
      N m y ε hε hzero
  have hcmp :=
    F.artinHasseExp_iterCorrection_mul_traceCarryIterCorrection_eq_base
      N m y ε hε
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) *
        F.artinHasseExpTraceCarryIterCorrection N y ε m
        =
          F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
            F.artinHasseExpTraceCarryIterCorrection N y ε m := by
          rw [hprod]
    _ =
          (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t := by
          rw [hcmp]
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
            (ℓ ^ m) := by
          rw [hbase]

/-- Zero-boundary `ℓ`-shifted form of the adjusted Dwork telescope, with the
trace-carry correction product displayed at the triangular powers needed for
the current-root endpoint. -/
theorem artinHasseExp_adjustedProduct_succ_mul_traceCarryTeichProduct_eq_base
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ (m + 1)) *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    ((F.traceCarry y).coeff r))))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - j))) =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^
        (ℓ ^ (m + 1)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let P : A :=
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε * zbar ^ (ℓ ^ (i : ℕ)))
  let C : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r)
              ((F.traceCarry y).coeff r))))) ^
        (ℓ ^ (r + 1))
  let B : A := ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t
  have hmain :
      P ^ (ℓ ^ m) * F.artinHasseExpTraceCarryIterCorrection N y ε m =
        B ^ (ℓ ^ m) := by
    simpa [A, Eps, zbar, t, P, B] using
      F.artinHasseExp_product_pow_prime_iterate_mul_traceCarry_eq_base_pow_prime_iterate
        N m y ε hε hzero
  have hcorr :
      F.artinHasseExpTraceCarryIterCorrection N y ε m =
        ∏ j ∈ Finset.range m, C j ^ (ℓ ^ (m - 1 - j)) := by
    simpa [A, θ, Rps, C] using
      F.traceCarryIterCorrection_eq_teichmuller_series_product_powers_traceCarry
        N m y ε hε
  have hcorr_pow :
      (F.artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ =
        ∏ j ∈ Finset.range m, C j ^ (ℓ ^ (m - j)) := by
    rw [hcorr]
    simpa [C] using
      (prod_range_pow_prime_pred_sub_eq_sub (A := A) ℓ m C)
  have hpow := congrArg (fun x : A => x ^ ℓ) hmain
  have hP :
      (P ^ (ℓ ^ m)) ^ ℓ = P ^ (ℓ ^ (m + 1)) := by
    rw [← pow_mul]
    have hexp : ℓ ^ (m + 1) = ℓ ^ m * ℓ := by
      rw [pow_succ]
    exact congrArg (fun n : ℕ => P ^ n) hexp.symm
  have hB :
      (B ^ (ℓ ^ m)) ^ ℓ = B ^ (ℓ ^ (m + 1)) := by
    rw [← pow_mul]
    have hexp : ℓ ^ (m + 1) = ℓ ^ m * ℓ := by
      rw [pow_succ]
    exact congrArg (fun n : ℕ => B ^ n) hexp.symm
  have htel :
      P ^ (ℓ ^ (m + 1)) *
          (∏ j ∈ Finset.range m, C j ^ (ℓ ^ (m - j))) =
        B ^ (ℓ ^ (m + 1)) := by
    calc
      P ^ (ℓ ^ (m + 1)) *
          (∏ j ∈ Finset.range m, C j ^ (ℓ ^ (m - j))) =
          (P ^ (ℓ ^ m) * F.artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ := by
            rw [mul_pow, hcorr_pow, hP]
      _ = (B ^ (ℓ ^ m)) ^ ℓ := hpow
      _ = B ^ (ℓ ^ (m + 1)) := hB
  simpa [A, θ, Eps, Rps, zbar, t, P, C, B] using htel

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
