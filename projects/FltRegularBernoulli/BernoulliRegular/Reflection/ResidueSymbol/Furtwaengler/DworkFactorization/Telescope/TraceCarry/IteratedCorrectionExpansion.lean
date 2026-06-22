module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.Basic

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

/-- The finite correction accumulated by the trace-carry terms while
iterating the Dwork recursion. -/
noncomputable def artinHasseExpTraceCarryIterCorrection
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) :
    ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1)
  | 0 => 1
  | m + 1 =>
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let Rps : PowerSeries A :=
        (rescale_exp_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      let zbar : A :=
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
      let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
      (artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) *
            ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))))

/-- Closed product form for the accumulated trace-carry correction.  The
recursive carry is exactly the product of the one-step carry factors, with
the earlier factors raised by the later Frobenius powers. -/
theorem artinHasseExpTraceCarryIterCorrection_eq_prod
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    F.artinHasseExpTraceCarryIterCorrection N y ε m =
      ∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let a : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) *
        ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            zbar ^ (ℓ ^ (i : ℕ))))
  change F.artinHasseExpTraceCarryIterCorrection N y ε m =
    ∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))
  induction m with
  | zero =>
      simp [artinHasseExpTraceCarryIterCorrection]
  | succ m ih =>
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
        F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1)
            =
              (F.artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ * a m := by
              rfl
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

/-- Every nonzero stage of the accumulated trace-carry correction is an
`ℓ`-th power. The root is obtained by adjoining the one-step Witt-carry root
at the current iterated parameter to the previous accumulated carry. -/
theorem exists_traceCarryIterCorrection_succ_eq_pow
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    ∃ c : WittVector ℓ k,
      F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1) =
        (F.artinHasseExpTraceCarryIterCorrection N y ε m *
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) * θ c)) ^ ℓ := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hεm : (ε ^ (ℓ ^ m)) ^ (N + 1) = 0 :=
    F.parameter_pow_iterate_pow_succ_eq_zero N m ε hε
  obtain ⟨c, hc⟩ :=
    F.exists_traceCarry_correction_eq_pow_wittTheta_of_parameter
      N y (ε ^ (ℓ ^ m)) hεm
  have hc' :
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) *
            ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ)))) =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) * θ c)) ^ ℓ := by
    simpa [A, θ, Rps, zbar, t] using hc
  refine ⟨c, ?_⟩
  calc
    F.artinHasseExpTraceCarryIterCorrection N y ε (m + 1)
        =
          (F.artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m) *
                ((t : A) -
                  ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                    zbar ^ (ℓ ^ (i : ℕ)))) := by
          rfl
    _ =
          (F.artinHasseExpTraceCarryIterCorrection N y ε m) ^ ℓ *
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m) * θ c)) ^ ℓ := by
          rw [hc']
    _ =
          (F.artinHasseExpTraceCarryIterCorrection N y ε m *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m) * θ c)) ^ ℓ := by
          rw [mul_pow]

/-- Positive accumulated trace-carry corrections are `ℓ`-th powers in the
finite quotient. -/
theorem exists_traceCarryIterCorrection_eq_pow_of_pos
    (N m : ℕ) (hm : 0 < m) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    ∃ u : A, F.artinHasseExpTraceCarryIterCorrection N y ε m = u ^ ℓ := by
  classical
  cases m with
  | zero =>
      cases hm
  | succ m =>
      dsimp only
      let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
      let θ : WittVector ℓ k →+* A :=
        F.toConcreteStickelbergerSetup.wittThetaModQPow N
      let Rps : PowerSeries A :=
        (rescale_exp_isRIntegral ℓ).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      obtain ⟨c, hc⟩ :=
        F.exists_traceCarryIterCorrection_succ_eq_pow N m y ε hε
      refine ⟨F.artinHasseExpTraceCarryIterCorrection N y ε m *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) * θ c), ?_⟩
      simpa [A, θ, Rps] using hc

/-- Fully expanded finite Teichmüller-coordinate form of the accumulated
trace carry.  Each one-step carry is expanded by the Witt-vector carry
coordinates at the corresponding iterated parameter. -/
theorem exists_traceCarryIterCorrection_eq_teichmuller_series_product_powers
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    ∃ c : ℕ → WittVector ℓ k,
      F.artinHasseExpTraceCarryIterCorrection N y ε m =
        ∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((c j).coeff r))))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let stepRoot : ℕ → WittVector ℓ k := fun j =>
    Classical.choose
      (F.exists_traceCarry_correction_eq_teichmuller_series_product_powers_of_parameter
        N y (ε ^ (ℓ ^ j))
        (F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε))
  have hstep :
      ∀ j : ℕ,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                  zbar ^ (ℓ ^ (i : ℕ)))) =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    ((stepRoot j).coeff r))))) ^ (ℓ ^ (r + 1)) := by
    intro j
    have h :=
      Classical.choose_spec
        (F.exists_traceCarry_correction_eq_teichmuller_series_product_powers_of_parameter
          N y (ε ^ (ℓ ^ j))
          (F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε))
    simpa [A, θ, Rps, zbar, t, stepRoot] using h
  have hcarry :=
    F.artinHasseExpTraceCarryIterCorrection_eq_prod N m y ε
  refine ⟨stepRoot, ?_⟩
  calc
    F.artinHasseExpTraceCarryIterCorrection N y ε m
        =
          ∏ j ∈ Finset.range m,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                ((t : A) -
                  ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                    zbar ^ (ℓ ^ (i : ℕ))))) ^ (ℓ ^ (m - 1 - j)) := by
          simpa [A, Rps, zbar, t] using hcarry
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      ((stepRoot j).coeff r))))) ^ (ℓ ^ (r + 1))) ^
              (ℓ ^ (m - 1 - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          rw [hstep j]

/-- Fully expanded finite Teichmüller-coordinate form of the accumulated
trace carry, using the same Witt carry vector at every Dwork iterate.  This is
the form needed for the later coordinate-by-coordinate Artin-Hasse tail
telescope. -/
theorem exists_traceCarryIterCorrection_eq_teichmuller_series_product_powers_const
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    ∃ c : WittVector ℓ k,
      F.artinHasseExpTraceCarryIterCorrection N y ε m =
        ∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_series N y
  let coord : ℕ → A := fun r =>
    θ (WittVector.teichmuller ℓ
      (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)))
  let u : ℕ → A := fun r => (ℓ : A) ^ (r + 1) * coord r
  have hsum :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        ∑ r ∈ Finset.Iic N, u r := by
    calc
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
          =
            (ℓ : A) *
              ∑ r ∈ Finset.Iic N,
                (ℓ : A) ^ r * coord r := by
              simpa [A, θ, zbar, t, coord] using hc
      _ =
            ∑ r ∈ Finset.Iic N, u r := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro r _hr
              simp [u, pow_succ]
              ring
  have hstep :
      ∀ j : ℕ,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                  zbar ^ (ℓ ^ (i : ℕ)))) =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) * coord r)) ^ (ℓ ^ (r + 1)) := by
    intro j
    have hεj : (ε ^ (ℓ ^ j)) ^ (N + 1) = 0 :=
      F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε
    have hprod :=
      rescale_exp_trunc_eval₂_finset_prod_eq_sum
        (r := ℓ)
        (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        (N := N)
        (δ := ε ^ (ℓ ^ j))
        hεj
        (s := Finset.Iic N)
        (u := u)
    calc
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))))
          =
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) * ∑ r ∈ Finset.Iic N, u r) := by
            rw [hsum]
      _ =
            ∏ r ∈ Finset.Iic N,
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) * u r) := by
            simpa [A, Rps] using hprod.symm
      _ =
            ∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) * coord r)) ^ (ℓ ^ (r + 1)) := by
            refine Finset.prod_congr rfl ?_
            intro r _hr
            simpa [A, θ, Rps, zbar, t, coord, u, mul_assoc, mul_left_comm,
              mul_comm] using
              (rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
                (r := ℓ)
                (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
                (N := N)
                (δ := ε ^ (ℓ ^ j))
                hεj
                (x := coord r)
                (t := ℓ ^ (r + 1)))
  have hcarry :=
    F.artinHasseExpTraceCarryIterCorrection_eq_prod N m y ε
  refine ⟨c, ?_⟩
  calc
    F.artinHasseExpTraceCarryIterCorrection N y ε m
        =
          ∏ j ∈ Finset.range m,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                ((t : A) -
                  ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                    zbar ^ (ℓ ^ (i : ℕ))))) ^ (ℓ ^ (m - 1 - j)) := by
          simpa [A, Rps, zbar, t] using hcarry
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) * coord r)) ^ (ℓ ^ (r + 1))) ^
              (ℓ ^ (m - 1 - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          rw [hstep j]
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
                (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
          rfl

/-- Non-existential accumulated trace-carry expansion using the fixed Witt
carry `traceCarry`.  This is the constant-carry expansion needed for a
deterministic coordinate telescope. -/
theorem traceCarryIterCorrection_eq_teichmuller_series_product_powers_traceCarry
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    F.artinHasseExpTraceCarryIterCorrection N y ε m =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r))))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let coord : ℕ → A := fun r =>
    θ (WittVector.teichmuller ℓ
      (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r)))
  let u : ℕ → A := fun r => (ℓ : A) ^ (r + 1) * coord r
  have hseries :
      θ (F.traceCarry y) =
        ∑ r ∈ Finset.Iic N,
          (ℓ : A) ^ r * coord r := by
    simpa [A, θ, coord] using
      F.toConcreteStickelbergerSetup.wittThetaModQPow_eq_sum_teichmuller_series
        N (F.traceCarry y)
  have hdiff :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        (ℓ : A) * θ (F.traceCarry y) := by
    simpa [A, θ, zbar, t] using
      F.traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_traceCarry
        N y
  have hsum :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        ∑ r ∈ Finset.Iic N, u r := by
    calc
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
          = (ℓ : A) * θ (F.traceCarry y) := hdiff
      _ =
          (ℓ : A) *
            ∑ r ∈ Finset.Iic N, (ℓ : A) ^ r * coord r := by
            rw [hseries]
      _ = ∑ r ∈ Finset.Iic N, u r := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro r _hr
            simp [u, pow_succ]
            ring
  have hstep :
      ∀ j : ℕ,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                  zbar ^ (ℓ ^ (i : ℕ)))) =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) * coord r)) ^ (ℓ ^ (r + 1)) := by
    intro j
    have hεj : (ε ^ (ℓ ^ j)) ^ (N + 1) = 0 :=
      F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε
    have hprod :=
      rescale_exp_trunc_eval₂_finset_prod_eq_sum
        (r := ℓ)
        (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        (N := N)
        (δ := ε ^ (ℓ ^ j))
        hεj
        (s := Finset.Iic N)
        (u := u)
    calc
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ j) *
            ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))))
          =
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) * ∑ r ∈ Finset.Iic N, u r) := by
            rw [hsum]
      _ =
            ∏ r ∈ Finset.Iic N,
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) * u r) := by
            simpa [A, Rps] using hprod.symm
      _ =
            ∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) * coord r)) ^ (ℓ ^ (r + 1)) := by
            refine Finset.prod_congr rfl ?_
            intro r _hr
            simpa [A, θ, Rps, zbar, t, coord, u, mul_assoc, mul_left_comm,
              mul_comm] using
              (rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
                (r := ℓ)
                (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
                (N := N)
                (δ := ε ^ (ℓ ^ j))
                hεj
                (x := coord r)
                (t := ℓ ^ (r + 1)))
  have hcarry :=
    F.artinHasseExpTraceCarryIterCorrection_eq_prod N m y ε
  calc
    F.artinHasseExpTraceCarryIterCorrection N y ε m
        =
          ∏ j ∈ Finset.range m,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                ((t : A) -
                  ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                    zbar ^ (ℓ ^ (i : ℕ))))) ^ (ℓ ^ (m - 1 - j)) := by
          simpa [A, Rps, zbar, t] using hcarry
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) * coord r)) ^ (ℓ ^ (r + 1))) ^
              (ℓ ^ (m - 1 - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          rw [hstep j]

/-- Accumulated coordinate-tail fold for the trace carry.  After expanding
the carry with one fixed Witt vector, every accumulated correction factor is
absorbed into an explicit Artin-Hasse tail at the corresponding Dwork
iterate. -/
theorem exists_traceCarryIterCorrection_mul_teichmuller_frobenius_tail_eq_tail
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
    ∃ c : WittVector ℓ k,
      F.artinHasseExpTraceCarryIterCorrection N y ε m *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((ε ^ (ℓ ^ j)) ^ ℓ *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) =
        ∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ j) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
              (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)) := by
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
  obtain ⟨c, hcarry⟩ :=
    F.exists_traceCarryIterCorrection_eq_teichmuller_series_product_powers_const
      N m y ε hε
  let coord : ℕ → k := fun r =>
    ((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)
  let C : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) * θ (WittVector.teichmuller ℓ (coord r)))) ^
        (ℓ ^ (r + 1))
  let S : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((coord r) ^ ℓ)))) ^
        (ℓ ^ (r + 1))
  let T : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) * θ (WittVector.teichmuller ℓ (coord r)))) ^
        (ℓ ^ (r + 2))
  have hfold : ∀ j : ℕ, C j * S j = T j := by
    intro j
    have hεj : (ε ^ (ℓ ^ j)) ^ (N + 1) = 0 :=
      F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε
    simpa [A, θ, Eps, Rps, coord, C, S, T] using
      F.artinHasseExp_wittTeich_correction_product_mul_frobenius_tail_eq_tail_pow
        (N := N) (ε := ε ^ (ℓ ^ j)) hεj c
  refine ⟨c, ?_⟩
  calc
    F.artinHasseExpTraceCarryIterCorrection N y ε m *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((ε ^ (ℓ ^ j)) ^ ℓ *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)))
        =
          (∏ j ∈ Finset.range m, (C j) ^ (ℓ ^ (m - 1 - j))) *
            (∏ j ∈ Finset.range m, (S j) ^ (ℓ ^ (m - 1 - j))) := by
          rw [hcarry]
    _ =
          ∏ j ∈ Finset.range m,
            ((C j) ^ (ℓ ^ (m - 1 - j)) *
              (S j) ^ (ℓ ^ (m - 1 - j))) := by
          rw [Finset.prod_mul_distrib]
    _ =
          ∏ j ∈ Finset.range m,
            (T j) ^ (ℓ ^ (m - 1 - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          rw [← mul_pow, hfold j]
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r))))) ^
                (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)) := by
          rfl

/-- Non-existential accumulated coordinate-tail fold for the fixed Witt carry
`traceCarry`. -/
theorem traceCarryIterCorrection_mul_teichmuller_frobenius_tail_eq_tail_traceCarry
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
    F.artinHasseExpTraceCarryIterCorrection N y ε m *
      (∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε ^ (ℓ ^ j)) ^ ℓ *
              θ (WittVector.teichmuller ℓ
                ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
            (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j))) =
      ∏ j ∈ Finset.range m,
        (∏ r ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ j) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                  ((F.traceCarry y).coeff r))))) ^
            (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)) := by
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
  let c : WittVector ℓ k := F.traceCarry y
  let coord : ℕ → k := fun r =>
    ((_root_.frobeniusEquiv k ℓ).symm ^ r) (c.coeff r)
  let C : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) * θ (WittVector.teichmuller ℓ (coord r)))) ^
        (ℓ ^ (r + 1))
  let S : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((ε ^ (ℓ ^ j)) ^ ℓ *
          θ (WittVector.teichmuller ℓ ((coord r) ^ ℓ)))) ^
        (ℓ ^ (r + 1))
  let T : ℕ → A := fun j =>
    ∏ r ∈ Finset.Iic N,
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ j) * θ (WittVector.teichmuller ℓ (coord r)))) ^
        (ℓ ^ (r + 2))
  have hcarry :=
    F.traceCarryIterCorrection_eq_teichmuller_series_product_powers_traceCarry
      N m y ε hε
  have hfold : ∀ j : ℕ, C j * S j = T j := by
    intro j
    have hεj : (ε ^ (ℓ ^ j)) ^ (N + 1) = 0 :=
      F.parameter_pow_iterate_pow_succ_eq_zero N j ε hε
    simpa [A, θ, Eps, Rps, c, coord, C, S, T] using
      F.artinHasseExp_wittTeich_correction_product_mul_frobenius_tail_eq_tail_pow
        (N := N) (ε := ε ^ (ℓ ^ j)) hεj c
  calc
    F.artinHasseExpTraceCarryIterCorrection N y ε m *
        (∏ j ∈ Finset.range m,
          (∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((ε ^ (ℓ ^ j)) ^ ℓ *
                θ (WittVector.teichmuller ℓ
                  ((((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    ((F.traceCarry y).coeff r)) ^ ℓ)))) ^
              (ℓ ^ (r + 1))) ^ (ℓ ^ (m - 1 - j)))
        =
          (∏ j ∈ Finset.range m, (C j) ^ (ℓ ^ (m - 1 - j))) *
            (∏ j ∈ Finset.range m, (S j) ^ (ℓ ^ (m - 1 - j))) := by
          rw [hcarry]
    _ =
          ∏ j ∈ Finset.range m,
            ((C j) ^ (ℓ ^ (m - 1 - j)) *
              (S j) ^ (ℓ ^ (m - 1 - j))) := by
          rw [Finset.prod_mul_distrib]
    _ =
          ∏ j ∈ Finset.range m,
            (T j) ^ (ℓ ^ (m - 1 - j)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          rw [← mul_pow, hfold j]
    _ =
          ∏ j ∈ Finset.range m,
            (∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ j) *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                      ((F.traceCarry y).coeff r))))) ^
                (ℓ ^ (r + 2))) ^ (ℓ ^ (m - 1 - j)) := by
          rfl

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
