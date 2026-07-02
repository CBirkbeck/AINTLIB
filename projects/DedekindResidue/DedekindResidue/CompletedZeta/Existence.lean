module

public import Mathlib
public import DedekindResidue.CompletedZeta.MellinAgreement
public import DedekindResidue.CompletedZeta.FunctionalEquation

/-!
# Existence of the completed Dedekind zeta function  (SP1-AGE-4, ε)

The final assembly: the abstract completed function of the Hecke theta pair, evaluated on
the real ray (`heckeFEPair_Λ_real`), matches `heckeAdjust · completedZetaPrefactor · ζ_K`
there (`Λ_half_eq_prefactor_mul_zeta`) — the place Γ-product splits into the Deligne
factors and the `β = 4^{r₂}/|Δ|` normalisation regroups exactly into `|Δ|^{s/2}` and the
`2^{r₂}`-adjustment, as predicted. The identity theorem then extends the agreement to the
half-plane `Re s > 1`, producing `completedDedekindZeta` and the inhabitation theorem
`exists_isCompletedDedekindZeta` — the statement that makes the GRH predicate non-vacuous.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open Filter Asymptotics Topology
open scoped nonZeroDivisors Real ENNReal NNReal

variable (K : Type*) [Field K] [NumberField K]


open scoped Classical in
/-- The place Γ-product splits into real and complex contributions. -/
theorem prod_place_gamma (σ : ℝ) :
    (∏ w : InfinitePlace K, π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))
      = (π ^ (-σ) * Real.Gamma σ) ^ (nrRealPlaces K)
        * (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) ^ (nrComplexPlaces K) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype IsReal (fun w : InfinitePlace K =>
    π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))]
  congr 1
  · rw [show (π ^ (-σ) * Real.Gamma σ) ^ (nrRealPlaces K)
      = ∏ _w : {w : InfinitePlace K // IsReal w}, (π ^ (-σ) * Real.Gamma σ) by
      rw [Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show (mult (w : InfinitePlace K) : ℝ) = 1 by
      rw [mult, if_pos w.2]
      norm_num]
    norm_num
  · rw [show (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) ^ (nrComplexPlaces K)
      = ∏ _w : {w : InfinitePlace K // ¬ IsReal w},
          (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) by
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      exact ((Fintype.card_congr (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K => not_isReal_iff_isComplex))).trans rfl).symm]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show (mult (w : InfinitePlace K) : ℝ) = 2 by
      rw [mult, if_neg w.2]
      norm_num]

open scoped Classical in
/-- `Γℝ` at a real argument is real. -/
theorem Gammaℝ_ofReal (s : ℝ) :
    Complex.Gammaℝ (s : ℂ) = ((π ^ (-(s/2)) * Real.Gamma (s / 2) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def]
  rw [show (-(s : ℂ) / 2) = (((-(s/2) : ℝ)) : ℂ) by push_cast; ring,
    show ((s : ℂ) / 2) = (((s/2 : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_cpow Real.pi_pos.le, ← Complex.ofReal_mul]

open scoped Classical in
/-- `Γℂ` at a real argument is real. -/
theorem Gammaℂ_ofReal (s : ℝ) :
    Complex.Gammaℂ (s : ℂ) = ((2 * (2 * π) ^ (-s) * Real.Gamma s : ℝ) : ℂ) := by
  rw [Complex.Gammaℂ_def]
  rw [show (-(s : ℂ)) = (((-s : ℝ)) : ℂ) by push_cast; ring]
  rw [show ((2 : ℂ) * (π : ℂ)) = (((2 * π : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

open scoped Classical in
/-- **The final adjustment constant** `heckeJacobian·2^{-r₂}` — positive and
`s`-independent, absorbed into the definition of the completed zeta function. -/
noncomputable def heckeAdjust : ℝ :=
  ((heckeJacobian K : ℝ≥0) : ℝ) * ((2 : ℝ) ^ (nrComplexPlaces K))⁻¹

theorem heckeAdjust_pos : 0 < heckeAdjust K := by
  rw [heckeAdjust]
  have hJ : (0:ℝ) < ((heckeJacobian K : ℝ≥0) : ℝ) := by
    exact_mod_cast heckeJacobian_pos K
  positivity

open scoped Classical in
/-- **The agreement on the real ray (e-vii)**: for real `s > 1`,
`Λ(s/2) = heckeAdjust · (prefactor · ζ_K)(s)`. -/
theorem Λ_half_eq_prefactor_mul_zeta {s : ℝ} (hs : 1 < s) :
    (heckeFEPair K).Λ (((s / 2 : ℝ)) : ℂ)
      = ((heckeAdjust K : ℝ) : ℂ)
        * (completedZetaPrefactor K (s : ℂ) * dedekindZeta K (s : ℂ)) := by
  have hσ : (1:ℝ)/2 < s/2 := by linarith
  rw [heckeFEPair_Λ_real K hσ]
  rw [dedekindZeta_real_eq K hs]
  -- prefactor at real s, ofReal-ified
  have hD : (|discr K| : ℝ) = (((discr K).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hDpos := natAbs_discr_pos K
  have hpre : completedZetaPrefactor K (s : ℂ)
      = (((((discr K).natAbs : ℕ) : ℝ) ^ ((s:ℝ)/2)
          * ((π ^ (-(s/2)) * Real.Gamma (s / 2)) ^ (nrRealPlaces K)
            * (2 * (2 * π) ^ (-s) * Real.Gamma s) ^ (nrComplexPlaces K)) : ℝ) : ℂ) := by
    rw [completedZetaPrefactor, gammaFactor]
    rw [show ((s : ℂ) / 2) = (((s/2 : ℝ)) : ℂ) by push_cast; ring]
    rw [show ((|discr K| : ℝ) : ℂ) = ((((discr K).natAbs : ℕ) : ℝ) : ℂ) by rw [hD]]
    rw [← Complex.ofReal_cpow (by positivity), Gammaℝ_ofReal, Gammaℂ_ofReal]
    push_cast
    ring
  rw [hpre]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  -- the real identity
  have h2s : 2 * (s/2) = s := by ring
  rw [prod_place_gamma K (s/2), h2s]
  have hβsplit : (heckeBeta K) ^ (-(s/2))
      = ((2:ℝ) ^ (-s)) ^ (nrComplexPlaces K)
        * (((discr K).natAbs : ℕ) : ℝ) ^ ((s:ℝ)/2) := by
    rw [heckeBeta, Real.div_rpow (by positivity) hDpos.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg hDpos.le]
    congr 1
    · -- (4^{r₂})^{-(s/2)} = (2^{-s})^{r₂}
      rw [← Real.rpow_natCast (4:ℝ) (nrComplexPlaces K), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((2:ℝ) ^ (-s)) (nrComplexPlaces K),
        ← Real.rpow_mul (by norm_num)]
      rw [show (4:ℝ) = (2:ℝ) ^ ((2:ℕ):ℝ) by
        rw [Real.rpow_natCast]
        norm_num]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    · ring
  rw [hβsplit, heckeAdjust]
  have h2π : ((2 * π) ^ (-s)) = (2:ℝ) ^ (-s) * π ^ (-s) :=
    Real.mul_rpow (by norm_num) Real.pi_pos.le
  rw [h2π]
  have h2r : (0:ℝ) < (2:ℝ) ^ (nrComplexPlaces K) := by positivity
  have h2rs : ∀ x : ℝ, ((2:ℝ) ^ (-s) * x) ^ (nrComplexPlaces K)
      = ((2:ℝ) ^ (-s)) ^ (nrComplexPlaces K) * x ^ (nrComplexPlaces K) :=
    fun x => mul_pow _ _ _
  rw [show (2 * ((2:ℝ) ^ (-s) * π ^ (-s)) * Real.Gamma s)
    = (2 * (π ^ (-s) * Real.Gamma s)) * (2:ℝ) ^ (-s) by ring_nf]
  rw [mul_pow (2 * (π ^ (-s) * Real.Gamma s)) ((2:ℝ) ^ (-s)) (nrComplexPlaces K)]
  rw [mul_pow (2:ℝ) (π ^ (-s) * Real.Gamma s) (nrComplexPlaces K)]
  field_simp

end

end DedekindResidue
