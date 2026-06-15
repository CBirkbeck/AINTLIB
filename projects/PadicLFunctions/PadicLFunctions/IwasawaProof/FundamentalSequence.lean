/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.LogDerivative
import PadicLFunctions.IwasawaProof.Equivariance

/-!
# The fundamental exact sequence (RJW §12.2.2, TeX 3382–3441) — E12.3

`def:Zp(1)`, `lem:rest zp*` (already partly in `LogDerivative`), and `thm:fund exact seq`:
`0 → ℤ_p(1) → 𝒰_{∞,1} →[Col] Λ(𝒢) → ℤ_p(1) → 0` as `Λ(𝒢)`-modules.

Status: **sorry-free**. Left-exactness `ker Col = ℤ_p(1)` (`mem_ker_Col_iff_mem_ZpOne`) and
right-exactness `image Col = ker(χ-moment)` (`range_Col_eq_ker_chiMoment`) are both complete.
The substrate `levelNorm_zpPow_zetaSys` (cyclotomic norm of the Tate twist) is proved for `p`
odd via the un-translated minpoly `X^p − C(ξ_n)` (`levelNorm_zetaSys`) extended to `ℤ_p`
exponents by the `ξ_n^{(toZModPow…).val}` representation (`zpPow_zetaSys'`); it is *false for
p = 2* so carries `hp2 : p ≠ 2` (errata #14), threaded through `normOp_binomialSeries` and
`mem_ker_Col_iff_mem_ZpOne`. The cokernel converse uses the inverse Coleman map
`invColeman`/`exists_invColeman_Col_eq` and divides off the **constant `ℤ_[p]`-Teichmüller
system** (`teichNCU`, from `Interpolation/Branches.lean`'s `teichmullerFun`) for the principal
split — so it no longer depends on the deferred `normCompat_eq_teichmuller_mul_principal`.
-/

open PadicLFunctions PadicLFunctions.Coleman

open scoped IntermediateField

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- The cyclotomic generator `ξ_n` is a `1`-unit for `n ≥ 1`: `‖ξ_n − 1‖ < 1`
(`ξ_n − 1 = π_n` is the uniformiser, `norm_pi_lt_one`). -/
private theorem norm_zetaSys_sub_one_lt_one {n : ℕ} (hn : 1 ≤ n) :
    ‖zetaSys p n - 1‖ < 1 := by
  have := norm_pi_lt_one p hn; rwa [pi] at this

/-! ## Substrate (I): the `ψ ↔ psiSeries` Mahler bridge for `PadicMeasure p ℤ_[p]`

The `MeasureR` analogue (`PadicLFunctions.mahlerTransform_psi`) is proved in
`MeasureR/FormalPsi.lean` for the field-coefficient `MeasureR K ℤ_[p]`. We port it to the
`ℤ_[p]`-valued `PadicMeasure p ℤ_[p]` here, reusing the series-side digit decomposition
over `ℤ_[p]` (`existsUnique_digits_padicInt`, in `NormOperator.lean`) and the measure-side
operators `psi`/`phi`/`psi_phi`/`phi_psi`/`dirac_mul_dirac` already in `Measure/Toolbox.lean`.
The key output is `mahlerTransform_psi` (used to transport the `(1−φ)`/`ψ`-fixed exact
sequence of `LogDerivative.lean` to the measure side). -/

/-- `𝓐_{φμ} = phiSeries 𝓐_μ` over `ℤ_[p]`: the `mahlerTransform_phi` substitution formula
(`Measure/Toolbox.lean`) is exactly `phiSeries` (both are `subst((1+T)^p − 1)`). -/
private theorem mahlerTransform_phiSeries (μ : PadicMeasure p ℤ_[p]) :
    PadicMeasure.mahlerTransform p (PadicMeasure.phi p μ)
      = phiSeries p (PadicMeasure.mahlerTransform p μ) :=
  PadicMeasure.mahlerTransform_phi p μ

/-- `𝓐_{δ_i} = (1+T)^i` over `ℤ_[p]` (`𝓐_{δ_a} = binomialSeries a` + `binomialSeries_nat`). -/
private theorem mahlerTransform_dirac_natCast (i : ℕ) :
    PadicMeasure.mahlerTransform p (PadicMeasure.dirac p ((i : ℕ) : ℤ_[p]))
      = (1 + PowerSeries.X) ^ i := by
  rw [PadicMeasure.mahlerTransform_dirac, PowerSeries.binomialSeries_nat]

/-- `𝓐` is additive over a finite sum (the `mahlerTransformₗ` linear-map form, repackaged). -/
private theorem mahlerTransform_sum {ι : Type*} (s : Finset ι)
    (m : ι → PadicMeasure p ℤ_[p]) :
    PadicMeasure.mahlerTransform p (∑ i ∈ s, m i)
      = ∑ i ∈ s, PadicMeasure.mahlerTransform p (m i) :=
  map_sum (PadicMeasure.mahlerTransformₗ p) m s

/-- `ψ` is additive (`psi` is `μ`-linear in its measure argument). -/
private theorem psi_add (μ ν : PadicMeasure p ℤ_[p]) :
    PadicMeasure.psi p (μ + ν) = PadicMeasure.psi p μ + PadicMeasure.psi p ν :=
  LinearMap.ext fun f => by
    change (μ + ν) _ = μ _ + ν _
    rw [LinearMap.add_apply]

/-- `ψ 0 = 0`. -/
private theorem psi_zero : PadicMeasure.psi p (0 : PadicMeasure p ℤ_[p]) = 0 :=
  LinearMap.ext fun f => by change (0 : PadicMeasure p ℤ_[p]) _ = _; rw [LinearMap.zero_apply]

/-- `ψ` is additive over a finite sum. -/
private theorem psi_sum {ι : Type*} (s : Finset ι) (m : ι → PadicMeasure p ℤ_[p]) :
    PadicMeasure.psi p (∑ i ∈ s, m i) = ∑ i ∈ s, PadicMeasure.psi p (m i) := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty, psi_zero])
    (fun a t hat ih => ?_)
  rw [Finset.sum_insert hat, Finset.sum_insert hat, psi_add, ih]

/-- A translate of a `φ`-image by a unit is supported off `pℤ_p`, hence killed by `ψ`:
`ψ(δ_a · φν) = 0` when `‖a‖ = 1`. (Port of the `MeasureR` lemma of the same shape.) -/
private theorem psi_dirac_mul_phi_eq_zero {a : ℤ_[p]} (ha : ‖a‖ = 1)
    (ν : PadicMeasure p ℤ_[p]) :
    PadicMeasure.psi p (PadicMeasure.dirac p a * PadicMeasure.phi p ν) = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [show PadicMeasure.psi p (PadicMeasure.dirac p a * PadicMeasure.phi p ν) f
      = (PadicMeasure.dirac p a * PadicMeasure.phi p ν)
          ((LocallyConstant.charFn ℤ_[p] (PadicMeasure.isClopen_pZp p) : C(ℤ_[p], ℤ_[p]))
            * f.comp (PadicMeasure.shiftDiv p)) from rfl,
    PadicMeasure.mul_apply, PadicMeasure.dirac_apply, PadicMeasure.convInner_apply]
  rw [LinearMap.zero_apply, PadicMeasure.phi, PadicMeasure.pushforward_apply]
  rw [show (((LocallyConstant.charFn ℤ_[p] (PadicMeasure.isClopen_pZp p) : C(ℤ_[p], ℤ_[p]))
        * f.comp (PadicMeasure.shiftDiv p)).comp
          ⟨fun y => a + y, by fun_prop⟩).comp (PadicMeasure.mulCM p (p : ℤ_[p]))
      = (0 : C(ℤ_[p], ℤ_[p])) from ?_, map_zero]
  refine ContinuousMap.ext fun z => ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply, LocallyConstant.coe_continuousMap,
    LocallyConstant.coe_charFn, PadicMeasure.mulCM, ContinuousMap.coe_mk, ContinuousMap.coe_zero,
    Pi.zero_apply]
  have hnotmem : (a + (p : ℤ_[p]) * z) ∉ {y : ℤ_[p] | ‖y‖ < 1} := by
    simp only [Set.mem_setOf_eq, not_lt]
    have hpz : ‖(p : ℤ_[p]) * z‖ < 1 := PadicMeasure.mem_pZp_of_mul p
    by_contra hlt
    push Not at hlt
    have hane : ‖a‖ ≤ max ‖a + (p : ℤ_[p]) * z‖ ‖(p : ℤ_[p]) * z‖ := by
      calc ‖a‖ = ‖(a + (p : ℤ_[p]) * z) + -((p : ℤ_[p]) * z)‖ := by rw [add_neg_cancel_right]
        _ ≤ max ‖a + (p : ℤ_[p]) * z‖ ‖-((p : ℤ_[p]) * z)‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖a + (p : ℤ_[p]) * z‖ ‖(p : ℤ_[p]) * z‖ := by rw [norm_neg]
    rw [ha] at hane
    exact absurd (hane.trans_lt (max_lt hlt hpz)) (lt_irrefl _)
  rw [Set.indicator_of_notMem hnotmem, zero_mul]

/-- The unit-translate norm fact for digits: `‖(i:ℤ_[p]) − (j:ℤ_[p])‖ = 1` for distinct
`i, j < p`. -/
private theorem norm_natCast_sub_natCast_eq_one {i j : ℕ} (hi : i < p) (hj : j < p)
    (hij : i ≠ j) : ‖((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p])‖ = 1 := by
  have hkey : ∀ m : ℕ, 0 < m → m < p → ‖((m : ℕ) : ℤ_[p])‖ = 1 := fun m hm0 hmp => by
    rw [PadicInt.norm_natCast_eq_one_iff, hp.out.coprime_iff_not_dvd]
    exact fun hdvd => absurd (Nat.le_of_dvd hm0 hdvd) (by omega)
  rcases le_total j i with hle | hle
  · rw [show ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) = ((i - j : ℕ) : ℤ_[p]) by rw [Nat.cast_sub hle]]
    exact hkey (i - j) (by omega) (by omega)
  · rw [show ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) = -(((j - i : ℕ) : ℤ_[p])) by
      rw [Nat.cast_sub hle]; ring, norm_neg]
    exact hkey (j - i) (by omega) (by omega)

/-- Digit extraction: `ψ(δ_{-j} · Σ_i δ_i φ(ν_i)) = ν_j` (the `i = j` term gives `ψφ = id`;
the others are unit-translates killed by `ψ`). -/
private theorem psi_dirac_neg_mul_sum (ν : Fin p → PadicMeasure p ℤ_[p]) (j : Fin p) :
    PadicMeasure.psi p (PadicMeasure.dirac p (-((j : ℕ) : ℤ_[p]))
        * ∑ i : Fin p, PadicMeasure.dirac p ((i : ℕ) : ℤ_[p]) * PadicMeasure.phi p (ν i))
      = ν j := by
  rw [Finset.mul_sum, psi_sum, Finset.sum_eq_single j]
  · rw [← mul_assoc, PadicMeasure.dirac_mul_dirac, neg_add_cancel, ← PadicMeasure.one_def,
      one_mul, PadicMeasure.psi_phi]
  · intro i _ hij
    rw [← mul_assoc, PadicMeasure.dirac_mul_dirac]
    refine psi_dirac_mul_phi_eq_zero p ?_ (ν i)
    rw [show -((j : ℕ) : ℤ_[p]) + ((i : ℕ) : ℤ_[p])
        = ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) by ring]
    exact norm_natCast_sub_natCast_eq_one p i.2 j.2 (fun h => hij (Fin.ext h))
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The measure-level `p`-residue digit decomposition over `ℤ_[p]`: every measure is uniquely
`Σ_{i<p} δ_i · φ(ν_i)`. (Port of `existsUnique_measure_digits`.) -/
private theorem existsUnique_measure_digits (μ : PadicMeasure p ℤ_[p]) :
    ∃! ν : Fin p → PadicMeasure p ℤ_[p],
      μ = ∑ i : Fin p,
        PadicMeasure.dirac p ((i : ℕ) : ℤ_[p]) * PadicMeasure.phi p (ν i) := by
  -- existence: transport through the unique SERIES-side digit decomposition over `ℤ_[p]`
  obtain ⟨G, hG, hGuniq⟩ := existsUnique_digits_padicInt p (PadicMeasure.mahlerTransform p μ)
  refine ⟨fun i => (PadicMeasure.mahlerLinearEquiv p).symm (G i), ?_, ?_⟩
  · -- `𝓐` of the assembled measure is `Σ (1+T)^i φ(G i) = 𝓐_μ`, so they agree (`𝓐` injective)
    apply PadicMeasure.mahlerTransform_injective
    rw [mahlerTransform_sum, hG]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PadicMeasure.mahlerTransform_mul, mahlerTransform_dirac_natCast,
      mahlerTransform_phiSeries, PadicMeasure.mahlerLinearEquiv_symm_apply,
      PadicMeasure.mahlerTransform_ofPowerSeries]
  · -- uniqueness, pulled back to the series-side decomposition
    intro ν hν
    have hdig : IsDigitDecomp p (PadicMeasure.mahlerTransform p μ)
        (fun i => PadicMeasure.mahlerTransform p (ν i)) := by
      rw [IsDigitDecomp]
      conv_lhs => rw [hν, mahlerTransform_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PadicMeasure.mahlerTransform_mul, mahlerTransform_dirac_natCast,
        mahlerTransform_phiSeries]
    have hνeq := hGuniq (fun i => PadicMeasure.mahlerTransform p (ν i)) hdig
    funext i
    apply PadicMeasure.mahlerTransform_injective
    rw [PadicMeasure.mahlerLinearEquiv_symm_apply, PadicMeasure.mahlerTransform_ofPowerSeries,
      ← congrFun hνeq i]

/-- **Substrate (I): the `ψ ↔ psiSeries` Mahler bridge** for `PadicMeasure p ℤ_[p]`:
`𝓐_{ψμ} = psiSeries 𝓐_μ`. (Port of the `MeasureR` `mahlerTransform_psi`.) The measure-side
digit family `(ν i)` of `μ` has `ν 0 = ψ μ` and `𝓐`-image the series-side digit family of
`𝓐_μ`, whose `0`-th digit is `psiSeries 𝓐_μ`. -/
theorem mahlerTransform_psi (μ : PadicMeasure p ℤ_[p]) :
    PadicMeasure.mahlerTransform p (PadicMeasure.psi p μ)
      = psiSeries p (PadicMeasure.mahlerTransform p μ) := by
  obtain ⟨ν, hν, -⟩ := existsUnique_measure_digits p μ
  -- the `0`-th digit is `ψ μ` (the `δ_0`-translate is trivial)
  have hν0 : ν 0 = PadicMeasure.psi p μ := by
    have := psi_dirac_neg_mul_sum p ν 0
    rw [← hν, show (-(((0 : Fin p) : ℕ) : ℤ_[p])) = 0 by simp, ← PadicMeasure.one_def,
      one_mul] at this
    exact this.symm
  -- `𝓐_μ = Σ_i (1+T)^i·φ(𝓐_{ν i})`, so `(𝓐_{ν i})` is its series digit decomposition
  have hdig : IsDigitDecomp p (PadicMeasure.mahlerTransform p μ)
      (fun i => PadicMeasure.mahlerTransform p (ν i)) := by
    rw [IsDigitDecomp]
    conv_lhs => rw [hν, mahlerTransform_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PadicMeasure.mahlerTransform_mul, mahlerTransform_dirac_natCast,
      mahlerTransform_phiSeries]
  rw [psiSeries_eq_of_isDigitDecomp_padicInt hdig, hν0]

/-! ## Substrate (II): the binomial series is `𝒩`-fixed and interpolates `ξ_n^a`

`binomialSeries a = (1+T)^a` is the Coleman series of the Tate-twist system `(ξ_n^a)_n`:
it interpolates `ξ_n^a` (`evalPi_binomialSeries`, from `seriesEval_map_binomialSeries`) and is
`𝒩`-fixed (`normOp_binomialSeries`, via the evaluation/norm square `evalPi_normOp` and the
cyclotomic norm `levelNorm(ξ_{n+1}^a) = ξ_n^a`). Coleman uniqueness then gives
`colemanSeries u = binomialSeries a` for `u ∈ ZpOne` with parameter `a`. -/

/-- `(binomialSeries a)(π_n) = zpPow ξ_n a` for `n ≥ 1`: the analytic `(1+π_n)^a = ξ_n^a`
(`seriesEval_map_binomialSeries` at `z = π_n`, with `1 + π_n = ξ_n`). -/
theorem evalPi_binomialSeries (a : ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (PowerSeries.binomialSeries ℤ_[p] a) n = zpPow p (zetaSys p n) a := by
  rw [evalPi, seriesEval_map_binomialSeries p a (norm_pi_lt_one p hn),
    show (1 : ℂ_[p]) + pi p n = zetaSys p n from by rw [pi]; ring]

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (cf. Tower.lean)
set_option maxHeartbeats 1000000 in
-- the `adjoin.powerBasis`/`norm_eq_norm_adjoin` computation runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer; both instance synthesis and the
-- power-basis term elaboration exceed the defaults (mirrors `minpoly_extendScalars_of_pow`)
/-- **The cyclotomic norm of `ξ_{n+1}`** (RJW TeX 2581–2585, the `b = 1` un-translated
analogue of `levelNorm_zetaSys_pow_sub_one`): for `n ≥ 1` and `p` odd,
`N_{n+1,n}(ξ_{n+1}) = ξ_n`. The generator `ξ_{n+1}` is a primitive `p^{n+1}`-th root not in
`K_n` (`primitiveRoot_notMem_K`) generating `K_{n+1}/K_n` (`extendScalars_adjoin_eq_top`)
with minimal polynomial `X^p − C(ξ_n)` (`minpoly_extendScalars_of_pow`, since `ξ_{n+1}^p =
ξ_n` by `zetaSys_pow_p`); the norm of a generator is `(−1)^p · coeff₀ = (−1)^p·(−ξ_n) = ξ_n`
(`p` odd, `(−1)^{p+1} = 1`).

`hp2 : p ≠ 2` is required (errata #14): at `p = 2`, `N(ξ_2) = (−1)^{2+1}·ξ_1 = −ξ_1 ≠ ξ_1`
(`N_{ℚ₂(i)/ℚ₂}(i) = 1 ≠ −1`). -/
private theorem levelNorm_zetaSys (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    levelNorm p n (zetaSys p (n + 1)) = zetaSys p n := by
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    IsCyclotomicExtension.finiteDimensional {p ^ (n + 1)} ℚ_[p] (K p (n + 1))
  haveI : FiniteDimensional (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    FiniteDimensional.right ℚ_[p] (K p n) _
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hwK : zetaSys p (n + 1) ∈ K p (n + 1) := zetaSys_mem_K p (n + 1)
  have hcK : zetaSys p n ∈ K p n := zetaSys_mem_K p n
  -- `W := ξ_{n+1}` as an `extendScalars` element, with `W^p = (c := ξ_n)`
  set W : IntermediateField.extendScalars (K_le_succ p n) :=
    ⟨zetaSys p (n + 1), (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hwK⟩ with hW
  set c : K p n := ⟨zetaSys p n, hcK⟩ with hc
  have hWc : W ^ p = algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) c := by
    apply Subtype.ext
    change (zetaSys p (n + 1)) ^ p = (zetaSys p n : ℂ_[p])
    rw [zetaSys_pow_p]
  have hWbot : (W : ℂ_[p]) ∉ K p n := primitiveRoot_notMem_K p hn (zetaSys_primitiveRoot p (n + 1))
  have hWtop : (K p n)⟮W⟯ = ⊤ := extendScalars_adjoin_eq_top p hn hWbot
  have hmpW : minpoly (K p n) W = (Polynomial.X : Polynomial (K p n)) ^ p - Polynomial.C c :=
    minpoly_extendScalars_of_pow p hn hWc hWtop
  have hroot : (Polynomial.aeval W) ((Polynomial.X : Polynomial (K p n)) ^ p - Polynomial.C c)
      = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hWc, sub_self]
  have hint : IsIntegral (K p n) W := ⟨_, Polynomial.monic_X_pow_sub_C c hp0, hroot⟩
  have hdeg : (minpoly (K p n) W).natDegree = p := by
    rw [hmpW, Polynomial.natDegree_X_pow_sub_C]
  -- the norm of the generator is `(−1)^p · coeff₀(minpoly) = (−1)^p·(−c) = c`
  have hnorm : Algebra.norm (K p n) W
      = (-1) ^ (minpoly (K p n) W).natDegree * (minpoly (K p n) W).coeff 0 := by
    rw [Algebra.norm_eq_norm_adjoin (K p n) W]
    have hrank : Module.finrank (↥(K p n)⟮W⟯)
        (IntermediateField.extendScalars (K_le_succ p n)) = 1 := by
      rw [hWtop]; exact IntermediateField.finrank_top
    rw [hrank, pow_one]
    have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis hint)
    rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] at hpb
  -- the norm value, as a `K_n`-element, is `c = ⟨ξ_n, _⟩`
  have hnval : Algebra.norm (K p n) W = c := by
    rw [hnorm, hdeg, hmpW, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
      Polynomial.coeff_X_pow, if_neg (show ¬(0 = p) by omega), zero_sub,
      (hp.out.odd_of_ne_two hp2).neg_one_pow, neg_one_mul, neg_neg]
  -- unfold `levelNorm` and coerce
  rw [levelNorm_apply p n hwK]
  change (Algebra.norm (K p n) W : ℂ_[p]) = zetaSys p n
  rw [hnval, hc]

/-- The `ℕ`-power form: `N_{n+1,n}(ξ_{n+1}^k) = ξ_n^k` for `n ≥ 1`, `p` odd. By
`levelNorm` multiplicativity (`levelNorm_mul`, `levelNorm_one`) and `levelNorm_zetaSys`. -/
private theorem levelNorm_zetaSys_pow (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    levelNorm p n (zetaSys p (n + 1) ^ k) = zetaSys p n ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, levelNorm_one]
  | succ m ih =>
    rw [pow_succ, pow_succ,
      levelNorm_mul p n (pow_mem (zetaSys_mem_K p (n + 1)) m) (zetaSys_mem_K p (n + 1)),
      ih, levelNorm_zetaSys p hp2 hn]

/-- `zpPow ξ_n c = ξ_n^{(toZModPow n c).val}` (the `p^n`-periodicity of `ξ_n^·`): both sides
are continuous in `c` and agree on `c ∈ ℕ` (`zpPow_natCast` vs `ξ_n^{k mod p^n} = ξ_n^k`).
Re-derivation of the `private` `GaloisAction.zpPow_zetaSys`, needed un-`private`-d here. -/
private theorem zpPow_zetaSys' {n : ℕ} (hn : 1 ≤ n) (c : ℤ_[p]) :
    zpPow p (zetaSys p n) c
      = zetaSys p n ^ ((PadicInt.toZModPow n c : ZMod (p ^ n)).val) := by
  have hz1 : ‖zetaSys p n - 1‖ < 1 := norm_zetaSys_sub_one_lt_one p hn
  have hcontL : Continuous (zpPow p (zetaSys p n)) := by
    have h : zpPow p (zetaSys p n) = (PadicInt.addChar_of_value_at_one (zetaSys p n - 1)
        (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hz1) : ℤ_[p] → ℂ_[p]) := by
      funext a; rw [zpPow, dif_pos (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hz1)]
    rw [h]; exact PadicInt.continuous_addChar_of_value_at_one _
  have hcontR : Continuous fun c : ℤ_[p] =>
      zetaSys p n ^ ((PadicInt.toZModPow n c : ZMod (p ^ n)).val) := by
    have hlcZ : IsLocallyConstant fun c : ℤ_[p] => (PadicInt.toZModPow n c : ZMod (p ^ n)) :=
      fun s => by
        rw [← Set.biUnion_preimage_singleton]
        exact isOpen_biUnion fun a _ => PadicMeasure.isOpen_toZModPow_fiber p n a
    exact ((hlcZ.comp ZMod.val).comp fun k => zetaSys p n ^ k).continuous
  have hnat : ∀ k : ℕ, zpPow p (zetaSys p n) (k : ℤ_[p])
      = zetaSys p n ^ ((PadicInt.toZModPow n (k : ℤ_[p]) : ZMod (p ^ n)).val) := by
    intro k
    rw [zpPow_natCast p hz1]
    refine zetaSys_pow_eq_pow_of_modEq p ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, map_natCast]
  exact congrFun (PadicInt.denseRange_natCast.equalizer hcontL hcontR (funext hnat)) c

/-- **The cyclotomic norm of `zpPow`** (RJW TeX 2581–2585, generalised from integer to
`ℤ_p`-exponents): for `n ≥ 1` and `p` odd, `N_{n+1,n}(ξ_{n+1}^a) = ξ_n^a`, the
norm-compatibility of the Tate-twist tower `(ξ_n^a)_n`.

`hp2 : p ≠ 2` is required (errata #14): the lemma is FALSE for `p = 2` (at odd `b`,
`N_{n+1,n}(ξ_{n+1}^b) = −ξ_n^b ≠ ξ_n^b`; concretely `N_{ℚ₂(i)/ℚ₂}(i) = 1 ≠ −1 = ξ_1`).
The `ℤ_p`-exponent `a` reduces to the `ℕ`-power case by `zpPow_zetaSys'` (the
`ξ_{n+1}^{(toZModPow…).val}` form at both levels): `levelNorm_zetaSys_pow` collapses the
`(n+1)`-level norm to `ξ_n^{(toZModPow (n+1) a).val}`, and `p^n`-periodicity
(`zetaSys_pow_eq_pow_of_modEq`, via `toZModPow (n+1) a ≡ toZModPow n a mod p^n`) matches it to
`ξ_n^{(toZModPow n a).val} = zpPow ξ_n a` — no `Algebra.norm` continuity needed. -/
private theorem levelNorm_zpPow_zetaSys (hp2 : p ≠ 2) (a : ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    levelNorm p n (zpPow p (zetaSys p (n + 1)) a) = zpPow p (zetaSys p n) a := by
  rw [zpPow_zetaSys' p (by omega : 1 ≤ n + 1) a, levelNorm_zetaSys_pow p hp2 hn,
    zpPow_zetaSys' p hn a]
  -- match the two exponents: `toZModPow (n+1) a ≡ toZModPow n a (mod p^n)`
  refine zetaSys_pow_eq_pow_of_modEq p ?_
  haveI : NeZero (p ^ (n + 1)) := ⟨(pow_pos hp.out.pos (n + 1)).ne'⟩
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff,
    show ((PadicInt.toZModPow (n + 1) a : ZMod (p ^ (n + 1))).val : ZMod (p ^ n))
        = ZMod.cast (PadicInt.toZModPow (n + 1) a : ZMod (p ^ (n + 1))) from
      ZMod.natCast_val _,
    PadicInt.cast_toZModPow n (n + 1) (by omega) a, ZMod.natCast_zmod_val]

/-- **Substrate (II): the binomial series is `𝒩`-fixed**: `𝒩(binomialSeries a) = binomialSeries
a`. By `evalPi_injective` it suffices that the evaluation/norm square `evalPi_normOp` reads
`levelNorm(ξ_{n+1}^a) = ξ_n^a` (`levelNorm_zpPow_zetaSys`), via `evalPi_binomialSeries`.
Carries `hp2 : p ≠ 2` (errata #14) from `levelNorm_zpPow_zetaSys` (false at `p = 2`). -/
theorem normOp_binomialSeries (hp2 : p ≠ 2) (a : ℤ_[p]) :
    normOp (PowerSeries.binomialSeries ℤ_[p] a) = PowerSeries.binomialSeries ℤ_[p] a := by
  refine evalPi_injective p (fun n hn => ?_)
  rw [evalPi_normOp _ hn, evalPi_binomialSeries p a (by omega : 1 ≤ n + 1),
    evalPi_binomialSeries p a hn, levelNorm_zpPow_zetaSys p hp2 a hn]

/-- For `u ∈ ZpOne` with parameter `a`, the Coleman series is the binomial series:
`colemanSeries u = binomialSeries a`. Both are `𝒩`-fixed units interpolating `ξ_n^a`
(`evalPi_binomialSeries`; `binomialSeries` is a unit by its constant coefficient `1`), so
they agree by Coleman uniqueness (`evalPi_injective`) — only the interpolation `ha` and
`evalPi`-multiplicativity enter, so no `hp2` is needed here. -/
theorem colemanSeries_eq_binomialSeries_of_mem_ZpOne {u : NormCompatUnits p} {a : ℤ_[p]}
    (ha : ∀ n, 1 ≤ n → ((u.elems n : ℂ_[p]ˣ) : ℂ_[p]) = zpPow p (zetaSys p n) a) :
    colemanSeries p u = PowerSeries.binomialSeries ℤ_[p] a := by
  refine evalPi_injective p (fun n hn => ?_)
  rw [evalPi_colemanSeries p u hn, evalPi_binomialSeries p a hn, ha n hn]

/-- **RJW def:Zp(1) (TeX 3407–3409)**: `ℤ_p(1) = {(ξ_n^a)_n : a ∈ ℤ_p} ⊂ 𝒰_∞`, the
integral Tate twist, realised as a subgroup of the unit tower. A system `u ∈ 𝒰_∞` lies
in `ℤ_p(1)` iff there is a single `a ∈ ℤ_p` with `u_n = ξ_n^a` (`zpPow`) for every
`n ≥ 1` (the level-`0` component is unconstrained, matching `compat`/`colemanSeries`).
The subgroup laws are the character laws of `zpPow` in the exponent: `a + b` for the
product, `0` for the identity, `−a` for the inverse. -/
def ZpOne : Subgroup (NormCompatUnits p) where
  carrier :=
    {u | ∃ a : ℤ_[p], ∀ n, 1 ≤ n → ((u.elems n : ℂ_[p]ˣ) : ℂ_[p]) = zpPow p (zetaSys p n) a}
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun n hn => ?_⟩
    have hval : ((((u * v).elems n) : ℂ_[p]ˣ) : ℂ_[p])
        = ((u.elems n : ℂ_[p]ˣ) : ℂ_[p]) * ((v.elems n : ℂ_[p]ˣ) : ℂ_[p]) := by
      change (((u.elems n * v.elems n : ℂ_[p]ˣ)) : ℂ_[p]) = _
      rw [Units.val_mul]
    rw [hval, ha n hn, hb n hn, zpPow_add p (norm_zetaSys_sub_one_lt_one p hn)]
  one_mem' := by
    refine ⟨0, fun n hn => ?_⟩
    have h1 : ‖(1 : ℂ_[p]) - 1‖ < 1 := by simp
    rw [show (((1 : NormCompatUnits p).elems n : ℂ_[p]ˣ) : ℂ_[p]) = 1 from rfl,
      show (0 : ℤ_[p]) = ((0 : ℕ) : ℤ_[p]) by norm_cast,
      zpPow_natCast p (norm_zetaSys_sub_one_lt_one p hn), pow_zero]
  inv_mem' := by
    rintro u ⟨a, ha⟩
    refine ⟨-a, fun n hn => ?_⟩
    have hz1 : ‖zetaSys p n - 1‖ < 1 := norm_zetaSys_sub_one_lt_one p hn
    have hval : (((u⁻¹).elems n : ℂ_[p]ˣ) : ℂ_[p]) = (((u.elems n : ℂ_[p]ˣ) : ℂ_[p]))⁻¹ := by
      change (((u.elems n)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = _
      rw [Units.val_inv_eq_inv_val]
    have hmul : zpPow p (zetaSys p n) a * zpPow p (zetaSys p n) (-a) = 1 := by
      rw [← zpPow_add p hz1, add_neg_cancel,
        show (0 : ℤ_[p]) = ((0 : ℕ) : ℤ_[p]) by norm_cast, zpPow_natCast p hz1, pow_zero]
    rw [hval, ha n hn]
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm

/-! ## The kernel of `1 − φ` on `ℤ_p⟦T⟧` is the constants (kernel half of `lem:rest zp*`)

`(1−φ)F = 0` forces `F = C(F₀)`: the substitution `φ = subst((1+T)^p − 1)` has order-`1`
substituend with leading coefficient `p`, so `[Tⁿ](φF) = pⁿ·Fₙ + Σ_{d<n} F_d·[Tⁿ](Sᵈ)`;
the equation `(1−pⁿ)Fₙ = Σ_{d<n} F_d·[Tⁿ](Sᵈ)` with `1−pⁿ` a unit (`n ≥ 1`) and the
sub-diagonal terms forced to `0` by strong induction kills every `Fₙ` (`n ≥ 1`). -/

/-- `[Tⁿ](Sᵈ) = 0` for `n < d`, `S = (1+T)^p − 1` (order `1`). -/
private theorem coeff_S_pow_vanish {d n : ℕ} (hdn : n < d) :
    PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) = 0 := by
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff
    (φ := ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]))).2 (by simp)
  rw [hU, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

/-- `[Tⁿ](φF) = Σ_{d ≤ n} F_d·[Tⁿ](Sᵈ)` (the finite substitution-coefficient formula). -/
private theorem coeff_phiSeries_split (F : PowerSeries ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (phiSeries p F)
      = ∑ d ∈ Finset.range (n + 1), (PowerSeries.coeff d F) •
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) := by
  rw [phiSeries, PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p)]
  refine finsum_eq_finsetSum_of_support_subset _ (fun d hd => ?_)
  simp only [Function.mem_support] at hd
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hcon
  push Not at hcon
  exact hd (by rw [coeff_S_pow_vanish p (by omega), smul_zero])

/-- `[T¹]((1+T)^p) = p`: from `(1+T)^p = binomialSeries p` and `Ring.choose p 1 = p`. -/
private theorem coeff_one_one_add_X_pow :
    PowerSeries.coeff 1 ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p) = (p : ℤ_[p]) := by
  rw [← PowerSeries.binomialSeries_nat (R := ℤ_[p]), PowerSeries.binomialSeries_coeff,
    Ring.choose_one_right, smul_eq_mul, mul_one]

/-- `[Tⁿ](Sⁿ) = pⁿ`, `S = (1+T)^p − 1` (`S = pT + O(T²)`, leading coefficient `p`). -/
private theorem coeff_S_pow_diag {d : ℕ} :
    PowerSeries.coeff d (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)
      = (p : ℤ_[p]) ^ d := by
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff
    (φ := ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]))).2 (by simp)
  have hU0 : PowerSeries.constantCoeff (R := ℤ_[p]) U = (p : ℤ_[p]) := by
    have h1 : PowerSeries.coeff 1 ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p])
        = (p : ℤ_[p]) := by
      rw [map_sub, coeff_one_one_add_X_pow, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero]
    rw [hU, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff] at h1
    exact h1
  rw [hU, mul_pow, show PowerSeries.coeff d (PowerSeries.X ^ d * U ^ d)
      = PowerSeries.coeff 0 (U ^ d) from by
    have := PowerSeries.coeff_X_pow_mul (U ^ d) d 0; rwa [zero_add] at this,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hU0]

/-- `1 − pⁿ` is a unit of `ℤ_[p]` for `n ≥ 1`. -/
private theorem isUnit_one_sub_p_pow {n : ℕ} (hn : 1 ≤ n) : IsUnit (1 - (p : ℤ_[p]) ^ n) := by
  refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ?_
  rw [mem_nonunits_iff, PadicInt.isUnit_iff, norm_pow]
  have hlt : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  exact fun hc => absurd hc (ne_of_lt (pow_lt_one₀ (norm_nonneg _) hlt (by omega)))

/-- **Kernel half of `lem:rest zp*`**: `(1 − φ)F = 0 ⟹ F = C(F₀)` (the `φ`-fixed series are
the constants). Strong induction on the coefficient index, using the diagonal `pⁿ` and the
unit `1 − pⁿ`. -/
private theorem phiHom_fixed_eq_C {F : PowerSeries ℤ_[p]} (h : F - phiHom p F = 0) :
    F = PowerSeries.C (PowerSeries.constantCoeff (R := ℤ_[p]) F) := by
  have hfix : phiSeries p F = F := by
    have := sub_eq_zero.1 h; rw [phiHom_apply] at this; exact this.symm
  -- every coefficient `n ≥ 1` vanishes (strong induction)
  have hvanish : ∀ n, 1 ≤ n → PowerSeries.coeff n F = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hcoeff : PowerSeries.coeff n F
          = ∑ d ∈ Finset.range (n + 1), (PowerSeries.coeff d F) •
              PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) := by
        conv_lhs => rw [← hfix]
        rw [coeff_phiSeries_split]
      rw [Finset.sum_range_succ] at hcoeff
      -- the diagonal term `F_n · [Tⁿ](Sⁿ)` and the sub-diagonal sum (all `F_d = 0`, `1≤d<n`)
      have hsub : ∀ d ∈ Finset.range n, (PowerSeries.coeff d F) •
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) = 0 := by
        intro d hd
        simp only [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with hd0 | hd0
        · subst hd0
          rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega), smul_zero]
        · rw [ih d hd (by omega), zero_smul]
      rw [Finset.sum_eq_zero hsub, zero_add, coeff_S_pow_diag] at hcoeff
      -- now `F_n = F_n · pⁿ`, i.e. `(1 − pⁿ)F_n = 0`, and `1 − pⁿ` is a unit
      have hzero : (1 - (p : ℤ_[p]) ^ n) * PowerSeries.coeff n F = 0 := by
        rw [sub_mul, one_mul]; nth_rewrite 1 [hcoeff]; rw [smul_eq_mul, mul_comm, sub_self]
      rcases mul_eq_zero.1 hzero with h1 | h2
      · exact absurd h1 (isUnit_one_sub_p_pow p hn).ne_zero
      · exact h2
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_C]
  | succ m => rw [PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m), hvanish (m + 1) (by omega)]

/-! ## `∂log` of the binomial series, and the `∂log = C c` ODE

`∂log(binomialSeries c) = C c` (the formal `(1+T)^c` has `∂log = c`), from the binomial
derivative identity `(1+T)·((1+T)^c)′ = c·(1+T)^c`. Conversely a unit `g` with `∂log g = C c`
is `C(g₀)·binomialSeries c` (the constant-coefficient-scaled binomial), since
`g·(binomialSeries c)⁻¹` has vanishing derivative. -/

/-- The descending-Pochhammer recursion for `Ring.choose` over `ℤ_[p]`:
`(n+1)·binom(r, n+1) = (r − n)·binom(r, n)` (re-derivation of the `GaloisAction` private
helper; engine of the binomial-series derivative identity). -/
private theorem succ_mul_ringChoose (r : ℤ_[p]) (n : ℕ) :
    ((n : ℤ_[p]) + 1) * Ring.choose r (n + 1) = (r - (n : ℤ_[p])) * Ring.choose r n := by
  have h1 : (descPochhammer ℤ (n + 1)).smeval r
      = ((n + 1).factorial : ℤ_[p]) * Ring.choose r (n + 1) := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose r (n + 1), nsmul_eq_mul]
  have h2 : (descPochhammer ℤ n).smeval r = (n.factorial : ℤ_[p]) * Ring.choose r n := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose r n, nsmul_eq_mul]
  have hX : ((Polynomial.X : Polynomial ℤ) - (n : Polynomial ℤ)).smeval r
      = r - (n : ℤ_[p]) := by
    rw [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one,
      pow_zero, nsmul_eq_mul, mul_one]
  have hkey : ((n + 1).factorial : ℤ_[p]) * Ring.choose r (n + 1)
      = ((n.factorial : ℤ_[p]) * Ring.choose r n) * (r - (n : ℤ_[p])) := by
    rw [← h1, descPochhammer_succ_right, Polynomial.smeval_mul, h2, hX]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hkey
  have hfac : (n.factorial : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  refine mul_left_cancel₀ hfac ?_
  linear_combination hkey

/-- `coeff k (binomialSeries r) = binom(r, k)` over `ℤ_[p]`. -/
private theorem coeff_binomialSeries' (r : ℤ_[p]) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.binomialSeries ℤ_[p] r) = Ring.choose r k := by
  rw [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

/-- **The binomial-series derivative identity**: `(1+T)·(binomialSeries r)′ = r·binomialSeries
r` (re-derivation of the `GaloisAction` private helper). -/
private theorem one_add_X_mul_derivative_binomialSeries (r : ℤ_[p]) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (PowerSeries.binomialSeries ℤ_[p] r)
      = r • PowerSeries.binomialSeries ℤ_[p] r := by
  set B : PowerSeries ℤ_[p] := PowerSeries.binomialSeries ℤ_[p] r with hB
  ext n
  rw [add_mul, one_mul, map_add, PowerSeries.smul_eq_C_mul, PowerSeries.coeff_C_mul,
    coeff_binomialSeries']
  rw [PowerSeries.coeff_derivativeFun, hB, coeff_binomialSeries']
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, add_zero, Ring.choose_one_right, Ring.choose_zero_right,
      mul_one]
    push_cast
    ring
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, coeff_binomialSeries']
    have h : ((m : ℤ_[p]) + 1 + 1) * Ring.choose r (m + 1 + 1)
        = (r - ((m : ℤ_[p]) + 1)) * Ring.choose r (m + 1) := by
      have := succ_mul_ringChoose p r (m + 1)
      rwa [Nat.cast_add, Nat.cast_one] at this
    push_cast
    linear_combination h

/-- `binomialSeries c` is a unit (constant coefficient `Ring.choose c 0 = 1`). -/
private theorem isUnit_binomialSeries (c : ℤ_[p]) :
    IsUnit (PowerSeries.binomialSeries ℤ_[p] c) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_binomialSeries', Ring.choose_zero_right]
  exact isUnit_one

/-- `∂log(binomialSeries c) = C c`: from `(1+T)·(bin c)′ = c·(bin c)` and `bin c` a unit. -/
private theorem dlog_binomialSeries (c : ℤ_[p]) :
    dlog p (PowerSeries.binomialSeries ℤ_[p] c) = PowerSeries.C c := by
  rw [dlog, one_add_X_mul_derivative_binomialSeries, PowerSeries.smul_eq_C_mul, mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_binomialSeries p c), mul_one]

/-- `∂log` is additive on units (`(gh)′ = g•h′ + h•g′`, divide by the unit `gh`). -/
private theorem dlogMul {g h : PowerSeries ℤ_[p]} (hg : IsUnit g) (hh : IsUnit h) :
    dlog p (g * h) = dlog p g + dlog p h := by
  rw [dlog, dlog, dlog, PowerSeries.derivativeFun_mul, smul_eq_mul, smul_eq_mul,
    Ring.mul_inverse_rev, mul_add, add_mul,
    show (1 + PowerSeries.X) * (g * PowerSeries.derivativeFun h)
        * (Ring.inverse h * Ring.inverse g)
        = (1 + PowerSeries.X) * PowerSeries.derivativeFun h * Ring.inverse h
          * (g * Ring.inverse g) from by ring, Ring.mul_inverse_cancel _ hg, mul_one,
    show (1 + PowerSeries.X) * (h * PowerSeries.derivativeFun g)
        * (Ring.inverse h * Ring.inverse g)
        = (1 + PowerSeries.X) * PowerSeries.derivativeFun g * Ring.inverse g
          * (h * Ring.inverse h) from by ring, Ring.mul_inverse_cancel _ hh, mul_one, add_comm]

/-- `∂log 1 = 0`. -/
private theorem dlogOne : dlog p (1 : PowerSeries ℤ_[p]) = 0 := by
  rw [dlog, PowerSeries.derivativeFun_one, mul_zero, zero_mul]

/-- `Ring.inverse` of a unit is a unit. -/
private theorem isUnit_ringInverse {g : PowerSeries ℤ_[p]} (hg : IsUnit g) :
    IsUnit (Ring.inverse g) := by
  obtain ⟨v, rfl⟩ := hg; rw [Ring.inverse_unit]; exact v⁻¹.isUnit

/-- `∂log(g⁻¹) = −∂log g` for a unit `g` (from `∂log(g·g⁻¹) = ∂log 1 = 0`). -/
private theorem dlogInverse {g : PowerSeries ℤ_[p]} (hg : IsUnit g) :
    dlog p (Ring.inverse g) = - dlog p g := by
  have hgi : IsUnit (Ring.inverse g) := isUnit_ringInverse p hg
  have hmul : g * Ring.inverse g = 1 := Ring.mul_inverse_cancel _ hg
  have := dlogMul p hg hgi
  rw [hmul, dlogOne] at this
  exact eq_neg_of_add_eq_zero_right this.symm

/-- A power series with vanishing formal derivative is its constant coefficient
(re-derivation of the `LogDerivative` private helper; `ℤ_[p]` is a domain). -/
private theorem eq_C_constantCoeff_of_derivativeFun_zero {g : PowerSeries ℤ_[p]}
    (h : PowerSeries.derivativeFun g = 0) :
    g = PowerSeries.C (PowerSeries.constantCoeff (R := ℤ_[p]) g) := by
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_C]
  | succ m =>
    rw [PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m)]
    have hcoeff := congrArg (PowerSeries.coeff m) h
    rw [PowerSeries.coeff_derivativeFun, map_zero] at hcoeff
    have hne : ((m : ℤ_[p]) + 1) ≠ 0 := by
      have : ((m + 1 : ℕ) : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      push_cast at this; exact this
    rcases mul_eq_zero.1 hcoeff with h1 | h2
    · exact h1
    · exact absurd h2 hne

/-- **The `∂log = C c` ODE**: a unit `g` with `∂log g = C c` is `C(g₀)·binomialSeries c`,
`g₀ = constantCoeff g`. Both `g` and `C(g₀)·binomialSeries c` are units with the same `∂log`
(`dlog_binomialSeries` + `∂log(C g₀) = 0`) and the same constant coefficient, so their ratio
`h` has `h′ = 0`, hence `h = C(h₀)` with `h₀ = 1`. -/
private theorem eq_C_mul_binomialSeries_of_dlog_eq_C {g : PowerSeries ℤ_[p]} (hg : IsUnit g)
    {c : ℤ_[p]} (hd : dlog p g = PowerSeries.C c) :
    g = PowerSeries.C (PowerSeries.constantCoeff (R := ℤ_[p]) g)
      * PowerSeries.binomialSeries ℤ_[p] c := by
  set B := PowerSeries.binomialSeries ℤ_[p] c with hB
  have hBu : IsUnit B := isUnit_binomialSeries p c
  set Bi := Ring.inverse B with hBi
  have hBiu : IsUnit Bi := isUnit_ringInverse p hBu
  have hBBi : B * Bi = 1 := Ring.mul_inverse_cancel _ hBu
  set h := g * Bi with hh
  have hhu : IsUnit h := hg.mul hBiu
  -- `∂log h = ∂log g + ∂log Bi = C c + (−∂log B) = C c − C c = 0`
  have hdh : dlog p h = 0 := by
    rw [hh, dlogMul p hg hBiu, hd, hBi, dlogInverse p hBu, hB, dlog_binomialSeries, add_neg_cancel]
  -- `∂log h = 0` and `h` a unit ⟹ `h′ = 0` (cancel the units `1+X` and `h`)
  have hh' : PowerSeries.derivativeFun h = 0 := by
    have hunit1 : IsUnit (1 + PowerSeries.X : PowerSeries ℤ_[p]) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp
    have hd0 : (1 + PowerSeries.X) * PowerSeries.derivativeFun h * Ring.inverse h = 0 := hdh
    have hmulh : (1 + PowerSeries.X) * PowerSeries.derivativeFun h
        * (Ring.inverse h * h) = 0 := by rw [← mul_assoc, hd0, zero_mul]
    rw [Ring.inverse_mul_cancel _ hhu, mul_one] at hmulh
    rcases hunit1.exists_left_inv with ⟨w, hw⟩
    have := congrArg (w * ·) hmulh
    simp only [mul_zero, ← mul_assoc, hw, one_mul] at this
    exact this
  have hhC : h = PowerSeries.C (PowerSeries.constantCoeff (R := ℤ_[p]) h) :=
    eq_C_constantCoeff_of_derivativeFun_zero p hh'
  -- `g = h·B`, `h₀ = g₀` (since `B₀ = 1`)
  have hghB : g = h * B := by
    rw [hh, mul_assoc, show Bi * B = 1 from by rw [mul_comm]; exact hBBi, mul_one]
  have hB0 : PowerSeries.constantCoeff (R := ℤ_[p]) B = 1 := by
    rw [hB, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_binomialSeries',
      Ring.choose_zero_right]
  have hBi0 : PowerSeries.constantCoeff (R := ℤ_[p]) Bi = 1 := by
    have := congrArg (PowerSeries.constantCoeff (R := ℤ_[p])) hBBi
    rw [map_mul, hB0, one_mul, map_one] at this
    exact this
  have hh0 : PowerSeries.constantCoeff (R := ℤ_[p]) h
      = PowerSeries.constantCoeff (R := ℤ_[p]) g := by
    rw [hh, map_mul, hBi0, mul_one]
  conv_lhs => rw [hghB, hhC, hh0]

/-! ## Transport of `Col` through the Mahler bridge

`Col u = unitsCmul invCM ((𝒜⁻¹(∂log f_u)).comp extendByZero)`. `unitsCmul invCM` and
`(·).comp extendByZero` (through `ι` injective) are injective, so the kernel/image of `Col`
is governed by `res_{ℤ_p^×}(𝒜⁻¹(∂log f_u)) = μ − φψμ`, which under `𝒜` is `(1−φ)(∂log f_u)`
(`mahlerTransform_psi` + `mahlerTransform_phiSeries`). -/

/-- `𝓐(Res_{ℤ_p^×} μ) = 𝓐μ − φ(ψ 𝓐μ)`: the restriction `Res = 1 − φψ` (`res_units_eq`)
transported through `𝓐` by the two Mahler bridges (`mahlerTransform_psi`,
`mahlerTransform_phiSeries`). -/
private theorem mahlerTransform_res_units (μ : PadicMeasure p ℤ_[p]) :
    PadicMeasure.mahlerTransform p (PadicMeasure.res p (PadicMeasure.isClopen_units p) μ)
      = PadicMeasure.mahlerTransform p μ
        - phiSeries p (psiSeries p (PadicMeasure.mahlerTransform p μ)) := by
  rw [PadicMeasure.res_units_eq,
    show PadicMeasure.mahlerTransform p (μ - PadicMeasure.phi p (PadicMeasure.psi p μ))
      = PadicMeasure.mahlerTransform p μ
        - PadicMeasure.mahlerTransform p (PadicMeasure.phi p (PadicMeasure.psi p μ)) from
      map_sub (PadicMeasure.mahlerTransformₗ p) _ _,
    mahlerTransform_phiSeries, mahlerTransform_psi]

/-- `x⁻¹·` is injective on measures: `unitsCmul invCM ν = 0 ↔ ν = 0` (multiplication by the
unit-valued `x⁻¹` is undone by multiplication by `x = unitsPowCM 1`). -/
private theorem unitsCmul_invCM_eq_zero_iff (ν : PadicMeasure p ℤ_[p]ˣ) :
    PadicMeasure.unitsCmul p (PadicMeasure.invCM p) ν = 0 ↔ ν = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
  refine LinearMap.ext fun f => ?_
  have hmul : (PadicMeasure.invCM p * PadicMeasure.unitsPowCM p 1) * f = f := by
    rw [show PadicMeasure.invCM p * PadicMeasure.unitsPowCM p 1 = 1 from ?_, one_mul]
    refine ContinuousMap.ext fun v => ?_
    simp only [ContinuousMap.mul_apply, PadicMeasure.invCM, PadicMeasure.unitsPowCM,
      ContinuousMap.coe_mk, pow_one, ContinuousMap.one_apply]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have := LinearMap.congr_fun h (PadicMeasure.unitsPowCM p 1 * f)
  rw [PadicMeasure.unitsCmul_apply, ← mul_assoc, hmul, LinearMap.zero_apply] at this
  rw [this, LinearMap.zero_apply]

/-- The kernel transport: `Col u = 0 ↔ (1−φ)(∂log f_u) = 0`. Peel `unitsCmul invCM`
(`unitsCmul_invCM_eq_zero_iff`), then `(·).comp extendByZero` through `ι` injective
(`iota_comp_extendByZero`), landing on `Res_{ℤ_p^×}(𝒜⁻¹(∂log f_u)) = 0`; `𝓐` injective and
`mahlerTransform_res_units` turn this into `(1−φ)(∂log f_u) = 0` (`∂log f_u ∈ ψ=id` by
`dlog_mem_psiIdSeries`, so `φψ(∂log f_u) = φ(∂log f_u)`). -/
private theorem Col_eq_zero_iff (u : NormCompatUnits p) :
    Col p u = 0 ↔ dlog p (colemanSeries p u) - phiHom p (dlog p (colemanSeries p u)) = 0 := by
  set g := colemanSeries p u with hg
  set F := dlog p g with hF
  have hFpsi : psiSeries p F = F := dlog_mem_psiIdSeries p (colemanSeries_isUnit p u)
    (normOp_colemanSeries p u)
  rw [Col, unitsCmul_invCM_eq_zero_iff]
  rw [show ((PadicMeasure.mahlerLinearEquiv p).symm (dlog p g)).comp
      (PadicMeasure.extendByZero p) = 0
      ↔ PadicMeasure.iota p (((PadicMeasure.mahlerLinearEquiv p).symm
          (dlog p g)).comp (PadicMeasure.extendByZero p)) = 0 from
    ⟨fun h => by rw [h]; exact map_zero _, fun h => PadicMeasure.iota_injective p (by
      rw [h]; exact (map_zero _).symm)⟩]
  rw [iota_comp_extendByZero]
  rw [show PadicMeasure.res p (PadicMeasure.isClopen_units p)
        ((PadicMeasure.mahlerLinearEquiv p).symm (dlog p g)) = 0
      ↔ PadicMeasure.mahlerTransform p (PadicMeasure.res p (PadicMeasure.isClopen_units p)
          ((PadicMeasure.mahlerLinearEquiv p).symm (dlog p g))) = 0 from
    ⟨fun h => by rw [h]; exact PadicMeasure.mahlerTransform_zero p,
      fun h => PadicMeasure.mahlerTransform_injective p (by
        rw [h, PadicMeasure.mahlerTransform_zero])⟩]
  rw [mahlerTransform_res_units, PadicMeasure.mahlerLinearEquiv_symm_apply,
    PadicMeasure.mahlerTransform_ofPowerSeries, hFpsi, phiHom_apply]

/-- A principal unit (`‖x − 1‖ < 1`) that is a `(p−1)`-th root of unity is `1`: factor
`x^{p−1} − 1 = (∑_{i<p−1} xⁱ)·(x − 1)`; the geometric sum is `≡ p−1 mod (x−1)`, hence a
unit (`‖p−1‖ = 1`), so `‖x − 1‖ = ‖x^{p−1} − 1‖ = 0`. -/
private theorem oneUnit_pow_p_sub_one_eq_one {x : ℤ_[p]} (hx : ‖x - 1‖ < 1)
    (hpow : x ^ (p - 1) = 1) : x = 1 := by
  -- the powers `xⁱ` are principal units, so `xⁱ − 1` has norm `< 1`
  have hxpow1 : ∀ i : ℕ, ‖x ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ k ih =>
      have hstep : x ^ (k + 1) - 1 = x ^ k * (x - 1) + (x ^ k - 1) := by ring
      rw [hstep]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ih)
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)) hx
  -- `‖∑_{i<m}(xⁱ − 1)‖ < 1` for every `m` (ultrametric, each term `< 1`)
  have hsumlt : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (x ^ i - 1)‖ < 1 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ih (hxpow1 k))
  -- the geometric sum `S = ∑_{i<p−1} xⁱ` is a unit (`S ≡ p−1 mod (x−1)`, `‖p−1‖ = 1`)
  set S : ℤ_[p] := ∑ i ∈ Finset.range (p - 1), x ^ i with hS
  have hSsub : ‖S - ((p - 1 : ℕ) : ℤ_[p])‖ < 1 := by
    have hrw : S - ((p - 1 : ℕ) : ℤ_[p]) = ∑ i ∈ Finset.range (p - 1), (x ^ i - 1) := by
      rw [hS, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hrw]; exact hsumlt (p - 1)
  have hpm1 : ‖((p - 1 : ℕ) : ℤ_[p])‖ = 1 := by
    have h1lt : 1 < p := hp.out.one_lt
    rw [PadicInt.norm_natCast_eq_one_iff, hp.out.coprime_iff_not_dvd]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hSnorm : ‖S‖ = 1 := by
    rw [show S = ((p - 1 : ℕ) : ℤ_[p]) + (S - ((p - 1 : ℕ) : ℤ_[p])) from by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hpm1]; exact ne_of_gt hSsub),
      hpm1, max_eq_left hSsub.le]
  -- `x^{p−1} − 1 = S·(x − 1) = 0`, and `S` is a unit, so `x − 1 = 0`
  have hfact : S * (x - 1) = S * 0 := by rw [mul_zero, hS, geom_sum_mul, hpow, sub_self]
  have hSunit : IsUnit S := by rw [PadicInt.isUnit_iff, hSnorm]
  have hx0 := hSunit.mul_left_cancel hfact
  rw [sub_eq_zero] at hx0; exact hx0

/-- **RJW thm:fund exact seq (TeX 3411–3418), left-exactness**: the kernel of `Col` on
`𝒰_{∞,1}` is `ℤ_p(1)`.

The composite `Col = (x⁻¹·) ∘ Res_{ℤ_p^×} ∘ 𝒜⁻¹ ∘ ∂log ∘ colemanSeries` is pulled back:
`Col_eq_zero_iff` reduces `Col u = 0` to `(1−φ)(∂log f_u) = 0` (through `unitsCmul invCM` and
`ι` injective, `mahlerTransform_psi`); `phiHom_fixed_eq_C` then gives `∂log f_u = C c`; the
`∂log = C c` ODE (`eq_C_mul_binomialSeries_of_dlog_eq_C`) writes `f_u = C(g₀)·binomialSeries
c`; `𝒩`-fixedness (`normOp_binomialSeries`, `normOp_mul`, `normOp_C`) forces `g₀^p = g₀`, and
`g₀` is a principal unit (the interpolation `f_u(π_n) = u_n ∈ 𝒰_{∞,1}` against
`binomialSeries c(π_n) = ξ_n^c`), so `g₀ = 1` (`oneUnit_pow_p_sub_one_eq_one`); hence
`f_u = binomialSeries c` and `u_n = ξ_n^c`. Conversely `u ∈ ZpOne` gives
`f_u = binomialSeries a` (`colemanSeries_eq_binomialSeries_of_mem_ZpOne`), `∂log = C a`,
`(1−φ)(C a) = 0`.

Carries `hp2 : p ≠ 2` (errata #14): the forward direction uses `normOp_binomialSeries`, hence
the cyclotomic norm `levelNorm_zpPow_zetaSys`, which is false at `p = 2`. RJW §12 fixes `p`
odd throughout (TeX 2470); the §12.5 milestone `iwasawa_theorem` already carries `hp2`. -/
theorem mem_ker_Col_iff_mem_ZpOne (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1 p) :
    Col p u = 0 ↔ u ∈ ZpOne p := by
  rw [Col_eq_zero_iff]
  set g := colemanSeries p u with hg
  constructor
  · -- forward: `(1−φ)(∂log g) = 0 ⟹ u ∈ ZpOne`
    intro h
    set c := PowerSeries.constantCoeff (R := ℤ_[p]) (dlog p g) with hc
    have hdC : dlog p g = PowerSeries.C c := phiHom_fixed_eq_C p h
    -- ODE: `g = C(g₀)·binomialSeries c`
    have hgODE := eq_C_mul_binomialSeries_of_dlog_eq_C p (colemanSeries_isUnit p u) hdC
    set g₀ := PowerSeries.constantCoeff (R := ℤ_[p]) g with hg0
    -- `g₀` is a principal unit (interpolation against `ξ_n^c`)
    have hg0unit : ‖g₀ - 1‖ < 1 := by
      have hn1 : (1 : ℕ) ≤ 1 := le_refl 1
      have hval : ((u.elems 1 : ℂ_[p]ˣ) : ℂ_[p]) = toCp p g₀ * zpPow p (zetaSys p 1) c := by
        rw [← evalPi_colemanSeries p u hn1, hgODE,
          evalPi_mul p _ _ hn1, evalPi_binomialSeries p c hn1, evalPi_C]
      -- `toCp g₀ = u_1 · (ξ_1^c)⁻¹`, a ratio of principal units, hence principal
      have hu1 : ‖((u.elems 1 : ℂ_[p]ˣ) : ℂ_[p]) - 1‖ < 1 :=
        (mem_localUnitsOne_iff (p := p).1 (hu 1 hn1)).2
      have hzc : ‖zpPow p (zetaSys p 1) c - 1‖ < 1 :=
        norm_zpPow_sub_one_lt_one p (norm_zetaSys_sub_one_lt_one p hn1) c
      have hzcunit : zpPow p (zetaSys p 1) c ≠ 0 := by
        intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hzc; exact absurd hzc (lt_irrefl 1)
      have hzcnorm : ‖zpPow p (zetaSys p 1) c‖ = 1 := by
        have hne : ‖(1 : ℂ_[p])‖ ≠ ‖zpPow p (zetaSys p 1) c - 1‖ := by
          rw [norm_one]; exact (ne_of_lt hzc).symm
        rw [show zpPow p (zetaSys p 1) c = 1 + (zpPow p (zetaSys p 1) c - 1) from by ring,
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_left hzc.le]
      -- `toCp g₀ = u_1 · (ξ_1^c)⁻¹`
      have htoCpval : toCp p g₀ = ((u.elems 1 : ℂ_[p]ˣ) : ℂ_[p]) * (zpPow p (zetaSys p 1) c)⁻¹ := by
        rw [hval, mul_assoc, mul_inv_cancel₀ hzcunit, mul_one]
      have hsub : ‖((u.elems 1 : ℂ_[p]ˣ) : ℂ_[p]) - zpPow p (zetaSys p 1) c‖ < 1 := by
        rw [show ((u.elems 1 : ℂ_[p]ˣ) : ℂ_[p]) - zpPow p (zetaSys p 1) c
            = (((u.elems 1 : ℂ_[p]ˣ) : ℂ_[p]) - 1) + -(zpPow p (zetaSys p 1) c - 1) from by ring]
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hu1 ?_)
        rwa [norm_neg]
      -- `toCp g₀ − 1 = (u_1 − ξ_1^c)·(ξ_1^c)⁻¹`, norm `< 1`
      have hnormtoCp : ‖toCp p g₀ - 1‖ < 1 := by
        have hkey : toCp p g₀ - 1
            = (((u.elems 1 : ℂ_[p]ˣ) : ℂ_[p]) - zpPow p (zetaSys p 1) c)
              * (zpPow p (zetaSys p 1) c)⁻¹ := by
          rw [sub_mul, mul_inv_cancel₀ hzcunit, htoCpval]
        rw [hkey, norm_mul, norm_inv, hzcnorm, inv_one, mul_one]; exact hsub
      rw [← norm_toCp p (g₀ - 1), map_sub, map_one]; exact hnormtoCp
    -- `g₀` is a unit (norm `1`)
    have hg0norm : ‖g₀‖ = 1 := by
      have hne : ‖(1 : ℤ_[p])‖ ≠ ‖g₀ - 1‖ := by rw [norm_one]; exact (ne_of_lt hg0unit).symm
      rw [show g₀ = 1 + (g₀ - 1) from by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_left hg0unit.le]
    have hg0u : IsUnit g₀ := by rw [PadicInt.isUnit_iff, hg0norm]
    -- `𝒩`-fixedness forces `g₀^p = g₀`
    have hg0pow : g₀ ^ p = g₀ := by
      have hNg := normOp_colemanSeries p u
      rw [hgODE, normOp_mul, normOp_C, normOp_binomialSeries p hp2] at hNg
      have hBu : IsUnit (PowerSeries.binomialSeries ℤ_[p] c) := isUnit_binomialSeries p c
      exact PowerSeries.C_injective (hBu.mul_right_cancel (by rw [hNg]))
    have hg0one : g₀ = 1 := by
      have hpsucc : (p - 1) + 1 = p := Nat.sub_add_cancel hp.out.one_le
      have hkk : g₀ ^ (p - 1) * g₀ = 1 * g₀ := by
        rw [one_mul, ← pow_succ, hpsucc]; exact hg0pow
      exact oneUnit_pow_p_sub_one_eq_one p hg0unit (mul_right_cancel₀ hg0u.ne_zero hkk)
    -- `g = binomialSeries c`, so `u_n = ξ_n^c`
    have hgbin : g = PowerSeries.binomialSeries ℤ_[p] c := by
      rw [hg0one, map_one, one_mul] at hgODE; exact hgODE
    refine ⟨c, fun n hn => ?_⟩
    rw [← evalPi_colemanSeries p u hn, ← hg, hgbin, evalPi_binomialSeries p c hn]
  · -- backward: `u ∈ ZpOne ⟹ (1−φ)(∂log g) = 0`
    rintro ⟨a, ha⟩
    have hgbin : g = PowerSeries.binomialSeries ℤ_[p] a :=
      colemanSeries_eq_binomialSeries_of_mem_ZpOne p ha
    rw [hgbin, dlog_binomialSeries, phiHom_apply,
      show phiSeries p (PowerSeries.C a) = PowerSeries.C a from by
        rw [phiSeries]; exact PowerSeries.subst_C a, sub_self]

/-- `x⁻¹ · x = 1` on `ℤ_p^×` (pointwise; `invCM · unitsPowCM 1 = 1`). -/
private theorem invCM_mul_unitsPowCM_one :
    PadicMeasure.invCM p * PadicMeasure.unitsPowCM p 1 = 1 := by
  refine ContinuousMap.ext fun v => ?_
  simp only [ContinuousMap.mul_apply, PadicMeasure.invCM, PadicMeasure.unitsPowCM,
    ContinuousMap.coe_mk, pow_one, ContinuousMap.one_apply]
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- `(mahler 0 : C(ℤ_[p], ℤ_[p])) = 1` (`mahler 0 x = binom(x, 0) = 1`). -/
private theorem mahler_zero_eq_one : (mahler 0 : C(ℤ_[p], ℤ_[p])) = 1 := by
  refine ContinuousMap.ext fun x => ?_
  rw [mahler_apply, Ring.choose_zero_right, ContinuousMap.one_apply]

/-- **Forward inclusion of the cokernel (image `⊆` ker χ-moment)**: `Col u (unitsPowCM 1) = 0`.
The `x⁻¹`-multiplication cancels (`invCM · unitsPowCM 1 = 1`) and `extendByZero 1 = 𝟙_{ℤ_p^×}`,
so `Col u (unitsPowCM 1) = Res_{ℤ_p^×}(𝒜⁻¹(∂log f_u))(1) = constantCoeff((1−φψ)(∂log f_u))`,
which vanishes (`φ`, `ψ` fix constant coefficients; `∂log f_u ∈ ψ=id`). -/
theorem Col_apply_unitsPowCM_one_eq_zero (u : NormCompatUnits p) :
    Col p u (PadicMeasure.unitsPowCM p 1) = 0 := by
  set g := colemanSeries p u with hg
  set M := (PadicMeasure.mahlerLinearEquiv p).symm (dlog p g) with hM
  -- `Col u (unitsPowCM 1) = M (extendByZero 1) = M (𝟙_{ℤ_p^×}) = Res_{ℤ_p^×}(M)(mahler 0)`
  have hone : PadicMeasure.extendByZero p (1 : C(ℤ_[p]ˣ, ℤ_[p]))
      = (LocallyConstant.charFn ℤ_[p] (PadicMeasure.isClopen_units p) : C(ℤ_[p], ℤ_[p])) := by
    rw [show (1 : C(ℤ_[p]ˣ, ℤ_[p])) = (1 : C(ℤ_[p], ℤ_[p])).comp (PadicMeasure.unitsValCM p) from
      by ext; rfl, PadicMeasure.extendByZero_comp_unitsVal, mul_one]
  have hstep1 : Col p u (PadicMeasure.unitsPowCM p 1)
      = PadicMeasure.res p (PadicMeasure.isClopen_units p) M (mahler 0) := by
    rw [Col, ← hM, PadicMeasure.unitsCmul_apply, invCM_mul_unitsPowCM_one]
    change M (PadicMeasure.extendByZero p 1) = M (_ * mahler 0)
    rw [hone, mahler_zero_eq_one, mul_one]
  rw [hstep1, ← PadicMeasure.coeff_mahlerTransform, PowerSeries.coeff_zero_eq_constantCoeff,
    mahlerTransform_res_units]
  -- `constantCoeff(𝓐M − φ(ψ 𝓐M)) = constantCoeff 𝓐M − constantCoeff(ψ 𝓐M) = 0`
  rw [map_sub, constantCoeff_phiSeries, hM, PadicMeasure.mahlerLinearEquiv_symm_apply,
    PadicMeasure.mahlerTransform_ofPowerSeries]
  have hFpsi : psiSeries p (dlog p g) = dlog p g :=
    dlog_mem_psiIdSeries p (colemanSeries_isUnit p u) (normOp_colemanSeries p u)
  rw [hFpsi, sub_self]

/-! ## The inverse Coleman map (core): a `𝒩`-fixed unit gives a `NormCompatUnits`

The heart of the right-exactness/cokernel converse is the *surjectivity of* `colemanSeries`:
every `𝒩`-fixed unit power series `g` is `colemanSeries u` for some norm-compatible system
`u ∈ 𝒰_∞`. We build that `u` here (`invColeman`): the level-`n` unit is the evaluation
`g(π_n) = evalPi g n` (a unit of `𝒪_n`, `evalPi_mem_O` + the ring-hom inverse), and
norm-compatibility `N_{n+1,n}(g(π_{n+1})) = g(π_n)` is exactly `evalPi_normOp` together with
`𝒩 g = g`. Coleman uniqueness (`evalPi_injective`) then gives `colemanSeries (invColeman g) = g`
(`colemanSeries_invColeman`). This is the converse of `coleman_existsUnique` for the existence
clause, with no `p`-odd hypothesis (the `evalPi_normOp` bridge is `p`-uniform). -/

/-- `g(π_n) = evalPi g n ≠ 0` for a unit series `g` and `n ≥ 1`: `evalPi (·) n` is a ring
homomorphism (`evalPiHom`), so it sends the unit `g` to a unit of `ℂ_[p]`, hence nonzero. -/
private theorem evalPi_unit_ne_zero {g : PowerSeries ℤ_[p]} (hg : IsUnit g) {n : ℕ}
    (hn : 1 ≤ n) : evalPi p g n ≠ 0 := by
  obtain ⟨v, rfl⟩ := hg
  have hmul : evalPi p (v : PowerSeries ℤ_[p]) n * evalPi p (↑v⁻¹) n = 1 := by
    rw [← evalPi_mul p _ _ hn, ← Units.val_mul, mul_inv_cancel, Units.val_one, evalPi_one]
  intro h0; rw [h0, zero_mul] at hmul; exact zero_ne_one hmul

/-- **The inverse Coleman map (core construction)**: from a `𝒩`-fixed unit power series `g`,
the norm-compatible system of units `u` with `u_n = g(π_n)` (`evalPi g n`) for `n ≥ 1`
(junk `1` at level `0`). `mem`/`inv_mem` are `evalPi_mem_O` (the value and, via the ring-hom
inverse, its inverse lie in `𝒪_n`); `compat` is `evalPi_normOp` + `𝒩 g = g`. -/
def invColeman (g : PowerSeries ℤ_[p]) (hg : IsUnit g) (hN : normOp g = g) :
    NormCompatUnits p where
  elems n := if hn : 1 ≤ n then Units.mk0 (evalPi p g n) (evalPi_unit_ne_zero p hg hn) else 1
  mem n := by
    by_cases hn : 1 ≤ n
    · rw [dif_pos hn]; exact evalPi_mem_O p g hn
    · rw [dif_neg hn]; exact one_mem _
  inv_mem n := by
    by_cases hn : 1 ≤ n
    · rw [dif_pos hn]
      obtain ⟨v, hv⟩ := id hg
      rw [show ((Units.mk0 (evalPi p g n) (evalPi_unit_ne_zero p hg hn))⁻¹ : ℂ_[p])
          = evalPi p (↑v⁻¹) n from ?_]
      · exact evalPi_mem_O p _ hn
      · rw [Units.val_mk0]
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← evalPi_mul p _ _ hn,
          show (g * ↑v⁻¹ : PowerSeries ℤ_[p]) = 1 from by
            rw [← hv, ← Units.val_mul, mul_inv_cancel, Units.val_one], evalPi_one]
    · rw [dif_neg hn]; simp [one_mem (O p _)]
  compat n hn := by
    rw [dif_pos (by omega : 1 ≤ n + 1), dif_pos hn, Units.val_mk0, Units.val_mk0,
      ← evalPi_normOp g hn, hN]

/-- `colemanSeries (invColeman g) = g`: both `g` and `colemanSeries (invColeman g)` are
`𝒩`-fixed units interpolating `invColeman g` (the latter by definition, `g` by construction
of `invColeman`), so they agree by Coleman uniqueness (`evalPi_injective`). The surjectivity
of `colemanSeries` onto the `𝒩`-fixed units. -/
theorem colemanSeries_invColeman (g : PowerSeries ℤ_[p]) (hg : IsUnit g) (hN : normOp g = g) :
    colemanSeries p (invColeman p g hg hN) = g := by
  refine evalPi_injective p (fun n hn => ?_)
  rw [evalPi_colemanSeries p (invColeman p g hg hN) hn]
  change ((if hn' : 1 ≤ n then Units.mk0 (evalPi p g n) (evalPi_unit_ne_zero p hg hn') else 1 :
      ℂ_[p]ˣ) : ℂ_[p]) = evalPi p g n
  rw [dif_pos hn, Units.val_mk0]

/-- `unitsCmul g` is additive in the measure argument (it is `μ ↦ μ ∘ (g·)`, `μ`-linear). -/
private theorem unitsCmul_add (g : C(ℤ_[p]ˣ, ℤ_[p])) (μ ν : PadicMeasure p ℤ_[p]ˣ) :
    PadicMeasure.unitsCmul p g (μ + ν)
      = PadicMeasure.unitsCmul p g μ + PadicMeasure.unitsCmul p g ν :=
  LinearMap.ext fun f => by
    rw [PadicMeasure.unitsCmul_apply, LinearMap.add_apply, LinearMap.add_apply,
      PadicMeasure.unitsCmul_apply, PadicMeasure.unitsCmul_apply]

/-- **`Col` is a homomorphism** `(𝒰_∞, ·) → (Λ(ℤ_p^×), +)`: `Col (u·v) = Col u + Col v`.
`colemanSeries` is multiplicative (`colemanSeries_mul`), `∂log` turns the product into a sum
(`dlog_mul`), and the tail `𝒜⁻¹ ∘ (·).comp extendByZero ∘ unitsCmul invCM` is additive. -/
theorem Col_add (u v : NormCompatUnits p) :
    Col p (u * v) = Col p u + Col p v := by
  rw [Col, Col, Col, colemanSeries_mul p,
    dlog_mul p (colemanSeries_isUnit p u) (colemanSeries_isUnit p v), map_add,
    LinearMap.add_comp, ← unitsCmul_add]

/-- **The measure-inversion step of the cokernel converse**: every `μ` killed by the
`χ`-moment (`μ(unitsPowCM 1) = 0`) is `Col (invColeman g)` for a `𝒩`-fixed unit `g`.
Construction: set `μ'' = (unitsPowCM 1)·μ` and `H = 𝒜(ι μ'')`. Then `H ∈ ℤ_p⟦T⟧^{ψ=0}`
(`ι μ''` is unit-supported, `res_iota` + `isSupportedOn_units_iff_psi_eq_zero`, transported
by `mahlerTransform_psi`) with `H(0) = (ι μ'')(1) = μ(unitsPowCM 1) = 0`; so
`exists_one_sub_phi_eq` gives a `ψ=id` series `F₀` with `(1−φ)F₀ = H`, and
`dlog_surjective_onto_psiId` a `𝒩`-fixed unit `g` with `∂log g = F₀`. Reversing the transport
(`iota_comp_extendByZero`, `mahlerTransform_res_units`, `𝒜` injective) gives
`(𝒜⁻¹ F₀).comp extendByZero = μ''`, and `unitsCmul invCM` undoes the `(unitsPowCM 1)·`,
so `Col (invColeman g) = μ`. No `p`-odd hypothesis. -/
theorem exists_invColeman_Col_eq (μ : PadicMeasure p ℤ_[p]ˣ)
    (hμ : μ (PadicMeasure.unitsPowCM p 1) = 0) :
    ∃ (g : PowerSeries ℤ_[p]) (hg : IsUnit g) (hN : normOp g = g),
      Col p (invColeman p g hg hN) = μ := by
  set μ'' : PadicMeasure p ℤ_[p]ˣ := PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1) μ
    with hμ''
  set H : PowerSeries ℤ_[p] := PadicMeasure.mahlerTransform p (PadicMeasure.iota p μ'') with hH
  -- `H ∈ ψ=0`: `ι μ''` is unit-supported, so `ψ(ι μ'') = 0`, hence `ψ-series H = 0`
  have hpsiiota : PadicMeasure.psi p (PadicMeasure.iota p μ'') = 0 :=
    (PadicMeasure.isSupportedOn_units_iff_psi_eq_zero p _).1 (PadicMeasure.res_iota p μ'')
  have hHmem : H ∈ psiZeroSeries p := by
    change psiSeries p H = 0
    rw [hH, ← mahlerTransform_psi, hpsiiota, PadicMeasure.mahlerTransform_zero]
  -- `H(0) = (ι μ'')(1) = μ(unitsPowCM 1) = 0`
  have hHcc : PowerSeries.constantCoeff H = 0 := by
    rw [hH, ← PowerSeries.coeff_zero_eq_constantCoeff, PadicMeasure.coeff_mahlerTransform,
      mahler_zero_eq_one, PadicMeasure.iota, PadicMeasure.pushforward_apply,
      show (1 : C(ℤ_[p], ℤ_[p])).comp (PadicMeasure.unitsValCM p) = 1 from by ext; rfl,
      hμ'', PadicMeasure.unitsCmul_apply, mul_one]
    exact hμ
  -- `ψ=id` series `F₀` with `(1−φ)F₀ = H`, then a `𝒩`-fixed unit `g` with `∂log g = F₀`
  obtain ⟨F₀, hF₀mem, hF₀eq⟩ := exists_one_sub_phi_eq p hHmem hHcc
  obtain ⟨g, hgu, hgN, hgdlog⟩ := dlog_surjective_onto_psiId p hF₀mem
  refine ⟨g, hgu, hgN, ?_⟩
  -- `(𝒜⁻¹ F₀).comp extendByZero = μ''` (reverse the restriction transport)
  have hρ : ((PadicMeasure.mahlerLinearEquiv p).symm F₀).comp (PadicMeasure.extendByZero p)
      = μ'' := by
    refine PadicMeasure.iota_injective p ?_
    rw [iota_comp_extendByZero]
    refine PadicMeasure.mahlerTransform_injective p ?_
    rw [mahlerTransform_res_units, PadicMeasure.mahlerLinearEquiv_symm_apply,
      PadicMeasure.mahlerTransform_ofPowerSeries, show psiSeries p F₀ = F₀ from hF₀mem, ← hH,
      show phiSeries p F₀ = phiHom p F₀ from (phiHom_apply p F₀).symm]
    linear_combination (norm := ring_nf) hF₀eq
  -- `unitsCmul invCM` undoes the `(unitsPowCM 1)·`
  rw [Col, colemanSeries_invColeman p g hgu hgN, hgdlog, hρ]
  refine LinearMap.ext fun f => ?_
  rw [PadicMeasure.unitsCmul_apply, hμ'', PadicMeasure.unitsCmul_apply, ← mul_assoc,
    show PadicMeasure.unitsPowCM p 1 * PadicMeasure.invCM p = 1 from by
      rw [mul_comm]; exact invCM_mul_unitsPowCM_one p, one_mul]

/-! ## The ℤ_[p]-Teichmüller principal split (cokernel converse, sorry-free)

The cokernel converse `ker ⊆ image` needs to turn the preimage `u₀ = invColeman g`
(`Col u₀ = μ`) into a *principal* preimage `w ∈ 𝒰_{∞,1}`. RJW splits off the Teichmüller
part; the project's deferred `normCompat_eq_teichmuller_mul_principal` does this through the
`𝒪_n`-residue section (still unbuilt). We avoid that entirely with the **constant**
`ℤ_[p]`-Teichmüller system `v.elems n = ω(a)` (`a = constantCoeff g`), built from the
already-formalised `ℤ_[p]` Teichmüller `teichmullerFun` of `Interpolation/Branches.lean`: it
is norm-compatible (`levelNorm_const_eq_pow` + `ω(a)^{p−1}=1`), `(p−1)`-torsion (so
`Col v = 0`), and `w := u₀·v⁻¹` is principal because `g(π_n) ≡ a mod 𝔭_n` and
`a·ω(a)⁻¹ ≡ 1 mod p`. -/

/-- The **constant `ℤ_[p]`-Teichmüller system**: every level is `toCp(ω(a))`, the image in
`ℂ_[p]` of the `ℤ_[p]`-Teichmüller representative `ω(a)` of a unit `a` (`teichmullerFun`). It
is norm-compatible: `N_{n+1,n}(ω(a)) = ω(a)^p = ω(a)` (`levelNorm_const_eq_pow` plus
`ω(a)^{p−1} = 1` ⟹ `ω(a)^p = ω(a)`); `ω(a) ∈ ℚ_p ⊂ K_n` gives the `𝒪_n`-memberships. -/
private def teichNCU (a : ℤ_[p]ˣ) : NormCompatUnits p where
  elems _ := Units.map (toCp p).toMonoidHom (PadicInt.isUnit_teichmullerFun p a).unit
  mem n := by
    change toCp p ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p]) ∈ O p n
    refine Subring.mem_inf.2 ⟨?_, ?_⟩
    · change toCp p _ ∈ K p n
      rw [toCp, RingHom.comp_apply]
      exact IntermediateField.algebraMap_mem (K p n) _
    · change ‖toCp p ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p])‖ ≤ 1
      rw [norm_toCp]; exact PadicInt.norm_le_one _
  inv_mem n := by
    rw [← Units.val_inv_eq_inv_val, ← map_inv, Units.coe_map]
    change toCp p (((PadicInt.isUnit_teichmullerFun p a).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ∈ O p n
    refine Subring.mem_inf.2 ⟨?_, ?_⟩
    · change toCp p _ ∈ K p n
      rw [toCp, RingHom.comp_apply]
      exact IntermediateField.algebraMap_mem (K p n) _
    · change ‖toCp p (((PadicInt.isUnit_teichmullerFun p a).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖ ≤ 1
      rw [norm_toCp]; exact PadicInt.norm_le_one _
  compat n hn := by
    have hmemK : (toCp p ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p])) ∈ K p n := by
      rw [toCp, RingHom.comp_apply]; exact IntermediateField.algebraMap_mem (K p n) _
    change levelNorm p n (toCp p ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p]))
      = toCp p ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p])
    rw [levelNorm_const_eq_pow p hn hmemK, ← map_pow]
    congr 1
    have hpow : ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p]) ^ (p - 1) = 1 := by
      rw [IsUnit.unit_spec]; exact PadicInt.teichmullerFun_pow_card_sub_one p a
    have hpsucc : (p - 1) + 1 = p := Nat.sub_add_cancel hp.out.one_le
    have hxp : ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p]) ^ p
        = ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p]) ^ (p - 1)
          * ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p]) := by
      rw [← pow_succ, hpsucc]
    rw [hxp, hpow, one_mul]

/-- `teichNCU a` is `(p−1)`-torsion: `(ω(a))^{p−1} = 1` (`teichmullerFun_pow_card_sub_one`). -/
private theorem teichNCU_torsion (a : ℤ_[p]ˣ) (n : ℕ) :
    (teichNCU p a).elems n ^ (p - 1) = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (toCp p ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p])) ^ (p - 1) = 1
  rw [IsUnit.unit_spec, ← map_pow, PadicInt.teichmullerFun_pow_card_sub_one p a, map_one]

/-- The `ℂ_[p]`-value of `teichNCU a` at any level is `toCp(ω(a))`. -/
private theorem teichNCU_elems (a : ℤ_[p]ˣ) (n : ℕ) :
    ((teichNCU p a).elems n : ℂ_[p]) = toCp p (PadicInt.teichmullerFun p (a : ℤ_[p])) := by
  change (toCp p ((PadicInt.isUnit_teichmullerFun p a).unit : ℤ_[p])) = _
  rw [IsUnit.unit_spec]

/-- `‖g(π_n) − toCp(constantCoeff g)‖ < 1` for `n ≥ 1`: `g(π_n) ≡ g₀ mod 𝔭_n`, because
`g − C g₀ = X·U` evaluates at `π_n` to `π_n · U(π_n)`, of norm `≤ ‖π_n‖ < 1`. -/
private theorem norm_evalPi_sub_constantCoeff_lt_one (g : PowerSeries ℤ_[p]) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖evalPi p g n - toCp p (PowerSeries.constantCoeff g)‖ < 1 := by
  set g₀ := PowerSeries.constantCoeff (R := ℤ_[p]) g with hg0
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff (φ := g - PowerSeries.C g₀)).2 (by
    rw [map_sub, PowerSeries.constantCoeff_C, ← hg0, sub_self])
  have hrw : evalPi p g n - toCp p g₀ = pi p n * evalPi p U n := by
    rw [← evalPi_C p g₀ n, ← evalPi_sub p g (PowerSeries.C g₀) hn, hU,
      evalPi_mul p _ _ hn, evalPi_X]
  rw [hrw, norm_mul]
  have hUle : ‖evalPi p U n‖ ≤ 1 := (Subring.mem_inf.1 (evalPi_mem_O p U hn)).2
  calc ‖pi p n‖ * ‖evalPi p U n‖ ≤ ‖pi p n‖ * 1 :=
        mul_le_mul_of_nonneg_left hUle (norm_nonneg _)
    _ = ‖pi p n‖ := mul_one _
    _ < 1 := norm_pi_lt_one p hn

/-- **RJW thm:fund exact seq, right-exactness / cokernel**: the image of `Col` on
`𝒰_{∞,1}` is the kernel of the `χ`-moment `μ ↦ ∫_𝒢 χ·μ = μ(x)` (cokernel `ℤ_p(1)`).

The forward inclusion `image(Col) ⊆ ker(χ-moment)` is `Col_apply_unitsPowCM_one_eq_zero`:
`Col u (unitsPowCM 1) = constantCoeff((1−φψ)(∂log f_u)) = 0`, since `φ` and `ψ` both fix the
constant coefficient (`∂log f_u ∈ ψ=id`).

The converse `ker ⊆ image` is assembled from three pieces. (1) The **inverse Coleman map**
`invColeman` (above) realises any `𝒩`-fixed unit `g` as `colemanSeries (invColeman g)`
(`colemanSeries_invColeman`), with `compat` from `evalPi_normOp`. (2) `exists_invColeman_Col_eq`
solves `Col (invColeman g) = μ` for such a `g` by inverting the measure transport off the
diagram `ℤ_p⟦T⟧^{ψ=id} →[1−φ] ℤ_p⟦T⟧^{ψ=0} → ℤ_p` (`exists_one_sub_phi_eq` +
`dlog_surjective_onto_psiId`, `mahlerTransform_psi`/`_res_units`, `iota_comp_extendByZero`),
the `μ(unitsPowCM 1)=0` condition feeding the `F(0)=0` hypothesis. (3) The resulting
`u₀ = invColeman g` need not be *principal*; instead of the deferred `𝒪_n`-residue split, we
divide off the **constant `ℤ_[p]`-Teichmüller system** `v = teichNCU a` for `a = constantCoeff
g` (a unit since `g` is): `Col v = 0` (`Col_eq_zero_of_torsion` + `teichNCU_torsion`), so by
`Col_add` `Col (u₀·v⁻¹) = Col u₀ = μ`, and `w := u₀·v⁻¹` is principal because
`g(π_n) ≡ a mod 𝔭_n` (`norm_evalPi_sub_constantCoeff_lt_one`) and `a·ω(a)⁻¹ ≡ 1 mod p`
(`teichmullerFun_sub_self_mem`), so `w.elems n ≡ 1 mod 𝔭_n`.

This `←` direction is now genuinely sorry-free: it no longer uses the deferred
`normCompat_eq_teichmuller_mul_principal` (only the already-formalised `ℤ_[p]` Teichmüller of
`Interpolation/Branches.lean`). No `p`-odd hypothesis enters the converse. -/
theorem range_Col_eq_ker_chiMoment (μ : PadicMeasure p ℤ_[p]ˣ) :
    (∃ u ∈ unitsTower1 p, Col p u = μ) ↔ μ (PadicMeasure.unitsPowCM p 1) = 0 := by
  constructor
  · -- forward: `Col u = μ ⟹ μ(unitsPowCM 1) = Col u (unitsPowCM 1) = 0`
    rintro ⟨u, -, rfl⟩
    exact Col_apply_unitsPowCM_one_eq_zero p u
  · -- converse: inverse Coleman map + constant ℤ_[p]-Teichmüller principal split
    intro hμ
    obtain ⟨g, hgu, hgN, hCol⟩ := exists_invColeman_Col_eq p μ hμ
    set u₀ := invColeman p g hgu hgN with hu0
    -- `a := constantCoeff g`, a unit; `v := teichNCU a`, `w := u₀ · v⁻¹`
    set aU : ℤ_[p]ˣ := (PowerSeries.isUnit_iff_constantCoeff.1 hgu).unit with haU
    have haUval : (aU : ℤ_[p]) = PowerSeries.constantCoeff g := IsUnit.unit_spec _
    set v := teichNCU p aU with hv
    set w := u₀ * v⁻¹ with hw
    -- the level-`n` value of `u₀` is `g(π_n)`
    have hu0elems : ∀ {n : ℕ}, 1 ≤ n → ((u₀.elems n : ℂ_[p]ˣ) : ℂ_[p]) = evalPi p g n := by
      intro n hn
      change ((if h : 1 ≤ n then Units.mk0 (evalPi p g n)
          (evalPi_unit_ne_zero p hgu h) else 1 : ℂ_[p]ˣ) : ℂ_[p]) = _
      rw [dif_pos hn, Units.val_mk0]
    -- the level-`n` value of `w` is `g(π_n)·(toCp ω(a))⁻¹`
    have hwelems : ∀ {n : ℕ}, 1 ≤ n → ((w.elems n : ℂ_[p]ˣ) : ℂ_[p])
        = evalPi p g n * (toCp p (PadicInt.teichmullerFun p (aU : ℤ_[p])))⁻¹ := by
      intro n hn
      have hval : ((w.elems n : ℂ_[p]ˣ) : ℂ_[p])
          = ((u₀.elems n : ℂ_[p]ˣ) : ℂ_[p]) * ((v.elems n : ℂ_[p]ˣ) : ℂ_[p])⁻¹ := by
        change ((u₀.elems n * (v.elems n)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = _
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
      rw [hval, hu0elems hn, teichNCU_elems p aU n]
    -- `toCp ω(a)` is a unit of norm `1`
    have hzetanorm : ‖PadicInt.teichmullerFun p (aU : ℤ_[p])‖ = 1 :=
      PadicInt.isUnit_iff.1 (PadicInt.isUnit_teichmullerFun p aU)
    have hzeta0 : toCp p (PadicInt.teichmullerFun p (aU : ℤ_[p])) ≠ 0 := by
      rw [← norm_pos_iff, norm_toCp, hzetanorm]; exact one_pos
    -- `w ∈ 𝒰_{∞,1}`: each `w.elems n` is a principal unit
    have hwmem : w ∈ unitsTower1 p := by
      intro n hn
      have hinv : ((w.elems n)⁻¹ : ℂ_[p]ˣ).val ∈ O p n := by
        rw [Units.val_inv_eq_inv_val]; exact w.inv_mem n
      refine (mem_localUnitsOne_iff (p := p)).2 ⟨⟨w.mem n, hinv⟩, ?_⟩
      rw [hwelems hn]
      -- `g(π_n)·ζ⁻¹ − 1 = (g(π_n) − ζ)·ζ⁻¹`, with `‖g(π_n) − ζ‖ < 1` and `‖ζ⁻¹‖ = 1`
      set ζ := toCp p (PadicInt.teichmullerFun p (aU : ℤ_[p])) with hζ
      have hζnorm : ‖ζ‖ = 1 := by rw [hζ, norm_toCp, hzetanorm]
      have hsub : ‖evalPi p g n - ζ‖ < 1 := by
        -- `g(π_n) − ζ = (g(π_n) − toCp a) + toCp(a − ω(a))`, both summands of norm `< 1`
        have h1 : ‖evalPi p g n - toCp p (PowerSeries.constantCoeff g)‖ < 1 :=
          norm_evalPi_sub_constantCoeff_lt_one p g hn
        have h2 : ‖toCp p (PowerSeries.constantCoeff g) - ζ‖ < 1 := by
          rw [hζ, ← haUval, ← map_sub, norm_toCp]
          have hmem : (aU : ℤ_[p]) - PadicInt.teichmullerFun p (aU : ℤ_[p])
              ∈ (Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) := by
            rw [pow_one]
            have := PadicInt.teichmullerFun_sub_self_mem p (aU : ℤ_[p])
            rwa [show (aU : ℤ_[p]) - PadicInt.teichmullerFun p (aU : ℤ_[p])
              = -(PadicInt.teichmullerFun p (aU : ℤ_[p]) - (aU : ℤ_[p])) by ring,
              neg_mem_iff]
          rw [← PadicInt.norm_le_pow_iff_mem_span_pow] at hmem
          refine lt_of_le_of_lt hmem ?_
          rw [Nat.cast_one, zpow_neg, zpow_one]
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
        have hsplit : evalPi p g n - ζ
            = (evalPi p g n - toCp p (PowerSeries.constantCoeff g))
              + (toCp p (PowerSeries.constantCoeff g) - ζ) := by ring
        rw [hsplit]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
      have hkey : evalPi p g n * ζ⁻¹ - 1 = (evalPi p g n - ζ) * ζ⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hzeta0]
      rw [hkey, norm_mul, norm_inv, hζnorm, inv_one, mul_one]
      exact hsub
    refine ⟨w, hwmem, ?_⟩
    -- `Col w = Col u₀ + Col v⁻¹ = Col u₀ = μ` (`v⁻¹` is `(p−1)`-torsion, so `Col v⁻¹ = 0`)
    have hvinv : Col p v⁻¹ = 0 := by
      refine Col_eq_zero_of_torsion p v⁻¹ (fun n => ?_)
      have hpow : (v⁻¹.elems n) ^ (p - 1) = ((v.elems n) ^ (p - 1))⁻¹ := by
        rw [show v⁻¹.elems n = (v.elems n)⁻¹ from rfl, inv_pow]
      rw [hpow, teichNCU_torsion p aU, inv_one]
    have hsplit : Col p w = Col p u₀ + Col p v⁻¹ := by rw [hw, Col_add]
    rw [hsplit, hvinv, add_zero, hu0, hCol]

end PadicLFunctions.Coleman
