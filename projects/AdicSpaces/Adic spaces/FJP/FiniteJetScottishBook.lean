/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetMain
import «Adic spaces».NoetherianTateModules
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The finite-jet algebra answers Nonarchimedean Scottish Book Problems 24 and 28

The [FJP] pinching algebra `𝓐` (a complete uniform nonnoetherian sheafy Tate domain)
together with the element `f = Q²` and the chart datum `α = (W; ϖ)` settles two problems
from Kedlaya's *Nonarchimedean Scottish Book*.

Everything analytic is already proved in `FiniteJetChart.lean`; this file only assembles
the two answers. The two inputs are:

* **the (3.3) collapse** `canonicalMap_Qa_sq`: `ρ(Q)² = 0` in `𝓐⟨W/ϖ⟩`, where
  `ρ = (chartDatum F).canonicalMap` is the rational-localization map. Note this is a
  *completion* phenomenon: `ϖ` is already a unit of the Tate ring `𝓐`, so the algebraic
  localization `Localization.Away ϖ` is just `𝓐` itself, in which `Q² ≠ 0`;
* **multiplicativity of the Gauss norm** `norm_JetA_mul`, giving `‖Q²a‖ = ‖a‖`, i.e.
  multiplication by `Q²` is an *isometry* — no open-mapping theorem is needed.

## Main results

* `scottishWitness_mul_isometry` / `_injective` / `_isStrictMap` / `_range_isClosed` —
  multiplication by `Q²` is a strict inclusion with closed image.
* `canonicalMap_scottishWitness` — `Q²` restricts to `0` on the rational subset
  `U = R(W/ϖ) = {|W| ≤ |ϖ| ≠ 0}`.
* `nontrivial_chart` — `𝒪_X(U) ≅ 𝓑 ≠ 0`, so `U` is not the degenerate empty chart.
* **Problem 28** (`finiteJet_problem28`): affirmative — such a pair `(f, U)` exists.
* **Problem 24** (`finiteJet_not_flat_canonicalMap`): negative — the completed rational
  localization `𝓐 → 𝓐⟨W/ϖ⟩` is **not flat**. Indeed flatness would make the
  nonzerodivisor `Q²` act injectively on `𝓐⟨W/ϖ⟩`, but it acts as `0` on a nonzero ring.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problems 24 and 28.
* [FJP] §3 (Proposition 3.1, Corollary 3.2) — the chart `𝓐⟨W/ϖ⟩ ≅ K⟨X,Q⟩/(Q²)`.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum

variable (F : Type*) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
  [IsFJPBase F]

local notation "K" => F

noncomputable section

/-! ### The witness ring

What makes the two answers below *strong* is the quality of the ring they use: `𝓐` is a
complete uniform **sheafy** Tate domain, failing only to be noetherian. Both problems are
known in the strongly noetherian case (Huber), so a counterexample is only interesting in
exactly this regime. -/

/-- **The witness ring is as good as it can be** ([FJP] Theorem 1.3): `𝓐` is a Tate ring,
sheafy, uniform, a domain, and **not** noetherian — precisely the regime that Problems 24
and 28 leave open. -/
theorem finiteJet_witnessRing_quality [IsFJPNoetherianBase F] :
    IsTateRing (JetA F) ∧
    ValuationSpectrum.IsSheafy (JetA F) ∧
    TopologicalRing.IsUniform (JetA F) ∧
    IsDomain (JetA F) ∧
    ¬ IsNoetherianRing (JetA F) :=
  ⟨inferInstance, finiteJet_isSheafy F, finiteJet_isUniform F, finiteJet_isDomain F,
    finiteJet_not_noetherian F⟩

/-! ### The witness element `f = Q²` and its norm -/

/-- The Scottish Book witness element `f = Q² ∈ 𝓐`. In the Milnor-square description
`Q = (Q, Q) ∈ 𝓑₀ × 𝓒₀`, so `Q² = (0, Q²)`: it dies in the `𝓑`-component but not in the
`𝓒`-component, hence is a nonzero element of `𝓐`. -/
def scottishWitness : JetA F := Qa F ^ 2

/-- `‖Q‖ = 1`: the jet of `Q` is the square-zero generator, of dual-number norm one. -/
theorem norm_Qa : ‖Qa F‖ = 1 := by
  show ‖sectionD F (TrivSqZeroExt.inr (1 : L F))‖ = 1
  rw [norm_sectionD, JetNorm.norm_def]
  simp

/-- `‖Q²‖ = 1` (the Gauss norm on `𝓐` is multiplicative). -/
theorem norm_scottishWitness : ‖scottishWitness F‖ = 1 := by
  rw [scottishWitness, norm_JetA_pow, norm_Qa, one_pow]

/-- **The central analytic fact**: multiplication by `Q²` preserves the norm exactly.
Elementary in coefficients — it shifts every `Q`-coefficient two places to the right,
with no cancellation. -/
theorem norm_scottishWitness_mul (a : JetA F) : ‖scottishWitness F * a‖ = ‖a‖ := by
  rw [norm_JetA_mul, norm_scottishWitness, one_mul]

theorem scottishWitness_ne_zero : scottishWitness F ≠ 0 := by
  intro h
  have := norm_scottishWitness F
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-! ### Multiplication by `Q²` is a strict inclusion with closed image -/

/-- Multiplication by `Q²` is an **isometry** of `𝓐`. This single fact gives injectivity,
strictness and closedness of the image at once, with no appeal to a nonarchimedean open
mapping theorem. -/
theorem scottishWitness_mul_isometry :
    Isometry (fun a : JetA F => scottishWitness F * a) := by
  refine Isometry.of_dist_eq fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_scottishWitness_mul]

/-- `Q²` is a non-zero-divisor: multiplication by it is injective. -/
theorem scottishWitness_mul_injective :
    Function.Injective (fun a : JetA F => scottishWitness F * a) :=
  (scottishWitness_mul_isometry F).injective

theorem scottishWitness_mul_continuous :
    Continuous (fun a : JetA F => scottishWitness F * a) :=
  (scottishWitness_mul_isometry F).continuous

/-- The image `Q²𝓐` is **closed**: an isometric embedding of a complete space has closed
range. -/
theorem scottishWitness_mul_range_isClosed :
    IsClosed (Set.range fun a : JetA F => scottishWitness F * a) :=
  (scottishWitness_mul_isometry F).isClosedEmbedding.isClosed_range

/-- Multiplication by `Q²` is **strict**: open onto its image (the range factorization is
the isometric equivalence `𝓐 ≃ᵢ Q²𝓐`, hence a homeomorphism). -/
theorem scottishWitness_mul_isStrictMap :
    IsStrictMap (fun a : JetA F => scottishWitness F * a) := by
  have hm := scottishWitness_mul_isometry F
  have hfun : Set.rangeFactorization (fun a : JetA F => scottishWitness F * a) =
      hm.isometryEquivOnRange := rfl
  show IsOpenMap (Set.rangeFactorization _)
  rw [hfun]
  exact hm.isometryEquivOnRange.toHomeomorph.isOpenMap

/-- `Q²` is a nonzerodivisor of `𝓐` (`𝓐` is a domain and `Q² ≠ 0`). -/
theorem scottishWitness_mem_nonZeroDivisors :
    scottishWitness F ∈ nonZeroDivisors (JetA F) :=
  mem_nonZeroDivisors_of_ne_zero (scottishWitness_ne_zero F)

/-! ### `Q²` restricts to zero on the chart `U = R(W/ϖ)` -/

/-- **`Q²` dies in the completed rational localization** — [FJP] (3.3), through the
already-proved `canonicalMap_Qa_sq`. This is a completion phenomenon: `ϖ` is a unit of
`𝓐`, so the *algebraic* localization at `ϖ` is `𝓐` itself, where `Q² ≠ 0`; the element
becomes zero only after imposing that `W/ϖ` be power-bounded and completing. -/
theorem canonicalMap_scottishWitness :
    (chartDatum F).canonicalMap (scottishWitness F) = 0 := by
  rw [scottishWitness, sq, map_mul]
  exact canonicalMap_Qa_sq F

/-- The square-zero disc algebra `𝓑 = K⟨X⟩[Q]/(Q²)` is a nonzero ring (`‖1‖ = 1 ≠ 0`). -/
theorem nontrivial_JetB : Nontrivial (JetB F) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have hn := congrArg (norm : JetB F → ℝ) h
  rw [norm_zero, norm_one] at hn
  exact zero_ne_one hn

/-- The chart `𝒪_X(U) = 𝓐⟨W/ϖ⟩ ≅ 𝓑` is a **nonzero** ring ([FJP] Prop 3.1), so the
vanishing above is not the degenerate "empty rational subset" phenomenon. -/
theorem nontrivial_chart : Nontrivial (presheafValue (chartDatum F)) :=
  have := nontrivial_JetB F
  (chartEquiv F).toEquiv.nontrivial

/-! ### The rational subset `U = R(W/ϖ)` is nonempty

Problem 28 does not say "nonempty", but the empty rational subset would be an
uninteresting loophole, so we rule it out by exhibiting a point. The point is the origin
`x₀₀`: evaluate the disc component at `W = 0`. Concretely `ev₀₀ : 𝓐 → K` sends
`f₀(W) + Qf₁(W) + Q²h ↦ f₀(0)`, factoring as `𝓐 → 𝓑 → K⟨X⟩ → K` (jet, disc component,
constant coefficient). Pulling the norm valuation of `K` back along `ev₀₀` gives a point
with `|W| = 0 ≤ |ϖ| ≠ 0`. -/

/-- The disc component `𝓑 → K⟨X⟩`, as a ring homomorphism. -/
def jetBFst : JetB F →+* PowerSeries.Restricted K (1 : ℝ) where
  toFun x := x.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' x y := TrivSqZeroExt.fst_mul x y
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' x y := TrivSqZeroExt.fst_add x y

/-- The constant coefficient `K⟨X⟩ → K`, as a ring homomorphism. -/
def constCoeffKW : PowerSeries.Restricted K (1 : ℝ) →+* K where
  toFun f := PowerSeries.constantCoeff f.1
  map_one' := map_one PowerSeries.constantCoeff
  map_mul' f g := map_mul PowerSeries.constantCoeff f.1 g.1
  map_zero' := map_zero PowerSeries.constantCoeff
  map_add' f g := map_add PowerSeries.constantCoeff f.1 g.1

/-- **The origin evaluation** `ev₀₀ : 𝓐 → K`, `f₀(W) + Qf₁(W) + Q²h ↦ f₀(0)`: discard the
terms of `Q`-degree `≥ 1` (the map to `𝓑`), then evaluate the disc component at `W = 0`. -/
def ev00 : JetA F →+* K :=
  (constCoeffKW F).comp ((jetBFst F).comp (jB F))

/-- `ev₀₀` is norm-nonincreasing (each of the three factors is). -/
theorem norm_ev00_le (a : JetA F) : ‖ev00 F a‖ ≤ ‖a‖ := by
  calc ‖ev00 F a‖ = ‖PowerSeries.coeff 0 ((jB F a).fst).1‖ := by
        rw [show ev00 F a = PowerSeries.constantCoeff ((jB F a).fst).1 from rfl,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    _ ≤ ‖(jB F a).fst‖ := norm_psCoeff_le _ 0
    _ ≤ ‖jB F a‖ := by rw [JetNorm.norm_def]; exact le_max_left _ _
    _ ≤ ‖a‖ := norm_jB_le F a

theorem ev00_continuous : Continuous (ev00 F) := by
  have hlip : LipschitzWith 1 (ev00 F) := LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_ev00_le F _
  exact hlip.continuous

/-- The origin kills `W` — this is what puts the point inside `{|W| ≤ |ϖ|}`. -/
theorem ev00_Wa : ev00 F (Wa F) = 0 := by
  show PowerSeries.constantCoeff ((jB F (Wa F)).fst).1 = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_jB_Wa_fst]
  norm_num

/-- The origin does not kill the pseudouniformizer. -/
theorem ev00_tA : ev00 F (tA F) = ϖ F := by
  show PowerSeries.constantCoeff ((jB F (tA F)).fst).1 = _
  rw [jB_tA]
  show PowerSeries.constantCoeff ((constHomPS F (ϖ F)).1 :
    PowerSeries K) = _
  show PowerSeries.constantCoeff (PowerSeries.C (ϖ F)) = _
  rw [PowerSeries.constantCoeff_C]

/-- The rank-one valuation of `𝓐` at the origin of the disc: `a ↦ |ev₀₀ a|`. -/
noncomputable def ev00Val : Valuation (JetA F) NNReal where
  toFun a := ‖ev00 F a‖₊
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by rw [map_mul, nnnorm_mul]
  map_add_le_max' a b := by
    have h := IsUltrametricDist.norm_add_le_max (ev00 F a) (ev00 F b)
    rw [← map_add] at h
    exact_mod_cast h

@[simp] theorem ev00Val_apply (a : JetA F) : ev00Val F a = ‖ev00 F a‖₊ := rfl

theorem ev00Val_isContinuous : (ev00Val F).IsContinuous := by
  intro γ
  have hset : {a : JetA F | ev00Val F a < γ} = ev00 F ⁻¹' Metric.ball 0 ((γ : ℝ)) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      ev00Val_apply]
    exact_mod_cast Iff.rfl
  rw [hset]
  exact Metric.isOpen_ball.preimage (ev00_continuous F)

/-- **The origin is a point of `Spa(𝓐, 𝓐°)`.** -/
def innerPoint : Spv (JetA F) := ofValuation (ev00Val F)

theorem innerPoint_mem_spa : innerPoint F ∈ Spa (JetA F) (JetA F)⁺ := by
  refine ⟨isContinuous_ofValuation_of _ (ev00Val_isContinuous F), fun f hf => ?_⟩
  show ev00Val F f ≤ ev00Val F 1
  rw [map_one]
  have hf1 : ‖f‖ ≤ 1 := (isPowerBounded_JetA_iff F f).mp hf
  have hle : ‖ev00 F f‖ ≤ 1 := (norm_ev00_le F f).trans hf1
  show ‖ev00 F f‖₊ ≤ 1
  exact_mod_cast hle

/-- **The chart is nonempty**: the origin `x₀₀` satisfies `|W| = 0 ≤ |ϖ| ≠ 0`, so it lies
in the rational subset `U = R(W/ϖ)`. -/
theorem innerPoint_mem_rationalOpen :
    innerPoint F ∈ rationalOpen (chartDatum F).T (chartDatum F).s := by
  classical
  have hϖ : ev00Val F (tA F) ≠ 0 := by
    simp only [ev00Val_apply, ne_eq, nnnorm_eq_zero, ev00_tA]
    exact norm_pos_iff.mp (norm_t_pos F)
  refine ⟨innerPoint_mem_spa F, fun t ht => ?_, ?_⟩
  · -- every generator of `T = {W, ϖ}` is bounded by `s = ϖ`
    show ev00Val F t ≤ ev00Val F (tA F)
    have ht' : t = Wa F ∨ t = tA F := by
      simpa [chartDatum] using ht
    rcases ht' with rfl | rfl
    · rw [ev00Val_apply, ev00_Wa, nnnorm_zero]
      exact zero_le
    · exact le_refl _
  · -- `ϖ` is not in the support
    show ¬ ev00Val F (tA F) ≤ ev00Val F 0
    rw [map_zero, le_zero_iff]
    exact hϖ

theorem chart_rationalOpen_nonempty :
    (rationalOpen (chartDatum F).T (chartDatum F).s).Nonempty :=
  ⟨innerPoint F, innerPoint_mem_rationalOpen F⟩

/-! ### Problem 28: an affirmative answer -/

/-- **Nonarchimedean Scottish Book, Problem 28 — affirmative answer for the finite-jet
algebra.** For the complete uniform nonnoetherian sheafy Tate domain `𝓐`, the element
`f = Q²` and the rational datum `α = (W; ϖ)`:

1. `α` is a genuine rational datum, the subset `U = R(W/ϖ)` is nonempty, and its chart
   `𝒪_X(U)` is a nonzero ring — none of the degenerate loopholes;
2. multiplication by `f` is injective, continuous, strict, and has closed image — a
   strict inclusion in both senses;
3. `f` restricts to `0` on the rational subset. -/
theorem finiteJet_problem28 :
    (chartDatum F).IsRational ∧
    (rationalOpen (chartDatum F).T (chartDatum F).s).Nonempty ∧
    Nontrivial (presheafValue (chartDatum F)) ∧
    Function.Injective (fun a : JetA F => scottishWitness F * a) ∧
    Continuous (fun a : JetA F => scottishWitness F * a) ∧
    IsStrictMap (fun a : JetA F => scottishWitness F * a) ∧
    IsClosed (Set.range fun a : JetA F => scottishWitness F * a) ∧
    (chartDatum F).canonicalMap (scottishWitness F) = 0 :=
  ⟨chartDatum_isRational F, chart_rationalOpen_nonempty F, nontrivial_chart F,
    scottishWitness_mul_injective F, scottishWitness_mul_continuous F,
    scottishWitness_mul_isStrictMap F, scottishWitness_mul_range_isClosed F,
    canonicalMap_scottishWitness F⟩

/-! ### Problem 24: a negative answer -/

/-- **Nonarchimedean Scottish Book, Problem 24 — negative answer for the finite-jet
algebra.** The completed rational localization `𝓐 → 𝓐⟨W/ϖ⟩` of the Tate pair
`(𝓐, 𝓐°)` at the rational datum `(W; ϖ)` is **not flat**.

Flatness would force the nonzerodivisor `Q²` to act injectively on `𝓐⟨W/ϖ⟩`
(`Module.Flat.isSMulRegular_of_nonZeroDivisors`); but `Q²` acts as multiplication by
`ρ(Q²) = 0` on a *nonzero* ring, so it annihilates a nonzero element.

Note the hypotheses are not vacuous: `𝓐` is a **complete uniform sheafy** Tate ring
(`finiteJet_isUniform`, `finiteJet_isSheafy`) — merely not strongly noetherian, which is
exactly the case Problem 24 leaves open. -/
theorem finiteJet_not_flat_canonicalMap :
    ¬ @Module.Flat (JetA F) (presheafValue (chartDatum F)) _ _
      (RingHom.toModule (chartDatum F).canonicalMap) := by
  intro hflat
  have := nontrivial_chart F
  -- flatness makes the nonzerodivisor `Q²` act injectively on the chart …
  have hreg := @Module.Flat.isSMulRegular_of_nonZeroDivisors (JetA F)
    (presheafValue (chartDatum F)) _ _ (RingHom.toModule (chartDatum F).canonicalMap)
    (scottishWitness F) (scottishWitness_mem_nonZeroDivisors F) hflat
  -- … but it acts as multiplication by `ρ(Q²) = 0`, which kills a nonzero ring
  refine zero_ne_one (α := presheafValue (chartDatum F)) (hreg ?_)
  show (chartDatum F).canonicalMap (scottishWitness F) *
      (0 : presheafValue (chartDatum F)) =
    (chartDatum F).canonicalMap (scottishWitness F) *
      (1 : presheafValue (chartDatum F))
  rw [canonicalMap_scottishWitness, zero_mul, zero_mul]

end

end FiniteJet
