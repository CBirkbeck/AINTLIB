module

public import Mathlib
public import DedekindResidue.CompletedZeta.IdealLattice

/-!
# The multivariable Hecke theta of a fractional ideal  (SP1-AGE-3)

Hecke's functional-equation argument for a number field of unit rank `> 0` uses the
**multivariable** theta of an ideal lattice, with one weight per infinite place, averaged
over a fundamental domain of the unit action. This file builds the per-place weight
machinery and the theta function itself:

* `placeWeights c` — expand per-place weights to the `index K` coordinates (equal on the
  `(re, im)` pair of a complex place — the shape preserved by the unit action, since complex
  multiplication mixes the pair but preserves `re² + im²`);
* `sum_placeWeights_embeddingCoords_sq` — `∑ᵢ c_i·ζ(x)ᵢ² = ∑_w c_w·w(x)²`: the weighted
  square-sum of embedding coordinates is the place-absolute-value form.

The unit equivariance `Θ(c·w(ε)², L_I) = Θ(c, L_I)` and the box-averaged `g_I` follow
(SP1-AGE-3 continuation), then the Mellin definition of `Λ_K` (AGE-4).
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]


/-- Expand per-place weights to per-coordinate weights (equal on the `(re, im)` pair of a
complex place). -/
noncomputable def placeWeights (c : InfinitePlace K → ℝ) : index K → ℝ :=
  Sum.elim (fun w => c w) (fun p => c p.1)

open scoped Classical in
/-- The place-weighted square-sum of the embedding coordinates is the weighted sum of squared
place absolute values: `∑ᵢ c_i·ζ(x)ᵢ² = ∑_w c_w·w(x)²`. -/
theorem sum_placeWeights_embeddingCoords_sq (c : InfinitePlace K → ℝ) (x : K) :
    (∑ i : index K, placeWeights K c i * embeddingCoords K x i ^ 2)
      = ∑ w : InfinitePlace K, c w * (w x) ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type,
    ← Fintype.sum_subtype_add_sum_subtype IsReal (fun w : InfinitePlace K => c w * (w x) ^ 2)]
  congr 1
  · -- real places
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [embeddingCoords_isReal]
    have h1 : (w : InfinitePlace K) x = ‖(w : InfinitePlace K).embedding x‖ :=
      (norm_embedding_eq _ x).symm
    have h2 : ((w : InfinitePlace K).embedding x) = ((embedding_of_isReal w.2 x : ℝ) : ℂ) :=
      (embedding_of_isReal_apply w.2 x).symm
    rw [h1, h2, Complex.norm_real, placeWeights]
    simp [sq_abs]
  · -- complex places
    have hre : (∑ i : {w : InfinitePlace K // ¬ IsReal w}, c ↑i * ((i : InfinitePlace K) x) ^ 2)
        = ∑ w : {w : InfinitePlace K // IsComplex w}, c ↑w * ((w : InfinitePlace K) x) ^ 2 :=
      Fintype.sum_equiv (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K => not_isReal_iff_isComplex)) _ _ (fun w => rfl)
    rw [hre]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Fin.sum_univ_two, embeddingCoords_isComplex_fst, embeddingCoords_isComplex_snd]
    have h1 : (w : InfinitePlace K) x = ‖(w : InfinitePlace K).embedding x‖ :=
      (norm_embedding_eq _ x).symm
    have h2 : ‖(w : InfinitePlace K).embedding x‖ ^ 2
        = ((w : InfinitePlace K).embedding x).re ^ 2
          + ((w : InfinitePlace K).embedding x).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [h1, h2, placeWeights]
    simp only [Sum.elim_inr]
    ring

open scoped Classical in
/-- The multivariable Hecke theta of a fractional ideal with per-place weights. -/
noncomputable def heckeTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : InfinitePlace K → ℝ) : ℝ :=
  ∑' v : idealZLattice K I, Real.exp (-π * ∑ i : index K,
    placeWeights K c i * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)

open scoped Classical in
/-- Multiplication by (the mixed embedding of) a field element `x`, as a linear map of the
Euclidean coordinate space (conjugated through the coordinate identifications). -/
noncomputable def mulCoords (x : K) :
    EuclideanSpace ℝ (index K) →ₗ[ℝ] EuclideanSpace ℝ (index K) :=
  ((((euclidean.stdOrthonormalBasis K).repr.toLinearEquiv.toLinearMap).comp
      ((euclidean.toMixed K).symm.toLinearMap)).comp
    (LinearMap.mulLeft ℝ (mixedEmbedding K x))).comp
    (((euclidean.toMixed K).toLinearMap).comp
      ((euclidean.stdOrthonormalBasis K).repr.symm.toLinearEquiv.toLinearMap))

open scoped Classical in
theorem mulCoords_embeddingCoords (x a : K) :
    mulCoords K x (embeddingCoords K a) = embeddingCoords K (x * a) := by
  rw [mulCoords, embeddingCoords, embeddingCoords]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]
  rw [LinearIsometryEquiv.symm_apply_apply]
  show (euclidean.stdOrthonormalBasis K).repr ((euclidean.toMixed K).symm
    (mixedEmbedding K x * ((euclidean.toMixed K) ((euclidean.toMixed K).symm
      (mixedEmbedding K a))))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ← map_mul]

open scoped Classical in
/-- Multiplication by the image of a unit permutes the points of an ideal lattice:
the induced self-equivalence of `idealZLattice K I`. -/
noncomputable def unitMulLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ε : (𝓞 K)ˣ) :
    idealZLattice K I ≃ idealZLattice K I where
  toFun v := ⟨mulCoords K (algebraMap (𝓞 K) K (ε : 𝓞 K)) v, by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    rw [mem_idealZLattice]
    refine ⟨algebraMap (𝓞 K) K (ε : 𝓞 K) * a, ?_, by rw [← hva, mulCoords_embeddingCoords]⟩
    have := Submodule.smul_mem ((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) (ε : 𝓞 K) ha
    rwa [Algebra.smul_def] at this⟩
  invFun v := ⟨mulCoords K (algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) v, by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    rw [mem_idealZLattice]
    refine ⟨algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * a, ?_,
      by rw [← hva, mulCoords_embeddingCoords]⟩
    have := Submodule.smul_mem ((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ha
    rwa [Algebra.smul_def] at this⟩
  left_inv v := by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    refine Subtype.ext ?_
    show mulCoords K _ (mulCoords K _ (v : EuclideanSpace ℝ (index K)))
      = (v : EuclideanSpace ℝ (index K))
    rw [← hva, mulCoords_embeddingCoords, mulCoords_embeddingCoords, ← mul_assoc,
      ← map_mul]
    norm_cast
    rw [inv_mul_cancel ε]
    simp
  right_inv v := by
    obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
    refine Subtype.ext ?_
    show mulCoords K _ (mulCoords K _ (v : EuclideanSpace ℝ (index K)))
      = (v : EuclideanSpace ℝ (index K))
    rw [← hva, mulCoords_embeddingCoords, mulCoords_embeddingCoords, ← mul_assoc,
      ← map_mul]
    norm_cast
    rw [mul_inv_cancel ε]
    simp

open scoped Classical in
/-- **Unit equivariance of the Hecke theta** (the symmetry making the unit average
well-defined): scaling the place weights by `w(ε)²` for a unit `ε` leaves the theta of the
ideal lattice unchanged — multiplication by `ε` permutes the lattice points. -/
theorem heckeTheta_unit_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ε : (𝓞 K)ˣ)
    (c : InfinitePlace K → ℝ) :
    heckeTheta K I (fun w => (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) ^ 2 * c w)
      = heckeTheta K I c := by
  rw [heckeTheta, heckeTheta]
  conv_rhs => rw [← Equiv.tsum_eq (unitMulLatticeEquiv K I ε)]
  refine tsum_congr (fun v => ?_)
  obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K I _).mp v.2
  congr 1
  have hcoe : ((unitMulLatticeEquiv K I ε v : idealZLattice K I) :
      EuclideanSpace ℝ (index K))
      = embeddingCoords K (algebraMap (𝓞 K) K (ε : 𝓞 K) * a) := by
    show mulCoords K _ (v : EuclideanSpace ℝ (index K)) = _
    rw [← hva, mulCoords_embeddingCoords]
  rw [hcoe, ← hva, sum_placeWeights_embeddingCoords_sq, sum_placeWeights_embeddingCoords_sq]
  refine congrArg (fun r => -π * r) ?_
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, mul_pow]
  ring

open scoped Classical in
/-- The dual place-weights: `c_w⁻¹` at real places and `4·c_w⁻¹` at complex places — the
factor `4 = 2²` is the square of the duality scaling (`dualityWeights`), the archimedean
bookkeeping that ultimately feeds `Γℂ`. -/
noncomputable def dualPlaceWeights (c : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  fun w => if IsReal w then (c w)⁻¹ else 4 * (c w)⁻¹

open scoped Classical in
omit [NumberField K] in
theorem placeWeights_dualPlaceWeights (c : InfinitePlace K → ℝ) (i : index K) :
    placeWeights K (dualPlaceWeights K c) i
      = (placeWeights K c i)⁻¹ * (dualityWeights K i) ^ 2 := by
  rcases i with w | ⟨w, j⟩
  · simp only [placeWeights, Sum.elim_inl, dualPlaceWeights, dualityWeights, if_pos w.2]
    norm_num
  · simp only [placeWeights, Sum.elim_inr, dualPlaceWeights, dualityWeights]
    rw [if_neg (by rw [not_isReal_iff_isComplex]; exact w.2)]
    fin_cases j <;> norm_num <;> ring

open scoped Classical in
/-- **The inversion law of the multivariable Hecke theta** (SP1-AGE-3):
`Θ_I(c) = covol(L_I)⁻¹ · (∏ᵢ c-coords)^{-1/2} · Θ_{I^∨}(dual weights)` — Poisson summation
over the ideal lattice, with the dual side identified as the theta of the trace-dual ideal
via `dualZLattice_idealZLattice` (the duality twist absorbed into the weights). -/
theorem heckeTheta_inversion (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w) :
    heckeTheta K I c
      = (ZLattice.covolume (idealZLattice K I) volume)⁻¹
        * (Real.sqrt (∏ i, placeWeights K c i))⁻¹
        * heckeTheta K (dualIdealUnit K I) (dualPlaceWeights K c) := by
  have hpos : ∀ i, 0 < placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hc _
  rw [heckeTheta, weightedThetaLattice_transform (idealZLattice K I) hpos]
  congr 1
  rw [dualZLattice_idealZLattice K I, heckeTheta,
    ← Equiv.tsum_eq (ZLattice.comap_equiv ℝ (idealZLattice K (dualIdealUnit K I))
      ((diagScale (dualityWeights K)
        (dualityWeights_ne_zero K)).symm.toContinuousLinearEquiv.toLinearEquiv)).toEquiv]
  refine tsum_congr (fun v => ?_)
  congr 1
  simp only [LinearEquiv.coe_toEquiv, ZLattice.comap_equiv_apply]
  refine congrArg (fun r => -π * r) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have he : (((diagScale (dualityWeights K)
      (dualityWeights_ne_zero K)).symm.toContinuousLinearEquiv.toLinearEquiv).symm)
        ((v : EuclideanSpace ℝ (index K)))
      = (diagScale (dualityWeights K) (dualityWeights_ne_zero K))
          ((v : EuclideanSpace ℝ (index K))) := rfl
  rw [he, placeWeights_dualPlaceWeights, diagScale_apply, mul_pow]
  ring



open scoped Classical in
/-- Extend hyperplane coordinates `u : logSpace K` (indexed by `w ≠ w₀`) to all infinite
places by the trace-zero condition: the `w₀`-component is `-∑_{w ≠ w₀} u_w`. On the image of
`logEmbedding` this recovers the full unit log-vector (`fullLog_logEmbedding`). -/
noncomputable def fullLog (u : logSpace K) : InfinitePlace K → ℝ := fun w =>
  if h : w = (w₀ : InfinitePlace K) then
    -∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w'
  else u ⟨w, h⟩

open scoped Classical in
theorem fullLog_logEmbedding (ε : (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullLog K (logEmbedding K (Additive.ofMul ε)) w
      = mult w * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) := by
  rw [fullLog]
  split_ifs with h
  · rw [sum_logEmbedding_component, h]
    ring
  · rw [logEmbedding_component]

open scoped Classical in
theorem fullLog_add (u v : logSpace K) :
    fullLog K (u + v) = fullLog K u + fullLog K v := by
  funext w
  simp only [fullLog, Pi.add_apply]
  split_ifs with h
  · rw [Finset.sum_add_distrib]
    ring
  · rfl

open scoped Classical in
/-- **The Hecke weight family**: `c(t,u)_w = t^{1/n}·exp(2·(trace-zero extension of u)_w / mult w)`.
Pinned by two requirements: `∏_w c_w^{mult w} = t` (the norm ray, giving `N(𝔞)^{-s}` under the
Mellin transform) and equivariance under `u ↦ u + logEmbedding ε` matching
`heckeTheta_unit_mul` (making the theta integrand periodic modulo the unit lattice). -/
noncomputable def heckeWeights (t : ℝ) (u : logSpace K) : InfinitePlace K → ℝ := fun w =>
  t ^ ((1 : ℝ) / (Module.finrank ℚ K)) * Real.exp (2 * fullLog K u w / mult w)

theorem heckeWeights_pos {t : ℝ} (ht : 0 < t) (u : logSpace K) (w : InfinitePlace K) :
    0 < heckeWeights K t u w := by
  rw [heckeWeights]
  positivity

open scoped Classical in
/-- **Equivariance of the Hecke weights**: translating `u` by the log of a unit scales the
weights by `w(ε)²` — exactly the scaling `heckeTheta_unit_mul` absorbs. -/
theorem heckeWeights_add_logEmbedding (t : ℝ) (u : logSpace K) (ε : (𝓞 K)ˣ) :
    heckeWeights K t (u + logEmbedding K (Additive.ofMul ε))
      = fun w => (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) ^ 2 * heckeWeights K t u w := by
  funext w
  rw [heckeWeights, heckeWeights, fullLog_add, Pi.add_apply, fullLog_logEmbedding]
  have hmult : (mult w : ℝ) ≠ 0 := by
    have := mult_pos (w := w)
    positivity
  have hpos : 0 < w (algebraMap (𝓞 K) K (ε : 𝓞 K)) := by
    rw [pos_iff]
    simp only [ne_eq, RingOfIntegers.coe_eq_zero_iff]
    exact Units.ne_zero ε
  rw [mul_add, add_div, Real.exp_add]
  have h2 : 2 * ((mult w : ℝ) * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K)))) / (mult w : ℝ)
      = 2 * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) := by
    field_simp
  have h3 : Real.exp (2 * Real.log (w (algebraMap (𝓞 K) K (ε : 𝓞 K))))
      = (w (algebraMap (𝓞 K) K (ε : 𝓞 K))) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hpos]
    ring
  rw [h2, h3]
  ring

open scoped Classical in
/-- **Periodicity of the theta integrand modulo the unit lattice**: the Hecke-weighted theta
is invariant under `u ↦ u + logEmbedding ε` — the equivariance of the weights matches the
unit symmetry of the theta exactly. This makes the unit-box average well-defined. -/
theorem heckeTheta_heckeWeights_periodic (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : logSpace K) (ε : (𝓞 K)ˣ) :
    heckeTheta K I (heckeWeights K t (u + logEmbedding K (Additive.ofMul ε)))
      = heckeTheta K I (heckeWeights K t u) := by
  rw [heckeWeights_add_logEmbedding]
  exact heckeTheta_unit_mul K I ε _


open scoped Classical in
theorem sum_fullLog (u : logSpace K) : ∑ w : InfinitePlace K, fullLog K u w = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)]
  have h1 : fullLog K u (w₀ : InfinitePlace K)
      = -∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w' := by
    rw [fullLog]
    exact dif_pos rfl
  have h2 : ∀ w : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)},
      fullLog K u (w : InfinitePlace K) = u w := by
    intro w
    rw [fullLog, dif_neg w.2]
  rw [h1, Finset.sum_congr rfl (fun w _ => h2 w)]
  ring

open scoped Classical in
/-- **The norm-ray property**: the place-multiplicity-weighted product of the Hecke weights
is exactly `t` — the Mellin variable. (`∑ mult = n` and the trace-zero sum of `fullLog`.) -/
theorem prod_heckeWeights_pow_mult {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ∏ w : InfinitePlace K, (heckeWeights K t u w) ^ mult w = t := by
  have hn : (0:ℝ) < (Module.finrank ℚ K : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  have hexp : ∀ w : InfinitePlace K,
      (Real.exp (2 * fullLog K u w / mult w)) ^ mult w = Real.exp (2 * fullLog K u w) := by
    intro w
    rw [← Real.exp_nat_mul]
    congr 1
    have hm : (mult w : ℝ) ≠ 0 := by
      have := mult_pos (w := w)
      positivity
    field_simp
  simp_rw [heckeWeights, mul_pow, hexp]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_pow_eq_pow_sum,
    ← Real.rpow_natCast (t ^ ((1:ℝ) / (Module.finrank ℚ K))), ← Real.rpow_mul ht.le,
    sum_mult_eq]
  rw [show (∑ x : InfinitePlace K, 2 * fullLog K u x) = 0 by
    rw [← Finset.mul_sum, sum_fullLog, mul_zero]]
  rw [Real.exp_zero, mul_one, one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one]

open scoped Classical in
/-- **Hecke's unit-averaged theta** `g_I(t)`: the multivariable theta at the Hecke weights,
averaged over the fundamental box of the unit lattice in log-coordinates and divided by the
number of roots of unity. Genuine Lebesgue integral over `logSpace K`; the integrand is
periodic modulo `unitLattice K` (`heckeTheta_heckeWeights_periodic`), so the box choice is
immaterial. The Mellin transform of `g_I` produces the completed partial zeta of the class
of `I` (SP1-AGE-4). -/
noncomputable def heckeG (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℝ :=
  (torsionOrder K : ℝ)⁻¹ *
    ∫ u in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      heckeTheta K I (heckeWeights K t u)

open scoped Classical in
/-- `fullLog` is odd. -/
theorem fullLog_neg (u : logSpace K) : fullLog K (-u) = -fullLog K u := by
  funext w
  simp only [fullLog, Pi.neg_apply]
  split_ifs with h
  · rw [Finset.sum_neg_distrib]
  · rfl

open scoped Classical in
/-- The duality bookkeeping of the Hecke weights: the dual weights of `c(t,u)` are the
weights `c(1/t, -u)` scaled by `1` at real and `4` at complex places. -/
theorem dualPlaceWeights_heckeWeights {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (w : InfinitePlace K) :
    dualPlaceWeights K (heckeWeights K t u) w
      = (if IsReal w then 1 else 4) * heckeWeights K t⁻¹ (-u) w := by
  rw [dualPlaceWeights, heckeWeights, heckeWeights, fullLog_neg]
  have hn : (0:ℝ) < (Module.finrank ℚ K : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  have hinv : (t ^ ((1:ℝ) / (Module.finrank ℚ K)))⁻¹
      = t⁻¹ ^ ((1:ℝ) / (Module.finrank ℚ K)) := by
    rw [← Real.rpow_neg ht.le, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  have hexp : (Real.exp (2 * fullLog K u w / mult w))⁻¹
      = Real.exp (2 * -fullLog K u w / mult w) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [mul_inv, hinv, hexp]
  simp only [Pi.neg_apply]
  split_ifs <;> ring

open scoped Classical in
/-- The coordinate product of place weights is the multiplicity-weighted place product:
real places contribute once, complex places (two coordinates) twice. -/
theorem prod_placeWeights (c : InfinitePlace K → ℝ) :
    (∏ i : index K, placeWeights K c i) = ∏ w : InfinitePlace K, c w ^ mult w := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type,
    ← Fintype.prod_subtype_mul_prod_subtype IsReal (fun w : InfinitePlace K => c w ^ mult w)]
  congr 1
  · refine Finset.prod_congr rfl (fun w _ => ?_)
    simp only [placeWeights, Sum.elim_inl]
    rw [mult, if_pos w.2, pow_one]
  · have hre : (∏ i : {w : InfinitePlace K // ¬ IsReal w}, c ↑i ^ mult (i : InfinitePlace K))
        = ∏ w : {w : InfinitePlace K // IsComplex w}, c ↑w ^ mult (w : InfinitePlace K) :=
      Fintype.prod_equiv (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K => not_isReal_iff_isComplex)) _ _ (fun w => rfl)
    rw [hre]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [Fin.prod_univ_two]
    simp only [placeWeights, Sum.elim_inr]
    rw [mult, if_neg (by rw [not_isReal_iff_isComplex]; exact w.2)]
    ring

open scoped Classical in
/-- The coordinate product of the Hecke weights is the Mellin variable `t` — so the middle
factor of `heckeTheta_inversion` at the Hecke weights is exactly `(√t)⁻¹`. -/
theorem prod_placeWeights_heckeWeights {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    (∏ i : index K, placeWeights K (heckeWeights K t u) i) = t := by
  rw [prod_placeWeights]
  exact prod_heckeWeights_pow_mult K ht u

end

end DedekindResidue
