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

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
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

end

end DedekindResidue
