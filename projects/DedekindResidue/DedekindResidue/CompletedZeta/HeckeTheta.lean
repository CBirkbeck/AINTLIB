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

end

end DedekindResidue
