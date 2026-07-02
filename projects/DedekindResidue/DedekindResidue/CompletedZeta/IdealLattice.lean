module

public import Mathlib
public import DedekindResidue.CompletedZeta.ThetaLattice

/-!
# Ideal lattices in Euclidean coordinates  (SP1-AGE-1)

The theta/Poisson layer (`ThetaLattice.lean`) lives on `EuclideanSpace ℝ ι`. Hecke's
construction sums Gaussians over the images of (fractional) ideals of `K` under the mixed
embedding. This file transports mathlib's ideal lattices into that Euclidean frame:

* `mixedEmbedding.idealLattice K I ⊂ mixedSpace K` (mathlib) is pulled back along the
  continuous linear equivalence `euclidean.toMixed K` to
  `euclideanIdealLattice K I ⊂ euclidean.mixedSpace K` — mirroring mathlib's own
  `euclidean.integerLattice` — and then along the orthonormal-basis coordinate isometry
  `(euclidean.stdOrthonormalBasis K).repr` to `idealZLattice K I ⊂ EuclideanSpace ℝ (index K)`.
* Both transports are measure-preserving, so the covolume is mathlib's
  `covolume_idealLattice`: `covol = N(I)·2^{-r₂}·√|Δ_K|` (`covolume_idealZLattice`).

The `ZLattice` instances come from `ZLattice.comap`. Everything is genuine; no stubs.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The ideal lattice of a fractional ideal `I`, in the Euclidean mixed space — the pullback
of mathlib's `mixedEmbedding.idealLattice` along `euclidean.toMixed` (mirroring mathlib's
`euclidean.integerLattice`). -/
noncomputable def euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (euclidean.toMixed K).toLinearMap

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (euclideanIdealLattice K I) := by
  exact inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (euclidean.toMixed K).toLinearMap))

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (euclideanIdealLattice K I) := by
  exact inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (euclidean.toMixed K).toLinearMap))

open scoped Classical in
/-- The ideal lattice of `I` in coordinates: the pullback of `euclideanIdealLattice` along
the orthonormal coordinate isometry, as a lattice in `EuclideanSpace ℝ (index K)` — the
frame in which the theta/Poisson layer (`thetaLattice`, `weightedThetaLattice_transform`)
applies directly. -/
noncomputable def idealZLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  ZLattice.comap ℝ (euclideanIdealLattice K I)
    ((euclidean.stdOrthonormalBasis K).repr.symm.toContinuousLinearEquiv).toLinearMap

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (idealZLattice K I) := by
  exact inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (euclideanIdealLattice K I)
    ((euclidean.stdOrthonormalBasis K).repr.symm.toContinuousLinearEquiv).toLinearMap))

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (idealZLattice K I) := by
  exact inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (euclideanIdealLattice K I)
    ((euclidean.stdOrthonormalBasis K).repr.symm.toContinuousLinearEquiv).toLinearMap))

open scoped Classical in
/-- The covolume of the Euclidean-coordinates ideal lattice is mathlib's
`covolume_idealLattice`: `N(I) · 2^{-r₂} · √|Δ_K|`. Both coordinate changes
(`euclidean.toMixed` and the orthonormal `repr`) are measure-preserving. -/
theorem covolume_idealZLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealZLattice K I) volume
      = (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K))
          * (2⁻¹) ^ nrComplexPlaces K * Real.sqrt |discr K| := by
  unfold idealZLattice euclideanIdealLattice
  rw [ZLattice.covolume_comap _ _ _
      ((euclidean.stdOrthonormalBasis K).measurePreserving_repr_symm),
    ZLattice.covolume_comap _ _ _ (euclidean.volumePreserving_toMixed K),
    covolume_idealLattice]

open scoped Real

open scoped Classical in
/-- The **theta function of a fractional ideal**: the lattice theta of its Euclidean ideal
lattice, `Θ_I(t) = ∑_{α ∈ I} e^{-πt‖σ(α)‖²}` (with `σ` the mixed embedding in Euclidean
coordinates). The 1-parameter member of Hecke's family; the unit-averaged multivariable
version (`weightedGaussianCM` weights over the log-unit box) is SP1-AGE-3. -/
noncomputable def idealTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℝ :=
  thetaLattice (idealZLattice K I) t

open scoped Classical in
/-- The transformation law of the ideal theta, with the covolume evaluated by
`covolume_idealZLattice`: `Θ_I(t) = (N(I)·2^{-r₂}·√|Δ_K|)⁻¹·t^{-n/2}·Θ_{(L_I)♯}(1/t)`.
Identifying the dual lattice `(L_I)♯` with the ideal lattice of `(I·𝔡_K)⁻¹` (the codifferent
twist) is SP1-AGE-2. -/
theorem idealTheta_transform (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : ℝ} (ht : 0 < t) :
    idealTheta K I t
      = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K))
            * (2⁻¹) ^ nrComplexPlaces K * Real.sqrt |discr K|)⁻¹
          * t ^ (-(Fintype.card (index K) : ℝ) / 2)
          * thetaLattice (dualZLattice (idealZLattice K I)) t⁻¹ := by
  rw [idealTheta, thetaLattice_transform (idealZLattice K I) ht, covolume_idealZLattice]

open scoped Classical in
/-- The mixed embedding in Euclidean coordinates: `K → EuclideanSpace ℝ (index K)`, the frame
of `idealZLattice`. Its coordinates are the `stdBasis` coordinates of `mixedEmbedding K x`
(`embeddingCoords_apply`): the real embedding values at real places and the real/imaginary
parts at complex places. -/
noncomputable def embeddingCoords (x : K) : EuclideanSpace ℝ (index K) :=
  (euclidean.stdOrthonormalBasis K).repr ((euclidean.toMixed K).symm (mixedEmbedding K x))

open scoped Classical in
theorem embeddingCoords_apply (x : K) (i : index K) :
    embeddingCoords K x i = (stdBasis K).repr (mixedEmbedding K x) i := by
  rw [embeddingCoords]
  have h := euclidean.stdOrthonormalBasis_map_eq K
  have h2 : (euclidean.stdOrthonormalBasis K).toBasis.repr
      ((euclidean.toMixed K).symm (mixedEmbedding K x)) i
      = (stdBasis K).repr (mixedEmbedding K x) i := by
    rw [← h, Module.Basis.map_repr]
    simp
  rw [← h2, OrthonormalBasis.coe_toBasis_repr_apply]

open scoped Classical in
theorem embeddingCoords_isReal (x : K) (w : {w : InfinitePlace K // IsReal w}) :
    embeddingCoords K x (Sum.inl w) = embedding_of_isReal w.2 x := by
  rw [embeddingCoords_apply, stdBasis_apply_isReal, mixedEmbedding_apply_isReal]

open scoped Classical in
theorem embeddingCoords_isComplex_fst (x : K) (w : {w : InfinitePlace K // IsComplex w}) :
    embeddingCoords K x (Sum.inr ⟨w, 0⟩) = ((w : InfinitePlace K).embedding x).re := by
  rw [embeddingCoords_apply, stdBasis_apply_isComplex_fst, mixedEmbedding_apply_isComplex]

open scoped Classical in
theorem embeddingCoords_isComplex_snd (x : K) (w : {w : InfinitePlace K // IsComplex w}) :
    embeddingCoords K x (Sum.inr ⟨w, 1⟩) = ((w : InfinitePlace K).embedding x).im := by
  rw [embeddingCoords_apply, stdBasis_apply_isComplex_snd, mixedEmbedding_apply_isComplex]

/-- The duality weights: `1` at real coordinates, `(2, -2)` at the `(re, im)` coordinates of
a complex place — the diagonal matrix of `conj ∘ (double)`. -/
noncomputable def dualityWeights : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 2 else -2)

omit [NumberField K] in
theorem dualityWeights_ne_zero : ∀ i, dualityWeights K i ≠ 0 := by
  rintro (w | ⟨w, j⟩)
  · norm_num [dualityWeights]
  · fin_cases j <;> norm_num [dualityWeights]

open scoped RealInnerProductSpace in
open scoped Classical in
/-- **The duality pairing dictionary** (SP1-AGE-2 core): pairing the `dualityWeights`-scaled
coordinates of `σ(b)` against the coordinates of `σ(a)` computes the rational trace form:
`⟪D·ζ(b), ζ(a)⟫ = Tr_{K/ℚ}(b·a)`. -/
theorem inner_diagScale_embeddingCoords (a b : K) :
    ⟪(diagScale (dualityWeights K) (dualityWeights_ne_zero K)) (embeddingCoords K b),
      embeddingCoords K a⟫ = ((Algebra.trace ℚ K (b * a) : ℚ) : ℝ) := by
  have h1 : ((Algebra.trace ℚ K (b * a) : ℚ) : ℂ) = ∑ τ : K →+* ℂ, τ (b * a) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ,
      ← Equiv.sum_comp (RingHom.equivRatAlgHom (R := K) (S := ℂ))]
    rfl
  have h2 : ((Algebra.trace ℚ K (b * a) : ℚ) : ℝ) = ∑ τ : K →+* ℂ, (τ (b * a)).re := by
    have h := congrArg Complex.re h1
    simpa using h
  rw [h2, ← Equiv.sum_comp (indexEquiv K) (fun τ => (τ (b * a)).re)]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · -- real places, termwise
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hD : (diagScale (dualityWeights K) (dualityWeights_ne_zero K))
        (embeddingCoords K b) (Sum.inl w) = embedding_of_isReal w.2 b := by
      rw [diagScale_apply, embeddingCoords_isReal]
      simp [dualityWeights]
    rw [hD, embeddingCoords_isReal, indexEquiv_apply_isReal]
    have hre : ((w : InfinitePlace K).embedding (b * a)).re
        = embedding_of_isReal w.2 (b * a) := by
      rw [← embedding_of_isReal_apply w.2, Complex.ofReal_re]
    rw [hre, map_mul]
    ring
  · -- complex places: group the (re, im) pair per place
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hD0 : (diagScale (dualityWeights K) (dualityWeights_ne_zero K))
        (embeddingCoords K b) (Sum.inr (w, 0))
        = 2 * ((w : InfinitePlace K).embedding b).re := by
      rw [diagScale_apply, embeddingCoords_isComplex_fst]
      simp [dualityWeights]
    have hD1 : (diagScale (dualityWeights K) (dualityWeights_ne_zero K))
        (embeddingCoords K b) (Sum.inr (w, 1))
        = -2 * ((w : InfinitePlace K).embedding b).im := by
      rw [diagScale_apply, embeddingCoords_isComplex_snd]
      simp [dualityWeights]
    rw [hD0, hD1, embeddingCoords_isComplex_fst, embeddingCoords_isComplex_snd,
      indexEquiv_apply_isComplex_fst, indexEquiv_apply_isComplex_snd,
      ComplexEmbedding.conjugate_coe_eq]
    simp only [map_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

end

end DedekindResidue
