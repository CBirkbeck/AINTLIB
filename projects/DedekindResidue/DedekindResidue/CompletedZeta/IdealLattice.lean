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

end

end DedekindResidue
