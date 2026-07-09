import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Grassmannian chart-transition ring layer ([NISOG-GRASS], [GR-E3] generic half)

The gluing data for the chart atlas of `Grass(k, n)`, at the level of generic matrix
rings — deliberately **Grassmannian-free** (no import of `GrassmannianChart`): the
pointwise spec tying these to `Module.Grassmannian.chartMatrix` is a separate increment
(artifact, [GR-E] design, single-writer discipline).

For two coordinate charts `ι ι' : Fin k ↪ Fin n` of the Grassmannian of rank-`k`
quotients of `R^n`:

* `Grassmannian.ChartRing R k n ι` — the ι-chart coordinate ring
  `R[X_{j,i} : j ∉ range ι, i : Fin k]` (the chart is `𝔸^{k(n−k)}`, Stacks 089T (3));
* `Grassmannian.Transition.matrix ι ι'` — the generic transition matrix `T`: column
  `i₂` is the ι'-tuple's `i₂`-th coordinate vector expressed through the generic
  ι-retraction (Kronecker column when `ι' i₂ ∈ range ι`, variable column otherwise);
* `Grassmannian.Transition.det ι ι'` — its determinant, the gluing denominator: the
  ι∩ι'-overlap is the basic open `D(det)` of the ι-chart ([GR-E2] criterion);
* `Grassmannian.Transition.ringHom ι ι'` — the transition
  `ChartRing ι' → (ChartRing ι)[1/det]`, sending the generic ι'-variable `X_{j',i'}` to
  the `i'`-entry of `T⁻¹ · (ι-coordinate column of j')` — the [GR-F] glue datum.

Decomposition artifact: `.mathlib-quality/decomposition-nisog-grass.md` ([STREAM-FP],
fable-FP, [GR-E] design 2026-07-09).
-/

universe u

namespace Module.Grassmannian

open MvPolynomial

variable (R : Type u) [CommRing R] {k n : ℕ}

/-- The coordinate ring of the ι-chart of `Grass(k, R^n)`: polynomials in one variable
per matrix entry `(j, i)`, `j` a complementary coordinate, `i : Fin k`. -/
abbrev ChartRing (ι : Fin k ↪ Fin n) : Type u :=
  MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R

namespace Transition

open Matrix

variable {R} (ι ι' : Fin k ↪ Fin n)

/-- The generic ι-coordinate column of an arbitrary index `j : Fin n`: the `ι`-indexed
Kronecker vector when `j = ι i₀`, the generic variable column when `j ∉ range ι`. This
is "the generic retraction evaluated at the `j`-th basis vector". -/
noncomputable def column (j : Fin n) : Fin k → ChartRing R ι :=
  if h : j ∈ Set.range ι then
    Pi.single ((Equiv.ofInjective ι ι.injective).symm ⟨j, h⟩) 1
  else fun i => X (⟨j, h⟩, i)

@[simp] lemma column_mem (i₀ : Fin k) :
    column ι (ι i₀) = (Pi.single i₀ 1 : Fin k → ChartRing R ι) := by
  rw [column, dif_pos ⟨i₀, rfl⟩]
  congr 1
  exact Equiv.ofInjective_symm_apply ι.injective i₀

lemma column_notMem {j : Fin n} (h : j ∉ Set.range ι) :
    column ι j = fun i => (X (⟨j, h⟩, i) : ChartRing R ι) := by
  rw [column, dif_neg h]

/-- The generic transition matrix from the ι-chart to the ι'-chart: `T i₁ i₂` is the
`i₁`-entry of the generic ι-coordinate column of `ι' i₂`. On the locus where its
determinant is invertible, the ι'-tuple is also a quotient basis ([GR-E2]). -/
noncomputable def matrix : Matrix (Fin k) (Fin k) (ChartRing R ι) :=
  Matrix.of fun i₁ i₂ => column ι (ι' i₂) i₁

/-- The transition determinant — the denominator of the chart transition, cutting the
overlap `D(det)` out of the ι-chart. -/
noncomputable def det : ChartRing R ι := (matrix ι ι').det

/-- The localized transition matrix over the overlap ring `(ChartRing ι)[1/det]`. -/
noncomputable def matrixAway :
    Matrix (Fin k) (Fin k) (Localization.Away (det (R := R) ι ι')) :=
  (matrix ι ι').map (algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι')))

/-- The image of the transition determinant is a unit on the overlap. -/
lemma isUnit_det_matrixAway : IsUnit (matrixAway ι ι' (R := R)).det := by
  rw [matrixAway, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (det (R := R) ι ι')

/-- **[GR-E3]** The chart-transition ring map `ChartRing ι' → (ChartRing ι)[1/det]`:
the generic ι'-variable `X_{j', i'}` goes to the `i'`-entry of `T⁻¹` applied to the
generic ι-column of `j'` — "express the ι'-retraction through the ι-retraction and the
inverted transition matrix". The [GR-F] glue datum. -/
noncomputable def ringHom :
    ChartRing R ι' →+* Localization.Away (det (R := R) ι ι') :=
  MvPolynomial.eval₂Hom
    ((algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))).comp
      (MvPolynomial.C : R →+* ChartRing R ι))
    (fun p => ((matrixAway (R := R) ι ι')⁻¹ *ᵥ
      fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
        (column ι p.1.1 i₁)) p.2)

end Transition

end Module.Grassmannian
