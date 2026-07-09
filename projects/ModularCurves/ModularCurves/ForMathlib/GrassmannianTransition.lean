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

@[simp] lemma matrix_apply (i₁ i₂ : Fin k) :
    matrix (R := R) ι ι' i₁ i₂ = column ι (ι' i₂) i₁ := rfl

private lemma mulVec_single_one {S : Type u} [CommRing S]
    (M : Matrix (Fin k) (Fin k) S) (j : Fin k) :
    M *ᵥ Pi.single j 1 = fun i => M i j := by
  funext i
  rw [Matrix.mulVec_single]
  simp

@[simp] lemma matrixAway_apply (i₁ i₂ : Fin k) :
    matrixAway (R := R) ι ι' i₁ i₂
      = algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
          (column ι (ι' i₂) i₁) := rfl

/-- The image of a delta column under the coefficient embedding is a delta column. -/
private lemma algebraMap_comp_single (i₂ : Fin k) :
    (fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
        (column ι (ι i₂) i₁))
      = Pi.single i₂ 1 := by
  funext l
  rw [congrFun (column_mem ι i₂) l, Pi.single_apply, Pi.single_apply,
    apply_ite (algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))),
    map_one, map_zero]

/-- The localized forward transition matrix has delta columns at indices hit by `ι`. -/
private lemma matrixAway_mulVec_single {i₀ i₂ : Fin k} (hcol : ι' i₀ = ι i₂) :
    matrixAway (R := R) ι ι' *ᵥ Pi.single i₀ 1 = Pi.single i₂ 1 := by
  rw [mulVec_single_one]
  funext i₁
  rw [matrixAway_apply, hcol]
  exact congrFun (algebraMap_comp_single ι ι' i₂) i₁

private lemma nonsing_inv_matrixAway_mulVec_single {i₀ i₂ : Fin k} (hcol : ι' i₀ = ι i₂) :
    (matrixAway (R := R) ι ι')⁻¹ *ᵥ Pi.single i₂ 1 = Pi.single i₀ 1 := by
  rw [← matrixAway_mulVec_single ι ι' hcol, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_det_matrixAway ι ι'), Matrix.one_mulVec]

/-- **[GR-F1]** The transition ring map carries the *reverse* transition matrix to the
inverse of the (localized) forward one — the generic content of "the coordinate changes
are mutually inverse on the overlap". -/
lemma map_ringHom_matrix :
    (matrix ι' ι).map ⇑(ringHom (R := R) ι ι') = (matrixAway (R := R) ι ι')⁻¹ := by
  classical
  funext i₁ i₂
  rw [Matrix.map_apply, matrix_apply]
  have hR : (matrixAway (R := R) ι ι')⁻¹ i₁ i₂
      = ((matrixAway (R := R) ι ι')⁻¹ *ᵥ Pi.single i₂ 1) i₁ := by
    rw [mulVec_single_one]
  by_cases hj : ι i₂ ∈ Set.range ι'
  · obtain ⟨i₀, hi₀⟩ := hj
    rw [← hi₀, congrFun (column_mem ι' i₀) i₁, hR,
      nonsing_inv_matrixAway_mulVec_single ι ι' hi₀, Pi.single_apply, Pi.single_apply]
    split <;> simp
  · rw [congrFun (column_notMem ι' hj) i₁, ringHom, eval₂Hom_X']
    rw [show (fun l => algebraMap (ChartRing R ι)
          (Localization.Away (det (R := R) ι ι')) (column ι (ι i₂) l))
        = Pi.single i₂ 1 from algebraMap_comp_single ι ι' i₂,
      hR]

/-- **[GR-F1]** The transition map sends the reverse transition determinant to a unit —
so it extends over the reverse overlap localization. -/
lemma isUnit_ringHom_det :
    IsUnit (ringHom (R := R) ι ι' (det (R := R) ι' ι)) := by
  have hd : det (R := R) ι' ι = (matrix ι' ι).det := rfl
  rw [hd, RingHom.map_det, RingHom.mapMatrix_apply, map_ringHom_matrix]
  exact Matrix.isUnit_det_of_left_inverse
    (Matrix.mul_nonsing_inv _ (isUnit_det_matrixAway ι ι'))

/-- **[GR-F2]** The chart transition on overlap rings — the `Scheme.GlueData` gluing map
at ring level: `(ChartRing ι')[1/det ι'ι] → (ChartRing ι)[1/det ιι']`. -/
noncomputable def ringHomAway :
    Localization.Away (det (R := R) ι' ι) →+* Localization.Away (det (R := R) ι ι') :=
  IsLocalization.Away.lift (det (R := R) ι' ι) (isUnit_ringHom_det ι ι')

lemma ringHomAway_algebraMap (q : ChartRing R ι') :
    ringHomAway ι ι' (algebraMap (ChartRing R ι')
        (Localization.Away (det (R := R) ι' ι)) q)
      = ringHom (R := R) ι ι' q :=
  IsLocalization.Away.lift_eq _ (isUnit_ringHom_det ι ι') q

/-- The transition image of ANY reverse-chart column, uniformly: `ringHom` sends the
ι'-column of `j` to `(matrixAway ι ι')⁻¹` applied to the embedded ι-column of `j`. The
variable case is definitional; the delta case is the inverse-column identity. -/
lemma ringHom_comp_column (j : Fin n) :
    (fun i₁ => ringHom (R := R) ι ι' (column ι' j i₁))
      = (matrixAway (R := R) ι ι')⁻¹ *ᵥ
        (fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
          (column ι j i₁)) := by
  classical
  by_cases hj : j ∈ Set.range ι'
  · obtain ⟨i₀, rfl⟩ := hj
    have hcol : (fun i₁ => algebraMap (ChartRing R ι)
        (Localization.Away (det (R := R) ι ι')) (column ι (ι' i₀) i₁))
        = matrixAway (R := R) ι ι' *ᵥ Pi.single i₀ 1 := by
      rw [mulVec_single_one]
      funext l
      rw [matrixAway_apply]
    rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_matrixAway ι ι'),
      Matrix.one_mulVec]
    funext i₁
    rw [congrFun (column_mem ι' i₀) i₁, Pi.single_apply, Pi.single_apply,
      apply_ite (ringHom (R := R) ι ι'), map_one, map_zero]
  · funext i₁
    rw [congrFun (column_notMem ι' hj) i₁, ringHom, eval₂Hom_X']

/-- Cancellation transport: the `ringHomAway`-image of the ι'-side solution vector is
the embedded ι-column — the pointwise heart of the inverse-pair identity. -/
private lemma ringHomAway_solution_column (j : Fin n) :
    (fun i => ringHomAway (R := R) ι ι'
      (((matrixAway (R := R) ι' ι)⁻¹ *ᵥ
        fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
          (column ι' j l)) i))
      = fun i => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
          (column ι j i) := by
  have hdet := isUnit_det_matrixAway (R := R) ι ι'
  have hinj : ∀ v w : Fin k → Localization.Away (det (R := R) ι ι'),
      (matrixAway (R := R) ι ι')⁻¹ *ᵥ v = (matrixAway (R := R) ι ι')⁻¹ *ᵥ w → v = w := by
    intro v w hvw
    have h2 := congrArg (fun u => matrixAway (R := R) ι ι' *ᵥ u) hvw
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec] using h2
  have hmapF : (matrixAway (R := R) ι' ι).map ⇑(ringHomAway (R := R) ι ι')
      = (matrixAway (R := R) ι ι')⁻¹ := by
    have hAM : ⇑(ringHomAway (R := R) ι ι') ∘
        ⇑(algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι)))
        = ⇑(ringHom (R := R) ι ι') :=
      funext fun q => ringHomAway_algebraMap ι ι' q
    rw [matrixAway, Matrix.map_map, hAM]
    exact map_ringHom_matrix ι ι'
  set z : Fin k → Localization.Away (det (R := R) ι' ι) :=
    (matrixAway (R := R) ι' ι)⁻¹ *ᵥ
      fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
        (column ι' j l) with hz
  have hMz : matrixAway (R := R) ι' ι *ᵥ z
      = fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
          (column ι' j l) := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_matrixAway ι' ι),
      Matrix.one_mulVec]
  refine hinj _ _ ?_
  conv_lhs => rw [← hmapF]
  funext i
  calc ((matrixAway (R := R) ι' ι).map ⇑(ringHomAway (R := R) ι ι') *ᵥ
        fun l => ringHomAway (R := R) ι ι' (z l)) i
      = ringHomAway (R := R) ι ι' ((matrixAway (R := R) ι' ι *ᵥ z) i) :=
        (RingHom.map_mulVec _ _ _ i).symm
    _ = ringHomAway (R := R) ι ι'
          (algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
            (column ι' j i)) := by rw [hMz]
    _ = ringHom (R := R) ι ι' (column ι' j i) := ringHomAway_algebraMap ι ι' _
    _ = ((matrixAway (R := R) ι ι')⁻¹ *ᵥ
          fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
            (column ι j i₁)) i := congrFun (ringHom_comp_column ι ι' j) i

/-- **[GR-E4]** The two chart transitions are mutually inverse on the overlap rings —
the `Scheme.GlueData` inverse-pair condition at ring level. -/
theorem ringHomAway_comp_ringHomAway :
    (ringHomAway (R := R) ι ι').comp (ringHomAway ι' ι)
      = RingHom.id (Localization.Away (det (R := R) ι ι')) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (det (R := R) ι ι')) ?_
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ringHomAway_algebraMap]
    rw [show ringHom (R := R) ι' ι (C a)
        = algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι)) (C a) from
      eval₂Hom_C _ _ a]
    rw [ringHomAway_algebraMap]
    rw [show ringHom (R := R) ι ι' (C a)
        = algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι')) (C a) from
      eval₂Hom_C _ _ a]
    rfl
  · obtain ⟨⟨j, hj⟩, i⟩ := p
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ringHomAway_algebraMap]
    rw [show ringHom (R := R) ι' ι (X (⟨j, hj⟩, i))
        = ((matrixAway (R := R) ι' ι)⁻¹ *ᵥ
            fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
              (column ι' j l)) i from by rw [ringHom, eval₂Hom_X']]
    rw [congrFun (ringHomAway_solution_column ι ι' j) i,
      congrFun (column_notMem ι hj) i]
    rfl

end Transition

end Module.Grassmannian
