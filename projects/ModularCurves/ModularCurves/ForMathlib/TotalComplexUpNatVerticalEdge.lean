import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdgeHOne

/-!
# The vertical edge map into a first-quadrant total complex

Construct the vertical edge map by applying the horizontal construction to the
flipped bicomplex and transporting along mathlib's total-complex symmetry.
-/

open CategoryTheory CategoryTheory.Preadditive

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- The vertical edge map from an augmented zeroth row to the total complex. -/
noncomputable def totalUpNatVerticalEdge
    (B : CochainComplex C ℕ) (e : ∀ p, B.X p ⟶ (K.X 0).X p)
    (he : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
      e p ≫ (K.X 0).d p p' = B.d p p' ≫ e p')
    (w : ∀ p, e p ≫ (K.d 0 1).f p = 0) :
    B ⟶ K.total (.up ℕ) :=
  K.flip.totalUpNatHorizontalEdge B e he w ≫ (K.totalFlipIso (.up ℕ)).hom

@[simp]
theorem totalUpNatVerticalEdge_f
    (B : CochainComplex C ℕ) (e : ∀ p, B.X p ⟶ (K.X 0).X p)
    (he : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
      e p ≫ (K.X 0).d p p' = B.d p p' ≫ e p')
    (w : ∀ p, e p ≫ (K.d 0 1).f p = 0) (p : ℕ) :
    (K.totalUpNatVerticalEdge B e he w).f p =
      e p ≫ K.ιTotal (.up ℕ) 0 p p (by
        change 0 + p = p
        exact zero_add p) := by
  dsimp only [totalUpNatVerticalEdge, HomologicalComplex.comp_f]
  rw [K.flip.totalUpNatHorizontalEdge_f]
  rw [Category.assoc, K.ιTotal_totalFlipIso_f_hom]
  simp
  congr

section

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- The vertical edge map is a quasi-isomorphism in degree one under the
corresponding three low-column exactness hypotheses. -/
theorem totalUpNatVerticalEdge_quasiIsoAt_one
    (B : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ p, B.X p ⟶ (K.X 0).X p)
    (he : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
      e p ≫ (K.X 0).d p p' = B.d p p' ≫ e p')
    (w : ∀ p, e p ≫ (K.d 0 1).f p = 0)
    (hcol00 : (ShortComplex.mk (e 0) ((K.d 0 1).f 0) (w 0)).Exact)
    (hcol10 : (ShortComplex.mk (e 1) ((K.d 0 1).f 1) (w 1)).Exact)
    (hcol01 : (ShortComplex.mk ((K.d 0 1).f 0) ((K.d 1 2).f 0)
      (K.d_f_comp_d_f 0 1 2 0)).Exact)
    [heOne : Mono (e 1)] [heTwo : Mono (e 2)] :
    QuasiIsoAt (K.totalUpNatVerticalEdge B e he w) 1 := by
  let edge := K.flip.totalUpNatHorizontalEdge B e he w
  haveI : QuasiIsoAt edge 1 :=
    @totalUpNatHorizontalEdge_quasiIsoAt_one K.flip (by infer_instance) B e he w
      hcol00 hcol10 hcol01 heOne heTwo
  haveI : QuasiIsoAt (K.totalFlipIso (.up ℕ)).hom 1 :=
    quasiIsoAt_of_isIso _ _
  change QuasiIsoAt (edge ≫ (K.totalFlipIso (.up ℕ)).hom) 1
  infer_instance

end

end HomologicalComplex₂
