import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdgeModule

/-!
# Module-valued vertical edge maps

The module-valued vertical edge theorem follows from the horizontal theorem by
flipping the bicomplex and composing with the total-flip isomorphism.
-/

open CategoryTheory

noncomputable section

universe u

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]

variable (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- The vertical edge of a module-valued first-quadrant bicomplex is a
quasi-isomorphism in degree one under the three low-column exactness
hypotheses. -/
theorem totalUpNatVerticalEdge_quasiIsoAt_one_module
    (B : CochainComplex (ModuleCat.{u} R) ℕ)
    (e : ∀ p, B.X p ⟶ (K.X 0).X p)
    (he : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
      e p ≫ (K.X 0).d p p' = B.d p p' ≫ e p')
    (w : ∀ p, e p ≫ (K.d 0 1).f p = 0)
    (hcol00 : (ShortComplex.mk
      (e 0) ((K.d 0 1).f 0) (w 0)).Exact)
    (hcol10 : (ShortComplex.mk
      (e 1) ((K.d 0 1).f 1) (w 1)).Exact)
    (hcol01 : (ShortComplex.mk
      ((K.d 0 1).f 0) ((K.d 1 2).f 0)
      (K.d_f_comp_d_f 0 1 2 0)).Exact)
    [Mono (e 1)] [Mono (e 2)] :
    QuasiIsoAt (K.totalUpNatVerticalEdge B e he w) 1 := by
  let edge := K.flip.totalUpNatHorizontalEdge B e he w
  letI : Mono
      (show B.X 1 ⟶ (K.flip.X 1).X 0 from e 1) := by
    change Mono (e 1)
    infer_instance
  letI : Mono
      (show B.X 2 ⟶ (K.flip.X 2).X 0 from e 2) := by
    change Mono (e 2)
    infer_instance
  haveI : QuasiIsoAt edge 1 :=
    totalUpNatHorizontalEdge_quasiIsoAt_one_module
      K.flip B e he w hcol00 hcol10 hcol01
  haveI : QuasiIsoAt (K.totalFlipIso (.up ℕ)).hom 1 :=
    quasiIsoAt_of_isIso _ _
  change QuasiIsoAt (edge ≫ (K.totalFlipIso (.up ℕ)).hom) 1
  infer_instance

end HomologicalComplex₂
