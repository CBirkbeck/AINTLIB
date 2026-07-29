import ModularCurves.ForMathlib.TotalComplexUpNatCycleElimination
import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdge

/-!
# Higher-degree horizontal-edge comparison

The positive vertical components of a total cycle can be eliminated, leaving a
horizontal-axis cycle lifted from the augmenting complex.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u

namespace HomologicalComplex₂

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- Under exactness of the positive vertical rows, every positive-degree total
cycle is homologous to the horizontal-edge image of a cycle in the augmenting
complex. -/
theorem exists_horizontalEdge_cycle_sub_boundary
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (n : ℕ)
    (hrowAxis : (ShortComplex.mk (e (n + 1))
      ((K.X (n + 1)).d 0 1) (w (n + 1))).Exact)
    (hrowPositive : ∀ q p, q + p = n + 1 → 0 < p →
      (ShortComplex.mk
        ((K.X q).d (p - 1) p)
        ((K.X q).d p (p + 1))
        ((K.X q).d_comp_d (p - 1) p (p + 1))).Exact)
    [Mono (e (n + 2))]
    (x : (K.total (.up ℕ)).X (n + 1))
    (hx : (K.total (.up ℕ)).d (n + 1) (n + 2) x = 0) :
    ∃ a : A.X (n + 1), ∃ b : (K.total (.up ℕ)).X n,
      A.d (n + 1) (n + 2) a = 0 ∧
        x - (K.total (.up ℕ)).d n (n + 1) b =
          (K.totalUpNatHorizontalEdge A e he w).f (n + 1) a := by
  obtain ⟨b, hb⟩ :=
    K.exists_boundary_killing_components_lt n (n + 1) (by omega)
      x hx hrowPositive
  let y := x - (K.total (.up ℕ)).d n (n + 1) b
  have hy : (K.total (.up ℕ)).d (n + 1) (n + 2) y = 0 := by
    have hd := congrArg (fun f ↦ f b)
      ((K.total (.up ℕ)).d_comp_d n (n + 1) (n + 2))
    have hd' :
        (K.total (.up ℕ)).d (n + 1) (n + 2)
            ((K.total (.up ℕ)).d n (n + 1) b) = 0 := by
      simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
        AddMonoidHom.zero_apply] using hd
    simp only [y, map_sub, hx]
    rw [hd']
    simp
  have hleft :
      K.πTotalUpNat n 1 (n + 1) y = 0 := by
    have h := hb n (by omega)
    have hdeg : n + 1 - n = 1 := by omega
    rw [hdeg] at h
    change K.πTotalUpNat n 1 (n + 1) y = 0
    simpa only [y] using h
  have hvertical :
      (K.X (n + 1)).d 0 1
        (K.πTotalUpNat (n + 1) 0 (n + 1) y) = 0 :=
    K.cycle_vertical_of_left_component_eq_zero
      (n + 1) (n + 1) 0 (by omega) y hy
        (Or.inr (by
          have hpred : n + 1 - 1 = n := by omega
          rw [hpred]
          simpa using hleft))
  obtain ⟨a, ha⟩ :=
    ((ShortComplex.mk (e (n + 1))
      ((K.X (n + 1)).d 0 1) (w (n + 1))).ab_exact_iff.mp hrowAxis)
      (K.πTotalUpNat (n + 1) 0 (n + 1) y) hvertical
  have hhorizontal :
      (K.d (n + 1) (n + 2)).f 0
        (K.πTotalUpNat (n + 1) 0 (n + 1) y) = 0 := by
    have h := congrArg (fun f ↦ f y)
      (K.total_d_πTotalUpNat (n + 1) (n + 2) 0 (by omega))
    simpa [ConcreteCategory.comp_apply, hy] using h.symm
  have hnat :
      (K.d (n + 1) (n + 2)).f 0 (e (n + 1) a) =
        e (n + 2) (A.d (n + 1) (n + 2) a) := by
    have h := congrArg (fun f ↦ f a) (he (n + 1) (n + 2) rfl)
    simpa only [ConcreteCategory.comp_apply] using h
  have haCycle : A.d (n + 1) (n + 2) a = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (e (n + 2))).mp inferInstance
    rw [map_zero, ← hnat, ha, hhorizontal]
  have hedge :
      (K.totalUpNatHorizontalEdge A e he w).f (n + 1) a =
        K.ιTotal (.up ℕ) (n + 1) 0 (n + 1) rfl
          (K.πTotalUpNat (n + 1) 0 (n + 1) y) := by
    have h := congrArg (fun f ↦ f a)
      (K.totalUpNatHorizontalEdge_f A e he w (n + 1))
    simpa only [ConcreteCategory.comp_apply, ha] using h
  refine ⟨a, b, haCycle, ?_⟩
  change y = (K.totalUpNatHorizontalEdge A e he w).f (n + 1) a
  rw [hedge]
  exact (K.ιTotal_horizontalAxis_eq_of_components_lt_eq_zero
    (n + 1) y (fun q hq ↦ hb q hq)).symm

end HomologicalComplex₂
