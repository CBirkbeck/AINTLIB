import ModularCurves.ForMathlib.TotalComplexUpNatCycleElimination
import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdge
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Higher-degree horizontal-edge comparison

The positive vertical components of a total cycle can be eliminated, leaving a
horizontal-axis cycle lifted from the augmenting complex.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u

namespace HomologicalComplex₂

private theorem up_prev_succ (n : ℕ) :
    (ComplexShape.up ℕ).prev (n + 1) = n :=
  (ComplexShape.up ℕ).prev_eq' rfl

private theorem up_next_succ (n : ℕ) :
    (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
  (ComplexShape.up ℕ).next_eq' rfl

private noncomputable def abCyclesMkAt
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    (x : L.X (n + 1))
    (hx : L.d (n + 1) (n + 2) x = 0) :
    L.cycles (n + 1) :=
  (L.cyclesIsoSc' n (n + 1) (n + 2)
    (up_prev_succ n) (up_next_succ n)).inv
      ((L.sc' n (n + 1) (n + 2)).abCyclesIso.inv ⟨x, hx⟩)

@[simp]
private theorem i_abCyclesMkAt
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    (x : L.X (n + 1))
    (hx : L.d (n + 1) (n + 2) x = 0) :
    L.iCycles (n + 1) (abCyclesMkAt L n x hx) = x := by
  have h₁ := congrArg
    (fun g ↦ g ((L.sc' n (n + 1) (n + 2)).abCyclesIso.inv ⟨x, hx⟩))
    (L.cyclesIsoSc'_inv_iCycles n (n + 1) (n + 2)
      (up_prev_succ n) (up_next_succ n))
  simp only [ConcreteCategory.comp_apply] at h₁
  have h₂ := (L.sc' n (n + 1) (n + 2)).abCyclesIso_inv_apply_iCycles
    ⟨x, hx⟩
  exact h₁.trans h₂

private theorem homologyπ_abCyclesMkAt_eq_of_sub_eq_boundary
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    (x y : L.X (n + 1))
    (hx : L.d (n + 1) (n + 2) x = 0)
    (hy : L.d (n + 1) (n + 2) y = 0)
    (b : L.X n) (hxy : x - y = L.d n (n + 1) b) :
    L.homologyπ (n + 1) (abCyclesMkAt L n x hx) =
      L.homologyπ (n + 1) (abCyclesMkAt L n y hy) := by
  rw [← sub_eq_zero, ← map_sub]
  have hcycles :
      abCyclesMkAt L n x hx - abCyclesMkAt L n y hy =
        L.toCycles n (n + 1) b := by
    apply (AddCommGrpCat.mono_iff_injective
      (L.iCycles (n + 1))).mp inferInstance
    simp only [map_sub, i_abCyclesMkAt]
    have h := congrArg (fun f ↦ f b)
      (L.toCycles_i n (n + 1))
    exact hxy.trans (by
      simpa only [ConcreteCategory.comp_apply] using h.symm)
  rw [hcycles]
  have h := congrArg (fun f ↦ f b)
    (L.toCycles_comp_homologyπ n (n + 1))
  simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply] using h

private theorem homologyMap_abCyclesMkAt
    {L M : CochainComplex AddCommGrpCat.{u} ℕ} (f : L ⟶ M)
    (n : ℕ) (x : L.X (n + 1))
    (hx : L.d (n + 1) (n + 2) x = 0)
    (hfx : M.d (n + 1) (n + 2) (f.f (n + 1) x) = 0) :
    HomologicalComplex.homologyMap f (n + 1)
        (L.homologyπ (n + 1) (abCyclesMkAt L n x hx)) =
      M.homologyπ (n + 1)
        (abCyclesMkAt M n (f.f (n + 1) x) hfx) := by
  have hcycles :
      HomologicalComplex.cyclesMap f (n + 1)
          (abCyclesMkAt L n x hx) =
        abCyclesMkAt M n (f.f (n + 1) x) hfx := by
    apply (AddCommGrpCat.mono_iff_injective
      (M.iCycles (n + 1))).mp inferInstance
    have h := congrArg
      (fun g ↦ g (abCyclesMkAt L n x hx))
      (HomologicalComplex.cyclesMap_i f (n + 1))
    simpa only [ConcreteCategory.comp_apply, i_abCyclesMkAt] using h
  have h := congrArg
    (fun g ↦ g (abCyclesMkAt L n x hx))
    (HomologicalComplex.homologyπ_naturality
      (φ := f) (i := n + 1))
  simpa only [ConcreteCategory.comp_apply, hcycles] using h

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

/-- The horizontal-edge map is surjective on homology in every positive degree
when the corresponding positive vertical rows are exact. -/
theorem totalUpNatHorizontalEdge_homologyMap_surjective_of_positive
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
    [Mono (e (n + 2))] :
    Function.Surjective (HomologicalComplex.homologyMap
      (K.totalUpNatHorizontalEdge A e he w) (n + 1)) := by
  let T := K.total (.up ℕ)
  let edge := K.totalUpNatHorizontalEdge A e he w
  intro ξ
  have hπ : Function.Surjective (T.homologyπ (n + 1)) :=
    (AddCommGrpCat.epi_iff_surjective
      (T.homologyπ (n + 1))).mp inferInstance
  obtain ⟨xc, rfl⟩ := hπ ξ
  let x : T.X (n + 1) := T.iCycles (n + 1) xc
  have hx : T.d (n + 1) (n + 2) x = 0 := by
    have h := congrArg (fun g ↦ g xc)
      (T.iCycles_d (n + 1) (n + 2))
    simpa only [x, ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  obtain ⟨a, b, haCycle, hdiff⟩ :=
    K.exists_horizontalEdge_cycle_sub_boundary A e he w n hrowAxis
      hrowPositive x hx
  have hedgeCycle :
      T.d (n + 1) (n + 2) (edge.f (n + 1) a) = 0 := by
    have h := congrArg (fun g ↦ g a)
      (edge.comm (n + 1) (n + 2))
    simpa only [ConcreteCategory.comp_apply, haCycle, map_zero] using h
  have hxc : abCyclesMkAt T n x hx = xc := by
    apply (AddCommGrpCat.mono_iff_injective
      (T.iCycles (n + 1))).mp inferInstance
    simp only [i_abCyclesMkAt, x]
  have hdiff' :
      x - edge.f (n + 1) a = T.d n (n + 1) b := by
    rw [← hdiff]
    abel
  refine ⟨A.homologyπ (n + 1)
    (abCyclesMkAt A n a haCycle), ?_⟩
  calc
    HomologicalComplex.homologyMap edge (n + 1)
        (A.homologyπ (n + 1)
          (abCyclesMkAt A n a haCycle)) =
      T.homologyπ (n + 1)
        (abCyclesMkAt T n (edge.f (n + 1) a) hedgeCycle) :=
        homologyMap_abCyclesMkAt edge n a haCycle hedgeCycle
    _ = T.homologyπ (n + 1)
        (abCyclesMkAt T n x hx) :=
      (homologyπ_abCyclesMkAt_eq_of_sub_eq_boundary
        T n x (edge.f (n + 1) a) hx hedgeCycle b hdiff').symm
    _ = T.homologyπ (n + 1) xc := by rw [hxc]

private theorem horizontalEdge_π_eq_zero_of_lt
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (d q p : ℕ) (hqp : q + p = d) (hq : q < d)
    (a : A.X d) :
    K.πTotalUpNat q p d
      ((K.totalUpNatHorizontalEdge A e he w).f d a) = 0 := by
  have h := congrArg (fun f ↦ f a)
    (K.totalUpNatHorizontalEdge_f A e he w d)
  rw [h]
  change
    (K.ιTotal (.up ℕ) d 0 d rfl ≫
      K.πTotalUpNat q p d) (e d a) = 0
  have hdq : d ≠ q := by omega
  simp [hdq]

private theorem horizontalEdge_π_horizontalAxis
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (d : ℕ) (a : A.X d) :
    K.πTotalUpNat d 0 d
      ((K.totalUpNatHorizontalEdge A e he w).f d a) = e d a := by
  have h := congrArg (fun f ↦ f a)
    (K.totalUpNatHorizontalEdge_f A e he w d)
  rw [h]
  change
    (K.ιTotal (.up ℕ) d 0 d rfl ≫
      K.πTotalUpNat d 0 d) (e d a) = e d a
  simp

/-- If a positive-degree horizontal-edge element is a total boundary, then the
original element is already a boundary in the augmenting complex. -/
theorem exists_boundary_of_horizontalEdge_eq_total_boundary
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (n : ℕ)
    (hrowAxis : (ShortComplex.mk (e n)
      ((K.X n).d 0 1) (w n)).Exact)
    (hrowPositive : ∀ q p, q + p = n → 0 < p →
      (ShortComplex.mk
        ((K.X q).d (p - 1) p)
        ((K.X q).d p (p + 1))
        ((K.X q).d_comp_d (p - 1) p (p + 1))).Exact)
    [Mono (e (n + 1))]
    (a : A.X (n + 1)) (b : (K.total (.up ℕ)).X n)
    (hb : (K.totalUpNatHorizontalEdge A e he w).f (n + 1) a =
      (K.total (.up ℕ)).d n (n + 1) b) :
    ∃ c : A.X n, A.d n (n + 1) c = a := by
  let T := K.total (.up ℕ)
  let edge := K.totalUpNatHorizontalEdge A e he w
  have hedgeZero :
      ∀ q, q < n + 1 →
        K.πTotalUpNat q (n + 1 - q) (n + 1)
          (edge.f (n + 1) a) = 0 := by
    intro q hq
    exact K.horizontalEdge_π_eq_zero_of_lt A e he w
      (n + 1) q (n + 1 - q) (by omega) hq a
  obtain ⟨b', hb'Components, hb'Differential⟩ :
      ∃ b' : T.X n,
        (∀ q, q < n →
          K.πTotalUpNat q (n - q) n b' = 0) ∧
        T.d n (n + 1) b' = edge.f (n + 1) a := by
    cases n with
    | zero =>
        refine ⟨b, ?_, hb.symm⟩
        intro q hq
        omega
    | succ m =>
        have hdSupport :
            ∀ q, q < m + 1 →
              K.πTotalUpNat q (m + 2 - q) (m + 2)
                (T.d (m + 1) (m + 2) b) = 0 := by
          intro q hq
          rw [← hb]
          exact hedgeZero q (by omega)
        obtain ⟨c, hc⟩ :=
          K.exists_boundary_killing_components_lt_of_differential_components_eq_zero
            m (m + 1) (by omega) b hdSupport hrowPositive
        let b' := b - T.d m (m + 1) c
        refine ⟨b', hc, ?_⟩
        have hd := congrArg (fun f ↦ f c)
          (T.d_comp_d m (m + 1) (m + 2))
        have hd' : T.d (m + 1) (m + 2)
            (T.d m (m + 1) c) = 0 := by
          simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
            AddMonoidHom.zero_apply] using hd
        simp only [b', map_sub, hd', sub_zero]
        exact hb.symm
  let β := K.πTotalUpNat n 0 n b'
  have haxis :
      K.ιTotal (.up ℕ) n 0 n rfl β = b' :=
    K.ιTotal_horizontalAxis_eq_of_components_lt_eq_zero
      n b' hb'Components
  have hdVertical :
      K.πTotalUpNat n 1 (n + 1) (T.d n (n + 1) b') = 0 := by
    rw [hb'Differential]
    exact K.horizontalEdge_π_eq_zero_of_lt A e he w
      (n + 1) n 1 (by omega) (by omega) a
  have hleft :
      n = 0 ∨ K.πTotalUpNat (n - 1) 1 n b' = 0 := by
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      have h := hb'Components (n - 1) (by omega)
      have hdeg : n - (n - 1) = 1 := by omega
      rw [hdeg] at h
      exact h
  have hβVertical :
      (K.X n).d 0 1 β = 0 :=
    K.component_vertical_of_left_component_eq_zero
      n n 0 (by omega) b' hdVertical hleft
  obtain ⟨c, hc⟩ :=
    ((ShortComplex.mk (e n) ((K.X n).d 0 1) (w n)).ab_exact_iff.mp
      hrowAxis) β hβVertical
  have hedgeAxis :
      K.πTotalUpNat (n + 1) 0 (n + 1)
        (edge.f (n + 1) a) = e (n + 1) a :=
    K.horizontalEdge_π_horizontalAxis A e he w (n + 1) a
  have hboundaryAxis :
      K.πTotalUpNat (n + 1) 0 (n + 1)
          (T.d n (n + 1)
            (K.ιTotal (.up ℕ) n 0 n rfl β)) =
        (K.d n (n + 1)).f 0 β := by
    simpa only [K.ιTotalOrZero_eq (.up ℕ) n 0 n rfl] using
      K.total_boundary_π_horizontal n n 0 (by omega) β
  have hea :
      e (n + 1) a = (K.d n (n + 1)).f 0 β := by
    calc
      _ = K.πTotalUpNat (n + 1) 0 (n + 1)
          (edge.f (n + 1) a) := hedgeAxis.symm
      _ = K.πTotalUpNat (n + 1) 0 (n + 1)
          (T.d n (n + 1) b') := by rw [hb'Differential]
      _ = K.πTotalUpNat (n + 1) 0 (n + 1)
          (T.d n (n + 1)
            (K.ιTotal (.up ℕ) n 0 n rfl β)) := by rw [haxis]
      _ = _ := hboundaryAxis
  have hnat :
      (K.d n (n + 1)).f 0 (e n c) =
        e (n + 1) (A.d n (n + 1) c) := by
    have h := congrArg (fun f ↦ f c) (he n (n + 1) rfl)
    simpa only [ConcreteCategory.comp_apply] using h
  refine ⟨c, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (e (n + 1))).mp inferInstance
  calc
    e (n + 1) (A.d n (n + 1) c) =
        (K.d n (n + 1)).f 0 (e n c) := hnat.symm
    _ = (K.d n (n + 1)).f 0 β := by rw [hc]
    _ = e (n + 1) a := hea.symm

private theorem exists_boundary_of_homologyπ_abCyclesMkAt_eq_zero
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    (x : L.X (n + 1))
    (hx : L.d (n + 1) (n + 2) x = 0)
    (hzero : L.homologyπ (n + 1)
      (abCyclesMkAt L n x hx) = 0) :
    ∃ b : L.X n, L.d n (n + 1) b = x := by
  let S := ShortComplex.mk
    (L.toCycles n (n + 1)) (L.homologyπ (n + 1))
      (L.toCycles_comp_homologyπ n (n + 1))
  have hExact : S.Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      (L.homologyIsCokernel n (n + 1) (up_prev_succ n))
  obtain ⟨b, hb⟩ :=
    (S.ab_exact_iff.mp hExact) (abCyclesMkAt L n x hx) hzero
  refine ⟨b, ?_⟩
  have h := congrArg (fun f ↦ f b)
    (L.toCycles_i n (n + 1))
  have hb' := congrArg (fun z ↦ L.iCycles (n + 1) z) hb
  simpa only [S, ConcreteCategory.comp_apply, i_abCyclesMkAt] using
    h.symm.trans hb'

/-- The horizontal-edge map is injective on homology in every positive degree
when the corresponding positive vertical rows are exact. -/
theorem totalUpNatHorizontalEdge_homologyMap_injective_of_positive
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (n : ℕ)
    (hrowAxis : (ShortComplex.mk (e n)
      ((K.X n).d 0 1) (w n)).Exact)
    (hrowPositive : ∀ q p, q + p = n → 0 < p →
      (ShortComplex.mk
        ((K.X q).d (p - 1) p)
        ((K.X q).d p (p + 1))
        ((K.X q).d_comp_d (p - 1) p (p + 1))).Exact)
    [Mono (e (n + 1))] :
    Function.Injective (HomologicalComplex.homologyMap
      (K.totalUpNatHorizontalEdge A e he w) (n + 1)) := by
  let T := K.total (.up ℕ)
  let edge := K.totalUpNatHorizontalEdge A e he w
  intro ξ η hξη
  rw [← sub_eq_zero]
  have hmapzero :
      HomologicalComplex.homologyMap edge (n + 1) (ξ - η) = 0 := by
    rw [map_sub, hξη, sub_self]
  have hπ : Function.Surjective (A.homologyπ (n + 1)) :=
    (AddCommGrpCat.epi_iff_surjective
      (A.homologyπ (n + 1))).mp inferInstance
  obtain ⟨ac, hac⟩ := hπ (ξ - η)
  let a : A.X (n + 1) := A.iCycles (n + 1) ac
  have haCycle : A.d (n + 1) (n + 2) a = 0 := by
    have h := congrArg (fun g ↦ g ac)
      (A.iCycles_d (n + 1) (n + 2))
    simpa only [a, ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  have hedgeCycle :
      T.d (n + 1) (n + 2) (edge.f (n + 1) a) = 0 := by
    have h := congrArg (fun g ↦ g a)
      (edge.comm (n + 1) (n + 2))
    simpa only [ConcreteCategory.comp_apply, haCycle, map_zero] using h
  have hac' : abCyclesMkAt A n a haCycle = ac := by
    apply (AddCommGrpCat.mono_iff_injective
      (A.iCycles (n + 1))).mp inferInstance
    simp only [i_abCyclesMkAt, a]
  have hedgeClassZero :
      T.homologyπ (n + 1)
        (abCyclesMkAt T n (edge.f (n + 1) a) hedgeCycle) = 0 := by
    calc
      _ = HomologicalComplex.homologyMap edge (n + 1)
          (A.homologyπ (n + 1)
            (abCyclesMkAt A n a haCycle)) :=
        (homologyMap_abCyclesMkAt edge n a haCycle hedgeCycle).symm
      _ = HomologicalComplex.homologyMap edge (n + 1) (ξ - η) := by
        rw [hac', hac]
      _ = 0 := hmapzero
  obtain ⟨b, hb⟩ :=
    exists_boundary_of_homologyπ_abCyclesMkAt_eq_zero
      T n (edge.f (n + 1) a) hedgeCycle hedgeClassZero
  obtain ⟨c, hc⟩ :=
    K.exists_boundary_of_horizontalEdge_eq_total_boundary
      A e he w n hrowAxis hrowPositive a b hb.symm
  have hzeroCycle : A.d (n + 1) (n + 2) (0 : A.X (n + 1)) = 0 := by
    simp
  have habZero : abCyclesMkAt A n 0 hzeroCycle = 0 := by
    apply (AddCommGrpCat.mono_iff_injective
      (A.iCycles (n + 1))).mp inferInstance
    simp only [i_abCyclesMkAt, map_zero]
  have haClassZero :
      A.homologyπ (n + 1) (abCyclesMkAt A n a haCycle) = 0 := by
    calc
      _ = A.homologyπ (n + 1)
          (abCyclesMkAt A n 0 hzeroCycle) :=
        homologyπ_abCyclesMkAt_eq_of_sub_eq_boundary
          A n a 0 haCycle hzeroCycle c
            (by simpa only [sub_zero] using hc.symm)
      _ = 0 := by rw [habZero, map_zero]
  calc
    ξ - η = A.homologyπ (n + 1) ac := hac.symm
    _ = A.homologyπ (n + 1)
        (abCyclesMkAt A n a haCycle) := by rw [hac']
    _ = 0 := haClassZero

/-- The horizontal-edge map is a quasi-isomorphism in every positive degree
when the two adjacent positive vertical rows are exact. -/
theorem totalUpNatHorizontalEdge_quasiIsoAt_succ
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (n : ℕ)
    (hrowAxis_n : (ShortComplex.mk (e n)
      ((K.X n).d 0 1) (w n)).Exact)
    (hrowAxis_succ : (ShortComplex.mk (e (n + 1))
      ((K.X (n + 1)).d 0 1) (w (n + 1))).Exact)
    (hrowPositive_n : ∀ q p, q + p = n → 0 < p →
      (ShortComplex.mk
        ((K.X q).d (p - 1) p)
        ((K.X q).d p (p + 1))
        ((K.X q).d_comp_d (p - 1) p (p + 1))).Exact)
    (hrowPositive_succ : ∀ q p, q + p = n + 1 → 0 < p →
      (ShortComplex.mk
        ((K.X q).d (p - 1) p)
        ((K.X q).d p (p + 1))
        ((K.X q).d_comp_d (p - 1) p (p + 1))).Exact)
    [Mono (e (n + 1))] [Mono (e (n + 2))] :
    QuasiIsoAt (K.totalUpNatHorizontalEdge A e he w) (n + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let f := HomologicalComplex.homologyMap
    (K.totalUpNatHorizontalEdge A e he w) (n + 1)
  haveI : Mono f := (AddCommGrpCat.mono_iff_injective f).mpr
    (K.totalUpNatHorizontalEdge_homologyMap_injective_of_positive
      A e he w n hrowAxis_n hrowPositive_n)
  haveI : Epi f := (AddCommGrpCat.epi_iff_surjective f).mpr
    (K.totalUpNatHorizontalEdge_homologyMap_surjective_of_positive
      A e he w n hrowAxis_succ hrowPositive_succ)
  exact isIso_of_mono_of_epi f

end HomologicalComplex₂
