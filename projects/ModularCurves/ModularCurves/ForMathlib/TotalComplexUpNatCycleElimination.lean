import ModularCurves.ForMathlib.TotalComplexUpNatDecomposition
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Component elimination in first-quadrant total complexes

Convert the total-cycle equation into vertical closedness of one bidegree
component, and compute the projections of a one-bidegree correction boundary.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped BigOperators

universe u

namespace HomologicalComplex₂

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- If the component immediately to the left is zero, the next component of a
total cycle is vertically closed. -/
theorem cycle_vertical_of_left_component_eq_zero
    (n q p : ℕ) (hqp : q + p = n)
    (x : (K.total (.up ℕ)).X n)
    (hx : (K.total (.up ℕ)).d n (n + 1) x = 0)
    (hleft : q = 0 ∨ K.πTotalUpNat (q - 1) (p + 1) n x = 0) :
    (K.X q).d p (p + 1) (K.πTotalUpNat q p n x) = 0 := by
  have h := congrArg (fun f ↦ f x)
    (K.total_d_πTotalUpNat n q (p + 1) (by omega))
  simp only [ConcreteCategory.comp_apply, hx, map_zero] at h
  have hhorizontal :
      (if _hq : 0 < q then
          K.πTotalUpNat (q - 1) (p + 1) n ≫
            (K.d (q - 1) q).f (p + 1)
        else 0) x = 0 := by
    split
    · obtain hq | hleft := hleft
      · omega
      · simp [hleft]
    · simp
  rw [AddCommGrpCat.hom_add_apply, hhorizontal, zero_add] at h
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ q) with hs | hs
  · simpa [hs] using h.symm
  · simpa [hs] using h.symm

/-- The vertical projection of the boundary of one bidegree component. -/
theorem total_boundary_π_vertical
    (n q p : ℕ) (hqp : q + p = n)
    (b : (K.X q).X p) :
    K.πTotalUpNat q (p + 1) (n + 1)
        ((K.total (.up ℕ)).d n (n + 1)
          (K.ιTotalOrZero (.up ℕ) q p n b)) =
      ((-1 : ℤˣ) ^ q) • ((K.X q).d p (p + 1) b) := by
  subst n
  rw [K.ιTotalOrZero_eq (.up ℕ) q p (q + p) rfl]
  have h := congrArg (fun f ↦ f b)
    (K.ιTotal_d_upNat_assoc q p
      (K.πTotalUpNat q (p + 1) (q + p + 1)))
  calc
    _ = (((-1 : ℤˣ) ^ q) • (K.X q).d p (p + 1)) b := by
      simpa [ConcreteCategory.comp_apply] using h
    _ = _ := by
      rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ q) with hs | hs
      · simp [hs]
      · simp [hs]

/-- Multiplying a correcting component by its Koszul sign makes its vertical
boundary project without a sign. -/
theorem total_boundary_π_vertical_negOnePow
    (n q p : ℕ) (hqp : q + p = n)
    (b : (K.X q).X p) :
    K.πTotalUpNat q (p + 1) (n + 1)
        ((K.total (.up ℕ)).d n (n + 1)
          (K.ιTotalOrZero (.up ℕ) q p n
            (((-1 : ℤˣ) ^ q) • b))) =
      (K.X q).d p (p + 1) b := by
  rw [K.total_boundary_π_vertical n q p hqp]
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ q) with hs | hs
  · simp [hs]
  · simp [hs]

/-- The horizontal projection of the boundary of one bidegree component. -/
theorem total_boundary_π_horizontal
    (n q p : ℕ) (hqp : q + p = n)
    (b : (K.X q).X p) :
    K.πTotalUpNat (q + 1) p (n + 1)
        ((K.total (.up ℕ)).d n (n + 1)
          (K.ιTotalOrZero (.up ℕ) q p n b)) =
      (K.d q (q + 1)).f p b := by
  subst n
  rw [K.ιTotalOrZero_eq (.up ℕ) q p (q + p) rfl]
  have h := congrArg (fun f ↦ f b)
    (K.ιTotal_d_upNat_assoc q p
      (K.πTotalUpNat (q + 1) p (q + p + 1)))
  simpa [ConcreteCategory.comp_apply] using h

/-- A one-bidegree correction boundary has zero projection in every strictly
earlier horizontal degree. -/
theorem total_boundary_π_eq_zero_of_lt
    (n q p i j : ℕ) (hqp : q + p = n) (hij : i + j = n + 1)
    (hi : i < q) (b : (K.X q).X p) :
    K.πTotalUpNat i j (n + 1)
        ((K.total (.up ℕ)).d n (n + 1)
          (K.ιTotalOrZero (.up ℕ) q p n b)) = 0 := by
  have h := congrArg
    (fun f ↦ f (K.ιTotalOrZero (.up ℕ) q p n b))
    (K.total_d_πTotalUpNat n i j hij)
  rw [K.ιTotalOrZero_eq (.up ℕ) q p n hqp] at h ⊢
  by_cases hi0 : 0 < i
  · have hqi : q ≠ i - 1 := by omega
    have hzHorizontal :
        K.πTotalUpNat (i - 1) j n
            (K.ιTotal (.up ℕ) q p n hqp b) = 0 := by
      change
        (K.ιTotal (.up ℕ) q p n hqp ≫
          K.πTotalUpNat (i - 1) j n) b = 0
      simp [hqi]
    by_cases hj0 : 0 < j
    · have hqi' : q ≠ i := by omega
      have hzVertical :
          K.πTotalUpNat i (j - 1) n
              (K.ιTotal (.up ℕ) q p n hqp b) = 0 := by
        change
          (K.ιTotal (.up ℕ) q p n hqp ≫
            K.πTotalUpNat i (j - 1) n) b = 0
        simp [hqi']
      rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ i) with hs | hs
      · simpa [hi0, hj0, hs, ConcreteCategory.comp_apply, hzHorizontal,
          hzVertical] using h
      · simpa [hi0, hj0, hs, ConcreteCategory.comp_apply, hzHorizontal,
          hzVertical] using h
    · simpa [hi0, hj0, ConcreteCategory.comp_apply, hzHorizontal] using h
  · by_cases hj0 : 0 < j
    · have hqi : q ≠ i := by omega
      have hzVertical :
          K.πTotalUpNat i (j - 1) n
              (K.ιTotal (.up ℕ) q p n hqp b) = 0 := by
        change
          (K.ιTotal (.up ℕ) q p n hqp ≫
            K.πTotalUpNat i (j - 1) n) b = 0
        simp [hqi]
      rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ i) with hs | hs
      · simpa [hi0, hj0, hs, ConcreteCategory.comp_apply, hzVertical] using h
      · simpa [hi0, hj0, hs, ConcreteCategory.comp_apply, hzVertical] using h
    · omega

/-- Exactness in the positive part of every vertical row lets us alter a total
cycle by a boundary so that all components before a prescribed horizontal
cutoff vanish. -/
theorem exists_boundary_killing_components_lt
    (n r : ℕ) (hr : r ≤ n + 1)
    (x : (K.total (.up ℕ)).X (n + 1))
    (hx : (K.total (.up ℕ)).d (n + 1) (n + 2) x = 0)
    (hrow : ∀ q p, q + p = n + 1 → 0 < p →
      (ShortComplex.mk
        ((K.X q).d (p - 1) p)
        ((K.X q).d p (p + 1))
        ((K.X q).d_comp_d (p - 1) p (p + 1))).Exact) :
    ∃ b : (K.total (.up ℕ)).X n,
      ∀ q, q < r →
        K.πTotalUpNat q (n + 1 - q) (n + 1)
          (x - (K.total (.up ℕ)).d n (n + 1) b) = 0 := by
  induction r with
  | zero =>
      refine ⟨0, ?_⟩
      intro q hq
      omega
  | succ r ih =>
      have hr' : r ≤ n + 1 := by omega
      obtain ⟨b, hb⟩ := ih hr'
      let p := n + 1 - r
      have hp : 0 < p := by
        dsimp [p]
        omega
      have hsum : r + p = n + 1 := by
        dsimp [p]
        omega
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
          r = 0 ∨ K.πTotalUpNat (r - 1) (p + 1) (n + 1) y = 0 := by
        by_cases hzero : r = 0
        · exact Or.inl hzero
        · right
          have hprev := hb (r - 1) (by omega)
          have hdeg : n + 1 - (r - 1) = p + 1 := by
            dsimp [p]
            omega
          rw [hdeg] at hprev
          change K.πTotalUpNat (r - 1) (p + 1) (n + 1) y = 0 at hprev
          exact hprev
      have hv :=
        K.cycle_vertical_of_left_component_eq_zero
          (n + 1) r p hsum y hy hleft
      obtain ⟨c, hc⟩ :=
        ((ShortComplex.mk
          ((K.X r).d (p - 1) p)
          ((K.X r).d p (p + 1))
          ((K.X r).d_comp_d (p - 1) p (p + 1))).ab_exact_iff.mp
            (hrow r p hsum hp))
          (K.πTotalUpNat r p (n + 1) y) hv
      have hsource : r + (p - 1) = n := by omega
      let t : (K.total (.up ℕ)).X n :=
        K.ιTotalOrZero (.up ℕ) r (p - 1) n
          (((-1 : ℤˣ) ^ r) • c)
      refine ⟨b + t, ?_⟩
      intro i hi
      have hy' :
          x - (K.total (.up ℕ)).d n (n + 1) (b + t) =
            y - (K.total (.up ℕ)).d n (n + 1) t := by
        simp only [map_add, y]
        abel
      rw [hy']
      by_cases hir : i = r
      · subst i
        change
          K.πTotalUpNat r p (n + 1)
            (y - (K.total (.up ℕ)).d n (n + 1) t) = 0
        rw [map_sub]
        change
          K.πTotalUpNat r p (n + 1) y -
            K.πTotalUpNat r p (n + 1)
              ((K.total (.up ℕ)).d n (n + 1)
                (K.ιTotalOrZero (.up ℕ) r (p - 1) n
                  (((-1 : ℤˣ) ^ r) • c))) = 0
        have hpsucc : p - 1 + 1 = p := by omega
        have hboundary :
            K.πTotalUpNat r p (n + 1)
                ((K.total (.up ℕ)).d n (n + 1)
                  (K.ιTotalOrZero (.up ℕ) r (p - 1) n
                    (((-1 : ℤˣ) ^ r) • c))) =
              (K.X r).d (p - 1) p c := by
          have h :=
            K.total_boundary_π_vertical_negOnePow n r (p - 1)
              hsource c
          rw [hpsucc] at h
          exact h
        rw [hboundary, hc, sub_self]
      · have hir' : i < r := by omega
        have hiy := hb i hir'
        have hit :=
          K.total_boundary_π_eq_zero_of_lt
            n r (p - 1) i (n + 1 - i) hsource (by omega) hir'
              (((-1 : ℤˣ) ^ r) • c)
        change
          K.πTotalUpNat i (n + 1 - i) (n + 1)
            (y - (K.total (.up ℕ)).d n (n + 1) t) = 0
        rw [map_sub, hiy]
        change
          0 -
            K.πTotalUpNat i (n + 1 - i) (n + 1)
              ((K.total (.up ℕ)).d n (n + 1)
                (K.ιTotalOrZero (.up ℕ) r (p - 1) n
                  (((-1 : ℤˣ) ^ r) • c))) = 0
        rw [hit, sub_zero]

private theorem totalUpNat_decomposition_apply
    (n : ℕ) (x : (K.total (.up ℕ)).X n) :
    ∑ qp ∈ Finset.antidiagonal n,
      K.ιTotalOrZero (.up ℕ) qp.1 qp.2 n
        (K.πTotalUpNat qp.1 qp.2 n x) = x := by
  classical
  have sum_apply
      (s : Finset (ℕ × ℕ))
      (f : ℕ × ℕ → ((K.total (.up ℕ)).X n ⟶
        (K.total (.up ℕ)).X n)) :
      (∑ qp ∈ s, f qp) x = ∑ qp ∈ s, f qp x := by
    let ev : (((K.total (.up ℕ)).X n ⟶
        (K.total (.up ℕ)).X n) →+ (K.total (.up ℕ)).X n) :=
      { toFun := fun g ↦ g x
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    exact map_sum ev f s
  have h := congrArg (fun f ↦ f x) (K.totalUpNat_decomposition n)
  rw [sum_apply] at h
  simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using h

/-- If every component before the horizontal axis vanishes, a total-complex
element is the inclusion of its horizontal-axis component. -/
theorem ιTotal_horizontalAxis_eq_of_components_lt_eq_zero
    (n : ℕ) (x : (K.total (.up ℕ)).X n)
    (hx : ∀ q, q < n →
      K.πTotalUpNat q (n - q) n x = 0) :
    K.ιTotal (.up ℕ) n 0 n rfl
        (K.πTotalUpNat n 0 n x) = x := by
  classical
  calc
    _ = ∑ qp ∈ Finset.antidiagonal n,
        K.ιTotalOrZero (.up ℕ) qp.1 qp.2 n
          (K.πTotalUpNat qp.1 qp.2 n x) := by
      rw [Finset.sum_eq_single (n, 0)]
      · rw [K.ιTotalOrZero_eq (.up ℕ) n 0 n rfl]
      · rintro ⟨q, p⟩ hmem hne
        have hsum : q + p = n := Finset.mem_antidiagonal.mp hmem
        have hq : q < n := by
          by_contra hnq
          have hqn : q = n := by omega
          subst q
          have hp : p = 0 := by omega
          exact hne (Prod.ext rfl hp)
        have hp : p = n - q := by omega
        subst p
        rw [hx q hq, map_zero]
      · intro hnot
        exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim
    _ = x := K.totalUpNat_decomposition_apply n x

end HomologicalComplex₂
