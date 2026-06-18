import HasseWeil.Curves.ProjectiveTuple

/-!
# Rational maps from a smooth curve to projective space

For a smooth plane curve `C` and a projective tuple `φ : C.ProjectiveTuple N`,
we define:

* `ProjectiveTuple.IsRegularAt φ P` — there exists a representative `[f₀, …, f_N]`
  with `ord_P f_i ≥ 0` for every `i` and `ord_P f_j = 0` for some `j`.
* `ProjectiveTuple.IsMorphism φ` — regular at every smooth point.

The **main theorem** (Silverman II.2.1, `isRegularAt_of_smooth`) is that
every rational map from a smooth curve is a morphism: given a representative
`[f₀, …, f_N]` and a uniformizer `t` at `P`, scaling by `t^(-n)` where
`n = min_i ord_P f_i` yields a representative satisfying the conditions.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.1
-/

open WithTop

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

namespace ProjectiveTuple

variable {F : Type*} [Field F] {C : SmoothPlaneCurve F} {N : ℕ}

/-- A projective tuple is **regular at** `P` if it admits a representative
`[f₀, …, f_N]` with every `ord_P f_i ≥ 0` and some `ord_P f_j = 0`.
Reference: Silverman I.3 / II.2 definition. -/
def IsRegularAt (φ : ProjectiveTuple C N) (P : C.SmoothPoint) : Prop :=
  ∃ f : Fin (N + 1) → C.FunctionField, ∃ hf : f ≠ 0,
    mk f hf = φ ∧
      (∀ i, (0 : WithTop ℤ) ≤ C.ord_P P (f i)) ∧
      (∃ j, C.ord_P P (f j) = 0)

/-- A **morphism** `C → ℙᴺ` is a rational map (projective tuple) regular at
every smooth point. Reference: Silverman I.3 Remark 3.2 / II.2.1. -/
def IsMorphism (φ : ProjectiveTuple C N) : Prop :=
  ∀ P : C.SmoothPoint, φ.IsRegularAt P

/-! ### Proposition II.2.1 -/

/-- Scaling a representative by a unit preserves the projective tuple.
Reference: standard property of projective space. -/
theorem mk_smul_eq_mk (s : C.FunctionField) (hs : s ≠ 0)
    (f : Fin (N + 1) → C.FunctionField) (hf : f ≠ 0) :
    mk (fun i ↦ s * f i) (fun h ↦ hf <| funext fun i ↦
      (mul_eq_zero.mp (congrFun h i)).resolve_left hs) = mk f hf := by
  apply (mk_eq_mk_iff _ hf).mpr
  exact ⟨Units.mk0 s hs, funext fun i ↦ rfl⟩

/-- **Silverman II.2.1**: every rational map from a smooth plane curve is
regular at every smooth point (hence a morphism). Proof: pick `j`
minimizing `ord_P(repr i)` over all `i` (via `Finset.exists_min_image`);
since `φ.repr ≠ 0`, `repr j ≠ 0`; scale by `s` with `ord_P s = -m` (where
`m = ord_P(repr j)`) via `Uniformizer.exists_ord_P_eq`. -/
theorem isRegularAt_of_smooth (φ : ProjectiveTuple C N) (P : C.SmoothPoint) :
    φ.IsRegularAt P := by
  have hf : φ.repr ≠ 0 := φ.repr_ne_zero
  obtain ⟨t, ht⟩ := C.exists_uniformizer P
  -- Find j minimizing ord_P(repr ·).
  obtain ⟨j, _, hj_min⟩ := (Finset.univ : Finset (Fin (N + 1))).exists_min_image
    (fun i ↦ C.ord_P P (φ.repr i)) Finset.univ_nonempty
  -- `repr j ≠ 0`: else ord_P(repr j) = ⊤ ≤ ord_P(repr i) ⟹ all are ⊤ ⟹ repr = 0.
  have hj_ne : φ.repr j ≠ 0 := by
    intro h_j_zero
    refine hf (funext fun i ↦ ?_)
    rw [Pi.zero_apply, ← ord_P_eq_top_iff]
    exact le_antisymm le_top
      ((ord_P_eq_top_iff _).mpr h_j_zero ▸ hj_min i (Finset.mem_univ _))
  have hj_lt : C.ord_P P (φ.repr j) ≠ ⊤ :=
    (not_iff_not.mpr (ord_P_eq_top_iff _)).mpr hj_ne
  set m : ℤ := (C.ord_P P (φ.repr j)).untop hj_lt with hm_def
  have hm_eq : C.ord_P P (φ.repr j) = (m : ℤ) := (WithTop.coe_untop _ _).symm
  obtain ⟨s, hs_ne, hs_ord⟩ := ht.exists_ord_P_eq (-m)
  set f : Fin (N + 1) → C.FunctionField := fun i ↦ s * φ.repr i with hf_def
  have hf_j_ne : f j ≠ 0 := mul_ne_zero hs_ne hj_ne
  have hf_ne : f ≠ 0 := fun h ↦ hf_j_ne (congrFun h j)
  refine ⟨f, hf_ne, ?_, ?_, j, ?_⟩
  · exact (mk_smul_eq_mk s hs_ne φ.repr hf).trans φ.mk_repr
  · intro i
    change 0 ≤ C.ord_P P (s * φ.repr i)
    rw [ord_P_mul, hs_ord]
    by_cases hi : φ.repr i = 0
    · rw [(ord_P_eq_top_iff _).mpr hi]
      rw [show ((↑(-m) : WithTop ℤ) + ⊤ : WithTop ℤ) = ⊤ from by
        cases hs_ord_cases : C.ord_P P s <;> rfl]
      exact le_top
    · have h_top_i : C.ord_P P (φ.repr i) ≠ ⊤ :=
        (not_iff_not.mpr (ord_P_eq_top_iff _)).mpr hi
      set k : ℤ := (C.ord_P P (φ.repr i)).untop h_top_i with hk_def
      have hk_eq : C.ord_P P (φ.repr i) = (k : ℤ) := (WithTop.coe_untop _ _).symm
      have h_ge : C.ord_P P (φ.repr j) ≤ C.ord_P P (φ.repr i) :=
        hj_min i (Finset.mem_univ _)
      rw [hm_eq, hk_eq] at h_ge
      have hmk : m ≤ k := WithTop.coe_le_coe.mp h_ge
      rw [hk_eq, ← WithTop.coe_add]
      exact_mod_cast (by omega : (0 : ℤ) ≤ -m + k)
  · change C.ord_P P (s * φ.repr j) = 0
    rw [ord_P_mul, hs_ord, hm_eq, ← WithTop.coe_add,
      show (-m + m : ℤ) = 0 from by omega]
    rfl

/-- **Silverman II.2.1 (corollary)**: every rational map from a smooth
plane curve to projective space is a morphism. -/
theorem isMorphism_of_smooth (φ : ProjectiveTuple C N) : φ.IsMorphism :=
  fun P ↦ φ.isRegularAt_of_smooth P

end ProjectiveTuple

end SmoothPlaneCurve

end HasseWeil.Curves
