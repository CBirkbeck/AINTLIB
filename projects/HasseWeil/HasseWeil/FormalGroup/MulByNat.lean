import HasseWeil.FormalGroup.Definition

/-!
# Multiplication by a natural number as a formal-group homomorphism (Silverman IV.2)

This file packages `HasseWeil.FG.mulByNatSeries F n` as a
`HasseWeil.FormalGroup.FormalGroupHom F F`, providing the missing
`preserves_add` axiom:
`[n](F(X, Y)) = F([n](X), [n](Y))`.

## Main definitions

* `HasseWeil.FormalGroup.FormalGroup.mulByNatHom F n` — the `FormalGroupHom F F`
  whose underlying series is `mulByNatSeries F n`.

## Main results

* `HasseWeil.FG.mulByNatSeries_preserves_add` — the identity
  `[n](F(X, Y)) = F([n](X), [n](Y))` in `MvPowerSeries (Fin 2) R`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.2.3.
-/

open MvPowerSeries

set_option linter.dupNamespace false

namespace HasseWeil.FG

variable {R : Type*} [CommRing R]

/-! ### Bivariate evaluation of a formal group law

We mirror `fAdd` (univariate target) with a bivariate variant `fAdd₂` that
evaluates `F(a, b)` for `a, b : MvPowerSeries (Fin 2) R`, giving bivariate
analogues of `fAdd_assoc` and `fAdd_comm`. -/

/-- `F(a, b)` for bivariate power series `a, b : MvPowerSeries (Fin 2) R`. -/
private noncomputable def fAdd₂ (F : FormalGroup.FormalGroup R)
    (a b : MvPowerSeries (Fin 2) R) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries (Fin 2) R) F.toSeries

private lemma hasSubst_pair₂ (a b : MvPowerSeries (Fin 2) R)
    (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s <;> simpa

private lemma hasSubst_triple₂ (a b c : MvPowerSeries (Fin 2) R)
    (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0)
    (hc : MvPowerSeries.constantCoeff c = 0) :
    MvPowerSeries.HasSubst
      (![a, b, c] : Fin 3 → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s <;> simpa

private lemma constantCoeff_fAdd₂ (F : FormalGroup.FormalGroup R)
    (a b : MvPowerSeries (Fin 2) R)
    (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (fAdd₂ F a b) = 0 := by
  unfold fAdd₂
  rw [constantCoeff_subst_vanishing (hasSubst_pair₂ a b ha hb)
    (fun s => by fin_cases s <;> simpa)]
  exact constantCoeff_FG_toSeries F

/-! ### Bivariate assoc and comm -/

set_option maxHeartbeats 800000 in
-- Deeply nested `MvPowerSeries.subst` expressions; the default limit is exceeded
-- while unifying the `Fin 3 → MvPowerSeries (Fin 2) R` specialization of `F.assoc`.
/-- Associativity of the bivariate `F`-addition: for `a, b, c` with vanishing
constant coefficients, `F(F(a, b), c) = F(a, F(b, c))`. -/
private theorem fAdd₂_assoc (F : FormalGroup.FormalGroup R)
    (a b c : MvPowerSeries (Fin 2) R)
    (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0)
    (hc : MvPowerSeries.constantCoeff c = 0) :
    fAdd₂ F (fAdd₂ F a b) c = fAdd₂ F a (fAdd₂ F b c) := by
  have h_XY : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have h_YZ : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
        Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have h_FXY_Z : MvPowerSeries.HasSubst
      (![MvPowerSeries.subst
            (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
              Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries,
          MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s
    · exact (constantCoeff_subst_vanishing h_XY (fun s => by fin_cases s <;> simp)
        F.toSeries).trans (constantCoeff_FG_toSeries F)
    · simp
  have h_X_FYZ : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 3),
          MvPowerSeries.subst
            (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
              Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries] :
        Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s
    · simp
    · exact (constantCoeff_subst_vanishing h_YZ (fun s => by fin_cases s <;> simp)
        F.toSeries).trans (constantCoeff_FG_toSeries F)
  have h_abc : MvPowerSeries.HasSubst
      (![a, b, c] : Fin 3 → MvPowerSeries (Fin 2) R) :=
    hasSubst_triple₂ a b c ha hb hc
  have comp_L : MvPowerSeries.subst (![a, b, c] : Fin 3 → MvPowerSeries (Fin 2) R)
      (MvPowerSeries.subst
        (![MvPowerSeries.subst
              (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
                Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries,
            MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries) =
      fAdd₂ F (fAdd₂ F a b) c := by
    rw [MvPowerSeries.subst_comp_subst_apply h_FXY_Z h_abc]
    unfold fAdd₂
    congr 1; funext s; fin_cases s
    · change MvPowerSeries.subst _ (MvPowerSeries.subst _ F.toSeries) = _
      rw [MvPowerSeries.subst_comp_subst_apply h_XY h_abc]
      congr 1; funext s; fin_cases s
      · exact subst_fin3_X _ h_abc 0
      · exact subst_fin3_X _ h_abc 1
    · change MvPowerSeries.subst _ (MvPowerSeries.X 2) = _
      exact subst_fin3_X _ h_abc 2
  have comp_R : MvPowerSeries.subst (![a, b, c] : Fin 3 → MvPowerSeries (Fin 2) R)
      (MvPowerSeries.subst
        (![MvPowerSeries.X (0 : Fin 3),
            MvPowerSeries.subst
              (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries] :
          Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries) =
      fAdd₂ F a (fAdd₂ F b c) := by
    rw [MvPowerSeries.subst_comp_subst_apply h_X_FYZ h_abc]
    unfold fAdd₂
    congr 1; funext s; fin_cases s
    · change MvPowerSeries.subst _ (MvPowerSeries.X 0) = _
      exact subst_fin3_X _ h_abc 0
    · change MvPowerSeries.subst _ (MvPowerSeries.subst _ F.toSeries) = _
      rw [MvPowerSeries.subst_comp_subst_apply h_YZ h_abc]
      congr 1; funext s; fin_cases s
      · exact subst_fin3_X _ h_abc 1
      · exact subst_fin3_X _ h_abc 2
  have step := congr_arg
    (MvPowerSeries.subst (![a, b, c] : Fin 3 → MvPowerSeries (Fin 2) R)) F.assoc
  rw [comp_L, comp_R] at step
  exact step

/-- Commutativity of the bivariate `F`-addition. -/
private theorem fAdd₂_comm (F : FormalGroup.FormalGroup R)
    (a b : MvPowerSeries (Fin 2) R)
    (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    fAdd₂ F a b = fAdd₂ F b a := by
  have h_swap : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  have h_ab := hasSubst_pair₂ a b ha hb
  unfold fAdd₂
  have step := congr_arg
    (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries (Fin 2) R)) F.comm
  rw [MvPowerSeries.subst_comp_subst_apply h_swap h_ab] at step
  have heq : (fun s => MvPowerSeries.subst
      (![a, b] : Fin 2 → MvPowerSeries (Fin 2) R)
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) s)) =
      (![b, a] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    funext s; fin_cases s
    · change MvPowerSeries.subst _ (MvPowerSeries.X 1) = _
      exact subst_matrix_X1 _ h_ab
    · change MvPowerSeries.subst _ (MvPowerSeries.X 0) = _
      exact subst_matrix_X0 _ h_ab
  rw [heq] at step; exact step.symm

/-- The **interchange law**: for bivariate series `a, b, c, d` with vanishing
constant coefficients, `F(F(a, b), F(c, d)) = F(F(a, c), F(b, d))`. -/
private theorem fAdd₂_interchange (F : FormalGroup.FormalGroup R)
    (a b c d : MvPowerSeries (Fin 2) R)
    (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0)
    (hc : MvPowerSeries.constantCoeff c = 0)
    (hd : MvPowerSeries.constantCoeff d = 0) :
    fAdd₂ F (fAdd₂ F a b) (fAdd₂ F c d) = fAdd₂ F (fAdd₂ F a c) (fAdd₂ F b d) := by
  have hcd := constantCoeff_fAdd₂ F c d hc hd
  have hbc := constantCoeff_fAdd₂ F b c hb hc
  have hcb := constantCoeff_fAdd₂ F c b hc hb
  have hbd := constantCoeff_fAdd₂ F b d hb hd
  calc fAdd₂ F (fAdd₂ F a b) (fAdd₂ F c d)
      = fAdd₂ F a (fAdd₂ F b (fAdd₂ F c d)) :=
        fAdd₂_assoc F a b (fAdd₂ F c d) ha hb hcd
    _ = fAdd₂ F a (fAdd₂ F (fAdd₂ F b c) d) := by
        rw [fAdd₂_assoc F b c d hb hc hd]
    _ = fAdd₂ F a (fAdd₂ F (fAdd₂ F c b) d) := by
        rw [fAdd₂_comm F b c hb hc]
    _ = fAdd₂ F a (fAdd₂ F c (fAdd₂ F b d)) := by
        rw [fAdd₂_assoc F c b d hc hb hd]
    _ = fAdd₂ F (fAdd₂ F a c) (fAdd₂ F b d) :=
        (fAdd₂_assoc F a c (fAdd₂ F b d) ha hc hbd).symm

/-! ### preserves_add for mulByNatSeries -/

/-- The `preserves_add` condition for a univariate power series `f` interpreted
as a candidate formal-group homomorphism `F → F`: `f(F(X, Y)) = F(f(X), f(Y))`
in `MvPowerSeries (Fin 2) R`. -/
private def PreservesAddCondition (F : FormalGroup.FormalGroup R) (f : PowerSeries R) :
    Prop :=
  PowerSeries.subst F.toSeries f =
    MvPowerSeries.subst
      (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
         PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f] :
        Fin 2 → MvPowerSeries (Fin 2) R)
      F.toSeries

/-- Substitute a `PowerSeries R` into itself via a bivariate target. -/
private lemma mv_subst_X_of_unit {τ : Type*}
    (a : Unit → MvPowerSeries τ R) (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (PowerSeries.X : PowerSeries R) = a () := by
  change MvPowerSeries.subst a (MvPowerSeries.X () : MvPowerSeries Unit R) = a ()
  exact MvPowerSeries.subst_X ha ()

private lemma hasSubst_const_F (F : FormalGroup.FormalGroup R) :
    MvPowerSeries.HasSubst
      (fun _ : Unit => F.toSeries : Unit → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro; exact constantCoeff_FG_toSeries F

private lemma hasSubst_const_Xi (i : Fin 2) :
    MvPowerSeries.HasSubst
      (fun _ : Unit => MvPowerSeries.X i : Unit → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro; simp

lemma constantCoeff_univariate_subst
    (g : MvPowerSeries (Fin 2) R) (hg : MvPowerSeries.constantCoeff g = 0)
    (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst g f) = 0 := by
  rw [PowerSeries.subst_def]
  have h : MvPowerSeries.HasSubst (fun _ : Unit => g) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro; exact hg
  exact MvPowerSeries.constantCoeff_subst_eq_zero h (fun _ => hg) hf

private lemma subst_F_applied_to_X (F : FormalGroup.FormalGroup R) :
    PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) (PowerSeries.X : PowerSeries R) =
      F.toSeries := by
  rw [PowerSeries.subst_def]
  exact mv_subst_X_of_unit _ (hasSubst_const_F F)

private lemma subst_Xi_applied_to_X (i : Fin 2) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)
        (PowerSeries.X : PowerSeries R) = MvPowerSeries.X i := by
  rw [PowerSeries.subst_def]
  exact mv_subst_X_of_unit _ (hasSubst_const_Xi i)

private lemma subst_univariate_zero (g : MvPowerSeries (Fin 2) R)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst g (0 : PowerSeries R) = 0 := by
  rw [PowerSeries.subst_def]
  have h : MvPowerSeries.HasSubst (fun _ : Unit => g) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro; exact hg
  exact subst_zero_eq h

/-- `MvPowerSeries.subst ![0, 0] F.toSeries = 0` when `constantCoeff F.toSeries = 0`. -/
private lemma subst_pair_zero_fin2 (F : FormalGroup.FormalGroup R) :
    MvPowerSeries.subst
      (![(0 : MvPowerSeries (Fin 2) R), 0] : Fin 2 → MvPowerSeries (Fin 2) R)
      F.toSeries = 0 := by
  have heq : (![(0 : MvPowerSeries (Fin 2) R), 0] :
      Fin 2 → MvPowerSeries (Fin 2) R) =
      (fun _ : Fin 2 => (0 : MvPowerSeries (Fin 2) R)) := by
    funext s; fin_cases s <;> rfl
  rw [heq]
  have h : MvPowerSeries.HasSubst (fun _ : Fin 2 => (0 : MvPowerSeries (Fin 2) R)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro; simp
  ext e
  rw [MvPowerSeries.coeff_subst h, MvPowerSeries.coeff_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    rw [Finsupp.prod_zero_index]
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_FG_toSeries]
    exact zero_smul _ _
  · have hprod : (d.prod fun _ exp => (0 : MvPowerSeries (Fin 2) R) ^ exp) = 0 := by
      rw [Finsupp.prod]
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      exact Finset.prod_eq_zero hi
        (by rw [zero_pow (Finsupp.mem_support_iff.mp hi)])
    rw [hprod, MvPowerSeries.coeff_zero, smul_zero]

/-- The base case of the induction: `0` satisfies `PreservesAddCondition`. -/
private lemma preservesAddCondition_zero (F : FormalGroup.FormalGroup R) :
    PreservesAddCondition F 0 := by
  unfold PreservesAddCondition
  rw [subst_univariate_zero F.toSeries (constantCoeff_FG_toSeries F)]
  rw [subst_univariate_zero (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (by simp)]
  rw [subst_univariate_zero (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (by simp)]
  exact (subst_pair_zero_fin2 F).symm

/-- The key inductive step: if `f` satisfies `PreservesAddCondition` and has
vanishing constant coefficient, then so does `fAdd F f X`. -/
private lemma preservesAddCondition_step (F : FormalGroup.FormalGroup R)
    (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0)
    (ih : PreservesAddCondition F f) :
    PreservesAddCondition F (fAdd F f PowerSeries.X) := by
  unfold PreservesAddCondition at ih ⊢
  set fX : MvPowerSeries (Fin 2) R :=
    PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f with hfX_def
  set fY : MvPowerSeries (Fin 2) R :=
    PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f with hfY_def
  have hfX0 : MvPowerSeries.constantCoeff fX = 0 :=
    constantCoeff_univariate_subst _ (by simp) f hf
  have hfY0 : MvPowerSeries.constantCoeff fY = 0 :=
    constantCoeff_univariate_subst _ (by simp) f hf
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) :
    MvPowerSeries (Fin 2) R) = 0 := by simp
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) :
    MvPowerSeries (Fin 2) R) = 0 := by simp
  have hF := hasSubst_const_F F
  have hpair_univ : MvPowerSeries.HasSubst
      (![f, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) :=
    hasSubst_pair f PowerSeries.X hf (by simp)
  have hX0_const := hasSubst_const_Xi (R := R) 0
  have hX1_const := hasSubst_const_Xi (R := R) 1
  -- LHS: subst F.toSeries (fAdd F f X) = fAdd₂ F (subst F f) F.toSeries
  have lhs_eq : PowerSeries.subst F.toSeries (fAdd F f PowerSeries.X) =
      fAdd₂ F (PowerSeries.subst F.toSeries f) F.toSeries := by
    unfold fAdd fAdd₂
    rw [PowerSeries.subst_def]
    rw [MvPowerSeries.subst_comp_subst_apply hpair_univ hF]
    congr 1
    funext s; fin_cases s
    · rfl
    · exact mv_subst_X_of_unit _ hF
  have rhs_lift_X0 : PowerSeries.subst
      (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)
      (fAdd F f PowerSeries.X) = fAdd₂ F fX (MvPowerSeries.X 0) := by
    unfold fAdd fAdd₂
    rw [PowerSeries.subst_def]
    rw [MvPowerSeries.subst_comp_subst_apply hpair_univ hX0_const]
    congr 1
    funext s; fin_cases s
    · rfl
    · exact mv_subst_X_of_unit _ hX0_const
  have rhs_lift_X1 : PowerSeries.subst
      (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)
      (fAdd F f PowerSeries.X) = fAdd₂ F fY (MvPowerSeries.X 1) := by
    unfold fAdd fAdd₂
    rw [PowerSeries.subst_def]
    rw [MvPowerSeries.subst_comp_subst_apply hpair_univ hX1_const]
    congr 1
    funext s; fin_cases s
    · rfl
    · exact mv_subst_X_of_unit _ hX1_const
  rw [lhs_eq, rhs_lift_X0, rhs_lift_X1]
  rw [show PowerSeries.subst F.toSeries f = fAdd₂ F fX fY from ih]
  -- Rewrite F.toSeries as fAdd₂ F (X 0) (X 1).
  have hFact : F.toSeries =
      fAdd₂ F (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)
              (MvPowerSeries.X (1 : Fin 2)) := by
    unfold fAdd₂
    have heq : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) =
        (fun s : Fin 2 => MvPowerSeries.X s) := by
      funext s; fin_cases s <;> rfl
    rw [heq]
    exact (congr_fun MvPowerSeries.subst_self F.toSeries).symm
  conv_lhs => rw [hFact]
  exact fAdd₂_interchange F fX fY (MvPowerSeries.X 0) (MvPowerSeries.X 1) hfX0 hfY0 hX0 hX1

/-- **The preserves_add identity** for multiplication-by-n on a formal group:
`[n](F(X, Y)) = F([n](X), [n](Y))`.

This is the axiom needed to package `mulByNatSeries F n` as a
`FormalGroupHom F F`.

Reference: Silverman IV.2.3. -/
theorem mulByNatSeries_preserves_add (F : FormalGroup.FormalGroup R) (n : ℕ) :
    PowerSeries.subst F.toSeries (mulByNatSeries F n) =
      MvPowerSeries.subst
        (![PowerSeries.subst
              (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (mulByNatSeries F n),
           PowerSeries.subst
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (mulByNatSeries F n)] :
          Fin 2 → MvPowerSeries (Fin 2) R)
        F.toSeries := by
  change PreservesAddCondition F (mulByNatSeries F n)
  induction n with
  | zero =>
    change PreservesAddCondition F 0
    exact preservesAddCondition_zero F
  | succ n ih =>
    change PreservesAddCondition F (fAdd F (mulByNatSeries F n) PowerSeries.X)
    exact preservesAddCondition_step F _ (constantCoeff_mulByNatSeries F n) ih

end HasseWeil.FG

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-- **Multiplication-by-n on a formal group**, as a `FormalGroupHom F F`.

The underlying power series is `HasseWeil.FG.mulByNatSeries F n`, and the
`preserves_add` axiom is `HasseWeil.FG.mulByNatSeries_preserves_add`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2.3. -/
noncomputable def FormalGroup.mulByNatHom (F : FormalGroup R) (n : ℕ) :
    FormalGroupHom F F where
  toSeries := HasseWeil.FG.mulByNatSeries F n
  zero_const := HasseWeil.FG.constantCoeff_mulByNatSeries F n
  preserves_add := HasseWeil.FG.mulByNatSeries_preserves_add F n

/-- The underlying power series of `mulByNatHom` is `mulByNatSeries`. -/
@[simp]
theorem FormalGroup.mulByNatHom_toSeries (F : FormalGroup R) (n : ℕ) :
    (F.mulByNatHom n).toSeries = HasseWeil.FG.mulByNatSeries F n :=
  rfl

/-- The linear coefficient of `mulByNatHom F n` is `n`: `[n](T) = n·T + O(T²)`.

Reference: Silverman IV.2.3(a). -/
@[simp]
theorem FormalGroup.coeff_one_mulByNatHom (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (F.mulByNatHom n).toSeries = (n : R) :=
  HasseWeil.FG.coeff_one_mulByNatSeries F n

/-- `mulByNatHom F 0 = 0` (as power series). -/
@[simp]
theorem FormalGroup.mulByNatHom_zero_toSeries (F : FormalGroup R) :
    (F.mulByNatHom 0).toSeries = 0 := rfl

/-- `mulByNatHom F 1` is the identity: underlying series is `X`. -/
@[simp]
theorem FormalGroup.mulByNatHom_one_toSeries (F : FormalGroup R) :
    (F.mulByNatHom 1).toSeries = PowerSeries.X :=
  HasseWeil.FG.mulByNatSeries_one F

/-! ### T-IV-2-008: Multiplication by a unit is an isomorphism

**Silverman IV.2.3(b)**: if `(n : R)` is a unit, then `mulByNatHom F n` is an
isomorphism of formal groups.

The `n = 1` case is trivial and is proved in `HasseWeil/FormalGroup/Hom.lean`
as `FormalGroup.mulByNatHom_one_isIso` (it reduces to `id_eq_mulByNatHom_one`
plus `comp_id`/`id_comp`, which live in `Hom.lean`).

The **general unit case** is not proved yet. It requires a compositional
inverse for power series whose linear coefficient is a unit
(rather than exactly `1`). The current `HasseWeil.FormalGroup.compInverse`
(in `Logarithm.lean`) is defined only under `coeff 1 f = 1`. Infrastructure
needed to close the general case:

  * **Option A (scaled `compInverse`)**: for a power series `f` with
    `coeff 1 f = u` a unit, define `compInverse_of_unit f` as
    `u⁻¹ · (compInverse (u⁻¹ · f))(u · T)`, i.e. conjugate the coeff-1-is-one
    version with the linear scaling `T ↦ u · T`. Prove the two-sided identity
    `subst g f = X` and `subst f g = X`.
  * **Option B (direct recurrence)**: build the inverse of
    `mulByNatSeries F n` coefficient by coefficient, using the fact that at
    each step the equation for the unknown coefficient is linear in `(n : R)`,
    which is a unit.

Downstream consumers (e.g. `T-IV-3-007`, p-power torsion order) will need
the general case; the `n = 1` statement in `Hom.lean` is a first step. -/

end HasseWeil.FormalGroup
