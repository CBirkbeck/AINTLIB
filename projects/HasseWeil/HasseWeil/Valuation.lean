import HasseWeil.Isogeny
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Discrete Valuations on Elliptic Curve Function Fields

We show the local ring of an elliptic curve at a nonsingular point is a DVR.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], I.1.7, II.1.1
-/

open WeierstrassCurve Polynomial AdjoinRoot Ideal
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace HasseWeil

variable {F : Type*} [Field F]

/-- Inner derivative commutes with outer eval: `d/dX(W(X,y₀)) = (∂W/∂X)(X,y₀)`. -/
private theorem eval_poly_deriv_eq_polynomialX_eval (W : Affine F) (y₀ : F) :
    (W.polynomial.eval (C y₀)).derivative = W.polynomialX.eval (C y₀) := by
  unfold Affine.polynomial Affine.polynomialX
  simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
    derivative_sub, derivative_mul, derivative_sq,
    map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  ring_nf; simp [C_ofNat]

variable (W : Affine F)

/-! ### Point ideal -/

noncomputable def pointIdeal (x : F) (y : F) : Ideal W.CoordinateRing :=
  Affine.CoordinateRing.XYIdeal W x (Polynomial.C y)

theorem pointIdeal_isMaximal {x y : F} (h : W.Nonsingular x y) :
    (pointIdeal W x y).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((Affine.CoordinateRing.quotientXYIdealEquiv h.1).toRingEquiv.isField (Field.toIsField F))

/-! ### Algebraic lemma: YClass · Q ∈ ⟨XClass⟩ -/

-- Type class synthesis in CoordinateRing is expensive.
set_option maxHeartbeats 800000 in
/-- `YClass · Q ∈ ⟨XClass⟩` from the curve equation linearization. -/
theorem yclass_mul_quot_in_xclass_span {x₀ y₀ : F} (h : W.Equation x₀ y₀) :
    Affine.CoordinateRing.YClass W (C y₀) *
      Affine.CoordinateRing.mk W (W.polynomial /ₘ (Y - C (C y₀))) ∈
      Ideal.span {Affine.CoordinateRing.XClass W x₀} := by
  have h1 := modByMonic_X_sub_C_eq_C_eval W.polynomial (C y₀ : F[X])
  have h2 := modByMonic_add_div W.polynomial (Y - C (C y₀ : F[X]))
  rw [h1] at h2
  have hmk := congr_arg (Affine.CoordinateRing.mk W) h2
  simp only [map_add, map_mul, mk_self] at hmk
  show Affine.CoordinateRing.mk W (Y - C (C y₀)) *
    Affine.CoordinateRing.mk W (W.polynomial /ₘ (Y - C (C y₀))) ∈ _
  rw [(neg_eq_of_add_eq_zero_right hmk).symm]
  refine neg_mem ?_
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr h
  have : Affine.CoordinateRing.mk W (C (W.polynomial.eval (C y₀))) =
      Affine.CoordinateRing.XClass W x₀ * Affine.CoordinateRing.mk W (C g) := by
    simp only [Affine.CoordinateRing.XClass, ← map_mul, ← hg]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (show _ ∈ ({_} : Set _) from rfl))

/-! ### Q.evalEval = polynomialY.evalEval via derivative -/

set_option maxHeartbeats 800000 in
/-- The quotient `Q` evaluates to `polynomialY` at `(x₀, y₀)`. -/
theorem quot_evalEval_eq_polynomialY {x₀ y₀ : F} (h : W.Equation x₀ y₀) :
    Polynomial.evalEval x₀ y₀ (W.polynomial /ₘ (Y - C (C y₀ : F[X]))) =
      Polynomial.evalEval x₀ y₀ W.polynomialY := by
  set Q := W.polynomial /ₘ (Y - C (C y₀ : F[X]))
  have h1 := modByMonic_X_sub_C_eq_C_eval W.polynomial (C y₀ : F[X])
  have h2 := modByMonic_add_div W.polynomial (Y - C (C y₀ : F[X]))
  rw [h1] at h2
  have hd := congr_arg Polynomial.derivative h2
  rw [derivative_add, derivative_C, zero_add, derivative_mul, derivative_sub,
    derivative_X, derivative_C, sub_zero, one_mul] at hd
  have hpoly : W.polynomial.derivative = W.polynomialY := by
    unfold Affine.polynomial Affine.polynomialY
    simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
      derivative_sub, derivative_mul, derivative_sq]; C_simp; ring1
  rw [hpoly] at hd
  have heval : Polynomial.evalEval x₀ y₀ (Q + (X - C (C y₀)) * Q.derivative) =
      Polynomial.evalEval x₀ y₀ Q := by
    simp [Polynomial.evalEval, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      sub_self, zero_mul, add_zero]
  exact (show Polynomial.evalEval x₀ y₀ Q = Polynomial.evalEval x₀ y₀ W.polynomialY from by
    rw [← heval, hd])

/-! ### mk(Q) ∉ XYIdeal when polynomialY ≠ 0 -/

/-- `mk(Q)` is not in the point ideal when `polynomialY(P) ≠ 0`. -/
theorem mk_quot_not_mem {x₀ y₀ : F}
    (h : W.Equation x₀ y₀)
    (hY : W.polynomialY.evalEval x₀ y₀ ≠ 0) :
    Affine.CoordinateRing.mk W (W.polynomial /ₘ (Y - C (C y₀ : F[X]))) ∉
      Affine.CoordinateRing.XYIdeal W x₀ (Polynomial.C y₀) := by
  intro hmem
  have hker : Affine.CoordinateRing.XYIdeal W x₀ (Polynomial.C y₀) ≤
      RingHom.ker (AdjoinRoot.evalEval h) := by
    rw [Affine.CoordinateRing.XYIdeal]
    apply span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact RingHom.mem_ker.mpr <| by
        unfold Affine.CoordinateRing.XClass
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval, eval_C, eval_X, eval_sub]
    · exact RingHom.mem_ker.mpr <| by
        unfold Affine.CoordinateRing.YClass
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval, eval_C, eval_X, eval_sub]
  have := RingHom.mem_ker.mp (hker hmem)
  rw [AdjoinRoot.evalEval_mk] at this
  rw [quot_evalEval_eq_polynomialY W h] at this
  exact hY this

/-! ### Symmetric algebraic lemmas: X-side analogs (for polynomialX ≠ 0 case)

The y-side helpers `yclass_mul_quot_in_xclass_span` + `mk_quot_not_mem`
above handle the polynomialY ≠ 0 case (the "Y-derivative non-zero"
branch). For the polynomialX ≠ 0 case (the "X-derivative non-zero"
branch, which includes 2-torsion smooth points), we need the symmetric
helpers swapping X ↔ Y roles.

These mirror the helpers above but operate on `g := W.polynomial.eval
(C y₀) /ₘ (X - C x₀)` (the inner X-quotient) instead of `Q :=
W.polynomial /ₘ (Y - C (C y₀))` (the Y-quotient). -/

set_option maxHeartbeats 800000 in
/-- **X-side analog of `yclass_mul_quot_in_xclass_span`**: `XClass · mk(C g) ∈
⟨YClass⟩` where `g := W.polynomial.eval (C y₀) /ₘ (X - C x₀)`. From the
inner X-factorization combined with the Y-mod-by-monic identity. -/
theorem xclass_mul_C_g_in_yclass_span {x₀ y₀ : F} (h : W.Equation x₀ y₀) :
    Affine.CoordinateRing.XClass W x₀ *
      Affine.CoordinateRing.mk W
        (C (W.polynomial.eval (C y₀) /ₘ (X - C x₀))) ∈
      Ideal.span {Affine.CoordinateRing.YClass W (C y₀)} := by
  set g := W.polynomial.eval (C y₀) /ₘ (X - C x₀) with hgdef
  -- Inner factorization: W(X,y₀) = (X - x₀) · g.
  have hinner : W.polynomial.eval (C y₀) = (X - C x₀) * g := by
    have := modByMonic_add_div (W.polynomial.eval (C y₀)) (X - C x₀)
    rw [modByMonic_X_sub_C_eq_C_eval,
      show (W.polynomial.eval (C y₀)).eval x₀ = 0 from h, C_0, zero_add] at this
    exact this.symm
  -- Y-mod-by-monic: W = (Y - C y₀) · Q + C(W.polynomial.eval(C y₀))
  -- so: mk(C(W.eval(Cy₀))) + YClass · mk(Q) = 0.
  have h1 := modByMonic_X_sub_C_eq_C_eval W.polynomial (C y₀ : F[X])
  have h2 := modByMonic_add_div W.polynomial (Y - C (C y₀ : F[X]))
  rw [h1] at h2
  have hmk := congr_arg (Affine.CoordinateRing.mk W) h2
  simp only [map_add, map_mul, mk_self] at hmk
  -- Factor: mk(C(W.eval(Cy₀))) = XClass · mk(C g).
  rw [hinner, map_mul] at hmk
  -- hmk: XClass·mk(Cg) + YClass·mk(Q) = 0, so XClass·mk(Cg) = -(YClass·mk(Q)).
  have : Affine.CoordinateRing.mk W (C (X - C x₀)) *
      Affine.CoordinateRing.mk W (C g) =
      -(Affine.CoordinateRing.mk W (Y - C (C y₀)) *
        Affine.CoordinateRing.mk W (W.polynomial /ₘ (Y - C (C y₀)))) :=
    eq_neg_of_add_eq_zero_left hmk
  show Affine.CoordinateRing.mk W (C (X - C x₀)) *
    Affine.CoordinateRing.mk W (C g) ∈ _
  rw [this]
  refine neg_mem ?_
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

set_option maxHeartbeats 800000 in
/-- **X-side analog of `mk_quot_not_mem`**: `mk(C g) ∉ XYIdeal` when
`polynomialX(P) ≠ 0`. Uses the derivative trick: `g.eval x₀ =
polynomialX.evalEval x₀ y₀`. -/
theorem mk_C_g_not_mem {x₀ y₀ : F}
    (h : W.Equation x₀ y₀)
    (hX : W.polynomialX.evalEval x₀ y₀ ≠ 0) :
    Affine.CoordinateRing.mk W
        (C (W.polynomial.eval (C y₀) /ₘ (X - C x₀))) ∉
      Affine.CoordinateRing.XYIdeal W x₀ (Polynomial.C y₀) := by
  set g := W.polynomial.eval (C y₀) /ₘ (X - C x₀) with hgdef
  intro hmem
  have hker : Affine.CoordinateRing.XYIdeal W x₀ (Polynomial.C y₀) ≤
      RingHom.ker (AdjoinRoot.evalEval h) := by
    rw [Affine.CoordinateRing.XYIdeal]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact RingHom.mem_ker.mpr <| by
        unfold Affine.CoordinateRing.XClass
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval, eval_C, eval_X, eval_sub]
    · exact RingHom.mem_ker.mpr <| by
        unfold Affine.CoordinateRing.YClass
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval, eval_C, eval_X, eval_sub]
  have hev := RingHom.mem_ker.mp (hker hmem)
  rw [AdjoinRoot.evalEval_mk] at hev
  simp only [Polynomial.evalEval, eval_C] at hev
  -- hev: g.eval x₀ = 0.
  -- Show: g.eval x₀ = polynomialX.evalEval x₀ y₀ ≠ 0.
  have hdiv2 := modByMonic_add_div (W.polynomial.eval (C y₀)) (X - C x₀)
  rw [modByMonic_X_sub_C_eq_C_eval,
    show (W.polynomial.eval (C y₀)).eval x₀ = 0 from h, C_0, zero_add] at hdiv2
  have hd := congr_arg Polynomial.derivative hdiv2
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    one_mul] at hd
  have he := congr_arg (fun r => r.eval x₀) hd
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    add_zero] at he
  have hpX : (W.polynomial.eval (C y₀)).derivative = W.polynomialX.eval (C y₀) :=
    eval_poly_deriv_eq_polynomialX_eval W y₀
  rw [hpX] at he
  exact hX (show Polynomial.evalEval x₀ y₀ W.polynomialX = 0 by
    simp only [Polynomial.evalEval]; rw [← he]; exact hev)

/-! ### The local ring is a DVR -/

private theorem mem_of_mul_unit {R : Type*} [CommRing R] {I : Ideal R}
    {a b : R} (hmul : a * b ∈ I) (hb : IsUnit b) : a ∈ I := by
  obtain ⟨u, rfl⟩ := hb; simpa [mul_assoc] using I.mul_mem_right ↑u⁻¹ hmul

private theorem map_mem_span_sing {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a x : R} (hmem : x ∈ span ({a} : Set R)) :
    f x ∈ span ({f a} : Set S) := by
  rw [mem_span_singleton] at hmem ⊢; obtain ⟨c, rfl⟩ := hmem; exact ⟨f c, by rw [map_mul]⟩

set_option maxHeartbeats 3200000 in
/-- The local ring of an elliptic curve at a nonsingular point is a DVR. -/
theorem localRing_isDVR {x₀ y₀ : F} (h : W.Nonsingular x₀ y₀) :
    let P := pointIdeal W x₀ y₀
    haveI : P.IsPrime := (pointIdeal_isMaximal W h).isPrime
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  intro P; letI : P.IsPrime := (pointIdeal_isMaximal W h).isPrime
  let f := algebraMap W.CoordinateRing (Localization.AtPrime P)
  -- Nonsingularity: WLOG polynomialY.evalEval x₀ y₀ ≠ 0
  -- (The other case swaps X↔Y roles; we handle the Y case.)
  obtain ⟨heq, hX | hY⟩ := h
  · -- Case: polynomialX ≠ 0 — show XClass ∈ ⟨YClass⟩, so 𝔪 = ⟨YClass⟩
    -- From Y-division + inner factorization: XClass·mk(C(g)) ∈ ⟨YClass⟩
    -- where g = W(X,y₀) /ₘ (X - C x₀). And g(x₀) = polynomialX(P) ≠ 0.
    set g := W.polynomial.eval (C y₀) /ₘ (X - C x₀) with hgdef
    -- Inner factorization: W(X,y₀) = (X-x₀)·g (since W(x₀,y₀) = 0)
    have hinner : W.polynomial.eval (C y₀) = (X - C x₀) * g := by
      have h := modByMonic_add_div (W.polynomial.eval (C y₀)) (X - C x₀)
      rw [modByMonic_X_sub_C_eq_C_eval,
        show (W.polynomial.eval (C y₀)).eval x₀ = 0 from heq, C_0, zero_add] at h
      exact h.symm
    -- Y-division: mk(C(W(X,y₀))) + YClass·mk(Q) = 0
    have h1 := modByMonic_X_sub_C_eq_C_eval W.polynomial (C y₀ : F[X])
    have h2 := modByMonic_add_div W.polynomial (Y - C (C y₀ : F[X]))
    rw [h1] at h2
    have hmk := congr_arg (Affine.CoordinateRing.mk W) h2
    simp only [map_add, map_mul, mk_self] at hmk
    -- Factor: mk(C(W(X,y₀))) = XClass·mk(C(g))
    rw [hinner, map_mul] at hmk
    -- hmk: mk(C(X-x₀)) * mk(C(g)) + mk(Y-y₀) * mk(Q) = 0
    -- mk(C(X-x₀)) = XClass, mk(Y-y₀) = YClass (by definition)
    have hxmem : Affine.CoordinateRing.mk W (C (X - C x₀)) *
        Affine.CoordinateRing.mk W (C g) ∈
        span {Affine.CoordinateRing.YClass W (C y₀)} := by
      -- hmk: a + b = 0 where b = YClass * mk(Q)
      -- So a = -b ∈ span{YClass}
      have hab : Affine.CoordinateRing.mk W (C (X - C x₀)) *
          Affine.CoordinateRing.mk W (C g) =
          -(Affine.CoordinateRing.mk W (Y - C (C y₀)) *
            Affine.CoordinateRing.mk W (W.polynomial /ₘ (Y - C (C y₀)))) := by
        exact eq_neg_of_add_eq_zero_left hmk
      rw [hab]; exact neg_mem (mul_mem_right _ _ (subset_span rfl))
    -- g(x₀) = polynomialX.evalEval x₀ y₀ ≠ 0
    have hgnotin : Affine.CoordinateRing.mk W (C g) ∉
        Affine.CoordinateRing.XYIdeal W x₀ (C y₀) := by
      intro hmem
      have hker : Affine.CoordinateRing.XYIdeal W x₀ (C y₀) ≤
          RingHom.ker (AdjoinRoot.evalEval heq) := by
        rw [Affine.CoordinateRing.XYIdeal]; apply span_le.mpr
        intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact RingHom.mem_ker.mpr <| by
            unfold Affine.CoordinateRing.XClass; rw [AdjoinRoot.evalEval_mk]
            simp [Polynomial.evalEval, eval_C, eval_X, eval_sub]
        · exact RingHom.mem_ker.mpr <| by
            unfold Affine.CoordinateRing.YClass; rw [AdjoinRoot.evalEval_mk]
            simp [Polynomial.evalEval, eval_C, eval_X, eval_sub]
      have hev := RingHom.mem_ker.mp (hker hmem)
      rw [AdjoinRoot.evalEval_mk] at hev
      simp only [Polynomial.evalEval, eval_C] at hev
      -- hev: g.eval x₀ = 0. Show g.eval x₀ = polynomialX.evalEval x₀ y₀ ≠ 0 → contradiction.
      -- Derivative trick: g.eval x₀ = W(X,y₀)'.eval x₀ = polynomialX.evalEval x₀ y₀
      have hdiv2 := modByMonic_add_div (W.polynomial.eval (C y₀)) (X - C x₀)
      rw [modByMonic_X_sub_C_eq_C_eval,
        show (W.polynomial.eval (C y₀)).eval x₀ = 0 from heq, C_0, zero_add] at hdiv2
      -- hdiv2: (X - C x₀) * g = W.polynomial.eval (C y₀)
      have hd := congr_arg Polynomial.derivative hdiv2
      rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hd
      -- hd: g + (X - C x₀) * g' = (W.polynomial.eval (C y₀)).derivative
      have he := congr_arg (fun r => r.eval x₀) hd
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
        add_zero] at he
      -- he: g.eval x₀ = (W.polynomial.eval (C y₀)).derivative.eval x₀
      -- And (W.polynomial.eval(Cy₀)).derivative = polynomialX.eval(Cy₀)
      have hpX : (W.polynomial.eval (C y₀)).derivative = W.polynomialX.eval (C y₀) :=
        eval_poly_deriv_eq_polynomialX_eval W y₀
      rw [hpX] at he
      -- he: g.eval x₀ = W.polynomialX.eval(Cy₀).eval x₀ = polynomialX.evalEval x₀ y₀
      exact hX (show Polynomial.evalEval x₀ y₀ W.polynomialX = 0 by
        simp only [Polynomial.evalEval]; rw [← he]; exact hev)
    -- Assembly: XClass ∈ ⟨YClass⟩ in localization → 𝔪 principal → DVR
    have hmul_mem : f (Affine.CoordinateRing.XClass W x₀) *
        f (Affine.CoordinateRing.mk W (C g)) ∈
        span {f (Affine.CoordinateRing.YClass W (C y₀))} := by
      rw [← map_mul]; exact map_mem_span_sing f hxmem
    have hunit : IsUnit (f (Affine.CoordinateRing.mk W (C g))) :=
      IsLocalization.map_units (Localization.AtPrime P)
        (⟨_, hgnotin⟩ : P.primeCompl)
    have halg_x := mem_of_mul_unit hmul_mem hunit
    have hmap_eq : Ideal.map f P = span {f (Affine.CoordinateRing.YClass W (C y₀))} := by
      show Ideal.map f (span {Affine.CoordinateRing.XClass W x₀,
        Affine.CoordinateRing.YClass W (C y₀)}) = _
      rw [map_span, Set.image_pair]
      exact le_antisymm (span_le.mpr fun z hz => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        exact hz.elim (· ▸ halg_x) (· ▸ subset_span rfl))
        (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)))
    have hprincipal : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
      rw [Localization.AtPrime.map_eq_maximalIdeal.symm, hmap_eq]; exact ⟨⟨_, rfl⟩⟩
    have hne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥ := by
      rw [Localization.AtPrime.map_eq_maximalIdeal.symm]; intro hbot
      rw [Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective
        (M := P.primeCompl) _ P.primeCompl_le_nonZeroDivisors)] at hbot
      exact (Affine.CoordinateRing.XClass_ne_zero (W' := W) (x := x₀))
        (eq_bot_iff.mp hbot (subset_span (Set.mem_insert _ _)))
    haveI : IsPrincipalIdealRing (Localization.AtPrime P) :=
      ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
        (Localization.AtPrime P)).out 4 0).mp hprincipal
    exact ⟨hne⟩
  · -- Case: polynomialY ≠ 0
    have hmul_mem : f (Affine.CoordinateRing.YClass W (C y₀)) *
        f (Affine.CoordinateRing.mk W (W.polynomial /ₘ (Y - C (C y₀)))) ∈
        span {f (Affine.CoordinateRing.XClass W x₀)} := by
      rw [← map_mul]; exact map_mem_span_sing f (yclass_mul_quot_in_xclass_span W heq)
    have hunit : IsUnit (f (Affine.CoordinateRing.mk W
        (W.polynomial /ₘ (Y - C (C y₀ : F[X]))))) :=
      IsLocalization.map_units (Localization.AtPrime P)
        (⟨_, mk_quot_not_mem W heq hY⟩ : P.primeCompl)
    have halg_y : f (Affine.CoordinateRing.YClass W (C y₀)) ∈
        span {f (Affine.CoordinateRing.XClass W x₀)} :=
      mem_of_mul_unit hmul_mem hunit
    have hmap_eq : Ideal.map f P = span {f (Affine.CoordinateRing.XClass W x₀)} := by
      show Ideal.map f (span {Affine.CoordinateRing.XClass W x₀,
        Affine.CoordinateRing.YClass W (C y₀)}) = _
      rw [map_span, Set.image_pair]
      exact le_antisymm (span_le.mpr fun z hz => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        exact hz.elim (· ▸ subset_span rfl) (· ▸ halg_y))
        (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
    have hprincipal : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
      rw [Localization.AtPrime.map_eq_maximalIdeal.symm, hmap_eq]; exact ⟨⟨_, rfl⟩⟩
    have hne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥ := by
      rw [Localization.AtPrime.map_eq_maximalIdeal.symm]; intro hbot
      rw [Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective
        (M := P.primeCompl) _ P.primeCompl_le_nonZeroDivisors)] at hbot
      exact (Affine.CoordinateRing.XClass_ne_zero (W' := W) (x := x₀))
        (eq_bot_iff.mp hbot (subset_span (Set.mem_insert _ _)))
    haveI : IsPrincipalIdealRing (Localization.AtPrime P) :=
      ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
        (Localization.AtPrime P)).out 4 0).mp hprincipal
    exact ⟨hne⟩

end HasseWeil
