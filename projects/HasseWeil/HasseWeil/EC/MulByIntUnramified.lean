/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.DifferentialOrd
import HasseWeil.EC.IsogenyOrdTransport
import HasseWeil.EC.TranslationOrd
import HasseWeil.EC.WronskianGeneral
import HasseWeil.WeilPairing.TorsionGeometric

/-!
# Unramifiedness of `[ℓ]` at an affine non-2-torsion image point (the `e = 1` input)

For an elliptic curve `W/F` and a smooth point `P` of `⟨W⟩` whose image `[ℓ]·P = Q = (x_Q, y_Q)`
is an *affine non-2-torsion* point, the pullback `[ℓ]^*(x_gen − x_Q) = mulByInt_x ℓ − x_Q` of the
uniformizer `x_gen − x_Q` at `Q` is a uniformizer at `P`: its order is exactly `1`. This is the
geometric *unramifiedness* of `[ℓ]` (Silverman III.4.10c), the `e = 1` normalization that feeds the
order-transport glue `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`
(`EC/IsogenyOrdTransport.lean`). No algebraic closure of `F` is needed.

## Strategy

Write `h := mulByInt_x ℓ − x_Q = (Φ_ℓ(x_gen) − x_Q·ΨSq_ℓ(x_gen)) / ΨSq_ℓ(x_gen)`.

* **Unit factor.** `ΨSq_ℓ(x_gen) = algebraMap (Polynomial F) KE (ΨSq_ℓ)` is a unit at `P`
  (`ord_P = 0`), because `ΨSq_ℓ(P.x) ≠ 0` — which holds since `[ℓ]·P = Q` is affine (so `P` is
  not a pole of `mulByInt_x ℓ`).
* **Numerator.** `Φ_ℓ(x_gen) − x_Q·ΨSq_ℓ(x_gen) = algebraMap (Polynomial F) KE g` for the *fibre
  polynomial* `g := Φ_ℓ − C x_Q·ΨSq_ℓ ∈ F[X]`, which has `P.x` as a root:
  `g(P.x) = ΨSq_ℓ(P.x)·(x([ℓ]P) − x_Q) = 0`.
* **`ord_P` = root multiplicity.** `ord_P (algebraMap g) = rootMultiplicity P.x g`: peel off
  `(X − P.x)^m`; the factor `(x_gen − P.x)^m` contributes `m·1`
  (`ord_P_x_gen_sub_const_eq_one_of_non_2_tor`, `P` non-2-torsion) and the cofactor (nonvanishing at
  `P.x`) contributes `0`.
* **Multiplicity one.** `rootMultiplicity P.x g = 1` — the separability content (`g'(P.x) ≠ 0`).
  Via the division-polynomial Wronskian `ΨSq_ℓ·Φ_ℓ' − Φ_ℓ·ΨSq_ℓ' = ℓ·preΨ_{2ℓ}`
  (`wronskian_Φ_ΨSq_general`), `g'(P.x)·ΨSq_ℓ(P.x) = ℓ·preΨ_{2ℓ}(P.x) ≠ 0` since `ℓ ≠ 0`,`2·Q ≠ O`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.2.5, III.4.10c.
-/

open WeierstrassCurve HasseWeil.Curves Polynomial

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

omit [W.toAffine.IsElliptic] in
/-- **Jacobian-coordinate facts at an affine `[ℓ]`-image.** If the base-field point `(x, y)` is
nonsingular and `n • (x, y) = (x_Q, y_Q)` is affine (`n ≠ 0`), then the `ψ`-value is nonzero and
the affine `x`-coordinate of `n • (x,y)` is `(W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2`.

This is the converse-reading of `zsmul_eq_smulEval`: an affine image forces `Z = ψ_n(x,y) ≠ 0`. -/
theorem smulEval_facts_of_zsmul_eq_some {x y x_Q y_Q : F}
    (h_ns : W.toAffine.Nonsingular x y) (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    (n : ℤ) (_hn : n ≠ 0)
    (hsmul : n • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns') :
    (W.ψ n).evalEval x y ≠ 0 ∧
      x_Q = (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 ∧
      y_Q = (W.ω n).evalEval x y / (W.ψ n).evalEval x y ^ 3 := by
  have h_fromAffine :
      n • WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x y h_ns) =
      WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x_Q y_Q h_ns') := by
    have h := congrArg (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W).symm hsmul
    rw [map_zsmul] at h
    simpa using h
  have h_pt : (⟦smulEval W x y n⟧ : WeierstrassCurve.Jacobian.PointClass F) = ⟦![x_Q, y_Q, 1]⟧ := by
    have h1 := WeierstrassCurve.zsmul_eq_smulEval (W := W) h_ns n
    have h2 : (WeierstrassCurve.Jacobian.Point.fromAffine
        (Affine.Point.some x_Q y_Q h_ns')).point = ⟦![x_Q, y_Q, 1]⟧ := by
      rw [WeierstrassCurve.Jacobian.Point.fromAffine_some]
    rw [← h1, h_fromAffine, h2]
  obtain ⟨u, hu⟩ := Quotient.exact h_pt
  simp only [Units.smul_def, WeierstrassCurve.Jacobian.smul_fin3] at hu
  have hc0 : (u : F) ^ 2 * x_Q = (W.φ n).evalEval x y := by
    simpa [smulEval] using congrFun hu 0
  have hc1 : (u : F) ^ 3 * y_Q = (W.ω n).evalEval x y := by
    simpa [smulEval] using congrFun hu 1
  have hc2 : (u : F) * 1 = (W.ψ n).evalEval x y := by
    simpa [smulEval] using congrFun hu 2
  have hψ_ne : (W.ψ n).evalEval x y ≠ 0 := by rw [← hc2, mul_one]; exact u.ne_zero
  refine ⟨hψ_ne, ?_, ?_⟩
  · rw [← hc0, ← hc2, mul_one]
    field_simp
  · rw [← hc1, ← hc2, mul_one]
    field_simp

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- For a point `(x, y)` *on* the curve, the bivariate `evalEval x y` respects coordinate-ring
equalities `mk p = mk q` (it factors through `AdjoinRoot.evalEval`). -/
theorem evalEval_eq_of_mk_eq {x y : F} (h_eq : W.toAffine.Equation x y)
    {p q : (Polynomial F)[X]}
    (h : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) :
    p.evalEval x y = q.evalEval x y := by
  have h0 : W.toAffine.polynomial.evalEval x y = 0 := h_eq
  have := congrArg (AdjoinRoot.evalEval h0) h
  rwa [AdjoinRoot.evalEval_mk, AdjoinRoot.evalEval_mk] at this

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`ΨSq_ℓ(x) = ψ_ℓ(x,y)²` on the curve.** -/
theorem ΨSq_eval_eq_psi_sq {x y : F} (h_eq : W.toAffine.Equation x y) (n : ℤ) :
    (W.ΨSq n).eval x = ((W.ψ n).evalEval x y) ^ 2 := by
  have h1 : ((W.ψ n).evalEval x y) ^ 2 = (Polynomial.C (W.ΨSq n)).evalEval x y := by
    rw [← Polynomial.evalEval_pow]
    refine evalEval_eq_of_mk_eq W h_eq ?_
    rw [map_pow,
      show Affine.CoordinateRing.mk W.toAffine (W.ψ n) = Affine.CoordinateRing.mk W.toAffine (W.Ψ n)
        from Affine.CoordinateRing.mk_ψ (W := W.toAffine) n]
    exact Affine.CoordinateRing.mk_Ψ_sq (W := W.toAffine) n
  rw [h1, Polynomial.evalEval_C]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`Φ_ℓ(x) = φ_ℓ(x,y)` on the curve.** -/
theorem Φ_eval_eq_phi {x y : F} (h_eq : W.toAffine.Equation x y) (n : ℤ) :
    (W.Φ n).eval x = (W.φ n).evalEval x y := by
  have h1 : (W.φ n).evalEval x y = (Polynomial.C (W.Φ n)).evalEval x y :=
    evalEval_eq_of_mk_eq W h_eq (Affine.CoordinateRing.mk_φ (W := W.toAffine) n)
  rw [h1, Polynomial.evalEval_C]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `algebraMap (Polynomial F) KE` agrees with `aeval (x_gen W)` (both send `X ↦ x_gen W` and fix
`F`). -/
theorem algebraMap_poly_eq_aeval_x_gen (p : Polynomial F) :
    algebraMap (Polynomial F) KE p = Polynomial.aeval (x_gen W) p := by
  have hX : algebraMap (Polynomial F) KE Polynomial.X = x_gen W := by
    rw [x_gen, ← IsScalarTower.algebraMap_apply (Polynomial F) R KE Polynomial.X]
  have key : (algebraMap (Polynomial F) KE : Polynomial F →+* KE) =
      (Polynomial.aeval (x_gen W) : Polynomial F →ₐ[F] KE).toRingHom := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply F (Polynomial F) KE a]
      simp [Polynomial.aeval_C]
    · rw [hX]; simp [Polynomial.aeval_X]
  exact congrFun (congrArg DFunLike.coe key) p

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `algebraMap (Polynomial F) KE p` evaluated at `P` is `p.eval P.x`. -/
theorem evalAt_algebraMap_poly (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (p : Polynomial F) :
    (⟨W⟩ : SmoothPlaneCurve F).evalAt P (algebraMap (Polynomial F) R p) = p.eval P.x := by
  have h : algebraMap (Polynomial F) R p =
      Affine.CoordinateRing.mk W.toAffine (Polynomial.C p) := by
    rw [show algebraMap (Polynomial F) R = (AdjoinRoot.of W.toAffine.polynomial) from
        AdjoinRoot.algebraMap_eq _]
    rfl
  rw [h]
  change (⟨W⟩ : SmoothPlaneCurve F).evalAt P
    (Affine.CoordinateRing.mk W.toAffine (Polynomial.C p)) = p.eval P.x
  rw [SmoothPlaneCurve.evalAt_mk, Polynomial.evalEval_C]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
private theorem exists_intCast_ord_P (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    {f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField} (hf : f ≠ 0) :
    ∃ m : ℤ, (⟨W⟩ : SmoothPlaneCurve F).ord_P P f = ((m : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff _).not.mpr hf)
  exact ⟨m, hm.symm⟩

-- The type carries no `DecidableEq F`, but the proof routes through the `DecidableEq`-scoped
-- `ord_P_x_gen_sub_const_eq_one_of_non_2_tor` (whose `negSmoothPoint`/`SmoothPoint.ext` steps need
-- the section instance, not a `classical` one); suppress the unused-in-type lint.
set_option linter.unusedDecidableInType false in
/-- **`ord_P (x_gen − P.x) = 1`** at a non-2-torsion smooth point `P` (its x-coordinate as the
constant). Bridges the `negSmoothPoint`-form `ord_P_x_gen_sub_const_eq_one_of_non_2_tor` via the
involution `negY (negY) = id`. -/
theorem ord_P_x_gen_sub_self_eq_one (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (h_not_2_tor : P.y ≠ W.toAffine.negY P.x P.y) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (x_gen W - algebraMap F KE P.x) =
      ((1 : ℤ) : WithTop ℤ) := by
  set xk := P.x with hxk
  set yk := W.toAffine.negY P.x P.y with hyk
  have hyk_invol : W.toAffine.negY xk yk = P.y := by
    rw [hxk, hyk, WeierstrassCurve.Affine.negY_negY]
  have h_ns' : W.toAffine.Nonsingular xk yk := by
    rw [hxk, hyk]; exact (Affine.nonsingular_neg P.x P.y).mpr P.nonsingular
  have h_not_2_tor' : yk ≠ W.toAffine.negY xk yk := by
    rw [hyk_invol]; rw [hyk]; exact fun h ↦ h_not_2_tor h.symm
  have h_pt_eq : negSmoothPoint W xk yk h_ns' = P := by
    apply SmoothPlaneCurve.SmoothPoint.ext
    · rfl
    · change W.toAffine.negY xk yk = P.y; exact hyk_invol
  have h := ord_P_x_gen_sub_const_eq_one_of_non_2_tor W xk yk h_ns' h_not_2_tor'
  rwa [h_pt_eq] at h

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `ord_P (algebraMap (Polynomial F) KE q) = 0` when `q.eval P.x ≠ 0` (regular & non-vanishing
at `P`). -/
theorem ord_P_algebraMap_poly_eq_zero_of_eval_ne (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    {q : Polynomial F} (hq : q ≠ 0) (h_eval : q.eval P.x ≠ 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap (Polynomial F) KE q) = 0 := by
  set u : R := algebraMap (Polynomial F) R q with hu_def
  have hu_ne : u ≠ 0 := by
    rw [hu_def]
    exact fun h ↦ hq (Affine.CoordinateRing.algebraMap_poly_injective (h.trans (map_zero _).symm))
  have h_factor : algebraMap (Polynomial F) KE q = algebraMap R KE u := by
    rw [hu_def, ← IsScalarTower.algebraMap_apply (Polynomial F) R KE q]
  rw [h_factor]
  have h_notmem : u ∉ (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P := by
    rw [← SmoothPlaneCurve.ker_evalAt, RingHom.mem_ker, hu_def, evalAt_algebraMap_poly W P q]
    exact h_eval
  by_contra h_ne
  exact h_notmem
    (((⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt hu_ne P).mp h_ne)

-- Proof routes through the `DecidableEq`-scoped `ord_P_x_gen_sub_self_eq_one`; the section instance
-- is needed even though the type does not mention it. Suppress the unused-in-type lint.
set_option linter.unusedDecidableInType false in
/-- **Step 2 — the root-multiplicity formula.** For a non-2-torsion smooth point `P` and nonzero
`p ∈ F[X]`, the order of `algebraMap (Polynomial F) KE p` at `P` is the multiplicity of `P.x`
as a root of `p`. Proof: peel off `(X − P.x)^m` (`m = rootMultiplicity P.x p`); the factor
`(x_gen − P.x)^m` contributes `m·1` (`ord_P_x_gen_sub_self_eq_one`), and the cofactor — which does
not vanish at `P.x` — contributes `0` (`ord_P_algebraMap_poly_eq_zero_of_eval_ne`). -/
theorem ord_P_algebraMap_poly_eq_rootMultiplicity
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (h_not_2_tor : P.y ≠ W.toAffine.negY P.x P.y)
    {p : Polynomial F} (hp : p ≠ 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap (Polynomial F) KE p) =
      ((p.rootMultiplicity P.x : ℤ) : WithTop ℤ) := by
  set m := p.rootMultiplicity P.x with hm
  set q := p /ₘ (Polynomial.X - Polynomial.C P.x) ^ m with hq_def
  have hpq : p = (Polynomial.X - Polynomial.C P.x) ^ m * q :=
    (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p P.x).symm
  have hq_ne : q ≠ 0 := by
    intro h; rw [h, mul_zero] at hpq; exact hp hpq
  have h_eval : q.eval P.x ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero P.x hp
  have h_lin : algebraMap (Polynomial F) KE (Polynomial.X - Polynomial.C P.x) =
      x_gen W - algebraMap F KE P.x := by
    rw [map_sub, algebraMap_poly_eq_aeval_x_gen W Polynomial.X, Polynomial.aeval_X,
      Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply F (Polynomial F) KE P.x]
  rw [hpq, map_mul, map_pow, h_lin,
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, (⟨W⟩ : SmoothPlaneCurve F).ord_P_pow,
    ord_P_x_gen_sub_self_eq_one W P h_not_2_tor,
    ord_P_algebraMap_poly_eq_zero_of_eval_ne W P hq_ne h_eval, add_zero]
  simp

/-- The fibre polynomial `g_ℓ(x_Q) := Φ_ℓ − C x_Q · ΨSq_ℓ ∈ F[X]`, whose roots are the
x-coordinates of the points `P'` with `x([ℓ]·P') = x_Q` (i.e. `[ℓ]·P' = ±Q`). -/
noncomputable def fibrePoly (ℓ : ℤ) (x_Q : F) : Polynomial F :=
  W.Φ ℓ - Polynomial.C x_Q * W.ΨSq ℓ

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `g_ℓ(x_Q)` is monic of degree `ℓ²` (so nonzero), since `Φ_ℓ` is monic of degree `ℓ²` and
`C x_Q · ΨSq_ℓ` has degree `< ℓ²`. Mirrors `mulByInt_x_transcendental`'s monicity argument. -/
theorem fibrePoly_monic {ℓ : ℤ} (hℓ : ℓ ≠ 0) (x_Q : F) :
    (fibrePoly W ℓ x_Q).Monic := by
  have hΦ_monic : (W.Φ ℓ).Monic := show (W.Φ ℓ).leadingCoeff = 1 from W.leadingCoeff_Φ ℓ
  have hΦ_natDeg : (W.Φ ℓ).natDegree = ℓ.natAbs ^ 2 := W.natDegree_Φ ℓ
  have hΨSq_le : (Polynomial.C x_Q * W.ΨSq ℓ).natDegree ≤ ℓ.natAbs ^ 2 - 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (W.natDegree_ΨSq_le ℓ)
  have hn2_pos : 0 < ℓ.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hℓ) 2
  refine hΦ_monic.sub_of_left ?_
  rw [Polynomial.degree_eq_natDegree hΦ_monic.ne_zero, hΦ_natDeg]
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  exact_mod_cast lt_of_le_of_lt hΨSq_le (Nat.sub_lt hn2_pos Nat.one_pos)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `g_ℓ(x_Q).eval x = Φ_ℓ(x) − x_Q · ΨSq_ℓ(x)`. -/
theorem fibrePoly_eval (ℓ : ℤ) (x_Q x : F) :
    (fibrePoly W ℓ x_Q).eval x = (W.Φ ℓ).eval x - x_Q * (W.ΨSq ℓ).eval x := by
  rw [fibrePoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]

omit [W.toAffine.IsElliptic] in
/-- **`P.x` is a root of `g`** (the lower-order content): `g(P.x) = ΨSq_ℓ(P.x)·(x([ℓ]P) − x_Q) = 0`
since `x([ℓ]P) = x_Q`. -/
theorem fibrePoly_isRoot_of_zsmul_eq_some {x y x_Q y_Q : F}
    (h_ns : W.toAffine.Nonsingular x y) (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (hsmul : ℓ • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns') :
    (fibrePoly W ℓ x_Q).eval x = 0 := by
  obtain ⟨hψ_ne, hx_eq, _⟩ := smulEval_facts_of_zsmul_eq_some W h_ns h_ns' ℓ hℓ hsmul
  have h_eq : W.toAffine.Equation x y := h_ns.1
  have hΨSq : (W.ΨSq ℓ).eval x = ((W.ψ ℓ).evalEval x y) ^ 2 := ΨSq_eval_eq_psi_sq W h_eq ℓ
  have hΦ : (W.Φ ℓ).eval x = (W.φ ℓ).evalEval x y := Φ_eval_eq_phi W h_eq ℓ
  rw [fibrePoly_eval, hx_eq, hΦ, hΨSq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ_ne), sub_self]

omit [W.toAffine.IsElliptic] in
/-- **`ψ_m(x,y) ≠ 0` when `m • (x,y) ≠ O`** (the division-polynomial torsion characterization at a
base-field point): the Jacobian `Z`-coordinate of `m • (x,y)` is `ψ_m(x,y)`, which is nonzero unless
the point is `O`. (Base-point analogue of `ψ_m_evalEval_mulByInt_ne_zero`.) -/
theorem psi_evalEval_ne_zero_of_zsmul_ne_zero {x y : F} (h_ns : W.toAffine.Nonsingular x y)
    (m : ℤ) (hm : m • (Affine.Point.some x y h_ns) ≠ 0) :
    (W.ψ m).evalEval x y ≠ 0 := by
  intro hZ
  apply hm
  have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := W) h_ns m
  have hZ' : smulEval W x y m 2 = 0 := hZ
  have h0 : WeierstrassCurve.Jacobian.Point.toAffineLift
      (m • WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x y h_ns)) =
      (0 : W.toAffine.Point) := by
    change (m • WeierstrassCurve.Jacobian.Point.fromAffine
      (Affine.Point.some x y h_ns)).point.lift _ _ = 0
    rw [h_smulEval]
    exact WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero hZ'
  have h_inv : WeierstrassCurve.Jacobian.Point.toAffineLift
      (WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x y h_ns)) =
      Affine.Point.some x y h_ns := by
    rw [← WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply]
    exact (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W).right_inv _
  have h_toAffine :
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x y h_ns)) =
      m • (Affine.Point.some x y h_ns) := by
    have h := map_zsmul (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W)
      m (WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x y h_ns))
    rw [WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply,
      WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply, h_inv] at h
    exact h
  rw [← h_toAffine, h0]

omit [W.toAffine.IsElliptic] in
/-- **`preΨ_ℓ(2ℓ)(P.x) ≠ 0`** when `2•Q ≠ O` (i.e. `Q` non-2-torsion), where `Q = [ℓ]·P`.
`2ℓ•P = 2•Q ≠ O ⟹ ψ_{2ℓ}(P) ≠ 0`; and `ψ_{2ℓ} ≡ Ψ_{2ℓ} = preΨ_{2ℓ}·ψ₂` on the curve, so
`preΨ_{2ℓ}(P.x) ≠ 0`. -/
theorem preΨ_two_mul_eval_ne_zero {x y x_Q y_Q : F}
    (h_ns : W.toAffine.Nonsingular x y) (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    {ℓ : ℤ} (h_not_2_tor_Q : y_Q ≠ W.toAffine.negY x_Q y_Q)
    (hsmul : ℓ • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns') :
    (W.preΨ (2 * ℓ)).eval x ≠ 0 := by
  have hQ2_ne : (2 : ℤ) • (Affine.Point.some x_Q y_Q h_ns') ≠ 0 := by
    intro hQ2
    have hQneg : Affine.Point.some x_Q y_Q h_ns' = -(Affine.Point.some x_Q y_Q h_ns') := by
      rw [eq_neg_iff_add_eq_zero, ← two_zsmul]; exact hQ2
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hQneg
    exact h_not_2_tor_Q hQneg.2
  have h2ℓ_ne : (2 * ℓ) • (Affine.Point.some x y h_ns) ≠ 0 := by
    rw [mul_zsmul, hsmul]; exact hQ2_ne
  have hψ_ne : (W.ψ (2 * ℓ)).evalEval x y ≠ 0 :=
    psi_evalEval_ne_zero_of_zsmul_ne_zero W h_ns (2 * ℓ) h2ℓ_ne
  have h_eq : W.toAffine.Equation x y := h_ns.1
  have hΨ_eq : (W.ψ (2 * ℓ)).evalEval x y = (W.Ψ (2 * ℓ)).evalEval x y :=
    evalEval_eq_of_mk_eq W h_eq (Affine.CoordinateRing.mk_ψ (W := W.toAffine) (2 * ℓ))
  have hΨ_factored : (W.Ψ (2 * ℓ)).evalEval x y =
      (W.preΨ (2 * ℓ)).eval x * (W.ψ₂).evalEval x y := by
    rw [show W.Ψ (2 * ℓ) = Polynomial.C (W.preΨ (2 * ℓ)) * W.ψ₂ from by
      rw [WeierstrassCurve.Ψ, if_pos (even_two_mul ℓ)],
      Polynomial.evalEval_mul, Polynomial.evalEval_C]
  rw [hΨ_eq, hΨ_factored] at hψ_ne
  exact fun h ↦ hψ_ne (by rw [h, zero_mul])

/-- **Separability kernel discharged: `P.x` is a *simple* root of `g`** — `g'(P.x) ≠ 0`.

`ΨSq_ℓ(P.x)·g'(P.x) = (ΨSq_ℓ·Φ_ℓ' − Φ_ℓ·ΨSq_ℓ')(P.x)` (using `Φ_ℓ(P.x) = x_Q·ΨSq_ℓ(P.x)`), and the
axiom-clean division-polynomial **Wronskian** `wronskian_Φ_ΨSq_general`
(`EC/WronskianGeneral.lean`, EDS-free, routed through the function-field differential `a_{[ℓ]} = ℓ`)
gives `ΨSq_ℓ·Φ_ℓ' − Φ_ℓ·ΨSq_ℓ' = C ℓ · preΨ_{2ℓ}`
(Silverman III.3.7). Hence `ΨSq_ℓ(P.x)·g'(P.x) = ℓ · preΨ_{2ℓ}(P.x) ≠ 0` since `(ℓ : F) ≠ 0` and
`preΨ_{2ℓ}(P.x) ≠ 0` (the latter is `2•Q ≠ O`, i.e. `Q` non-2-torsion). As `ΨSq_ℓ(P.x) ≠ 0`, we get
`g'(P.x) ≠ 0`. This is exactly the unramifiedness/separability of `[ℓ]` (Silverman III.4.10c). -/
theorem fibrePoly_derivative_eval_ne_zero {x y x_Q y_Q : F}
    (h_ns : W.toAffine.Nonsingular x y) (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) (h_not_2_tor_Q : y_Q ≠ W.toAffine.negY x_Q y_Q)
    (hsmul : ℓ • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns') :
    (fibrePoly W ℓ x_Q).derivative.eval x ≠ 0 := by
  obtain ⟨hψ_ne, hx_eq, _⟩ := smulEval_facts_of_zsmul_eq_some W h_ns h_ns' ℓ hℓ hsmul
  have h_eq : W.toAffine.Equation x y := h_ns.1
  have hΨSq_ne : (W.ΨSq ℓ).eval x ≠ 0 := by
    rw [ΨSq_eval_eq_psi_sq W h_eq ℓ]; exact pow_ne_zero 2 hψ_ne
  have hΦ_root : (W.Φ ℓ).eval x = x_Q * (W.ΨSq ℓ).eval x := by
    rw [ΨSq_eval_eq_psi_sq W h_eq ℓ, Φ_eval_eq_phi W h_eq ℓ, hx_eq,
      div_mul_cancel₀ _ (pow_ne_zero 2 hψ_ne)]
  have h_der : (fibrePoly W ℓ x_Q).derivative =
      Polynomial.derivative (W.Φ ℓ) - Polynomial.C x_Q * Polynomial.derivative (W.ΨSq ℓ) := by
    rw [fibrePoly, Polynomial.derivative_sub, Polynomial.derivative_C_mul]
  have h_wron := congrArg (Polynomial.eval x) (HasseWeil.EC.wronskian_Φ_ΨSq_general W ℓ hℓ)
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C] at h_wron
  have h_key : (W.ΨSq ℓ).eval x * (fibrePoly W ℓ x_Q).derivative.eval x =
      (ℓ : F) * (W.preΨ (2 * ℓ)).eval x := by
    rw [h_der, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, ← h_wron, hΦ_root]
    ring
  have h_rhs_ne : (ℓ : F) * (W.preΨ (2 * ℓ)).eval x ≠ 0 :=
    mul_ne_zero hℓF (preΨ_two_mul_eval_ne_zero W h_ns h_ns' h_not_2_tor_Q hsmul)
  intro h_der_zero
  rw [h_der_zero, mul_zero] at h_key
  exact h_rhs_ne h_key.symm

/-- **`rootMultiplicity x_P g = 1`.** `P.x` is a root (`fibrePoly_isRoot_of_zsmul_eq_some`) so
`1 ≤ rootMultiplicity`; the simple-root kernel (`g'(P.x) ≠ 0`) gives `rootMultiplicity ≤ 1`. -/
theorem fibrePoly_rootMultiplicity_eq_one {x y x_Q y_Q : F}
    (h_ns : W.toAffine.Nonsingular x y) (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) (h_not_2_tor_Q : y_Q ≠ W.toAffine.negY x_Q y_Q)
    (hsmul : ℓ • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns') :
    (fibrePoly W ℓ x_Q).rootMultiplicity x = 1 := by
  have hg_ne : fibrePoly W ℓ x_Q ≠ 0 := (fibrePoly_monic W hℓ x_Q).ne_zero
  have h_root : (fibrePoly W ℓ x_Q).IsRoot x :=
    fibrePoly_isRoot_of_zsmul_eq_some W h_ns h_ns' hℓ hsmul
  have h_ge : 1 ≤ (fibrePoly W ℓ x_Q).rootMultiplicity x :=
    (Polynomial.rootMultiplicity_pos hg_ne).2 h_root
  have h_le : (fibrePoly W ℓ x_Q).rootMultiplicity x ≤ 1 := by
    by_contra! h
    have h_der_root : (fibrePoly W ℓ x_Q).derivative.IsRoot x := by
      simpa using Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
        (p := fibrePoly W ℓ x_Q) (t := x) (n := 1) h
    exact fibrePoly_derivative_eval_ne_zero W h_ns h_ns' hℓ hℓF h_not_2_tor_Q hsmul h_der_root
  omega

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `Φ_ff W ℓ = algebraMap (Polynomial F) KE (W.Φ ℓ)` (scalar tower `F[X] → R → KE`). -/
theorem Φ_ff_eq_algebraMap (ℓ : ℤ) :
    Φ_ff W ℓ = algebraMap (Polynomial F) KE (W.Φ ℓ) :=
  (IsScalarTower.algebraMap_apply (Polynomial F) R KE (W.Φ ℓ)).symm

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `ΨSq_ff W ℓ = algebraMap (Polynomial F) KE (W.ΨSq ℓ)` (scalar tower `F[X] → R → KE`). -/
theorem ΨSq_ff_eq_algebraMap (ℓ : ℤ) :
    ΨSq_ff W ℓ = algebraMap (Polynomial F) KE (W.ΨSq ℓ) :=
  (IsScalarTower.algebraMap_apply (Polynomial F) R KE (W.ΨSq ℓ)).symm

/-- **`ΨSq_ℓ(x_gen)` is a unit at `P` (`ord_P = 0`)** when `[ℓ]·P` is affine: the affine image
forces `ΨSq_ℓ(P.x) = ψ_ℓ(P.x,P.y)² ≠ 0`, so `mulByInt_x ℓ` has no pole at `P`. -/
theorem ord_P_ΨSq_ff_eq_zero {x y x_Q y_Q : F}
    (h_ns : W.toAffine.Nonsingular x y) (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (hsmul : ℓ • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns')
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (hPx : P.x = x) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ΨSq_ff W ℓ) = 0 := by
  obtain ⟨hψ_ne, _, _⟩ := smulEval_facts_of_zsmul_eq_some W h_ns h_ns' ℓ hℓ hsmul
  have hΨSq_eval_ne : (W.ΨSq ℓ).eval P.x ≠ 0 := by
    rw [hPx, ΨSq_eval_eq_psi_sq W h_ns.1 ℓ]; exact pow_ne_zero 2 hψ_ne
  rw [ΨSq_ff_eq_algebraMap]
  exact ord_P_algebraMap_poly_eq_zero_of_eval_ne W P (ΨSq_poly_ne_zero W hℓ) hΨSq_eval_ne

-- `ΨSq_ff`/`mulByInt_x` carry the section `DecidableEq F` (via the coordinate ring) although the
-- type does not mention it; `classical` cannot substitute. Suppress the unused-in-type lint.
set_option linter.unusedDecidableInType false in
/-- `mulByInt_x ℓ − x_Q = algebraMap g / algebraMap ΨSq_ℓ` for the fibre polynomial `g`. -/
theorem mulByInt_x_sub_const_eq_div {ℓ : ℤ} (hℓ : ℓ ≠ 0) (x_Q : F) :
    mulByInt_x W ℓ - algebraMap F KE x_Q =
      algebraMap (Polynomial F) KE (fibrePoly W ℓ x_Q) / ΨSq_ff W ℓ := by
  have hΨ : algebraMap (Polynomial F) KE (W.ΨSq ℓ) ≠ 0 := by
    rw [← ΨSq_ff_eq_algebraMap]; exact ΨSq_ff_ne_zero W hℓ
  rw [mulByInt_x, Φ_ff_eq_algebraMap, ΨSq_ff_eq_algebraMap, fibrePoly, map_sub, map_mul,
    show algebraMap (Polynomial F) KE (Polynomial.C x_Q) = algebraMap F KE x_Q from by
      rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply F (Polynomial F) KE x_Q],
    sub_div, mul_div_assoc, div_self hΨ, mul_one]

omit [W.toAffine.IsElliptic] in
/-- **`P` is non-2-torsion when `Q = [ℓ]·P` is** (`2•P = 0 ⟹ 2•Q = ℓ•(2•P) = 0`). -/
theorem not_2_tor_of_image_not_2_tor {x_Q y_Q : F} (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    {ℓ : ℤ} (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (h_not_2_tor_Q : y_Q ≠ W.toAffine.negY x_Q y_Q)
    (hsmul : ℓ • P.toAffinePoint = Affine.Point.some x_Q y_Q h_ns') :
    P.y ≠ W.toAffine.negY P.x P.y := by
  intro h2P
  have hneg : P.toAffinePoint = -P.toAffinePoint := by
    rw [SmoothPlaneCurve.SmoothPoint.toAffinePoint_def,
      WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨rfl, h2P⟩
  have hP2 : (2 : ℤ) • P.toAffinePoint = 0 := by
    rw [two_zsmul]; nth_rewrite 1 [hneg]; rw [neg_add_cancel]
  have hQ2 : (2 : ℤ) • (Affine.Point.some x_Q y_Q h_ns') = 0 := by
    rw [← hsmul, smul_comm, hP2, smul_zero]
  have hQneg : Affine.Point.some x_Q y_Q h_ns' = -(Affine.Point.some x_Q y_Q h_ns') := by
    rw [eq_neg_iff_add_eq_zero, ← two_zsmul]; exact hQ2
  rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hQneg
  exact h_not_2_tor_Q hQneg.2

/-- **Main lemma (the `e = 1` unramifiedness of `[ℓ]`).** For `[ℓ]` separable (`(ℓ : F) ≠ 0`) and a
smooth point `P` of `⟨W⟩` whose image `[ℓ]·P = (x_Q, y_Q)` is an affine *non-2-torsion* point, the
pullback `[ℓ]^*(x_gen − x_Q) = mulByInt_x ℓ − x_Q` of the uniformizer `x_gen − x_Q` at `Q` is a
uniformizer at `P`:
`ord_P P (mulByInt_x ℓ − x_Q) = 1`.

This is the `e = 1` input to `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`. The whole reduction
is **axiom-clean** (`[propext, Classical.choice, Quot.sound]`): the division-polynomial Wronskian it
consumes (through `fibrePoly_derivative_eval_ne_zero`) is the EDS-free `wronskian_Φ_ΨSq_general`
(`EC/WronskianGeneral.lean`), proved downstream via the function-field differential `a_{[ℓ]} = ℓ`
(`omegaCoeff_mulByInt`, Route-B), so it carries no `sorryAx`. -/
theorem ord_P_mulByInt_x_sub_const_eq_one (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x_Q y_Q : F}
    (h_ns' : W.toAffine.Nonsingular x_Q y_Q) (h_not_2_tor_Q : y_Q ≠ W.toAffine.negY x_Q y_Q)
    (hQ : (mulByInt W.toAffine ℓ).toAddMonoidHom P.toAffinePoint =
      Affine.Point.some x_Q y_Q h_ns') :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_x W ℓ - algebraMap F KE x_Q) =
      ((1 : ℤ) : WithTop ℤ) := by
  have hsmul : ℓ • (Affine.Point.some P.x P.y P.nonsingular) =
      Affine.Point.some x_Q y_Q h_ns' := by
    rw [mulByInt_apply] at hQ
    rw [← SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]; exact hQ
  have hsmul' : ℓ • P.toAffinePoint = Affine.Point.some x_Q y_Q h_ns' := by
    rw [SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]; exact hsmul
  have h_not_2_tor_P : P.y ≠ W.toAffine.negY P.x P.y :=
    not_2_tor_of_image_not_2_tor W h_ns' P h_not_2_tor_Q hsmul'
  have hΨ_ne : ΨSq_ff W ℓ ≠ 0 := ΨSq_ff_ne_zero W hℓ
  have hg_ne : fibrePoly W ℓ x_Q ≠ 0 := (fibrePoly_monic W hℓ x_Q).ne_zero
  rw [mulByInt_x_sub_const_eq_div W hℓ, div_eq_mul_inv,
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hΨ_ne,
    ord_P_ΨSq_ff_eq_zero W P.nonsingular h_ns' hℓ hsmul P rfl,
    ord_P_algebraMap_poly_eq_rootMultiplicity W P h_not_2_tor_P hg_ne,
    fibrePoly_rootMultiplicity_eq_one W P.nonsingular h_ns' hℓ hℓF h_not_2_tor_Q hsmul]
  norm_num

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`ord_P (algebraMap R KE u) ≥ 1` when `u` vanishes at `P`** (`evalAt P u = 0`) and `u ≠ 0`.
The coordinate-ring membership form: `u ∈ m_P` ⟹ `ord_P ≥ 1` (combining
`ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt` with `ord_P ≥ 0`). -/
theorem one_le_ord_P_algebraMap_of_evalAt_zero
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {u : R} (hu_ne : u ≠ 0)
    (heval : (⟨W⟩ : SmoothPlaneCurve F).evalAt P u = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap R KE u) := by
  have hu_mem : u ∈ (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P := by
    rw [← (⟨W⟩ : SmoothPlaneCurve F).ker_evalAt P, RingHom.mem_ker]; exact heval
  have h_ord_ne_zero : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap R KE u) ≠ 0 :=
    ((⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt hu_ne P).mpr hu_mem
  have h_au_ne : algebraMap R KE u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R KE)).mpr hu_ne
  have h_ord_nonneg : (0 : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap R KE u) := by
    have hv : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (algebraMap R KE u) ≠ 0 :=
      ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).ne_zero_iff.mpr h_au_ne
    have h_v_le : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (algebraMap R KE u) ≤ 1 :=
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one u P
    unfold SmoothPlaneCurve.ord_P
    rw [dif_neg hv, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    have h_unz_le : WithZero.unzero hv ≤ 1 := by
      rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]; exact h_v_le
    have h_toAdd : (WithZero.unzero hv).toAdd ≤ 0 := h_unz_le
    omega
  have h_ne_top : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap R KE u) ≠ ⊤ :=
    (SmoothPlaneCurve.ord_P_eq_top_iff _).not.mpr h_au_ne
  cases h : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap R KE u) with
  | top => exact absurd h h_ne_top
  | coe n =>
    rw [h] at h_ord_nonneg h_ord_ne_zero
    have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast h_ord_nonneg
    have hn_ne : n ≠ 0 := fun hn ↦ h_ord_ne_zero (by rw [hn]; rfl)
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`ord_P (algebraMap (Polynomial F) KE p) ≥ 1` when `p(P.x) = 0`** and `p ≠ 0`. Univariate
specialisation of `one_le_ord_P_algebraMap_of_evalAt_zero` (`evalAt P (algMap p) = p.eval P.x`). -/
theorem one_le_ord_P_algebraMap_poly_of_root
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {p : Polynomial F} (hp : p ≠ 0)
    (heval : p.eval P.x = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap (Polynomial F) KE p) := by
  set u : R := algebraMap (Polynomial F) R p with hu_def
  have hu_ne : u ≠ 0 := fun h ↦
    hp (Affine.CoordinateRing.algebraMap_poly_injective (h.trans (map_zero _).symm))
  have h_factor : algebraMap (Polynomial F) KE p = algebraMap R KE u := by
    rw [hu_def, ← IsScalarTower.algebraMap_apply (Polynomial F) R KE p]
  rw [h_factor]
  refine one_le_ord_P_algebraMap_of_evalAt_zero W P hu_ne ?_
  rw [hu_def, evalAt_algebraMap_poly W P p]; exact heval

private theorem mulByInt_neg_mem_kernel_of_torsion (n : ℤ)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W.toAffine n).toAddMonoidHom P.toAffinePoint = (0 : W.toAffine.Point)) :
    -P.toAffinePoint ∈ (mulByInt W.toAffine n).kernel := by
  rw [HasseWeil.Isogeny.mem_kernel_iff, map_neg, hQ, neg_zero]

/-- **`ord_P (mulByInt_x n) = -2` at an `n`-torsion point `P`** (`[n]·P = O`), via the
kernel-translation invariance of `mulByInt_x n` (`hxy_mulByInt`) and the translation order-transport
`ord_P (τ_{-P} g) = ord_∞ g`, transporting `ord_∞ (mulByInt_x n) = -2` to `P`. (Upstream-only
re-derivation of `ord_P_mulByInt_x_eq_neg_two_of_torsion`, which lives in the downstream
`MulByIntSamePlace.lean`; the proof uses only `TranslateOrdInfty`/`TorsionGeometric` ingredients
available here.) -/
theorem ord_P_mulByInt_x_eq_neg_two_of_torsion' (n : ℤ) (hn : n ≠ 0) (hnF : (n : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W.toAffine n).toAddMonoidHom P.toAffinePoint = (0 : W.toAffine.Point)) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_x W n) = ((-2 : ℤ) : WithTop ℤ) := by
  set k : W.toAffine.Point := -P.toAffinePoint with hk
  have hk_mem : k ∈ (mulByInt W.toAffine n).kernel := mulByInt_neg_mem_kernel_of_torsion W n P hQ
  have h_zero : P.toAffinePoint + k = Affine.Point.zero := by rw [hk]; exact add_neg_cancel _
  have h_compat := isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint W P k h_zero
  have h_inv : translateAlgEquivOfPoint W k (mulByInt_x W n) = mulByInt_x W n :=
    (WeilPairing.TorsionGeometric.hxy_mulByInt W n hn ⟨k, hk_mem⟩).1
  exact (ord_P_eq_ordAtInfty_of_invariant_and_compatible W P k h_zero h_compat
    (mulByInt_x W n) h_inv).trans (ordAtInfty_mulByInt_x W n hn hnF)

omit [DecidableEq F] in
/-- **`Φ_{2ℓ}(P.x) ≠ 0` from `ΨSq_{2ℓ}(P.x) = 0`.** Coprimality of `Φ_{2ℓ}, ΨSq_{2ℓ}`
(`isCoprime_Φ_ΨSq`) rules out a common root. -/
theorem Φ_two_mul_eval_ne_zero_of_ΨSq_zero {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (hΨSq0 : (W.ΨSq (2 * ℓ)).eval P.x = 0) :
    (W.Φ (2 * ℓ)).eval P.x ≠ 0 := by
  have h2ℓ : (2 * ℓ : ℤ) ≠ 0 := by omega
  have hcop : IsCoprime (W.Φ (2 * ℓ)) (W.ΨSq (2 * ℓ)) :=
    isCoprime_Φ_ΨSq W (W.coe_Δ' ▸ W.Δ'.ne_zero) h2ℓ
  intro hΦ0
  obtain ⟨u, v, huv⟩ := hcop
  have hev := congrArg (Polynomial.eval P.x) huv
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hΦ0, hΨSq0,
    mul_zero, mul_zero, add_zero, Polynomial.eval_one] at hev
  exact one_ne_zero hev.symm

/-- **`ord_P (ψ_ff(2ℓ)) = 1` at a `2ℓ`-torsion point `P`** with `(2ℓ : F) ≠ 0`. From the
`[2ℓ]`-torsion pole `ord_P (mulByInt_x (2ℓ)) = -2` (which already forces `ΨSq_{2ℓ}(P.x) = 0`) and
`mulByInt_x (2ℓ) = Φ_ff(2ℓ)/ΨSq_ff(2ℓ)`: since `ord_P (Φ_ff(2ℓ)) = 0` (`Φ_{2ℓ}(P.x) ≠ 0`,
coprimality), we get `ord_P (ΨSq_ff(2ℓ)) = 2`, and `ΨSq_ff = ψ_ff²` halves it. This is the simple
zero of `ψ_{2ℓ}` at the `2ℓ`-torsion point. -/
theorem ord_P_ψ_ff_two_mul_eq_one {ℓ : ℤ} (hℓ : ℓ ≠ 0) (h2ℓF : (2 * ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ2 : (mulByInt W.toAffine (2 * ℓ)).toAddMonoidHom P.toAffinePoint = (0 : W.toAffine.Point)) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ψ_ff W (2 * ℓ)) = ((1 : ℤ) : WithTop ℤ) := by
  have h2ℓ : (2 * ℓ : ℤ) ≠ 0 := by omega
  have h2ℓF' : ((2 * ℓ : ℤ) : F) ≠ 0 := by push_cast; exact h2ℓF
  have hpole := ord_P_mulByInt_x_eq_neg_two_of_torsion' W (2 * ℓ) h2ℓ h2ℓF' P hQ2
  have hΨ_ne : ΨSq_ff W (2 * ℓ) ≠ 0 := ΨSq_ff_ne_zero W h2ℓ
  have hΦnonneg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Φ_ff W (2 * ℓ)) := by
    rw [Φ_ff_eq_algebraMap]
    rcases eq_or_ne ((W.Φ (2 * ℓ)).eval P.x) 0 with h0 | h0
    · exact le_trans (by norm_num)
        (one_le_ord_P_algebraMap_poly_of_root W P (W.Φ_ne_zero (2 * ℓ)) h0)
    · rw [ord_P_algebraMap_poly_eq_zero_of_eval_ne W P (W.Φ_ne_zero (2 * ℓ)) h0]
  have hΨpos : (0 : WithTop ℤ) < (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ΨSq_ff W (2 * ℓ)) := by
    have hxeq : mulByInt_x W (2 * ℓ) = Φ_ff W (2 * ℓ) * (ΨSq_ff W (2 * ℓ))⁻¹ := by
      rw [mulByInt_x, div_eq_mul_inv]
    rw [hxeq, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hΨ_ne] at hpole
    obtain ⟨m, hm⟩ := exists_intCast_ord_P W P hΨ_ne
    obtain ⟨k, hk⟩ := exists_intCast_ord_P W P (Φ_ff_ne_zero W (2 * ℓ))
    rw [hm, hk] at hpole
    rw [hk] at hΦnonneg
    rw [hm]
    have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast hΦnonneg
    have hkm : (k : ℤ) + -m = -2 := by exact_mod_cast hpole
    exact_mod_cast (by omega : (0 : ℤ) < m)
  have hΨSq0 : (W.ΨSq (2 * ℓ)).eval P.x = 0 := by
    by_contra h0
    rw [ΨSq_ff_eq_algebraMap, ord_P_algebraMap_poly_eq_zero_of_eval_ne W P
      (ΨSq_poly_ne_zero W h2ℓ) h0] at hΨpos
    exact lt_irrefl _ hΨpos
  have hΦeval : (W.Φ (2 * ℓ)).eval P.x ≠ 0 := Φ_two_mul_eval_ne_zero_of_ΨSq_zero W hℓ P hΨSq0
  have hΦ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Φ_ff W (2 * ℓ)) = 0 := by
    rw [Φ_ff_eq_algebraMap]
    exact ord_P_algebraMap_poly_eq_zero_of_eval_ne W P (W.Φ_ne_zero (2 * ℓ)) hΦeval
  have hΨ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ΨSq_ff W (2 * ℓ)) = ((2 : ℤ) : WithTop ℤ) := by
    have hx_eq : mulByInt_x W (2 * ℓ) = Φ_ff W (2 * ℓ) * (ΨSq_ff W (2 * ℓ))⁻¹ := by
      rw [mulByInt_x, div_eq_mul_inv]
    rw [hx_eq, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hΨ_ne, hΦ_ord, zero_add] at hpole
    obtain ⟨m, hm⟩ := exists_intCast_ord_P W P hΨ_ne
    rw [hm] at hpole ⊢
    have : (-m : ℤ) = -2 := by exact_mod_cast hpole
    exact_mod_cast (by omega : m = 2)
  have hψ_ne : ψ_ff W (2 * ℓ) ≠ 0 := ψ_ff_ne_zero W h2ℓ
  rw [← ψ_ff_sq_eq_ΨSq_ff, sq, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul] at hΨ_ord
  obtain ⟨m, hm⟩ := exists_intCast_ord_P W P hψ_ne
  rw [hm] at hΨ_ord ⊢
  have : (m + m : ℤ) = 2 := by exact_mod_cast hΨ_ord
  exact_mod_cast (by omega : m = 1)

omit [W.toAffine.IsElliptic] in
/-- **`ord_P (ψ_ff ℓ) = 0` at an affine `[ℓ]`-image** (`ψ_ℓ(P) ≠ 0`). The `y`-denominator is a unit
at `P`. -/
theorem ord_P_ψ_ff_eq_zero {x y x_Q y_Q : F}
    (h_ns : W.toAffine.Nonsingular x y) (h_ns' : W.toAffine.Nonsingular x_Q y_Q)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (hsmul : ℓ • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns')
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (hPx : P.x = x) (hPy : P.y = y) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ψ_ff W ℓ) = 0 := by
  obtain ⟨hψ_ne, _, _⟩ := smulEval_facts_of_zsmul_eq_some W h_ns h_ns' ℓ hℓ hsmul
  have heval : (⟨W⟩ : SmoothPlaneCurve F).evalAt P (Affine.CoordinateRing.mk W.toAffine (W.ψ ℓ))
      ≠ 0 := by
    rw [SmoothPlaneCurve.evalAt_mk, hPx, hPy]; exact hψ_ne
  have hne : Affine.CoordinateRing.mk W.toAffine (W.ψ ℓ) ≠ 0 := fun h ↦ heval (by rw [h]; simp)
  have h_notmem : Affine.CoordinateRing.mk W.toAffine (W.ψ ℓ) ∉
      (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P := by
    rw [← SmoothPlaneCurve.ker_evalAt, RingHom.mem_ker]; exact heval
  by_contra h_ne
  exact h_notmem
    (((⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt hne P).mp h_ne)

omit [DecidableEq F] in
private theorem ord_P_y_numerator_eq_zero
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {X Y : KE} {x_Q y_Q : F}
    (hc : (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q : F) ≠ 0)
    (hX_reg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P X)
    (hX_sub : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (X - algebraMap F KE x_Q))
    (hY_sub : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Y - algebraMap F KE y_Q)) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        (3 * X ^ 2 + 2 * algebraMap F KE W.a₂ * X + algebraMap F KE W.a₄ -
          algebraMap F KE W.a₁ * Y) = 0 := by
  classical
  set xq := algebraMap F KE x_Q with hxq
  set yq := algebraMap F KE y_Q with hyq
  have hC_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (algebraMap F KE (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q)) = 0 :=
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero hc P
  have hX_xq_reg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (X + xq) := by
    have hxqreg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P xq := by
      rw [hxq]; exact ord_P_algebraMap_F_nonneg W P _
    exact le_trans (le_min hX_reg hxqreg) (SmoothPlaneCurve.ord_P_add_le (P := P) _ _)
  have ht1 : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (3 * ((X - xq) * (X + xq))) := by
    have h3reg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (3 : KE) := by
      rw [show (3 : KE) = algebraMap F KE 3 from (map_ofNat (algebraMap F KE) 3).symm]
      exact ord_P_algebraMap_F_nonneg W P _
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul]
    have hh := add_le_add (add_le_add h3reg hX_sub) hX_xq_reg
    rwa [zero_add, add_zero, add_assoc] at hh
  have ht2 : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (algebraMap F KE (2 * W.a₂) * (X - xq)) := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul]
    have hh := add_le_add (ord_P_algebraMap_F_nonneg W P (2 * W.a₂)) hX_sub
    rwa [zero_add] at hh
  have ht3 : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (algebraMap F KE W.a₁ * (Y - yq)) := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul]
    have hh := add_le_add (ord_P_algebraMap_F_nonneg W P W.a₁) hY_sub
    rwa [zero_add] at hh
  have hR'_pos : (0 : WithTop ℤ) < (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (3 * ((X - xq) * (X + xq)) + algebraMap F KE (2 * W.a₂) * (X - xq) -
        algebraMap F KE W.a₁ * (Y - yq)) := by
    refine lt_of_lt_of_le (show (0 : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ) by
      exact_mod_cast Int.zero_lt_one) ?_
    rw [sub_eq_add_neg]
    refine le_trans (le_min (le_trans (le_min ht1 ht2)
      (SmoothPlaneCurve.ord_P_add_le (P := P) _ _)) ?_)
      (SmoothPlaneCurve.ord_P_add_le (P := P) _ _)
    rw [SmoothPlaneCurve.ord_P_neg]; exact ht3
  have hsplit : 3 * X ^ 2 + 2 * algebraMap F KE W.a₂ * X + algebraMap F KE W.a₄ -
        algebraMap F KE W.a₁ * Y =
      algebraMap F KE (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q) +
      (3 * ((X - xq) * (X + xq)) + algebraMap F KE (2 * W.a₂) * (X - xq) -
        algebraMap F KE W.a₁ * (Y - yq)) := by
    rw [hxq, hyq]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hsplit, SmoothPlaneCurve.ord_P_add_eq_of_lt (by rw [hC_ord]; exact hR'_pos), hC_ord]

omit [DecidableEq F] in
/-- **The ratio-cofactor `B` is a unit at `P`** (`ord_P B = 0`). With `X := mulByInt_x ℓ`, the
cofactor in `(Y − y_Q)·A = (X − x_Q)·B` is
`B = X² + X·x_Q + x_Q² + a₂(X + x_Q) + a₄ − a₁·y_Q`, which splits as
`(X − x_Q)·(X + 2x_Q + a₂) + (3x_Q² + 2a₂x_Q + a₄ − a₁y_Q)`: the first summand has order `≥ 1`
(`X − x_Q` vanishes at `P`), the constant summand is a nonzero base-field element (order `0`, the
smooth 2-torsion condition `polynomialX(Q) ≠ 0`), so the minimum picks out `0`. -/
private theorem ord_P_y_cofactor_eq_zero
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {X : KE} {x_Q y_Q : F}
    (hc : (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q : F) ≠ 0)
    (hX_reg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P X)
    (hX_sub : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (X - algebraMap F KE x_Q)) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        (X ^ 2 + X * algebraMap F KE x_Q + algebraMap F KE x_Q ^ 2 +
          algebraMap F KE W.a₂ * (X + algebraMap F KE x_Q) + algebraMap F KE W.a₄ -
          algebraMap F KE W.a₁ * algebraMap F KE y_Q) = 0 := by
  classical
  set xq := algebraMap F KE x_Q with hxq
  have hBma_decomp : X ^ 2 + X * xq + xq ^ 2 +
        algebraMap F KE W.a₂ * (X + xq) + algebraMap F KE W.a₄ -
        algebraMap F KE W.a₁ * algebraMap F KE y_Q =
      (X - xq) * (X + algebraMap F KE (2 * x_Q + W.a₂)) +
        algebraMap F KE (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q) := by
    rw [hxq]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hBma_decomp]
  have hConst_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap F KE
      (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q)) = 0 :=
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero hc P
  have hRfactor_nonneg : (0 : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (X + algebraMap F KE (2 * x_Q + W.a₂)) := by
    have hConstNonneg : (0 : WithTop ℤ) ≤
        (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap F KE (2 * x_Q + W.a₂)) :=
      ord_P_algebraMap_F_nonneg W P _
    exact le_trans (le_min hX_reg hConstNonneg) (SmoothPlaneCurve.ord_P_add_le (P := P) _ _)
  have h_prod_ge : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P ((X - xq) * (X + algebraMap F KE (2 * x_Q + W.a₂))) := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul]
    have hh := add_le_add hX_sub hRfactor_nonneg
    rwa [add_zero] at hh
  have h_lt : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (algebraMap F KE (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q)) <
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P ((X - xq) * (X + algebraMap F KE (2 * x_Q + W.a₂))) := by
    rw [hConst_ord]
    exact lt_of_lt_of_le (by exact_mod_cast (show (0 : ℤ) < 1 by norm_num)) h_prod_ge
  rw [add_comm, SmoothPlaneCurve.ord_P_add_eq_of_lt h_lt, hConst_ord]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **The `y`-uniformizer pullback vanishes at `P`** (`ord_P (mulByInt_y ℓ − y_Q) ≥ 1`). Writing
`mulByInt_y ℓ − y_Q = (ω_ℓ − y_Q·ψ_ℓ³)/ψ_ℓ³` with `ψ_ℓ³` a unit at `P` (`ord_P (ψ_ff ℓ) = 0`),
the order equals that of the numerator `u := ω_ℓ − y_Q·ψ_ℓ³ ∈ R`, which evaluates to
`y_Q·ψ_ℓ(P)³ − y_Q·ψ_ℓ(P)³ = 0` at `P` since `y([ℓ]P) = ω_ℓ(P)/ψ_ℓ(P)³ = y_Q`; a coordinate-ring
element vanishing at `P` has `ord_P ≥ 1`. -/
private theorem one_le_ord_P_mulByInt_y_sub_const {ℓ : ℤ}
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {y_Q : F}
    (hψ_ne : (W.ψ ℓ).evalEval P.x P.y ≠ 0)
    (hyQ_eq : y_Q = (W.ω ℓ).evalEval P.x P.y / (W.ψ ℓ).evalEval P.x P.y ^ 3)
    (hψℓ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ψ_ff W ℓ) = 0)
    (hY_sub_ne : mulByInt_y W ℓ - algebraMap F KE y_Q ≠ 0) :
    ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_y W ℓ - algebraMap F KE y_Q) := by
  classical
  have hψℓ_ne : ψ_ff W ℓ ≠ 0 := by
    intro h; rw [h, (⟨W⟩ : SmoothPlaneCurve F).ord_P_zero] at hψℓ_ord
    exact (by simp : (⊤ : WithTop ℤ) ≠ 0) hψℓ_ord
  set uY : R := Affine.CoordinateRing.mk W.toAffine (W.ω ℓ) -
    algebraMap F R y_Q * Affine.CoordinateRing.mk W.toAffine (W.ψ ℓ) ^ 3 with huY
  have hψ3_ne : ψ_ff W ℓ ^ 3 ≠ 0 := pow_ne_zero 3 hψℓ_ne
  have hYdiv : mulByInt_y W ℓ - algebraMap F KE y_Q = algebraMap R KE uY * (ψ_ff W ℓ ^ 3)⁻¹ := by
    rw [mulByInt_y, huY, map_sub, map_mul, map_pow,
      show algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ω ℓ)) = ω_ff W ℓ from rfl,
      show algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ ℓ)) = ψ_ff W ℓ from rfl,
      show algebraMap R KE (algebraMap F R y_Q) = algebraMap F KE y_Q from
        (IsScalarTower.algebraMap_apply F R KE y_Q).symm,
      sub_mul, mul_assoc, mul_inv_cancel₀ hψ3_ne, mul_one, div_eq_mul_inv]
  have huY_ne : uY ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hYdiv
    exact hY_sub_ne hYdiv
  have heval : (⟨W⟩ : SmoothPlaneCurve F).evalAt P uY = 0 := by
    rw [huY, map_sub, map_mul, map_pow, SmoothPlaneCurve.evalAt_mk, SmoothPlaneCurve.evalAt_mk,
      show (⟨W⟩ : SmoothPlaneCurve F).evalAt P (algebraMap F R y_Q) = y_Q from by
        rw [show algebraMap F R y_Q =
            algebraMap F (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing y_Q from rfl,
          (⟨W⟩ : SmoothPlaneCurve F).evalAt_algebraMap], hyQ_eq,
      div_mul_cancel₀ _ (pow_ne_zero 3 hψ_ne), sub_self]
  rw [hYdiv, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hψ3_ne,
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_pow, hψℓ_ord]
  simp only [smul_zero, neg_zero, add_zero]
  exact one_le_ord_P_algebraMap_of_evalAt_zero W P huY_ne heval

/-- **The image is killed by `[2ℓ]`.** If `[ℓ]·P = Q = (x_Q, y_Q)` with `Q` 2-torsion
(`y_Q = negY x_Q y_Q`), then `[2ℓ]·P = 2·([ℓ]·P) = 2·Q = O`. -/
private theorem mulByInt_two_mul_eq_zero_of_image_2_tor (ℓ : ℤ)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x_Q y_Q : F}
    (h_ns' : W.toAffine.Nonsingular x_Q y_Q) (h_2_tor_Q : y_Q = W.toAffine.negY x_Q y_Q)
    (hsmul' : ℓ • P.toAffinePoint = Affine.Point.some x_Q y_Q h_ns') :
    (mulByInt W.toAffine (2 * ℓ)).toAddMonoidHom P.toAffinePoint = (0 : W.toAffine.Point) := by
  have hQ2_O : (2 : ℤ) • (Affine.Point.some x_Q y_Q h_ns') = 0 := by
    have hQneg : Affine.Point.some x_Q y_Q h_ns' = -(Affine.Point.some x_Q y_Q h_ns') := by
      rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, h_2_tor_Q⟩
    rw [two_zsmul]; nth_rewrite 1 [hQneg]; rw [neg_add_cancel]
  rw [mulByInt_apply, mul_zsmul, hsmul', hQ2_O]

/-- **The pulled-back `2`-division polynomial `[ℓ]^*Ψ₂` is a uniformizer at `P`** in char `≠ 2`
(`ord_P (2·mulByInt_y ℓ + a₁·mulByInt_x ℓ + a₃) = 1`). The duplication formula
`Ψ₂ ∘ [ℓ] = ψ_{2ℓ}/ψ_ℓ⁴` (`mulByInt_y_sub_negY`) gives
`ord_P ([ℓ]^*Ψ₂) = ord_P (ψ_ff (2ℓ)) − 4·ord_P (ψ_ff ℓ) = 1 − 0`, the numerator order `1` being the
`[2ℓ]`-torsion pole computation `ord_P_ψ_ff_two_mul_eq_one` (valid as `(2ℓ : F) ≠ 0`). -/
private theorem ord_P_psiTwo_pullback_eq_one (ℓ : ℤ) (hℓ : ℓ ≠ 0) (h2ℓF : (2 * ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ2P : (mulByInt W.toAffine (2 * ℓ)).toAddMonoidHom P.toAffinePoint = (0 : W.toAffine.Point))
    (hψℓ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ψ_ff W ℓ) = 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        ((2 : KE) * mulByInt_y W ℓ + algebraMap F KE W.a₁ * mulByInt_x W ℓ +
          algebraMap F KE W.a₃) = ((1 : ℤ) : WithTop ℤ) := by
  have hψℓ_ne : ψ_ff W ℓ ≠ 0 := ψ_ff_ne_zero W hℓ
  have hψ2ℓ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ψ_ff W (2 * ℓ)) = ((1 : ℤ) : WithTop ℤ) :=
    ord_P_ψ_ff_two_mul_eq_one W hℓ h2ℓF P hQ2P
  have hdup := mulByInt_y_sub_negY W ℓ hℓ
  have hnegY : (W_KE W).toAffine.negY (mulByInt_x W ℓ) (mulByInt_y W ℓ) =
      -mulByInt_y W ℓ - algebraMap F KE W.a₁ * mulByInt_x W ℓ - algebraMap F KE W.a₃ := rfl
  have hAprime : (2 : KE) * mulByInt_y W ℓ + algebraMap F KE W.a₁ * mulByInt_x W ℓ +
      algebraMap F KE W.a₃ = ψ_ff W (2 * ℓ) / ψ_ff W ℓ ^ 4 := by
    rw [← hdup, hnegY]; ring
  rw [hAprime, div_eq_mul_inv, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ (pow_ne_zero 4 hψℓ_ne),
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_pow, hψℓ_ord, hψ2ℓ_ord]; simp

/-- **The `y`-variant `e = 1` unramifiedness of `[ℓ]` (2-torsion image).** For `[ℓ]` separable
(`(ℓ : F) ≠ 0`) and a smooth point `P` of `⟨W⟩` whose image `[ℓ]·P = (x_Q, y_Q)` is an affine
*2-torsion* point (`y_Q = negY x_Q y_Q`), the pullback `[ℓ]^*(y_gen − y_Q) = mulByInt_y ℓ − y_Q`
of the uniformizer `y_gen − y_Q` at `Q` is a uniformizer at `P`:
`ord_P P (mulByInt_y ℓ − algebraMap F KE y_Q) = 1`.

This is the `y`-analogue of `ord_P_mulByInt_x_sub_const_eq_one`, the `e = 1` input the
order-transport glue consumes at a 2-torsion image. Geometrically it is the unramifiedness of `[ℓ]`
(Silverman III.4.10c) at the fibre over a 2-torsion point: `mulByInt_y ℓ = ω_ℓ/ψ_ℓ³`, the
denominator `ψ_ℓ³` a unit at `P` (`ψ_ℓ(P) ≠ 0`, the image being affine), and the numerator
`ω_ℓ − y_Q·ψ_ℓ³` a *simple* zero at `P`.

**Proof (char `≠ 2` complete; char `2` isolated).** The skeleton is char-uniform and uses no
algebraic closure and no `Valuation.IsEquiv`. From the pulled-back Weierstrass equation alone (with
`Q` on the curve and 2-torsion, `polynomialX(Q) ≠ 0` at the smooth 2-torsion point) one gets the
**ratio relation** `ord_P (mulByInt_x − x_Q) = 2 · ord_P (mulByInt_y − y_Q)`: writing
`(mulByInt_y − y_Q)·A = (mulByInt_x − x_Q)·B` with `B` a unit at `P` and
`A = (mulByInt_y − y_Q) + a₁(mulByInt_x − x_Q)` (using `2y_Q + a₁x_Q + a₃ = 0`), and noting `A`
vanishes at `P`, forces the `(mulByInt_y − y_Q)` summand of `A` to dominate, hence
`M := ord_P(mulByInt_x − x_Q) = 2·n` with `n := ord_P(mulByInt_y − y_Q) ≥ 1`. It remains to pin
`n = 1`.

* **char `≠ 2`:** the duplication formula `Ψ₂ ∘ [ℓ] = ψ_{2ℓ}/ψ_ℓ⁴` (`mulByInt_y_sub_negY`) gives
  `ord_P ([ℓ]^*Ψ₂) = ord_P (ψ_ff (2ℓ)) − 4·ord_P (ψ_ff ℓ) = 1 − 0 = 1`, where
  `ord_P (ψ_ff (2ℓ)) = 1` (`ord_P_ψ_ff_two_mul_eq_one`) is the `[2ℓ]` torsion-pole
  `ord_P (mulByInt_x (2ℓ)) = -2` plus coprimality `Φ_{2ℓ}(P.x) ≠ 0`, valid as `(2ℓ : F) ≠ 0`. Since
  `[ℓ]^*Ψ₂ = 2(mulByInt_y − y_Q) + a₁(mulByInt_x − x_Q)` has the `2(mulByInt_y − y_Q)` term (order
  `n`) strictly dominating the `a₁(mulByInt_x − x_Q)` term (order `2n > n`), its order is `n`, so
  `n = 1`.
* **char `2` (isolated, single residual):** both legs collapse — `Ψ₂ = a₁X + a₃` loses the `2Y`
  term and `[2ℓ]` is inseparable (`(2ℓ : F) = 0`). The honest witness is the invariant differential
  `[ℓ]^*ω = ℓ·ω` (`omegaCoeff_mulByInt`); formalising it needs an `ord_P` theory on Kähler
  differentials not yet in the repo. Isolated as a single sharp leaf.

Everything else in the `[ℓ]`-divisor-pullback functoriality — the affine non-2-torsion case, the
infinity case, and this affine 2-torsion case in every characteristic `≠ 2` — is axiom-clean. -/
theorem ord_P_mulByInt_y_sub_const_eq_one (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x_Q y_Q : F}
    (h_ns' : W.toAffine.Nonsingular x_Q y_Q) (h_2_tor_Q : y_Q = W.toAffine.negY x_Q y_Q)
    (hQ : (mulByInt W.toAffine ℓ).toAddMonoidHom P.toAffinePoint =
      Affine.Point.some x_Q y_Q h_ns') :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_y W ℓ - algebraMap F KE y_Q) =
      ((1 : ℤ) : WithTop ℤ) := by
  classical
  have hsmul : ℓ • (Affine.Point.some P.x P.y P.nonsingular) =
      Affine.Point.some x_Q y_Q h_ns' := by
    rw [mulByInt_apply] at hQ
    rw [← SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]; exact hQ
  have hsmul' : ℓ • P.toAffinePoint = Affine.Point.some x_Q y_Q h_ns' := by
    rw [SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]; exact hsmul
  set X := mulByInt_x W ℓ with hX
  set Y := mulByInt_y W ℓ with hY
  set xq := algebraMap F KE x_Q with hxq
  set yq := algebraMap F KE y_Q with hyq
  have h2KE : algebraMap F KE 2 = (2 : KE) := map_ofNat (algebraMap F KE) 2
  have h2tor : 2 * y_Q + W.a₁ * x_Q + W.a₃ = 0 := by
    have hneg : W.toAffine.negY x_Q y_Q = -y_Q - W.a₁ * x_Q - W.a₃ := rfl
    rw [hneg] at h_2_tor_Q; linear_combination h_2_tor_Q
  have h2torKE : (2 : KE) * yq + algebraMap F KE W.a₁ * xq + algebraMap F KE W.a₃ = 0 := by
    rw [hxq, hyq, ← h2KE, ← map_mul, ← map_mul, ← map_add, ← map_add, h2tor, map_zero]
  have hXpb : (mulByInt W.toAffine ℓ).pullback (x_gen W) = X := mulByInt_pullback_x W ℓ hℓ
  have hYpb : (mulByInt W.toAffine ℓ).pullback (y_gen W) = Y := mulByInt_pullback_y W ℓ hℓ
  have hWeq : Y ^ 2 + algebraMap F KE W.a₁ * X * Y + algebraMap F KE W.a₃ * Y =
      X ^ 3 + algebraMap F KE W.a₂ * X ^ 2 + algebraMap F KE W.a₄ * X + algebraMap F KE W.a₆ := by
    have h_alg := pullback_equation W (mulByInt W.toAffine ℓ)
    rw [hXpb, hYpb, WeierstrassCurve.Affine.equation_iff] at h_alg
    exact h_alg
  have hQeq : (W_KE W).toAffine.Equation xq yq :=
    translate_constant_equation W x_Q y_Q h_ns'.1
  have hQeq' : yq ^ 2 + algebraMap F KE W.a₁ * xq * yq + algebraMap F KE W.a₃ * yq =
      xq ^ 3 + algebraMap F KE W.a₂ * xq ^ 2 + algebraMap F KE W.a₄ * xq +
        algebraMap F KE W.a₆ := by
    have hh := (WeierstrassCurve.Affine.equation_iff _ _).mp hQeq
    simpa only [show (W_KE W).a₁ = algebraMap F KE W.a₁ from rfl,
      show (W_KE W).a₂ = algebraMap F KE W.a₂ from rfl,
      show (W_KE W).a₃ = algebraMap F KE W.a₃ from rfl,
      show (W_KE W).a₄ = algebraMap F KE W.a₄ from rfl,
      show (W_KE W).a₆ = algebraMap F KE W.a₆ from rfl] using hh
  set A : KE := Y + yq + algebraMap F KE W.a₁ * X + algebraMap F KE W.a₃ with hA
  set Bma : KE := X ^ 2 + X * xq + xq ^ 2 +
      algebraMap F KE W.a₂ * (X + xq) + algebraMap F KE W.a₄ -
      algebraMap F KE W.a₁ * yq with hBma
  have h_id : (Y - yq) * A = (X - xq) * Bma := by
    rw [hA, hBma]; linear_combination hWeq - hQeq'
  have hA_eq : A = (Y - yq) + algebraMap F KE W.a₁ * (X - xq) := by
    rw [hA]; linear_combination h2torKE
  have hX_sub_ne : X - xq ≠ 0 := by
    have heq : X - xq = (mulByInt W.toAffine ℓ).pullback (x_gen W - algebraMap F KE x_Q) := by
      rw [map_sub, hXpb, (mulByInt W.toAffine ℓ).pullback.commutes]
    rw [heq]
    exact fun h ↦ x_gen_sub_const_ne_zero W x_Q
      ((mulByInt W.toAffine ℓ).pullback.injective (h.trans (map_zero _).symm))
  have hygen_ne : y_gen W - algebraMap F KE y_Q ≠ 0 := by
    rw [y_gen_sub_const_eq_algebraMap_YClass]
    exact (map_ne_zero_iff _ (IsFractionRing.injective W.toAffine.CoordinateRing KE)).mpr
      (Affine.CoordinateRing.YClass_ne_zero (Polynomial.C y_Q))
  have hY_sub_ne : Y - yq ≠ 0 := by
    have heq : Y - yq = (mulByInt W.toAffine ℓ).pullback (y_gen W - algebraMap F KE y_Q) := by
      rw [map_sub, hYpb, (mulByInt W.toAffine ℓ).pullback.commutes]
    rw [heq]
    exact fun h ↦ hygen_ne
      ((mulByInt W.toAffine ℓ).pullback.injective (h.trans (map_zero _).symm))
  obtain ⟨hψ_ne, hxQ_eq, hyQ_eq⟩ :=
    smulEval_facts_of_zsmul_eq_some W P.nonsingular h_ns' ℓ hℓ hsmul
  have hΨSqℓ_ne : ΨSq_ff W ℓ ≠ 0 := ΨSq_ff_ne_zero W hℓ
  have hψℓ_ne : ψ_ff W ℓ ≠ 0 := ψ_ff_ne_zero W hℓ
  have hΨSqℓ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ΨSq_ff W ℓ) = 0 :=
    ord_P_ΨSq_ff_eq_zero W P.nonsingular h_ns' hℓ hsmul P rfl
  have hψℓ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (ψ_ff W ℓ) = 0 :=
    ord_P_ψ_ff_eq_zero W P.nonsingular h_ns' hℓ hsmul P rfl rfl
  have h_one_le_X : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (X - xq) := by
    rw [hX, hxq, mulByInt_x_sub_const_eq_div W hℓ, div_eq_mul_inv,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hΨSqℓ_ne, hΨSqℓ_ord, neg_zero, add_zero]
    refine one_le_ord_P_algebraMap_poly_of_root W P (fibrePoly_monic W hℓ x_Q).ne_zero ?_
    exact fibrePoly_isRoot_of_zsmul_eq_some W P.nonsingular h_ns' hℓ hsmul
  have h_one_le_Y : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Y - yq) :=
    one_le_ord_P_mulByInt_y_sub_const W P hψ_ne hyQ_eq hψℓ_ord hY_sub_ne
  have hX_reg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P X := by
    rw [hX, mulByInt_x, div_eq_mul_inv, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hΨSqℓ_ne, hΨSqℓ_ord,
      neg_zero, add_zero, Φ_ff_eq_algebraMap]
    rcases eq_or_ne ((W.Φ ℓ).eval P.x) 0 with hΦ0 | hΦ0
    · exact le_trans (by norm_num) (one_le_ord_P_algebraMap_poly_of_root W P (W.Φ_ne_zero ℓ) hΦ0)
    · rw [ord_P_algebraMap_poly_eq_zero_of_eval_ne W P (W.Φ_ne_zero ℓ) hΦ0]
  have hCconst : (3 * x_Q ^ 2 + 2 * W.a₂ * x_Q + W.a₄ - W.a₁ * y_Q : F) ≠ 0 := by
    have h_polX : W.toAffine.polynomialX.evalEval x_Q y_Q ≠ 0 :=
      polynomialX_evalEval_ne_zero_at_2tor W x_Q y_Q h_ns' h_2_tor_Q
    rw [WeierstrassCurve.Affine.evalEval_polynomialX] at h_polX
    intro h; exact h_polX (by linear_combination -h)
  have hBma_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P Bma = 0 := by
    rw [hBma]; exact ord_P_y_cofactor_eq_zero W P hCconst hX_reg h_one_le_X
  obtain ⟨n, hn⟩ := exists_intCast_ord_P W P hY_sub_ne
  obtain ⟨M, hM⟩ := exists_intCast_ord_P W P hX_sub_ne
  have hn1 : (1 : ℤ) ≤ n := by rw [hn] at h_one_le_Y; exact_mod_cast h_one_le_Y
  have hM1 : (1 : ℤ) ≤ M := by rw [hM] at h_one_le_X; exact_mod_cast h_one_le_X
  have hBma_ne : Bma ≠ 0 := by
    intro h; rw [h, (⟨W⟩ : SmoothPlaneCurve F).ord_P_zero] at hBma_ord
    exact (by simp : (⊤ : WithTop ℤ) ≠ 0) hBma_ord
  have hA_ne : A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h_id
    exact (mul_ne_zero hX_sub_ne hBma_ne) h_id.symm
  obtain ⟨a, ha⟩ := exists_intCast_ord_P W P hA_ne
  have h_one_le_A : (1 : ℤ) ≤ a := by
    have hge : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P A := by
      rw [hA_eq]
      have ha1X : ((1 : ℤ) : WithTop ℤ) ≤
          (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap F KE W.a₁ * (X - xq)) := by
        by_cases ha1 : W.a₁ = 0
        · rw [ha1, map_zero, zero_mul, (⟨W⟩ : SmoothPlaneCurve F).ord_P_zero]; exact le_top
        · rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
            (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero ha1, zero_add]
          exact h_one_le_X
      exact le_trans (le_min h_one_le_Y ha1X) (SmoothPlaneCurve.ord_P_add_le (P := P) _ _)
    rw [ha] at hge; exact_mod_cast hge
  have h_orders : (n : ℤ) + a = M := by
    have hh := congrArg ((⟨W⟩ : SmoothPlaneCurve F).ord_P P) h_id
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, hn, ha, hM,
      hBma_ord, add_zero] at hh
    exact_mod_cast hh
  have hM_gt_n : (n : ℤ) < M := by omega
  have ha_eq_n : a = n := by
    by_cases ha1 : W.a₁ = 0
    · have hAeq2 : (⟨W⟩ : SmoothPlaneCurve F).ord_P P A =
          (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Y - yq) := by
        rw [hA_eq, ha1, map_zero, zero_mul, add_zero]
      rw [ha, hn] at hAeq2; exact_mod_cast hAeq2
    · have hterm2 : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap F KE W.a₁ * (X - xq)) =
          ((M : ℤ) : WithTop ℤ) := by
        rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
          (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero ha1, zero_add, hM]
      have hlt : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Y - yq) <
          (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap F KE W.a₁ * (X - xq)) := by
        rw [hn, hterm2]; exact_mod_cast hM_gt_n
      have hAeq2 : (⟨W⟩ : SmoothPlaneCurve F).ord_P P A =
          (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Y - yq) := by
        rw [hA_eq]; exact SmoothPlaneCurve.ord_P_add_eq_of_lt hlt
      rw [ha, hn] at hAeq2; exact_mod_cast hAeq2
  have hM_eq : M = 2 * n := by omega
  have hQ2P : (mulByInt W.toAffine (2 * ℓ)).toAddMonoidHom P.toAffinePoint =
      (0 : W.toAffine.Point) :=
    mulByInt_two_mul_eq_zero_of_image_2_tor W ℓ P h_ns' h_2_tor_Q hsmul'
  suffices hgoal : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Y - yq) = ((1 : ℤ) : WithTop ℤ) by
    exact hgoal
  rw [hn]
  congr 1
  rcases eq_or_ne (2 * ℓ : F) 0 with _h2 | h2
  · -- In char 2 the duplication route degenerates (`Ψ₂ = a₁X + a₃`, `[2ℓ]` inseparable), so the
    -- witness is the differential bound `ord_P_mulByInt_y_sub_const_le_one`, valid in every char.
    have hPX_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        (3 * X ^ 2 + 2 * algebraMap F KE W.a₂ * X + algebraMap F KE W.a₄ -
          algebraMap F KE W.a₁ * Y) = 0 :=
      ord_P_y_numerator_eq_zero W P hCconst hX_reg h_one_le_X h_one_le_Y
    have hle : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Y - yq) ≤ ((1 : ℤ) : WithTop ℤ) := by
      rw [hY, hyq]
      exact ord_P_mulByInt_y_sub_const_le_one W ℓ hℓ hℓF P y_Q
        (by rw [← hyq, ← hY]; exact hY_sub_ne) (by rw [← hX, ← hY]; exact hPX_ord)
    rw [hn] at hle
    have hn_le : n ≤ 1 := by exact_mod_cast hle
    have hn_ge : (1 : ℤ) ≤ n := by rw [hn] at h_one_le_Y; exact_mod_cast h_one_le_Y
    omega
  · have hAprime_ord :
        (⟨W⟩ : SmoothPlaneCurve F).ord_P P
          ((2 : KE) * Y + algebraMap F KE W.a₁ * X + algebraMap F KE W.a₃) =
        ((1 : ℤ) : WithTop ℤ) :=
      ord_P_psiTwo_pullback_eq_one W ℓ hℓ h2 P hQ2P hψℓ_ord
    have hAprime_eq : (2 : KE) * Y + algebraMap F KE W.a₁ * X + algebraMap F KE W.a₃ =
        2 * (Y - yq) + algebraMap F KE W.a₁ * (X - xq) := by
      linear_combination h2torKE
    have h2F : (2 : F) ≠ 0 := by
      intro h; apply h2
      rw [show (2 * ℓ : F) = 2 * (ℓ : F) from by ring, h, zero_mul]
    have hterm1_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (2 * (Y - yq)) =
        ((n : ℤ) : WithTop ℤ) := by
      rw [← h2KE, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
        (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero h2F, zero_add, hn]
    rw [hAprime_eq] at hAprime_ord
    by_cases ha1 : W.a₁ = 0
    · rw [ha1, map_zero, zero_mul, add_zero, hterm1_ord] at hAprime_ord
      exact_mod_cast hAprime_ord
    · have hterm2 : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap F KE W.a₁ * (X - xq)) =
          ((M : ℤ) : WithTop ℤ) := by
        rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
          (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero ha1, zero_add, hM]
      have hlt : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (2 * (Y - yq)) <
          (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap F KE W.a₁ * (X - xq)) := by
        rw [hterm1_ord, hterm2]; exact_mod_cast (by omega : (n : ℤ) < M)
      rw [SmoothPlaneCurve.ord_P_add_eq_of_lt hlt, hterm1_ord] at hAprime_ord
      exact_mod_cast hAprime_ord

end HasseWeil
