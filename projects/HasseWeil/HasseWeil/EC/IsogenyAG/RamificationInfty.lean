/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG
import HasseWeil.Curves.OrdAtInftyRamification

/-!
# The ramification-pullback formula at infinity, for isogenies (Silverman II.2.6)

This file specialises the abstract valuation-pullback law
`Curves.SmoothPlaneCurve.exists_ramificationIdx_ordAtInfty_ringHom` to an
`EC.Isogeny φ : E₁ → E₂`, using that the basepoint condition

  `pullback_ordAtInfty_nonneg : ord_∞ f ≥ 0 ⟹ ord_∞ (φ* f) ≥ 0`

is carried as a structure field of `EC.Isogeny` (the morphism is *defined at* `O₁`
and sends it to `O₂`).  This is exactly the geometric hypothesis `hreg` the
abstract law needs, so we obtain, axiom-clean, the **ramification index at the
basepoint** and the pullback formula:

  `ord_∞^{E₁}(φ* g) = e_φ(O) · ord_∞^{E₂}(g)`   (for `g ≠ 0`),

with `e_φ(O) = (ord_∞(φ* (x/y))).toNat` produced explicitly.  This discharges the
`hramO` residual carried by the dual-isogeny construction
(`EC.reflects_ordAtInfty_of_ramificationIdx`, file `Dual.lean`).

The positivity `e_φ(O) ≥ 1` (non-triviality of the place above `O`) is also a
**theorem** here, with no extra hypotheses: `F(E₁)` is algebraic over `φ* F(E₂)`
(CoordHom-free, by the transcendence-degree argument
`CurveMap.isAlgebraic_toAlgebra`), and a discrete valuation vanishing on a
subfield vanishes on everything algebraic over it
(`ordAtInfty_eq_zero_of_isAlgebraic`) — which `ord_∞ x = -2` forbids.  Hence
`reflects_ordAtInfty` below is *unconditional*: the former `hnt` hypothesis is
discharged (`pos_ordAtInfty_pullback_uniformizer`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2 (ramification index),
  II.2.6 (`Σ e = deg`), III.4.10a (`e = deg_i`, separable ⟹ `e = 1`), IV.1.
-/

open WeierstrassCurve

namespace HasseWeil.EC.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The ramification index at infinity of an isogeny, with the pullback formula**
(Silverman II.2.6, RAMI-1 formula leaf).  For an isogeny `φ : E₁ → E₂` there is a
natural number `e = e_φ(O)` such that for every nonzero `g ∈ F(E₂)`,

  `ord_∞^{E₁}(φ* g) = e · ord_∞^{E₂}(g)`.

The index is `e = (ord_∞(φ* (x/y))).toNat`, the order of the pullback of the
uniformizer `x/y` at `O`.  This is the genuine geometric content previously
carried as the hypothesis `hramO` of `reflects_ordAtInfty_of_ramificationIdx`:
here it is a *theorem*, derived from the basepoint condition
`pullback_ordAtInfty_nonneg` (a structure field of `EC.Isogeny`) via the abstract
valuation-pullback law `exists_ramificationIdx_ordAtInfty_ringHom`. -/
theorem exists_ramificationIdx_at_infinity (φ : Isogeny W₁ W₂) :
    ∃ e : ℕ, ∀ g : (⟨W₂⟩ : Curves.SmoothPlaneCurve F).FunctionField, g ≠ 0 →
      (⟨W₁⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) =
        e • (⟨W₂⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g :=
  Curves.SmoothPlaneCurve.exists_ramificationIdx_ordAtInfty_ringHom
    (φ.toCurveMap.pullback.toRingHom) φ.pullback_ordAtInfty_nonneg

/-- **Non-triviality of the place at infinity over `O₂`** (the former `hnt`
hypothesis, now a theorem): the pullback of an isogeny sends the
`∞`-uniformizer `x/y` to a function *vanishing at `O₁`*.  Unconditional: the
algebraicity of `F(E₁)` over `φ* F(E₂)` is CoordHom-free
(`CurveMap.isAlgebraic_toAlgebra`, transcendence-degree argument), and the
basepoint condition `pullback_ordAtInfty_nonneg` provides regularity
preservation. -/
theorem pos_ordAtInfty_pullback_uniformizer (φ : Isogeny W₁ W₂) :
    0 < (⟨W₁⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
      (φ.toCurveMap.pullback
        ((⟨W₂⟩ : Curves.SmoothPlaneCurve F).coordX /
          (⟨W₂⟩ : Curves.SmoothPlaneCurve F).coordY)) :=
  φ.toCurveMap.pos_ordAtInfty_pullback_coordX_div_coordY
    φ.pullback_ordAtInfty_nonneg

/-- **The ramification index at infinity is `≥ 1`, with the pullback formula**
(Silverman II.2.6 at `P = O`, with positivity): for any isogeny `φ : E₁ → E₂`,

  `∃ e ≥ 1, ∀ g ≠ 0, ord_∞(φ* g) = e · ord_∞(g)`.

Fully unconditional: the former non-triviality hypothesis `hnt` is discharged by
`pos_ordAtInfty_pullback_uniformizer`. -/
theorem exists_pos_ramificationIdx_at_infinity (φ : Isogeny W₁ W₂) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ g : (⟨W₂⟩ : Curves.SmoothPlaneCurve F).FunctionField, g ≠ 0 →
      (⟨W₁⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) =
        e • (⟨W₂⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g :=
  Curves.SmoothPlaneCurve.exists_pos_ramificationIdx_ordAtInfty_ringHom
    (φ.toCurveMap.pullback.toRingHom) φ.pullback_ordAtInfty_nonneg
    (pos_ordAtInfty_pullback_uniformizer φ)

/-! ### `∞`-regularity reflection (the `hrefl`/`hramO` residual of `Dual.lean`) -/

/-- The coercion `ℤ → WithTop ℤ` commutes with `nsmul`. -/
private theorem withTop_coe_nsmul' (e : ℕ) (k : ℤ) :
    (e • ((k : ℤ) : WithTop ℤ)) = (((e • k : ℤ)) : WithTop ℤ) := by
  induction e with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih, ← WithTop.coe_add]

/-- `0 ≤ e • x → 0 ≤ x` in `WithTop ℤ` for `e ≥ 1` (order-reflection of `nsmul`).
A self-contained copy of the same mechanism used in `Dual.lean`. -/
private theorem nonneg_of_nsmul_nonneg' {e : ℕ} (he : 1 ≤ e) {x : WithTop ℤ}
    (h : 0 ≤ e • x) : 0 ≤ x := by
  induction x with
  | top => exact le_top
  | coe k =>
    rw [withTop_coe_nsmul', ← WithTop.coe_zero, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [← WithTop.coe_zero, WithTop.coe_le_coe]
    have hepos : (0 : ℤ) < e := by exact_mod_cast he
    exact (mul_nonneg_iff_of_pos_left hepos).mp h

/-- **`∞`-regularity reflection from an isogeny — unconditional** (Silverman
III.4.10a, the `hrefl`/`hramO` residual of the dual-isogeny construction,
discharged for *every* isogeny).  From the ramification formula
`ord_∞(φ* g) = e_φ(O)·ord_∞ g` with `e_φ(O) ≥ 1` (both now theorems, via
`exists_pos_ramificationIdx_at_infinity`), a regular pullback forces a regular
function:

  `0 ≤ ord_∞(φ* g) ⟹ 0 ≤ ord_∞ g`.

This is exactly the `hrefl` field of `DualGaloisData` / `HasDualWitness`, with
both the ramification formula `hramO` *and* the non-triviality `hnt`
internalised: no hypotheses remain. -/
theorem reflects_ordAtInfty (φ : Isogeny W₁ W₂)
    (g : (⟨W₂⟩ : Curves.SmoothPlaneCurve F).FunctionField)
    (h : 0 ≤ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g)) :
    0 ≤ (⟨W₂⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · obtain ⟨e, he, hformula⟩ := exists_pos_ramificationIdx_at_infinity φ
    apply nonneg_of_nsmul_nonneg' he
    rwa [← hformula g hg]

end HasseWeil.EC.Isogeny
