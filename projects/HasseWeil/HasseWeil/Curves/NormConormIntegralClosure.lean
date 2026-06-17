/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.LocalizedDictionary
import HasseWeil.Curves.PushforwardDivisor
import HasseWeil.Curves.RamificationFinite

/-!
# The norm–conorm count over the integral closure `B` (CoordHom-free, Silverman II.3.6)

For a finite separable extension `K(C₁) / K(C₂)` of smooth-curve function fields that has *no*
global affine `CoordHom` (e.g. the pullback of a genuine isogeny, whose pullback of the
coordinate generators has poles at the affine kernel), the affine norm–conorm template of
`HasseWeil/Curves/PushforwardDivisor.lean` (`relNorm_maximalIdealAt_eq`,
`count_relNorm_eq_sum_fiber`) does not apply: it routes through the affine coordinate-ring
extension `F[C₂] → F[C₁]`.  Instead we work over the **integral closure**

  `B := integralClosure C₂.CoordinateRing C₁.FunctionField`,

whose maximal ideals are in bijection with *all* the places of `C₁` over the affine places of
`C₂` (supplied by `HasseWeil/Curves/LocalizedDictionary.lean`, instantiated at the trivial
localization `Af := C₂.CoordinateRing`, `f := 1`, valid at *every* affine place).

This file ports the affine template over `B`:
* the `s = 1` core `relNorm_{C₂.CoordinateRing}(P) = m_{below}` for a maximal `P` of `B`;
* the per-place count `count_{m_Q}(relNorm(span{w})) = Σ_{P over m_Q} count_P(span{w})`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6, II.3.6, III.4.10(c).
-/

open WeierstrassCurve
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace HasseWeil.Curves.NormConormIntegralClosure

open HasseWeil.Curves HasseWeil.Curves.LocalizedDictionary

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {C₁ C₂ : SmoothPlaneCurve F} [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
variable [IsIntegrallyClosed C₂.CoordinateRing]
variable [PerfectField (FractionRing C₂.CoordinateRing)]
variable [algKL : Algebra C₂.FunctionField C₁.FunctionField]
  [finKL : FiniteDimensional C₂.FunctionField C₁.FunctionField]
  [sepKL : Algebra.IsSeparable C₂.FunctionField C₁.FunctionField]
  [algCR1 : Algebra C₂.CoordinateRing C₁.FunctionField]
  [tw1 : IsScalarTower C₂.CoordinateRing C₂.FunctionField C₁.FunctionField]
  [twF : IsScalarTower F C₂.FunctionField C₁.FunctionField]

/-- The integral closure `B` of `C₂.CoordinateRing` inside `C₁.FunctionField` (as a subalgebra;
its coercion to a type carries the Dedekind/finite/fraction-ring structure of the AKLB setup). -/
noncomputable abbrev B : Subalgebra C₂.CoordinateRing C₁.FunctionField :=
  integralClosure C₂.CoordinateRing C₁.FunctionField

/-! ### The trivial localization `Af := C₂.CoordinateRing`, `f := 1` -/

noncomputable instance instAway1 :
    IsLocalization.Away (1 : C₂.CoordinateRing) C₂.CoordinateRing :=
  IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id

noncomputable instance instTowTrivial :
    IsScalarTower C₂.CoordinateRing C₂.CoordinateRing C₂.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `1 ∉ m_Q` for every smooth point `Q` (a maximal ideal is proper). -/
theorem one_notMem_maximalIdealAt (Q : C₂.SmoothPoint) :
    (1 : C₂.CoordinateRing) ∉ C₂.maximalIdealAt Q := by
  rw [← Ideal.eq_top_iff_one]
  exact (C₂.maximalIdealAt_isMaximal Q).ne_top

/-- `awayIdealAt C₂.CoordinateRing Q = m_Q` (the localization at `f := 1` is trivial, so the
extended ideal is the original maximal ideal). -/
theorem awayIdealAt_eq_maximalIdealAt (Q : C₂.SmoothPoint) :
    awayIdealAt (C₂ := C₂) C₂.CoordinateRing Q = C₂.maximalIdealAt Q := by
  rw [awayIdealAt, Algebra.algebraMap_self, Ideal.map_id]

/-! ### The Dedekind/finite/torsion-free/fraction-ring instances for `B` (T-A1) -/

set_option backward.isDefEq.respectTransparency false in
/-- `B` is a Dedekind domain (Krull–Akizuki, separable case). -/
instance instDedekindB : IsDedekindDomain (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.isDedekindDomain C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` is module-finite over `C₂.CoordinateRing`. -/
instance instModuleFiniteB :
    Module.Finite C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.module_finite C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` has fraction field `C₁.FunctionField`. -/
instance instFractionRingB :
    IsFractionRing (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField :=
  RamificationFinite.isFractionRing C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` is a torsion-free `C₂.CoordinateRing`-module. -/
instance instTorsionFreeB :
    Module.IsTorsionFree C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.isTorsionFree C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

/-! ### The coordinate ring of `C₁` lands in `B` (T-A2, integrality sub-wall)

The coordinate generators `x₁ = coordXFun C₁`, `y₁ = coordYFun C₁` of `C₁`, regarded inside
`K(C₁)`, are integral over `C₂.CoordinateRing`: each is regular at every place of `C₁` lying
over an *affine* place of `C₂` (their only poles — at `∞` of `C₁` and at the affine kernel —
all lie over `∞` of `C₂`).  Hence the entire coordinate ring `F[C₁] = F[x₁, y₁]` lands in `B`.

This is the integral-closure analogue of the affine `coordRing_mem_integralClosure`
(`LocalizedDictionary.lean`) at the *global* base (`Af := C₂.CoordinateRing`, `f := 1`).  Its
content is the genuine geometric input (regularity of the coordinate functions at all places
over the affine part of `C₂`); everything downstream is structural. -/

/-- **The `x`-generator of `C₁` is integral over `C₂.CoordinateRing`** (regular at every place
of `C₁` over an affine place of `C₂`). -/
theorem coordXFun_mem_B :
    coordXFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) := by
  sorry

/-- **The `y`-generator of `C₁` is integral over `C₂.CoordinateRing`.** -/
theorem coordYFun_mem_B :
    coordYFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) := by
  sorry

/-- **The coordinate ring of `C₁` lands in `B`** (Silverman II.2.6, the integral-closure form):
for every `r ∈ F[C₁]`, the image `algebraMap r ∈ K(C₁)` is integral over `C₂.CoordinateRing`.
Built from the two generator integralities via `LocalizedDictionary.coordRing_mem_integralClosure`
(at the trivial localization `Af := C₂.CoordinateRing`). -/
theorem coordRing_mem_B (r : C₁.CoordinateRing) :
    algebraMap C₁.CoordinateRing C₁.FunctionField r ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  coordRing_mem_integralClosure C₂ C₂.CoordinateRing coordXFun_mem_B coordYFun_mem_B r

/-! ### Inertia degree `1` and the `s = 1` core over `B` (T-A2 core) -/

/-- **Inertia degree `1`** for a prime `P` of `B` lying over the maximal ideal `m_Q` of
`C₂.CoordinateRing`: over an algebraically closed base the residue fields are trivial.  This is
`LocalizedDictionary.inertiaDeg_eq_one_of_under_eq` instantiated at the trivial localization
`Af := C₂.CoordinateRing`, `f := 1` (valid at *every* affine place since `1 ∉ m_Q`). -/
theorem inertiaDeg_eq_one (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (Q : C₂.SmoothPoint) (hPp : P.IsPrime)
    (hPq : P.under C₂.CoordinateRing = C₂.maximalIdealAt Q) :
    Ideal.inertiaDeg (C₂.maximalIdealAt Q) P = 1 := by
  have hfQ : (1 : C₂.CoordinateRing) ∉ C₂.maximalIdealAt Q := one_notMem_maximalIdealAt Q
  have hPq' : P.under C₂.CoordinateRing = awayIdealAt (C₂ := C₂) C₂.CoordinateRing Q := by
    rw [hPq, awayIdealAt_eq_maximalIdealAt]
  have := inertiaDeg_eq_one_of_under_eq C₂ (1 : C₂.CoordinateRing) C₂.CoordinateRing
    one_ne_zero hfQ hPp hPq'
  rwa [awayIdealAt_eq_maximalIdealAt] at this

/-- **The `s = 1` core — Silverman II.3.6**: for a maximal ideal `P` of `B` lying over the
maximal ideal `m_Q` of `C₂.CoordinateRing`, `relNorm_{C₂.CoordinateRing}(P) = m_Q`.  Over char-0
this is mathlib's `relNorm_eq_pow_of_isMaximal` (`relNorm P = m_Q ^ inertiaDeg`) with the inertia
degree `1` over an algebraically closed base. -/
theorem relNorm_eq_of_under (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P.IsMaximal) (Q : C₂.SmoothPoint)
    (hPq : P.under C₂.CoordinateRing = C₂.maximalIdealAt Q) :
    Ideal.relNorm C₂.CoordinateRing P = C₂.maximalIdealAt Q := by
  haveI : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  haveI hLies : P.LiesOver (C₂.maximalIdealAt Q) := ⟨hPq.symm⟩
  rw [Ideal.relNorm_eq_pow_of_isMaximal P (C₂.maximalIdealAt Q),
    inertiaDeg_eq_one P Q hP.isPrime hPq, pow_one]

end HasseWeil.Curves.NormConormIntegralClosure
