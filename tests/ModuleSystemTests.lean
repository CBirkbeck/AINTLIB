module

import HasseWeil.HasseBound
import BernoulliRegular.BernoulliFast.Tactic

/-! Regression checks for importing AINTLIB from a module-system client. -/

/-- info: 'HasseWeil.WeilPairing.hasse_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasseWeil.WeilPairing.hasse_bound

/-- info: 'HasseWeil.WeilPairing.hasse_bound_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasseWeil.WeilPairing.hasse_bound_unconditional

example {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] :
    |(↑(HasseWeil.pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  HasseWeil.WeilPairing.hasse_bound W

example : BernoulliRegular.BernoulliFast.Cbv.bernoulliPascalFrac 18 = (43867, 798) := by
  cbv

example : BernoulliRegular.BernoulliFast.Cbv.toRat (2, 3) = mkRat 2 3 := rfl

example : (bernoulli 12 : ℚ) = -691 / 2730 := by
  bernoulli_decide

section

-- Prevent cbv unfolding and inspect its result before reflexivity can unfold the definition.
attribute [local cbv_opaque] BernoulliRegular.BernoulliFast.Cbv.simplify

example : BernoulliRegular.BernoulliFast.Cbv.simplify (6, 9) = (2, 3) := by
  conv_lhs =>
    cbv
    guard_target =ₛ ((2 : Int), (3 : Nat))

attribute [-cbvSimprocAttr] BernoulliRegular.BernoulliFast.Cbv.simpSimplify

example : BernoulliRegular.BernoulliFast.Cbv.simplify (6, 9) = (2, 3) := by
  fail_if_success
    conv_lhs =>
      cbv
      guard_target =ₛ ((2 : Int), (3 : Nat))
  rfl

end
