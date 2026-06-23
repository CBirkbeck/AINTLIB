/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.Dual
import HasseWeil.EC.IsogenyAG.MulByIntBasepoint
import HasseWeil.Verschiebung.PurelyInsep
import HasseWeil.Verschiebung.UniversalQthRootWitness

/-!
# The Frobenius dual — the Verschiebung as an `EC.Isogeny` (Silverman III.6.1 Case 2)

This file discharges the **inseparable side** of the dual-isogeny story: the
`q`-power Frobenius `π : E → E` over a finite field `K` (`q = #K`) admits a
`HasDualWitness` with **every field a theorem**, so its dual — the
**Verschiebung** `V = π̂` — exists unconditionally as an `EC.Isogeny W W`, with
the defining identity `(V ∘ π)* = [q]*` (Silverman III.6.1 with `ν = [deg π] = [q]`).

This is the Frobenius counterpart of the separable capstone `dualMulByInt`
(`EC/IsogenyAG/DualGaloisClosed.lean`); together they realize the two cases of
Silverman III.6.1 inside the witness machinery of `EC/IsogenyAG/Dual.lean`.

## The three witness fields, all theorems

* **Range inclusion** `Im([q]*) ⊆ Im(π*)` (Silverman II.2.11–2.12 / III.6.2):
  the universal `q`-th-root witness `qth_root_witness_general`
  (`Verschiebung/QthRootRouteB.lean`, any finite field, any characteristic)
  through `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`
  (`Verschiebung/PurelyInsep.lean`). The Basic-level `(mulByInt W q).pullback`
  is converted to `mulByInt_pullbackAlgHom` by `dif_neg`, and the Basic-level
  Frobenius pullback (`frobeniusIsog`) coincides **definitionally** with the
  `EC`-level one (`EC.Isogeny.frobenius`): both are
  `FiniteField.frobeniusAlgHom K K(E)`.
* **`ν = [q]` basepoint**: `EC.mulByIntBasepoint_holds`
  (`EC/IsogenyAG/MulByIntBasepoint.lean`), proven for all `n ≠ 0` including
  `p ∣ n`, so `n = q = p^r` is covered.
* **`π` reflects `∞`-regularity**: `EC.frobenius_reflects_ordAtInfty`
  (`EC/IsogenyAG/Dual.lean`), from `π* g = g^q` and `ord_∞(g^q) = q·ord_∞ g`.

## Main definitions and results

* `EC.frobenius_mulByInt_q_rangeIncl` — `Im([q]*) ⊆ Im(π*)` in the `EC` shapes.
* `EC.frobeniusMulByIntDualWitness` — the faithful `[q]`-dual witness for `π`.
* `EC.hasDualWitness_frobenius` — `HasDualWitness (Isogeny.frobenius W)`,
  every field a theorem.
* `EC.dualFrobenius` — **the Verschiebung** `V : E → E` as an `EC.Isogeny`.
* `EC.frobenius_pullback_dualFrobenius_pullback` — `π* (V* z) = [q]* z`, the
  function-field shadow of `V ∘ π = [q]`.
* `EC.dualFrobenius_compose_frobenius` — `V ∘ π = [q]` as `EC.Isogeny`s
  (the `mulByIntDual` defining identity in fully bundled form).
* `EC.exists_dual_frobenius` — the `exists_dual` instance for `π`.
* `EC.Isogeny.HasDualWitness.compose` — **dual-of-composition at the witness
  level** (field-general): witnesses compose along `ψ ∘ φ`, with the composite
  endomorphism `ν = φ̂ ∘ ν_ψ ∘ φ` (conjugation, not multiplication; the faithful
  `[m·n]` form is `Isogeny.HasMulByIntDualWitness.compose`,
  `EC/IsogenyAG/MulByIntPullbackComp.lean`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.11–2.12, III.6.1
  (Case 2: the inseparable/Frobenius side), III.6.2.
-/

open WeierstrassCurve

namespace HasseWeil.EC

open Curves

/-! ### The Frobenius dual witness (Silverman III.6.1 Case 2) -/

/-- `q = #K` is nonzero as an integer — the `hn` index of the faithful
`[q]`-dual witness for Frobenius. -/
theorem intCardK_ne_zero {K : Type*} [Fintype K] [Nonempty K] :
    ((Fintype.card K : ℕ) : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.mpr Fintype.card_ne_zero

section FrobeniusDual

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

-- `[DecidableEq K]` is genuinely required (the type contains the
-- division-polynomial pullback `mulByInt_pullbackAlgHom`), but the linter only
-- inspects the surface signature.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **The range inclusion `Im([q]*) ⊆ Im(π*)`** (Silverman II.2.11–2.12 /
III.6.2) for the `q`-power Frobenius on `E/K`, in the `EC` shapes — the deep
field of the Frobenius dual witness, now a theorem. From the universal
`q`-th-root witness (`qth_root_witness_general`: every `[q]*`-pullback is a
`q`-th power in `K(E)`, uniformly in the characteristic) via
`mulByInt_q_pullback_image_subset_frobenius_of_element_witness`. The
Basic-level `(mulByInt W q).pullback` is `mulByInt_pullbackAlgHom` by
`dif_neg`; the Basic-level Frobenius pullback is definitionally the `EC`-level
one (both are `FiniteField.frobeniusAlgHom`). -/
theorem frobenius_mulByInt_q_rangeIncl :
    (HasseWeil.mulByInt_pullbackAlgHom W ((Fintype.card K : ℕ) : ℤ)
        intCardK_ne_zero).range ≤
      (Isogeny.frobenius W).toCurveMap.pullback.range := by
  have h := HasseWeil.mulByInt_q_pullback_image_subset_frobenius_of_element_witness W
    (HasseWeil.qth_root_witness_general W)
  rwa [show (HasseWeil.mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
      HasseWeil.mulByInt_pullbackAlgHom W ((Fintype.card K : ℕ) : ℤ)
        intCardK_ne_zero from dif_neg intCardK_ne_zero] at h

/-- **The faithful `[q]`-dual witness for the `q`-power Frobenius** (Silverman
III.6.1 Case 2) — every field a theorem:
* `hincl` is the range inclusion `frobenius_mulByInt_q_rangeIncl`;
* `hbase` is assembled by `hbase_of_reflects` from the `[q]`-basepoint theorem
  (`mulByIntBasepoint_holds`, valid at `n = q` including `p ∣ q`) and the
  `∞`-regularity reflection of `π` (`frobenius_reflects_ordAtInfty`). -/
noncomputable def frobeniusMulByIntDualWitness :
    Isogeny.HasMulByIntDualWitness (Isogeny.frobenius W)
      ((Fintype.card K : ℕ) : ℤ) intCardK_ne_zero where
  hincl := frobenius_mulByInt_q_rangeIncl W
  hbase := Isogeny.hbase_of_reflects (Isogeny.frobenius W)
    (HasseWeil.mulByInt_pullbackAlgHom W ((Fintype.card K : ℕ) : ℤ)
      intCardK_ne_zero)
    (frobenius_mulByInt_q_rangeIncl W)
    (mulByIntBasepoint_holds W intCardK_ne_zero)
    (frobenius_reflects_ordAtInfty W)

/-- **`HasDualWitness` for the `q`-power Frobenius** (Silverman III.6.1
Case 2): the `q`-power Frobenius admits a dual witness with every field a
theorem — no carried hypotheses. -/
noncomputable def hasDualWitness_frobenius :
    Isogeny.HasDualWitness (Isogeny.frobenius W) :=
  (frobeniusMulByIntDualWitness W).toHasDualWitness

/-- **The Verschiebung** `V = π̂ : E → E` (Silverman III.6.1 Case 2): the dual
of the `q`-power Frobenius as an `EC.Isogeny`, built from the fully-discharged
faithful `[q]`-witness. Satisfies `(V ∘ π)* = [q]*`
(`frobenius_pullback_dualFrobenius_pullback`). -/
noncomputable def dualFrobenius : Isogeny W W :=
  Isogeny.mulByIntDual (frobeniusMulByIntDualWitness W)

/-- The Verschiebung agrees with the generic `Isogeny.dual` at the Frobenius witness. -/
@[simp] theorem dualFrobenius_eq_dual :
    dualFrobenius W = (Isogeny.frobenius W).dual (hasDualWitness_frobenius W) :=
  rfl

/-- **The defining identity of the Verschiebung, function-field form**
(Silverman III.6.1 Case 2): `π* (V* z) = [q]* z`, i.e. `(V ∘ π)* = [q]*` —
the pullback shadow of `V ∘ π = [q]` with `q = deg π`. -/
theorem frobenius_pullback_dualFrobenius_pullback
    (z : (⟨W⟩ : SmoothPlaneCurve K).FunctionField) :
    (Isogeny.frobenius W).toCurveMap.pullback
        ((dualFrobenius W).toCurveMap.pullback z) =
      HasseWeil.mulByInt_pullbackAlgHom W ((Fintype.card K : ℕ) : ℤ)
        intCardK_ne_zero z :=
  Isogeny.mulByIntDual_comp_pullback (frobeniusMulByIntDualWitness W) z

/-- Extensionality for `EC.Isogeny`: the basepoint field is a proposition, so
an isogeny is determined by its underlying curve map. -/
theorem Isogeny.ext_toCurveMap {F : Type*} [Field F] {W₁ W₂ : Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] {φ ψ : Isogeny W₁ W₂}
    (h : φ.toCurveMap = ψ.toCurveMap) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

/-- **`V ∘ π = [q]` as `EC.Isogeny`s** (Silverman III.6.1, the `mulByIntDual`
defining identity in fully bundled form): the composite of the Verschiebung
with Frobenius *is* the multiplication-by-`q` isogeny. -/
theorem dualFrobenius_compose_frobenius :
    (dualFrobenius W).compose (Isogeny.frobenius W) =
      Isogeny.mulByInt W (intCardK_ne_zero (K := K)) :=
  Isogeny.ext_toCurveMap (CurveMap.ext (AlgHom.ext fun z ↦
    frobenius_pullback_dualFrobenius_pullback W z))

-- `[Fintype K]`/`[DecidableEq K]` are genuinely required: the inhabitant is the
-- dual of the `q`-power Frobenius (which only exists over a finite field), but
-- the linter only inspects the type `Nonempty (Isogeny W W)`.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **`exists_dual` for the `q`-power Frobenius** (Silverman III.6.1 Case 2):
the Frobenius admits a reverse isogeny — the concrete inseparable-side instance
of the `exists_dual` story, with all witnesses discharged. -/
theorem exists_dual_frobenius : Nonempty (Isogeny W W) :=
  (Isogeny.frobenius W).exists_dual_of_witness (hasDualWitness_frobenius W)

-- `[DecidableEq K]` is genuinely required by `Isogeny.frobenius` in the type,
-- but the linter only inspects the surface signature.
set_option linter.unusedDecidableInType false in
/-- **The universal dual witness holds for `φ = π`**: the Frobenius instance of
the `universal_dual_witness` shape (`Dual.lean`), unconditionally. -/
theorem nonempty_hasDualWitness_frobenius :
    Nonempty (Isogeny.HasDualWitness (Isogeny.frobenius W)) :=
  ⟨hasDualWitness_frobenius W⟩

end FrobeniusDual

/-! ### Dual-of-composition at the witness level (field-general)

Given dual witnesses for `ψ : E₂ → E₃` and `φ : E₁ → E₂`, the composite
`ψ ∘ φ : E₁ → E₃` carries a dual witness whose endomorphism is the
**conjugation** `ν = φ̂ ∘ ν_ψ ∘ φ` (an endomorphism of `E₁`), with pullback
`ν* = φ* ∘ ν_ψ* ∘ φ̂*`. Indeed `Im(ν*) ⊆ φ*(Im ν_ψ*) ⊆ φ*(Im ψ*) = Im((ψ∘φ)*)`,
and `ν*` preserves `∞`-regularity because each factor does (`wφ.hbase`, then
`ν_ψ* = ψ* ∘ ψ̂*` via the factoring identity, then `φ`'s basepoint condition).

**The faithful `ν = [n·m]` form** (the Silverman bookkeeping
`(ψ∘φ)^ ∘ (ψ∘φ) = [deg φ · deg ψ]`): with `ν_φ = [m]*`, `ν_ψ = [n]*`, turning
the conjugation into multiplication requires the pullback-level covariance
`φ* ∘ [n]*_{E₂} = [n]*_{E₁} ∘ φ*` (the function-field shadow of
`φ ∘ [n] = [n] ∘ φ`, Silverman III.4.8) — for an abstract `EC.Isogeny` this is
exactly the project's open generic-point covariance leaf (DUAL-2) — plus the
multiplicativity `[m·n]* = [n]* ∘ [m]*` of `mulByInt_pullbackAlgHom`. Neither is
a formal consequence of the witness data, so the faithful composition is not
constructible *here*; it is shipped in `EC/IsogenyAG/MulByIntPullbackComp.lean`
(`Isogeny.HasMulByIntDualWitness.compose`), where the multiplicativity is a
theorem and the covariance is carried per-isogeny (a theorem for Frobenius and
`[m]`). The generic `HasDualWitness` composition below needs neither. -/

section WitnessComposition

variable {F : Type*} [Field F]
variable {W₁ W₂ W₃ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

namespace Isogeny.HasDualWitness

/-- The composite witness endomorphism pullback `ν* = φ* ∘ ν_ψ* ∘ φ̂*` — the
pullback of the conjugation `φ̂ ∘ ν_ψ ∘ φ : E₁ → E₁`, where `φ̂` is the dual of
`φ` produced by `wφ`. -/
noncomputable def composeNuPb {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    (wψ : ψ.HasDualWitness) (wφ : φ.HasDualWitness) :
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField :=
  (φ.toCurveMap.pullback.comp wψ.νPb).comp
    (Isogeny.dualPullback φ wφ.νPb wφ.hincl)

set_option maxHeartbeats 800000 in
-- unifying `dualPullback` applications (which unfold to `factorThroughPullback` =
-- `AlgEquiv.ofInjective.symm ∘ codRestrict`) against the curve-indexed function
-- fields is `whnf`-heavy and exceeds the default heartbeat budget
/-- **Range inclusion for the composite witness**:
`Im(φ* ∘ ν_ψ* ∘ φ̂*) ⊆ Im((ψ ∘ φ)*)`, since `Im(ν_ψ*) ⊆ Im(ψ*)` and
`(ψ ∘ φ)* = φ* ∘ ψ*`. -/
theorem composeNuPb_rangeIncl {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    (wψ : ψ.HasDualWitness) (wφ : φ.HasDualWitness) :
    (composeNuPb wψ wφ).range ≤
      (ψ.compose φ).toCurveMap.pullback.range := by
  rintro z ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := wψ.hincl
    ⟨Isogeny.dualPullback φ wφ.νPb wφ.hincl w, rfl⟩
  exact ⟨u, congrArg φ.toCurveMap.pullback hu⟩

set_option maxHeartbeats 800000 in
-- same `whnf` blowup as `composeNuPb_rangeIncl`: `dualPullback` applications must
-- be unified against the curve-indexed function fields
/-- **The composite witness endomorphism preserves `∞`-regularity**: each
factor of `ν* = φ* ∘ ν_ψ* ∘ φ̂*` does — `φ̂*` by `wφ.hbase`, `ν_ψ* = ψ* ∘ ψ̂*`
by `wψ.hbase` plus `ψ`'s basepoint condition (via the factoring identity), and
the outer `φ*` by `φ`'s basepoint condition. -/
theorem composeNuPb_ordAtInfty_nonneg {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    (wψ : ψ.HasDualWitness) (wφ : φ.HasDualWitness)
    (f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
    (hf : 0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f) :
    0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (composeNuPb wψ wφ f) := by
  have h3 := ψ.pullback_ordAtInfty_nonneg _ (wψ.hbase _ (wφ.hbase f hf))
  rw [show ψ.toCurveMap.pullback (Isogeny.dualPullback ψ wψ.νPb wψ.hincl
      (Isogeny.dualPullback φ wφ.νPb wφ.hincl f)) =
        wψ.νPb (Isogeny.dualPullback φ wφ.νPb wφ.hincl f) from
    CurveMap.factorThroughPullback_spec ψ.toCurveMap ⟨wψ.νPb⟩ wψ.hincl _] at h3
  exact φ.pullback_ordAtInfty_nonneg _ h3

/-- **Dual-of-composition at the witness level** (Silverman III.6.1, assembly
step): dual witnesses compose — `HasDualWitness ψ → HasDualWitness φ →
HasDualWitness (ψ ∘ φ)`, with composite endomorphism `ν = φ̂ ∘ ν_ψ ∘ φ`
(conjugation; the faithful `[m·n]` form is
`Isogeny.HasMulByIntDualWitness.compose`, `EC/IsogenyAG/MulByIntPullbackComp.lean`,
which additionally needs the per-isogeny `[n]`-covariance of `φ`). Together with
the Frobenius witness (`hasDualWitness_frobenius`) this is the witness-level
engine for the dual of a factored `φ = φ_sep ∘ Frob^r`. -/
noncomputable def compose {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    (wψ : ψ.HasDualWitness) (wφ : φ.HasDualWitness) :
    (ψ.compose φ).HasDualWitness :=
  Isogeny.hasDualWitness_of_reflects (ψ.compose φ)
    (composeNuPb wψ wφ)
    (composeNuPb_rangeIncl wψ wφ)
    (composeNuPb_ordAtInfty_nonneg wψ wφ)
    (Isogeny.reflects_ordAtInfty (ψ.compose φ))

end Isogeny.HasDualWitness

end WitnessComposition

/-! ### Demonstration: iterated Frobenius carries a dual witness

Composing the Frobenius witness with itself through
`Isogeny.HasDualWitness.compose` gives a dual witness for `π ∘ π` — the first
instance of the witness-level engine on a genuinely inseparable composite, and
the `r = 2` step of the `φ_sep ∘ Frob^r` assembly. -/

section FrobeniusSquare

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

/-- **The dual witness for `π ∘ π`** (iterated Frobenius), by witness
composition — every field still a theorem. -/
noncomputable def hasDualWitness_frobenius_compose_frobenius :
    ((Isogeny.frobenius W).compose (Isogeny.frobenius W)).HasDualWitness :=
  (hasDualWitness_frobenius W).compose (hasDualWitness_frobenius W)

-- `[Fintype K]`/`[DecidableEq K]` are genuinely required: the inhabitant is the
-- dual of the iterated Frobenius, but the linter only inspects the type.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **`exists_dual` for `π ∘ π`**: the iterated Frobenius admits a reverse
isogeny, via the composed witness. -/
theorem exists_dual_frobenius_compose_frobenius : Nonempty (Isogeny W W) :=
  ((Isogeny.frobenius W).compose (Isogeny.frobenius W)).exists_dual_of_witness
    (hasDualWitness_frobenius_compose_frobenius W)

end FrobeniusSquare

end HasseWeil.EC
