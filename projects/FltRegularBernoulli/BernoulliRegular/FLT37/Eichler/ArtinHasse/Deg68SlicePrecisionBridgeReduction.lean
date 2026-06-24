import BernoulliRegular.FLT37.Eichler.ArtinHasse.DworkCoordFunctionalPrecisionCompat
import BernoulliRegular.FLT37.Eichler.ArtinHasse.Deg68SliceThirdOrderCoordRelation

/-!
# The precision-bridge residual reduced to a single same-level (`72`) deg-`68` slice-coordinate
# agreement, via the unconditional coordinate-functional precision compatibility

The precision-bridge residual `CaseIICor823Level71Deg68ModCubePrecisionBridge37`
(`CaseIICor823Level71Deg68ModCubeRelation.lean`),

  `castHom (37²∣37³) (unscaled32SliceCoordCube) = unscaled32SliceCoord 68`,

is here **reduced** — using only the unconditional functional precision-compatibility
`castHom_valuedLambdaQuotientDworkCoeffModCube_eq_coeffModSq_factorPow`
(`CaseIICor823CoeffCubePrecisionCompat.lean`) — to the single same-level statement

  `valuedLambdaQuotientDworkCoeffModSq 32 (factorPow (72≤108) (deg-68 slice @ level 107)) =
     unscaled32SliceCoord 68`.

`castHom (37²∣37³) (unscaled32SliceCoordCube)` is, by the precision-compatibility,
`coordModSq 32 (factorPow (deg-68 slice @ level 107))`; the right side `unscaled32SliceCoord 68` is
`coordModSq 32 (deg-68 slice @ level 71)`.  So the bridge is exactly the **slice-coordinate
agreement** between the level-`107` deg-`68` slice folded down to precision `72` and the level-`71`
deg-`68` slice, read at the `varpi^{32}` coordinate mod `37²`.  Both slices are the degree-`68`
homogeneous part of the Artin-Hasse normalized log; the level-`107` one (precision `108`) reduces to
precision `72` and the question is whether its `varpi^{32}` coordinate agrees with the level-`71` one.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## What is proven here

* `castHom_unscaled32SliceCoordCube_eq_coeffModSq_factorPow_slice107`: the precision-compatibility
  specialised to the level-`107` deg-`68` slice (the argument of `unscaled32SliceCoordCube`).
* `caseII_precisionBridge_of_sliceCoordAgreement`: from the same-level slice-coordinate agreement,
  the precision bridge `CaseIICor823Level71Deg68ModCubePrecisionBridge37`.

## The reduced residual

`CaseIICor823Level71Deg68SliceCoordAgreement37` (`def … : Prop`, **not** an axiom): the same-level
`varpi^{32}` coordinate of the level-`107` deg-`68` slice folded to precision `72` equals the
level-`71` deg-`68` coordinate `unscaled32SliceCoord 68`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 1. The level-`107` deg-`68` slice (the argument of `unscaled32SliceCoordCube`) -/

omit [NumberField.IsCMField K] in
/-- **The level-`107` deg-`68` homogeneous slice** (a name): the argument of `unscaled32SliceCoordCube`
— the degree-`68` homogeneous slice of the level-`107` Dwork-parameter normalized Artin-Hasse log, an
element of `ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K)^(3*(37-1)) = ⧸(λ)^{108}` (mod `37³`). -/
def deg68Slice107 : ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K) ^ (3 * (37 - 1)) :=
  samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
    (p := 37) (K := K) 107 68
    (dworkParameterApprox (p := 37) (K := K) (3 * (37 - 1)))
    (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (3 * (37 - 1)))

omit [NumberField.IsCMField K] in
/-- **`unscaled32SliceCoordCube` is `coordCube 32` of the level-`107` deg-`68` slice** (proven,
unfolding the def).  Re-expresses `unscaled32SliceCoordCube` on the `deg68Slice107` name. -/
theorem unscaled32SliceCoordCube_eq :
    unscaled32SliceCoordCube K =
      valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (deg68Slice107 K) :=
  rfl

/-! ## 2. The precision-compatibility specialised to `unscaled32SliceCoordCube` -/

omit [NumberField.IsCMField K] in
/-- **`castHom (unscaled32SliceCoordCube) = coordModSq 32 (factorPow (72≤108) (deg-68 slice@107))`**
(proven, axiom-clean): the unconditional precision-compatibility
`castHom_valuedLambdaQuotientDworkCoeffModCube_eq_coeffModSq_factorPow` specialised to the level-`107`
deg-`68` slice at the irregular index `(kummerLogEvenPowerIndex 15).1` (value `32`).  The left side is
the mod-`37²` reduction of the level-`107` (mod-`37³`) coordinate; the right side is the level-`107`
slice folded to precision `72` and read at `varpi^{32}` mod `37²`. -/
theorem castHom_unscaled32SliceCoordCube_eq_coeffModSq_factorPow_slice107 :
    (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
        (unscaled32SliceCoordCube K) =
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (Ideal.Quotient.factorPow (lambdaIdeal 37 K)
          (by nlinarith : 2 * (37 - 1) ≤ 3 * (37 - 1)) (deg68Slice107 K)) := by
  rw [unscaled32SliceCoordCube_eq]
  exact castHom_valuedLambdaQuotientDworkCoeffModCube_eq_coeffModSq_factorPow
    (p := 37) (K := K) _ _

/-! ## 3. The reduced residual: the same-level deg-`68` slice-coordinate agreement -/

open BernoulliRegular (CPlusGenerator) in
/-- **The same-level deg-`68` slice-coordinate agreement residual** (a `def … : Prop`, **not** an
axiom): the `varpi^{32}` mod-`37²` coordinate of the level-`107` deg-`68` slice folded down to
precision `72` equals the level-`71` deg-`68` coordinate `unscaled32SliceCoord 68`:

  `coordModSq 32 (factorPow (72≤108) (deg-68 slice @ 107)) = unscaled32SliceCoord 68`.

This is the **single genuine content** of the precision bridge once the functional
precision-compatibility (`castHom ∘ coordCube = coordModSq ∘ factorPow`, proven unconditionally) is
factored out: a same-level (`72`) statement comparing the level-`107` deg-`68` slice (folded to
precision `72`) and the level-`71` deg-`68` slice at the `varpi^{32}` coordinate.  Both are the
degree-`68` homogeneous part of the Artin-Hasse normalized log; they differ only through the
truncation level (`107` vs `71`) and the Dwork-parameter approximant (`108` vs `72`), and the
difference is supported on the Frobenius (`n = 37`) term, whose `varpi^{32}` coordinate carries the
genuine mod-`37³` second digit. -/
def CaseIICor823Level71Deg68SliceCoordAgreement37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
      (Ideal.Quotient.factorPow (lambdaIdeal 37 (CyclotomicField 37 ℚ))
        (by nlinarith : 2 * (37 - 1) ≤ 3 * (37 - 1)) (deg68Slice107 (CyclotomicField 37 ℚ))) =
    unscaled32SliceCoord (K := CyclotomicField 37 ℚ) 68

open BernoulliRegular (CPlusGenerator) in
/-- **The precision bridge from the same-level slice-coordinate agreement** (proven, axiom-clean given
the agreement): `CaseIICor823Level71Deg68SliceCoordAgreement37 →
CaseIICor823Level71Deg68ModCubePrecisionBridge37`.

By the precision-compatibility (`castHom_unscaled32SliceCoordCube_eq_coeffModSq_factorPow_slice107`),
`castHom (unscaled32SliceCoordCube) = coordModSq 32 (factorPow (deg-68 slice@107))`; the agreement says
this equals `unscaled32SliceCoord 68`, which is exactly the bridge. -/
theorem caseII_precisionBridge_of_sliceCoordAgreement
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hAgree : CaseIICor823Level71Deg68SliceCoordAgreement37) :
    CaseIICor823Level71Deg68ModCubePrecisionBridge37 := by
  rw [CaseIICor823Level71Deg68ModCubePrecisionBridge37,
    castHom_unscaled32SliceCoordCube_eq_coeffModSq_factorPow_slice107]
  exact hAgree

end BernoulliRegular.FLT37.Eichler

end
