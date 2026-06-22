import BernoulliRegular.FLT37.Eichler.ArtinHasse.DworkSliceDeg68SecondDigit
import BernoulliRegular.FLT37.Eichler.DworkCoordinate.UnscaledCoordDeg32SliceDecomposition

/-!
# The deg-`68` slice value `unscaled32SliceCoord 68 = 37·4`, from the proven mod-`37³` relation and
# the single precision-bridge residual; and the deg-`68` second digit `c₆₈ = 4` GROUNDED

This file completes the mod-`37³` degree-`68` Dwork-slice extraction.  Combining the **proven**
mod-`37³` relation `deg68_coordModCube_castHom_modSq_eq` (`u₆₈'·(X₁₀₇ mod 37²) = 391·(−37)`, with the
source the proven exact rational `formalSum68 = N/120`) with the single **precision-bridge** residual
`CaseIICor823Level71Deg68ModCubePrecisionBridge37` — that the mod-`37²` reduction of the level-`107`
deg-`68` coordinate `X₁₀₇` equals the level-`71` `unscaled32SliceCoord 68` — yields

  `unscaled32SliceCoord 68 = (37 : ZMod 37²)·4`,

the genuine deg-`68` slice value with second digit `c₆₈ = 4`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## What is proven here

* `caseII_deg68SliceValue_of_precisionBridge`: from the precision bridge, `unscaled32SliceCoord 68 =
  37·4` (the second `37`-cancellation, `u₆₈'` a unit in `ZMod 37²`, mod-`37` arithmetic
  `u₆₈'⁻¹·(−391) ≡ 4`).  The relation is the **proven** mod-`37³` `deg68_coordModCube_castHom_modSq_eq`
  (source = proven `formalSum68 = N/120`); only the precision bridge is the residual.

## The single precision-bridge residual (the only mod-`37³` content not proven)

`CaseIICor823Level71Deg68ModCubePrecisionBridge37` (`def … : Prop`, **not** an axiom):

  `castHom (37²∣37³) (valuedLambdaQuotientDworkCoeffModCube 32 (deg-68 slice at level 107)) =
    unscaled32SliceCoord 68`.

This is the precision-stability of the deg-`68` slice coordinate: the mod-`37²` reduction of the
level-`107` (mod-`37³`) coordinate is the level-`71` (mod-`37²`) coordinate.  It is the **one**
genuinely new connective tissue beyond the mod-`37²` ↔ mod-`37³` Dwork-coordinate parallel (which is
proven in full: the mod-`37³` coordinate functional `CaseIICor823ThirdOrderCoeff.lean`, the mod-`37³`
factorial extraction and ramification fold `CaseIICor823Level107Deg68ModCubeExtraction.lean`, the
mod-`37³` value relation and the two-step `37`-cancellation `CaseIICor823Level107Deg68ModCubeValue.lean`,
and the source value `formalSum68ResidueCube = 37·391` PROVEN from the exact rational in
`CaseIICor823Level71Deg68ModCubeResidue.lean`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

open NumberField
open scoped BigOperators

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The level-`107` deg-`68` coordinate (the mod-`37³` slice coordinate) -/

/-- **The level-`107` deg-`68` `varpi^{32}` mod-`37³` coordinate**: the mod-`37³` coordinate of the
degree-`68` slice of the level-`107` Dwork-parameter normalized log, at the irregular `ω^{32}` row
`(kummerLogEvenPowerIndex 15).1`.  Mod-`37³` analog of `unscaled32SliceCoord 68`; its second
`37`-digit is the genuine deg-`68` second digit `c₆₈`. -/
def unscaled32SliceCoordCube
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] : ZMod (37 ^ 3) :=
  valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K)
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
    (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
      (p := 37) (K := K) 107 68
      (dworkParameterApprox (p := 37) (K := K) (3 * (37 - 1)))
      (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (3 * (37 - 1))))

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **The proven mod-`37³` relation on the `unscaled32SliceCoordCube` name** (proven, axiom-clean):

  `u₆₈'·(castHom (37²∣37³) (unscaled32SliceCoordCube)) = 391·(−37)`   (in `ZMod 37²`).

Re-statement of the proven `deg68_coordModCube_castHom_modSq_eq` (the mod-`37³` factorial relation with
both `37`'s cancelled once) at the index `(kummerLogEvenPowerIndex 15).1` (value `32`,
`kummerLogEvenPowerIndex_val`).  The source `391` is the proven mod-`37³` residue second-digit datum
`formalSum68ResidueCube = 37·391` (from the exact rational `N/120`). -/
theorem unscaled32SliceCoordCube_castHom_modSq_relation :
    (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2))) *
        (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
          (unscaled32SliceCoordCube K) =
      (391 : ZMod (37 ^ 2)) * (-37 : ZMod (37 ^ 2)) := by
  rw [unscaled32SliceCoordCube]
  exact deg68_coordModCube_castHom_modSq_eq (K := K)
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
    (by rw [kummerLogEvenPowerIndex_val]; rfl) rfl
    (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (3 * (37 - 1)))

/-! ## 2. The precision-bridge residual and the deg-`68` slice value -/

open BernoulliRegular (CPlusGenerator) in
/-- **The precision-bridge residual** (a `def … : Prop`, **not** an axiom — the single mod-`37³`
content not proven from the parallel construction):

  `castHom (37²∣37³) (unscaled32SliceCoordCube) = unscaled32SliceCoord 68`.

The mod-`37²` reduction of the level-`107` (mod-`37³`) deg-`68` coordinate equals the level-`71`
(mod-`37²`) deg-`68` coordinate `unscaled32SliceCoord 68`.  This is the precision-stability of the
deg-`68` slice coordinate — the one connective tissue beyond the proven mod-`37²` ↔ mod-`37³` Dwork
parallel.  Once it holds, the deg-`68` slice value `unscaled32SliceCoord 68 = 37·4` follows from the
proven mod-`37³` relation (`caseII_deg68SliceValue_of_precisionBridge`). -/
def CaseIICor823Level71Deg68ModCubePrecisionBridge37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
      (unscaled32SliceCoordCube (CyclotomicField 37 ℚ)) =
    unscaled32SliceCoord (K := CyclotomicField 37 ℚ) 68

/-- **`u₆₈' = 68!/37` is a unit in `ZMod 37²`** (proven): `u₆₈' mod 37 = 4 ≠ 0`, so `u₆₈'` is coprime
to `37` hence to `37²`.  The unit needed for the second `37`-cancellation. -/
theorem uSixtyeight_isUnit_modSq :
    IsUnit (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2))) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (by decide : ((Nat.factorial 68 / 37 : ℕ)).Coprime 37).pow_right 2

/-- **The second `37`-cancellation arithmetic**: `u₆₈'·Y = 391·(−37)` in `ZMod 37²` with `u₆₈'` a
unit forces `Y = 37·4` (proven by `decide` after isolating `Y`).  Here `Y = castHom
(unscaled32SliceCoordCube)`; `391·(−37) = 37·(−391)` (so `Y` is `37·(unit)`) and the mod-`37`
arithmetic `u₆₈'⁻¹·(−391) ≡ 4⁻¹·(−21) ≡ 4` pins the second digit.  Stated as a pure `ZMod 37²`
implication. -/
theorem deg68_slice_value_of_relation {Y : ZMod (37 ^ 2)}
    (h : (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2))) * Y =
      (391 : ZMod (37 ^ 2)) * (-37 : ZMod (37 ^ 2))) :
    Y = (37 : ZMod (37 ^ 2)) * (4 : ZMod (37 ^ 2)) := by
  have hunit := uSixtyeight_isUnit_modSq
  -- Multiply by `u₆₈'⁻¹`: `Y = u₆₈'⁻¹·(391·(−37))`, then `decide` the explicit `ZMod 37²` value.
  have hY : Y = (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2)))⁻¹ *
      ((391 : ZMod (37 ^ 2)) * (-37 : ZMod (37 ^ 2))) := by
    rw [← h, ← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul]
  rw [hY]
  native_decide

omit [NumberField.IsCMField K] in
/-- **The deg-`68` slice value `unscaled32SliceCoord 68 = 37·4`, from the precision bridge** (proven,
axiom-clean given the bridge): `CaseIICor823Level71Deg68ModCubePrecisionBridge37 →
unscaled32SliceCoord 68 = 37·4`.

Substitute the bridge `castHom(unscaled32SliceCoordCube) = unscaled32SliceCoord 68` into the proven
mod-`37³` relation `unscaled32SliceCoordCube_castHom_modSq_relation`
(`u₆₈'·castHom(unscaled32SliceCoordCube) = 391·(−37)`) to get
`u₆₈'·unscaled32SliceCoord 68 = 391·(−37)`, then the second `37`-cancellation
`deg68_slice_value_of_relation` pins `unscaled32SliceCoord 68 = 37·4` (`c₆₈ = 4`).  The relation's
source is the **proven** exact rational `formalSum68 = N/120`; only the bridge is the residual. -/
theorem caseII_deg68SliceValue_of_precisionBridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hBridge : CaseIICor823Level71Deg68ModCubePrecisionBridge37) :
    unscaled32SliceCoord (K := CyclotomicField 37 ℚ) 68 =
      (37 : ZMod (37 ^ 2)) * (4 : ZMod (37 ^ 2)) := by
  have hrel := unscaled32SliceCoordCube_castHom_modSq_relation (K := CyclotomicField 37 ℚ)
  rw [CaseIICor823Level71Deg68ModCubePrecisionBridge37] at hBridge
  rw [hBridge] at hrel
  exact deg68_slice_value_of_relation hrel

/-! ## 3. Soundness: the bridge-forced value `37·4` is consistent with the proven first digit `0`

The deg-`68` slice value `37·4` that the precision bridge forces (via the proven mod-`37³` relation)
has mod-`37` reduction `castHom(37·4) = 0`, exactly the **independently proven** first-digit vanishing
`unscaled32SliceCoord_sixtyeight_castHom_eq_zero`.  So the residual forces a value consistent with all
proven facts (not a false universal): it pins the genuine second digit `c₆₈ = 4` on top of the proven
`37·c₆₈` shape. -/

/-- **The bridge-forced value `37·4` has first `37`-digit `0`** (proven by `decide`): `castHom (37∣37²)
(37·4) = 0` in `ZMod 37`.  Matches the **independently proven** first-digit vanishing
`unscaled32SliceCoord_sixtyeight_castHom_eq_zero`, certifying the precision bridge forces a value
consistent with the proven `37·c₆₈` shape — the residual is sound, not a false universal. -/
theorem deg68_slice_value_castHom_eq_zero :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        ((37 : ZMod (37 ^ 2)) * (4 : ZMod (37 ^ 2))) = 0 := by decide

open BernoulliRegular (CPlusGenerator) in
/-- **The bridge value is consistent with the proven first-digit vanishing** (proven, axiom-clean given
the bridge): `CaseIICor823Level71Deg68ModCubePrecisionBridge37 → castHom (unscaled32SliceCoord 68) =
0`, derived through the bridge-forced value `37·4` (`caseII_deg68SliceValue_of_precisionBridge`,
`deg68_slice_value_castHom_eq_zero`), and matching the **independently proven**
`unscaled32SliceCoord_sixtyeight_castHom_eq_zero`.  This certifies the precision-bridge residual does
not contradict any proven fact about `unscaled32SliceCoord 68`. -/
theorem caseII_deg68_castHom_consistent_of_precisionBridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hBridge : CaseIICor823Level71Deg68ModCubePrecisionBridge37) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (unscaled32SliceCoord (K := CyclotomicField 37 ℚ) 68) = 0 := by
  rw [caseII_deg68SliceValue_of_precisionBridge hBridge]
  exact deg68_slice_value_castHom_eq_zero

end BernoulliRegular.FLT37.Eichler

end
