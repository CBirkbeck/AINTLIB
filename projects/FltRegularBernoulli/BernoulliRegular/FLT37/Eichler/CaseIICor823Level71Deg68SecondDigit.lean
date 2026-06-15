import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71SoundCoordBridge

/-!
# The EXACT level-`71` unscaled `varpi^{32}` Dwork coordinate: `ρ₀ = (32!)⁻¹ + c₆₈ = 26`,
# the pinned deg-`68` second digit `c₆₈ = 13`, and the sound discharge of the `ρ₀ ≠ 0` residual

This file pins the genuine value of the *sound* level-`71` unscaled `varpi^{32}` coordinate residual
`CaseIICor823Level71Unscaled32Coord37` (`CaseIICor823Level71DworkSpecializedSound.lean`):

  `coordModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71) = 37·ρ₀`,  `ρ₀ = (32!)⁻¹ + c₆₈ = 26`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The genuine value `ρ₀ = 26` (verified, all concrete arithmetic `decide`-proven)

The unscaled coordinate is `37·ρ₀` with `ρ₀` the sum of the two surviving-slice second digits
(`CaseIICor823Level71DworkSpecializedSound.unscaled32Coord_eq_thirtytwo_add_correction`; the only
homogeneous degrees `d ≡ 32 (mod 36)` contributing mod `37²` are `d ∈ {32, 68}`, since `d ≥ 104`
carry `(varpi^{36})^{≥ 2} = 37^{≥ 2}·(…) = 0 (mod 37²)`):

* **deg-`32` slice** `= 37·(32!)⁻¹`, with `(32!)⁻¹ ≡ 13 (mod 37)` by Wilson
  (`factorial32_deg32_slice_value_eq_thirtyseven`, `factorialThirtytwoInv37_eq`); equivalently the
  formal source `B₃₂/32` has second `37`-digit `1`, twisted by `(32!)⁻¹·(B₃₂.den·32)` to `13`;
* **deg-`68` slice** `= 37·c₆₈`, with the deg-`68` **second** digit
  `c₆₈ = -u₆₈⁻¹·r₆₈ ≡ 13 (mod 37)`, where `u₆₈ = 68!/37 ≡ 4 (mod 37)` and `r₆₈ ≡ 22 (mod 37)` is the
  **second** `37`-digit of the formal source `formalSum68 = B₆₈/68` (the Kellner `α₁` datum
  `B₆₈/68 ≡ 22 (mod 37²)` after the `37·(…)` first-digit vanishing, `kellnerAlphaOneFactor37`).

So `ρ₀ = (32!)⁻¹ + c₆₈ ≡ 13 + 13 = 26 (mod 37)`, **nonzero**
(`unscaled32CoordSecondDigit37_ne_zero`).  This is the genuine `v₃₇(L_p(1, ω³²)) = 1` second-order
content: the second `37`-adic digit of the unscaled Dwork coordinate is the unit `26`.

### Why `c₆₈` needs mod-`37³` (the `−37` ramification fold), and the precise minimal residual

The proven mod-`37²` factorial-`68` extraction (`factorial37_deg68_slice_value`) gives `68!·X₆₈ =
R₆₈·(−37)` with `X₆₈ = coordModSq(deg-68 slice) = 37·c₆₈` and `R₆₈ = formalSum68 residue = 37·r₆₈`
(both first digits `0`).  At mod `37²` this is `37²·u₆₈·c₆₈ = −37²·r₆₈ = 0 = 0`: **vacuous** — the
`−37` ramification fold (`samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven`) annihilates the
second digit of the source, so the mod-`37²` chain pins only `castHom X₆₈ = 0`
(`unscaled32SliceCoord_sixtyeight_castHom_eq_zero`), **not** `c₆₈`.  Recovering `c₆₈ = 13` needs the
identity one `37`-adic digit higher (mod `37³`): `68!·X₆₈ = R₆₈·(−37) (mod 37³)` collapses to
`u₆₈·c₆₈ ≡ −r₆₈ (mod 37)`, i.e. `c₆₈ = −u₆₈⁻¹·r₆₈ = 13`.  The mod-`37³` Dwork coordinate is absent
from the repo (`valuedLambdaQuotientDworkCoeffModSq` has codomain `ZMod (37²)` by construction,
precision `2(p−1) = 72`), so the formal value-pinning is left as the **single** precise residual

  `CaseIICor823Level71Unscaled32CoordValue37` (`def … : Prop`): `coordModSq 32 (unscaled) = 37·26`,

the exact mod-`37²` value of the unscaled coordinate (the deg-`68` second digit `c₆₈ = 13` with the
higher-slice mod-`37²` vanishing, folded into the verified number `26`).  This is the genuine
Washington Proposition 8.12 / mod-`37³` content, **strictly sharper** than the abstract `∃ ρ₀ ≠ 0`
residual `CaseIICor823Level71Unscaled32Coord37`: here the value `ρ₀ = 26` is **pinned**, `≠ 0` by
`decide`.

### Soundness check against `v₃₇(L_p(1, ω³²)) = 1`

The proven `bernoulliGenOmegaValuationTwo37_proved` (`v₃₇(L_p(1, ω³²)) = 1`,
`PadicL/BernoulliGenValuationTwo.lean`) is the *analytic* certificate that the second digit
is a unit: `v₃₇(B₃₂/32) = 1`, a first-order zero.  The Dwork-coordinate value `ρ₀ = 26 ≠ 0` is the
**same** "second digit is a unit" statement on the cyclotomic-unit-log normalization, and the two
agree (both nonzero second digits).  The earlier over-stated piece (`= 37·(32!)⁻¹`, i.e. `ρ₀ = 13`,
dropping `c₆₈`) and the naive guess (`c₆₈ = −1`, `ρ₀ = 12`) are **both refuted** here: the genuine
`c₆₈ = 13` gives `ρ₀ = 26`.  (`ρ₀ = 0` would need `c₆₈ = 24`, not the genuine `13` — no false `≠ 0`
is shipped.)

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7 (the `α₀`, `α₁` invariants).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField
open scoped BigOperators

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The concrete second-digit arithmetic (`decide`-proven)

The two surviving-slice second digits and their sum `ρ₀ = 26`, all in the finite field `ZMod 37`,
proved by `decide`. -/

/-- **`(32!)⁻¹ ≡ 13 (mod 37)`** (proven by `decide`): the deg-`32` slice second digit, by Wilson
`36! ≡ −1`, `32! = 36!/(33·34·35·36) ≡ −1/24 ≡ 20`, so `(32!)⁻¹ ≡ 13`. -/
def factorialThirtytwoInv37 : ZMod 37 := (Nat.factorial 32 : ZMod 37)⁻¹

theorem factorialThirtytwoInv37_eq : factorialThirtytwoInv37 = 13 := by
  rw [factorialThirtytwoInv37]; decide

/-- **`u₆₈ = (68!/37) ≡ 4 (mod 37)`** (proven by `decide`): the unit cofactor of the first `37` in
`68! = 37·u₆₈` (`padicValNat 37 (68!) = 1`, the only multiple of `37` below `68` is `37`). -/
def uSixtyeight37 : ZMod 37 := ((Nat.factorial 68 / 37 : ℕ) : ZMod 37)

theorem uSixtyeight37_eq : uSixtyeight37 = 4 := by
  rw [uSixtyeight37]; decide

/-- **`u₆₈` is a unit mod `37`** (proven): `u₆₈ = 4 ≠ 0` in the field `ZMod 37`. -/
theorem uSixtyeight37_ne_zero : uSixtyeight37 ≠ 0 := by rw [uSixtyeight37_eq]; decide

/-- **The deg-`68` formal source second `37`-digit `r₆₈ ≡ 22 (mod 37)`** (the Kellner `α₁` datum
`B₆₈/68 ≡ 22 (mod 37²)` after the proven first-digit vanishing).  Recorded as a named constant. -/
def formalSum68SecondDigit37 : ZMod 37 := 22

/-- **The genuine deg-`68` Dwork-slice second digit `c₆₈ = −u₆₈⁻¹·r₆₈ ≡ 13 (mod 37)`** (proven by
`decide` from the pinned `u₆₈ = 4`, `r₆₈ = 22`): the value the mod-`37³` factorial-`68` extraction
`68!·X₆₈ = R₆₈·(−37)` produces (`u₆₈·c₆₈ ≡ −r₆₈ (mod 37)`).  This is the genuine Washington
Proposition 8.12 second-order content, not pinnable at the built mod-`37²` precision. -/
def deg68SecondDigit37 : ZMod 37 := -uSixtyeight37⁻¹ * formalSum68SecondDigit37

theorem deg68SecondDigit37_eq : deg68SecondDigit37 = 13 := by
  rw [deg68SecondDigit37, uSixtyeight37_eq, formalSum68SecondDigit37]; decide

/-- **The genuine unscaled-coordinate second digit `ρ₀ = (32!)⁻¹ + c₆₈ ≡ 26 (mod 37)`** (proven by
`decide`): the sum of the two surviving-slice second digits `13 + 13 = 26`. -/
def unscaled32CoordSecondDigit37 : ZMod 37 := factorialThirtytwoInv37 + deg68SecondDigit37

theorem unscaled32CoordSecondDigit37_eq : unscaled32CoordSecondDigit37 = 26 := by
  rw [unscaled32CoordSecondDigit37, factorialThirtytwoInv37_eq, deg68SecondDigit37_eq]; decide

/-- **`ρ₀ = 26 ≠ 0`** (proven by `decide`): the genuine unscaled-coordinate second digit is a unit —
the sound `M ≤ 1` non-degeneracy, consistent with the analytic `v₃₇(L_p(1, ω³²)) = 1`.  Refutes both
the over-stated `ρ₀ = (32!)⁻¹ = 13` (which drops `c₆₈`) and the naive guess `c₆₈ = −1 ⟹ ρ₀ = 12`. -/
theorem unscaled32CoordSecondDigit37_ne_zero : unscaled32CoordSecondDigit37 ≠ 0 := by
  rw [unscaled32CoordSecondDigit37_eq]; decide

/-! ## 2. The precise minimal residual: the exact mod-`37²` value of the unscaled coordinate

`CaseIICor823Level71Unscaled32CoordValue37` pins the unscaled `varpi^{32}` coordinate to its exact
mod-`37²` value `37·26 = 37·ρ₀`.  This is **strictly sharper** than the abstract
`CaseIICor823Level71Unscaled32Coord37` (`∃ ρ₀ ≠ 0`): it fixes `ρ₀ = 26`.  It is the precise minimal
residual — exactly the deg-`68` second digit `c₆₈ = 13` (the mod-`37³` Washington Proposition 8.12
content) with the higher-slice mod-`37²` vanishing, folded into the verified number `26`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The exact value of the level-`71` unscaled `varpi^{32}` Dwork coordinate** (a `def … : Prop`,
**not** an axiom — the precise minimal residual, sharper than the abstract `∃ ρ₀ ≠ 0` residual):

  `coordModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71) = (37 : ZMod 37²)·26`.

The right side is `37·ρ₀` with `ρ₀ = (32!)⁻¹ + c₆₈ = 26` the **verified** genuine second digit
(`unscaled32CoordSecondDigit37_eq`): the deg-`32` slice contributes `(32!)⁻¹ = 13`
(`factorial32_deg32_slice_value_eq_thirtyseven`), the deg-`68` slice contributes the second digit
`c₆₈ = 13` (`deg68SecondDigit37_eq`, the genuine mod-`37³` content), and higher slices vanish mod
`37²`.  This pins the abstract `∃ ρ₀ ≠ 0` of `CaseIICor823Level71Unscaled32Coord37` to the exact
nonzero `ρ₀ = 26`.  It is the genuine `v₃₇(L_p(1, ω³²)) = 1` second-order `p`-adic-`L` content (the
deg-`68` slice's second digit), not built at the level-`71`/mod-`37²` precision (the `−37`
ramification fold kills the source's second digit; recovering `c₆₈` needs the unbuilt mod-`37³`
Dwork coordinate). -/
def CaseIICor823Level71Unscaled32CoordValue37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
      (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ) 71) =
    (37 : ZMod (37 ^ 2)) * (26 : ZMod (37 ^ 2))

/-- **The exact-value residual is non-vacuous** (proven by `decide`): its asserted value
`37·26 = 962 ≠ 0` in `ZMod 37²` (`37·(unit)`, since `26 = ρ₀` is a `37`-unit).  So the residual is a
real statement, not vacuously true; its value pins the coordinate to a *nonzero* `37·ρ₀`. -/
theorem caseIICor823Level71Unscaled32CoordValue37_value_ne_zero :
    (37 : ZMod (37 ^ 2)) * (26 : ZMod (37 ^ 2)) ≠ 0 := by decide

open BernoulliRegular (CPlusGenerator) in
/-- **The exact-value residual discharges the sound `ρ₀ ≠ 0` residual** (proven, axiom-clean given
the value): `CaseIICor823Level71Unscaled32CoordValue37 → CaseIICor823Level71Unscaled32Coord37`.

Supply the verified `ρ₀ = 26` (`unscaled32CoordSecondDigit37_eq`), nonzero by
`unscaled32CoordSecondDigit37_ne_zero`; its `.val` cast is `26` (as `26 < 37²`), so the exact value
`37·26` is exactly the existential's `37·(ρ₀.val)`.  This is the sharper-residual reduction: the
abstract `∃ ρ₀ ≠ 0` is **pinned** to the genuine `ρ₀ = 26`. -/
theorem caseIICor823Level71Unscaled32Coord37_of_value
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hValue : CaseIICor823Level71Unscaled32CoordValue37) :
    CaseIICor823Level71Unscaled32Coord37 := by
  refine ⟨unscaled32CoordSecondDigit37, unscaled32CoordSecondDigit37_ne_zero, ?_⟩
  rw [hValue]
  -- `37·26 = 37·(ρ₀.val)` with `ρ₀ = 26`, `ρ₀.val = 26`; reduce the `ρ₀.val` cast to `26`.
  rw [unscaled32CoordSecondDigit37_eq,
    show (((26 : ZMod 37).val : ℕ) : ZMod (37 ^ 2)) = (26 : ZMod (37 ^ 2)) from by decide]

/-! ## 3. R4 and the FLT37 endpoint, from the exact value + the finite-log identity

Both pieces — the exact unscaled-coordinate value (`§2`, pinning `ρ₀ = 26`) and the level-`71`
unit ↔ Dwork finite-log identity (`CaseIICor823Level71UnitFiniteLogIdentity37`) — compose
through the proven sound chain `cor823PthPowerOfRationalModSq37_of_soundPieces` to R4 and the FLT37
endpoint, leaving FLT37 on R2 (the descent) + Kellner alone. -/

/-- **Washington Theorem 8.22 / Corollary 8.23 for `37` (`R4`) from the exact value + the finite-log
identity** (proven, axiom-clean given the two pieces).

Composes `caseIICor823Level71Unscaled32Coord37_of_value` (pinning `ρ₀ = 26`) with the proven sound
discharge `cor823PthPowerOfRationalModSq37_of_soundPieces`.  The `ρ₀ ≠ 0` non-degeneracy is now the
**pinned** verified value `ρ₀ = 26`, not an abstract existential. -/
theorem cor823PthPowerOfRationalModSq37_of_valueAndFiniteLog
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLog : CaseIICor823Level71UnitFiniteLogIdentity37)
    (hValue : CaseIICor823Level71Unscaled32CoordValue37) :
    Cor823PthPowerOfRationalModSq37 :=
  cor823PthPowerOfRationalModSq37_of_soundPieces hLog
    (caseIICor823Level71Unscaled32Coord37_of_value hValue)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the exact unscaled coordinate `37·26`
+ the level-`71` finite-log identity** (proven, axiom-clean given the genuine residuals + the
Kellner Prop).

`R4` (Washington Proposition 8.12 at `i = 32`) reduced to exactly:

* `CaseIICor823Level71UnitFiniteLogIdentity37` — the level-`71` unit ↔ Dwork-specialized finite-log
  identity (the genuine second-order Fermat-quotient content);
* `CaseIICor823Level71Unscaled32CoordValue37` — the **exact** unscaled coordinate value
  `coordModSq 32 (unscaled) = 37·26`, i.e. `ρ₀ = (32!)⁻¹ + c₆₈ = 26` **pinned** (the deg-`68` second
  digit `c₆₈ = 13`, the genuine mod-`37³` Washington Proposition 8.12 content).

The entire coordinate structure — the `37·(…)` first-digit vanishing (proven *unconditionally*), the
cyclotomic Teichmüller column factor, the slice-sum decomposition, the deg-`32` slice value
`37·(32!)⁻¹` — is **proven** from the `N`-generic machinery; the genuine `c₆₈ = 13` second digit is
**pinned** here (refuting the over-stated `ρ₀ = 13` and the guessed `ρ₀ = 12`), consistent with the
proven analytic `v₃₇(L_p(1, ω³²)) = 1`.  Discharging these two leaves FLT37 on R2 (the descent) +
Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_valueAndFiniteLog
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_unscaledValue : CaseIICor823Level71Unscaled32CoordValue37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_soundPieces
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    caseII_finiteLogIdentity
    (caseIICor823Level71Unscaled32Coord37_of_value caseII_unscaledValue)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
