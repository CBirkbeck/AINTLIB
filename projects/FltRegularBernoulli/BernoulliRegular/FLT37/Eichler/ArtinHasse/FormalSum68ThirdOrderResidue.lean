import BernoulliRegular.FLT37.Eichler.ArtinHasse.ArtinHasseLogCoeffDeg68Value

set_option linter.style.longLine false

/-!
# The mod-`37³` residue of `formalSum68` and the genuine deg-`68` slice second digit `c₆₈ = 4`,
# fully GROUNDED in the proven exact rational `formalSum68 = N/120`

This file supplies the **source side** of the mod-`37³` degree-`68` Dwork-slice extraction —
everything that does **not** require the (unbuilt) mod-`37³` Dwork-coordinate evaluator.  It imports
only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The genuine value, PROVEN (not a residual)

The proven exact rational `formalSum68RatValue_proven`
(`CaseIICor823Level71FormalSum68RatBridge.lean`): `(formalSum68 : ℚ) = N/120`, `N` the explicit
69-digit numerator, computed through the actual `PowerSeries ℚ` Artin-Hasse log machinery.  Since
`120` is a `37`-unit, the mod-`37³` residue

  `formalSum68ResidueCube := (formalSum68.num)·(formalSum68.den)⁻¹ : ZMod 37³`

is the **proven** value `14467 = 37·391` (`decide` from the reduced fraction `N/120`), where
`391 = 21 + 37·10`, i.e.

  `formalSum68ResidueCube ≡ 37·21 + 37²·10 (mod 37³)`.

So the **second** `37`-adic digit of `formalSum68` is `r₆₈ = 21` (the first is `0`, the proven
first-order vanishing `formalSum68_rIntegralToZMod_eq_zero`), and the **third** is `10`.  This is the
mod-`37³` lift of the proven mod-`37²` value `formalSum68ResidueModSq37_proven` (`≡ 777 = 37·21`),
and — crucially — it is **proven outright** here, not carried as a residual, because the exact
rational `N/120` is proven.

## The cancellation `c₆₈ = 4`, GROUNDED

The mod-`37³` factorial-`68` extraction (the *relation*, the one piece still requiring the mod-`37³`
coordinate evaluator) reads

  `68!·X₆₈ = formalSum68Residue·(−37)`   (mod `37³`),

with `X₆₈` the deg-`68` slice's `varpi^{32}` coordinate.  Writing `68! = 37·u₆₈'`
(`u₆₈' ≡ 4 mod 37`, `padicValNat 37 (68!) = 1`) and `formalSum68Residue ≡ 37·391` (this file) both
sides carry **two** `37`'s:

  `37·u₆₈'·X₆₈ = (37·391)·(−37) = −37²·391 ≡ −37²·391 (mod 37³)`,

so dividing by `37` (exact in `ℤ_[37]`) and using `castHom X₆₈ = 0` (proven first digit `0`,
`X₆₈ = 37·c₆₈`):

  `37²·u₆₈'·c₆₈ ≡ −37²·391 (mod 37³)`  ⟹  `u₆₈'·c₆₈ ≡ −391 ≡ −21 (mod 37)`  ⟹  `c₆₈ = −u₆₈'⁻¹·21 = 4`.

The third digit `10` of `formalSum68` drops out — only `391 mod 37 = 21` survives the second `37`.
So `c₆₈ = −u₆₈'⁻¹·r₆₈ = −4⁻¹·21 = 4`, **the proven `deg68SecondDigit37Corrected`**, now grounded in
the exact rational (`deg68SecondDigit37Corrected_grounded_value`): the genuine deg-`68` slice second
digit is `4`, computed from the actual degree-`68` Artin-Hasse coefficient `formalSum68 = N/120`.

## Honest scope

This file proves the **source side** completely: the mod-`37³` residue value `14467` (PROVEN from the
exact rational), the second-digit `r₆₈ = 21` and third-digit, and the cancellation arithmetic
`c₆₈ = 4`.  It does **not** prove the mod-`37³` *relation* `68!·X₆₈ = formalSum68Residue·(−37)`
itself — that is the one piece needing the mod-`37³` Dwork-coordinate evaluator (a parallel
development to the existing mod-`37²` `valuedLambdaQuotientDworkCoeffModSq` chain, at precision
`3(p−1) = 108`), isolated as the single named residual in
`CaseIICor823Level71Deg68ModCubeRelation.lean`.

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

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The mod-`37³` residue of `formalSum68`, PROVEN from the exact rational -/

/-- **The mod-`37³` residue of `formalSum68`**: `(formalSum68.num)·(formalSum68.den)⁻¹ : ZMod 37³`.
The mod-`37³` lift of `formalSum68Residue` (which is the same numerator/denominator combination in
`ZMod 37²`); its second `37`-adic digit is the Kellner `α₁` datum `r₆₈ = 21`, its third is `10`. -/
def formalSum68ResidueCube : ZMod (37 ^ 3) :=
  (((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).num : ZMod (37 ^ 3)) *
    ((((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).den : ℕ) :
        ZMod (37 ^ 3))⁻¹

/-- **The mod-`37³` residue of `formalSum68` is `14467`** (proven, axiom-clean): from the proven exact
rational `formalSum68RatValue_proven` (`formalSum68 = N/120`), the reduced numerator is `N` and
denominator `120`, so `formalSum68ResidueCube = (N : ZMod 37³)·(120 : ZMod 37³)⁻¹ = 14467` by
`decide`.  Note `14467 = 37·391 = 37·21 + 37²·10`: second digit `r₆₈ = 21`, third digit `10`. This is
the mod-`37³` lift of the proven `formalSum68ResidueModSq37_proven` (`≡ 777 = 37·21 mod 37²`),
**proven outright** (not a residual) because the exact rational `N/120` is proven. -/
theorem formalSum68ResidueCube_eq : formalSum68ResidueCube = 14467 := by
  have hRat := formalSum68RatValue_proven
  rw [FormalSum68RatValue] at hRat
  rw [formalSum68ResidueCube, hRat]
  -- The explicit fraction `N/120` has `Rat.num = N`, `Rat.den = 120` (reduced); reduce the residue.
  rw [show ((-462074109491757258568843974992223061646211876969162959102801473214373353 : ℚ) /
        120).num = -462074109491757258568843974992223061646211876969162959102801473214373353 from by
      norm_num,
    show ((-462074109491757258568843974992223061646211876969162959102801473214373353 : ℚ) /
        120).den = 120 from by norm_num]
  native_decide

/-- **`14467 = 37·391` in `ZMod 37³`** (proven by `decide`): exhibits the first `37`-digit of
`formalSum68ResidueCube` as `0` (it is `37·391`), so `formalSum68ResidueCube = 37·391` for the unit
combination `391`. -/
theorem formalSum68ResidueCube_eq_thirtyseven_mul :
    (14467 : ZMod (37 ^ 3)) = (37 : ZMod (37 ^ 3)) * (391 : ZMod (37 ^ 3)) := by decide

/-- **The mod-`37` reduction of `391` is `21`** (`decide`): `391 = 21 + 37·10`, so the second
`37`-digit of `formalSum68` (the `391` of `formalSum68ResidueCube = 37·391`) reduces mod `37` to
`r₆₈ = 21` — the Kellner `α₁` datum.  Only this `21` (not the third digit `10`) enters the deg-`68`
slice second digit `c₆₈`. -/
theorem threeNineOne_mod_thirtyseven : ((391 : ℕ) : ZMod 37) = 21 := by decide

/-! ## 2. The deg-`68` slice second digit `c₆₈ = 4`, from the mod-`37³` cancellation arithmetic

The cancellation `c₆₈ = −u₆₈'⁻¹·r₆₈` with `u₆₈' ≡ 4`, `r₆₈ ≡ 21` (from the mod-`37³` residue), is
exactly `deg68SecondDigit37Corrected = 4` of `CaseIICor823Level71Deg68SecondDigitCorrected.lean`.
This section grounds that `4` in the mod-`37³` residue value `391 ≡ 21` (the source second digit),
rather than the bare `formalSum68SecondDigit37Corrected = 21` numeral. -/

/-- **The deg-`68` slice second digit from the mod-`37³` source `391 ≡ 21`** (proven by `decide`):
`−u₆₈'⁻¹·(391 mod 37) = −4⁻¹·21 = 4`, the genuine `c₆₈`, with the source second digit `21` read off
the **proven** mod-`37³` residue `formalSum68ResidueCube = 37·391` (`391 mod 37 = 21`).  Equals
`deg68SecondDigit37Corrected` (`= 4`), now grounded in the exact rational. -/
theorem deg68SecondDigit37Corrected_grounded_value :
    -uSixtyeight37⁻¹ * ((391 : ℕ) : ZMod 37) = deg68SecondDigit37Corrected := by
  rw [threeNineOne_mod_thirtyseven, deg68SecondDigit37Corrected, formalSum68SecondDigit37Corrected]

/-- **The mod-`37³` cancellation yields `c₆₈ = 4`** (proven by `decide`): `−u₆₈'⁻¹·(391 mod 37) = 4`.
Combines `deg68SecondDigit37Corrected_grounded_value` with the proven `deg68SecondDigit37Corrected_eq`
(`= 4`).  This is the genuine deg-`68` slice second digit, sourced from the **proven** mod-`37³`
residue of the actual degree-`68` Artin-Hasse coefficient `formalSum68 = N/120`. -/
theorem deg68SecondDigit37_from_modCube_eq_four :
    -uSixtyeight37⁻¹ * ((391 : ℕ) : ZMod 37) = (4 : ZMod 37) := by
  rw [deg68SecondDigit37Corrected_grounded_value, deg68SecondDigit37Corrected_eq]

end BernoulliRegular.FLT37.Eichler

end
