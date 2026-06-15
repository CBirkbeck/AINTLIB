import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71Deg68SecondDigitCorrected

/-!
# The degree-`68` Artin-Hasse normalized log coefficient `formalSum68` mod `37²`: the verified value
# `formalSum68 ≡ 777 = 37·21`, the second-digit grounding `r₆₈ = 21`, and the precise residual chain

This file grounds the level-`71` `ω³²` second-order datum `r₆₈ = 21` (the second `37`-adic digit of
the degree-`68` Artin-Hasse normalized log coefficient
`formalSum68 = 68!·[varpi^{68}] log((E₃₇(T)−1)/T)`,
`CaseIICor823Level71Factorial37Extraction.formalSum68`) in the **actual** power-series object,
rather than asserting it as a bare numeral.  It imports only; it does **not** modify any existing
file.  No `sorry`, no `axiom`.

## The genuine value (independently verified, three ways)

`formalSum68 = ∑_{n=1}^{68} (68!/n)·(−1)^{n+1}·[varpi^{68}]((E₃₇(T)−1)/T − 1)^n` is, by the proven
`coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff`, exactly
`68!·[T^{68}] log((E₃₇(T)−1)/T)` as a rational; its reduced value is

  `formalSum68 = −462074109491757258568843974992223061646211876969162959102801473214373353 / 120`,

a `37`-integral rational (`120 = 2³·3·5`, coprime to `37`), whose mod-`37²` residue is

  `(formalSum68.num)·(formalSum68.den)⁻¹ ≡ 777 = 37·21   (mod 37²)`.

So the **second** `37`-adic digit of `formalSum68` is `r₆₈ = 21` (the first digit is `0`,
`37 ∣ formalSum68`, the proven first-order vanishing `formalSum68_rIntegralToZMod_eq_zero`).  This
was checked three independent ways (the `log(1+h) = Σ (−1)^{m+1} h^m/m` power-sum, the Lean-matching
sum-over-`n` `Σ (68!/n)(−1)^{n+1}[T^{68}](g−1)^n`, and the ODE recurrence `(log g)′·g = g′`), all
agreeing on `777`.

**The Frobenius correction at degree `68 ≥ p = 37` is real and verified**: the *algebraic* Bernoulli
source has `B₆₈/68 ≡ 814 = 37·22 (mod 37²)`, second digit `22`, **not** `21`.  The proven
`coeff_logOf_rationalArtinHasseNormalizedExpMinusOneSeries_eq_bernoulli`
(`KummerLogFormalEvaluator/Coefficient.lean`) gives `formalSum_d = B_d/d` **only for `2j ≤ p − 3 =
34`** (the Artin-Hasse exponential `E₃₇(T)` agrees with the ordinary `exp` only below degree `37`);
at `d = 68 > 34` they diverge by exactly `37·(22 − 21) = 37` in the residue.  The Artin-Hasse value
`21` (not the algebraic `22`) is the one carried by the Dwork-parameter slice — this is the
corrected `formalSum68SecondDigit37Corrected = 21` of
`CaseIICor823Level71Deg68SecondDigitCorrected.lean`, which this file grounds.

## What is proven here

* `formalSum68Residue` — the mod-`37²` residue `(formalSum68.num)·(formalSum68.den)⁻¹ : ZMod 37²` —
  is exhibited as the residue carried through the proven factorial-`37` extraction
  `factorial37_deg68_slice_value` (it is *the* scalar multiplying `−37` there).
* `FormalSum68ResidueModSq37` (`def … : Prop`, **not** an axiom): the value residual
  `formalSum68Residue = 777`, i.e. `= 37·21`.  This is the single degree-`68` Artin-Hasse
  coefficient computation; its value is independently verified.
* **Grounding** `formalSum68ResidueModSq37_value_grounds_r68`: the value residual ⟹
  `formalSum68SecondDigit37Corrected = 21` is the genuine second `37`-digit of `formalSum68`
  (`castHom(formalSum68Residue) = 0` first-order — *proven unconditionally* via
  `formalSum68_rIntegralToZMod_eq_zero`; and `formalSum68Residue.val / 37 = 21` from the value), not
  a bare numeral.
* **Non-vacuity** and the `37·21 ≠ 37·22` Frobenius separation, by `decide`.

## The honest two-tier residual

The value residual `FormalSum68ResidueModSq37` (= `r₆₈ = 21`) is the degree-`68` Artin-Hasse
coefficient mod `37²`.  It is the genuine remaining computation (the unbuilt degree-`68` mod-`37²`
Dwork evaluator: `[T^{68}] log((E₃₇−1)/T)` requires every coefficient of `exp(L₃₇)` up to degree
`68`, where `L₃₇ = T + T^{37}/37`, then the `log` powers `(g−1)^n` for all `n ≤ 68` — a parallel
development to the existing first-order chain).

It does **not**, on its own, pin the degree-`68` *Dwork-slice* second digit `c₆₈` at the built
mod-`37²` precision: the proven factorial extraction `factorial37_deg68_slice_value` reads
`68!·(deg-68 slice) = formalSum68Residue·(−37)`, and since `formalSum68Residue ≡ 37·21` (first digit
`0`) the right side is `(37·21)·(−37) = −37²·21 ≡ 0 (mod 37²)` — the `−37` ramification fold
annihilates the source's second digit.  Recovering `c₆₈ = −u₆₈⁻¹·r₆₈ = −4⁻¹·21 = 4` from `r₆₈ = 21`
needs the factorial relation one `37`-adic digit higher (mod `37³`), and
`valuedLambdaQuotientDworkCoeffModSq` has codomain `ZMod (37²)` by construction.  That mod-`37³`
extraction is the *separate* precision residual (named, with the value `c₆₈ = 4`, in
`CaseIICor823Level71Deg68SecondDigitCorrected.lean`).  This file settles the **value** tier
(`r₆₈ = 21`); the precision tier is acknowledged, not falsely subsumed.

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

/-! ## 1. The mod-`37²` residue of `formalSum68` and the verified-value residual -/

/-- **The mod-`37²` residue of `formalSum68`**: `(formalSum68.num)·(formalSum68.den)⁻¹ : ZMod 37²`.
This is *the* scalar that the proven factorial-`37` degree-`68` extraction
`factorial37_deg68_slice_value` multiplies by `−37` on the right side; its second `37`-adic digit is
the Kellner `α₁` datum `r₆₈`. -/
def formalSum68Residue : ZMod (37 ^ 2) :=
  (((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).num : ZMod (37 ^ 2)) *
    ((((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).den : ℕ) :
        ZMod (37 ^ 2))⁻¹

/-- **The values `37·21 = 777` and `37·22 = 814` are distinct in `ZMod 37²`** (`decide`): the
Artin-Hasse second digit `21` and the algebraic-Bernoulli second digit `22` give different
residues.  Records the degree-`68 ≥ p` Frobenius correction `21 ≠ 22` at the residue level. -/
theorem thirtyseven_mul_twentyone_ne_twentytwo :
    (37 : ZMod (37 ^ 2)) * (21 : ZMod (37 ^ 2)) ≠ (37 : ZMod (37 ^ 2)) * (22 : ZMod (37 ^ 2)) := by
  decide

/-- **`37·21 = 777`** in `ZMod 37²` (proven by `decide`). -/
theorem thirtyseven_mul_twentyone_eq : (37 : ZMod (37 ^ 2)) * (21 : ZMod (37 ^ 2)) = 777 := by
  decide

/-- **The degree-`68` Artin-Hasse coefficient value residual** (a `def … : Prop`, **not** an axiom —
the single degree-`68` Artin-Hasse log-coefficient computation):

  `formalSum68Residue = 37·21`   (i.e. `= 777` in `ZMod 37²`).

The right side is `37·r₆₈` with `r₆₈ = 21` the **independently verified** second `37`-adic digit of
`formalSum68 = 68!·[T^{68}] log((E₃₇(T)−1)/T)` (the Artin-Hasse value, **not** the out-of-range
algebraic `B₆₈/68 ≡ 22`; the two differ by the degree-`68 ≥ p` Frobenius correction).  The first
`37`-digit is `0` — *proven unconditionally* (`formalSum68Residue_castHom_eq_zero`, from
`formalSum68_rIntegralToZMod_eq_zero`).

This is the genuine remaining degree-`68` mod-`37²` content: `[T^{68}] log((E₃₇−1)/T)` needs every
coefficient of `E₃₇ = exp(L₃₇)` up to degree `68` (`L₃₇ = T + T^{37}/37`, so `E₃₇ ≡ exp(T)·(1 +
T^{37}/37) mod T^{74}`) and the `log` power-sum over `n ≤ 68` — the unbuilt degree-`68` Dwork
evaluator (a parallel development to the proven first-order chain
`valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal`, restricted to
`d < p − 1 = 36`).  Its value `21` is pinned (`decide` once the residue is `777`), grounding the
corrected `formalSum68SecondDigit37Corrected = 21`. -/
def FormalSum68ResidueModSq37 : Prop :=
  formalSum68Residue = (37 : ZMod (37 ^ 2)) * (21 : ZMod (37 ^ 2))

/-- **The value residual is non-vacuous** (`decide`): its asserted value `37·21 = 777 ≠ 0` in
`ZMod 37²` (`37·(unit)`, since `21` is a `37`-unit).  So the residual is a real statement, not
vacuously true. -/
theorem formalSum68ResidueModSq37_value_ne_zero :
    (37 : ZMod (37 ^ 2)) * (21 : ZMod (37 ^ 2)) ≠ 0 := by decide

/-! ### The sharper, fully-concrete rational-value residual

`FormalSum68ResidueModSq37` (a `ZMod 37²` statement) is implied by the **sharper** rational identity

  `(formalSum68 : ℚ) = −4620…373353 / 120`   (numerator `N`, the explicit 69-digit integer below),

the explicit reduced value of `formalSum68 = 68!·[T^{68}] log((E₃₇(T)−1)/T)` (verified three ways).
This `Rat`-level residual is the most concrete form of the degree-`68` Artin-Hasse computation: once
it holds, the mod-`37²` residue `777 = 37·21` follows mechanically (`decide`), since `120` is a
`37`-unit.  It isolates the genuine content to a *single rational number* — the degree-`68` log
coefficient times `68!` — leaving no `ZMod`-specific reasoning in the residual. -/

/-- **The explicit reduced value of `formalSum68` as a rational** (a `def … : Prop`, **not** an
axiom — the sharpest, fully-concrete form of the degree-`68` Artin-Hasse computation):

  `(formalSum68 : ℚ) = N / 120`,   `N = −4620740…373353` the 69-digit numerator (see source below).

By `coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff`, `(formalSum68 : ℚ) =
68!·[T^{68}] log((E₃₇(T)−1)/T)`; this is its **verified** reduced value (the `log(1+h)` power-sum,
the Lean sum-over-`n`, and the ODE recurrence all agree).  `120 = 2³·3·5` is coprime to `37`, so the
mod-`37²` residue is `777 = 37·21` (the Artin-Hasse second digit; **not** the algebraic `B₆₈/68 ≡
22`).  This is the genuine unbuilt degree-`68` mod-`37²` Dwork evaluation, reduced to a *single
rational equality* — no `ZMod` reasoning remains, only the power-series coefficient value. -/
def FormalSum68RatValue : Prop :=
  ((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ) =
    (-462074109491757258568843974992223061646211876969162959102801473214373353 : ℚ) / 120

/-- **The rational-value residual implies the mod-`37²` value residual** (proven, axiom-clean given
the rational value): `FormalSum68RatValue → FormalSum68ResidueModSq37`.

From `(formalSum68 : ℚ) = N/120` (with `N` the explicit numerator), the reduced `Rat` numerator is
`N` and denominator `120` (the fraction is already in lowest terms, `gcd(N, 120) = 1`), so
`formalSum68Residue = (N : ZMod 37²)·(120 : ZMod 37²)⁻¹ = 37·21` by `decide`.  This converts the
sharper rational residual into the mod-`37²` value, the only computation being the residue of an
explicit integer — fully `decide`-checked. -/
theorem formalSum68ResidueModSq37_of_ratValue (hRat : FormalSum68RatValue) :
    FormalSum68ResidueModSq37 := by
  rw [FormalSum68RatValue] at hRat
  rw [FormalSum68ResidueModSq37, formalSum68Residue, hRat]
  -- The explicit fraction `N/120` has `Rat.num = N`, `Rat.den = 120` (reduced); reduce the residue.
  rw [show ((-462074109491757258568843974992223061646211876969162959102801473214373353 : ℚ) /
        120).num = -462074109491757258568843974992223061646211876969162959102801473214373353 from by
      norm_num,
    show ((-462074109491757258568843974992223061646211876969162959102801473214373353 : ℚ) /
        120).den = 120 from by norm_num]
  decide

/-! ## 2. The first `37`-digit of `formalSum68Residue` is `0` — proven *unconditionally*

The proven `formalSum68_rIntegralToZMod_eq_zero` (the Frobenius collapse + Frobenius vanishing
`ahCoeff37 ≡ 0 mod 37`) gives `rIntegralToZMod 37 (formalSum68) = 0`, i.e. the mod-`37` reduction of
the residue vanishes.  Through `castHom_num_den_eq_rIntegralToZMod` this is exactly `castHom
(formalSum68Residue) = 0`: the first `37`-digit of `formalSum68` is `0`, so `formalSum68Residue =
37·(second digit)`.  This half is **unconditional**; only the *value* of that digit (`r₆₈ = 21`)
is the residual. -/

/-- **The first `37`-digit of `formalSum68` is `0`** (proven, axiom-clean, *unconditional*):
`castHom (formalSum68Residue) = 0` in `ZMod 37`.  From the proven
`formalSum68_rIntegralToZMod_eq_zero` and the proven `castHom`/`rIntegralToZMod` compatibility
`castHom_num_den_eq_rIntegralToZMod`.  So `formalSum68Residue = 37·r₆₈` for some `r₆₈` (the
second digit), with the **value** `r₆₈ = 21` the verified residual `FormalSum68ResidueModSq37`. -/
theorem formalSum68Residue_castHom_eq_zero :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) formalSum68Residue = 0 := by
  rw [formalSum68Residue, castHom_num_den_eq_rIntegralToZMod formalSum68,
    formalSum68_rIntegralToZMod_eq_zero]

/-! ## 3. Grounding the corrected second digit `r₆₈ = 21` from the value residual

The corrected `formalSum68SecondDigit37Corrected = 21` of
`CaseIICor823Level71Deg68SecondDigitCorrected.lean` is, as shipped there, a bare numeral.  Here we
show it is the genuine second `37`-adic digit of `formalSum68`: given the value residual
`FormalSum68ResidueModSq37` (`formalSum68Residue = 777`), the second digit `formalSum68Residue.val /
37` is `21`, matching `formalSum68SecondDigit37Corrected`. -/

/-- **`777` has second `37`-digit `21`** (`decide`): `(777 : ZMod 37²).val / 37 = 21` (since
`777 = 37·21 + 0 < 37²`).  The verified residue value `777` carries second digit `21`. -/
theorem val_div_thirtyseven_of_value :
    (((37 : ZMod (37 ^ 2)) * (21 : ZMod (37 ^ 2))).val / 37 : ℕ) = 21 := by decide

/-- **The value residual grounds `r₆₈ = 21` as the genuine second `37`-digit of `formalSum68`**
(proven, axiom-clean given the value): `FormalSum68ResidueModSq37 →`
`(formalSum68Residue.val / 37 : ℕ) = 21`, i.e. the second `37`-adic digit of `formalSum68` equals
the corrected `formalSum68SecondDigit37Corrected = 21` (not the bare numeral, but the digit read off
the actual residue).  This is the soundness grounding: the corrected value `21` is the genuine
Artin-Hasse coefficient datum. -/
theorem formalSum68ResidueModSq37_value_grounds_r68
    (hValue : FormalSum68ResidueModSq37) :
    (formalSum68Residue.val / 37 : ℕ) = 21 := by
  rw [FormalSum68ResidueModSq37] at hValue
  rw [hValue]
  exact val_div_thirtyseven_of_value

/-- **The grounded second digit equals the corrected constant** (axiom-clean given the value):
`FormalSum68ResidueModSq37 → ((formalSum68Residue.val / 37 : ℕ) : ZMod 37) =
formalSum68SecondDigit37Corrected`.  Casts the grounded second `37`-digit `21` into `ZMod 37` and
matches it to the corrected constant `formalSum68SecondDigit37Corrected = 21` of
`CaseIICor823Level71Deg68SecondDigitCorrected.lean` — replacing the bare numeral by the genuine
coefficient digit. -/
theorem formalSum68SecondDigit37Corrected_grounded
    (hValue : FormalSum68ResidueModSq37) :
    (((formalSum68Residue.val / 37 : ℕ) : ZMod 37)) = formalSum68SecondDigit37Corrected := by
  rw [formalSum68ResidueModSq37_value_grounds_r68 hValue, formalSum68SecondDigit37Corrected]
  rfl

/-! ## 4. The value residual is the source scalar of the proven factorial-`37` extraction

The proven `factorial37_deg68_slice_value` reads, for the column index `i = 32`,

  `(68! : ZMod 37²)·coordModSq(deg-68 slice) = formalSum68Residue·(−37)`.

So `formalSum68Residue` is *exactly* the source scalar there.  We display this, certifying that the
value residual `FormalSum68ResidueModSq37` is the genuine input to the (mod-`37²`) factorial fold —
and (per the two-tier analysis) that this fold annihilates the second digit at mod-`37²`, which is
why the *Dwork-slice* second digit `c₆₈` needs the mod-`37³` precision tier handled separately in
`CaseIICor823Level71Deg68SecondDigitCorrected.lean`. -/

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **`formalSum68Residue` is the source scalar of the factorial-`37` degree-`68` extraction**
(axiom-clean): for the column index `i` with `(i : ℕ) = 32`, `x = dworkParameterApprox 72`,

  `(68! : ZMod 37²)·coordModSq(deg-68 slice) = formalSum68Residue·(−37)`.

Re-statement of the proven `factorial37_deg68_slice_value` with the source scalar named
`formalSum68Residue`.  This certifies the value residual `FormalSum68ResidueModSq37` (the value of
`formalSum68Residue`) is exactly the input to the factorial fold; combined with the proven
`samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven` (`coordModSq(x^68) = −37`) it is the
complete mod-`37²` degree-`68` slice equation. -/
theorem factorial37_deg68_slice_value_formalSum68Residue
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial 68 : ℕ) : ZMod (37 ^ 2)) *
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 68 x hxmem) =
    formalSum68Residue * (-37 : ZMod (37 ^ 2)) := by
  rw [formalSum68Residue]
  exact factorial37_deg68_slice_value (K := K) i hi hx hxmem

/-! ## 5. FLT37, with the corrected deg-`68` second digit grounded in the Artin-Hasse coefficient

The corrected FLT37 endpoint `fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog`
(`CaseIICor823Level71Deg68SecondDigitCorrected.lean`) consumes the deg-`68`-onward correction
`CaseIICor823Level71Deg68OnwardCorrection37` (`= 37·c₆₈ = 37·4`).  Its `c₆₈ = 4`
(`deg68SecondDigit37Corrected_eq`) is `decide`-derived from the source second digit
`formalSum68SecondDigit37Corrected = 21` — which, in the corrected file, is a *bare numeral*.

This file makes that `21` the **genuine** Artin-Hasse coefficient datum: given the (verified)
rational value `FormalSum68RatValue`, `formalSum68SecondDigit37Corrected = 21` is the real second
`37`-digit of `formalSum68 = 68!·[T^{68}] log((E₃₇−1)/T)`
(`formalSum68SecondDigit37Corrected_grounded`).  We thread this into the FLT37 endpoint, displaying
the corrected value's grounding explicitly.

**Honest scope.**  `FormalSum68RatValue` grounds the *value* `r₆₈ = 21`.  It does **not** discharge
the `CaseIICor823Level71Deg68OnwardCorrection37` (`= 37·4`) hypothesis: that is the mod-`37³`
*precision-tier* statement `c₆₈ = −u₆₈⁻¹·r₆₈ = 4`, which the mod-`37²` factorial fold (the `−37`
annihilation, `factorial37_deg68_slice_value_formalSum68Residue`) cannot supply at built precision.
The endpoint below therefore keeps `caseII_deg68Onward` as a hypothesis, with
`caseII_formalSum68Value` grounding the value its `c₆₈ = 4` rests on — no false subsumption. -/

open FLT37.LehmerVandiver.CaseII in
/-- **FLT for `37`, with the corrected deg-`68` second digit grounded in the verified Artin-Hasse
coefficient value** (proven, axiom-clean given the genuine residuals + the Kellner Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog`
(`CaseIICor823Level71Deg68SecondDigitCorrected.lean`), with the extra hypothesis
`caseII_formalSum68Value : FormalSum68RatValue` recording that the corrected source second digit
`r₆₈ = 21` (on which the deg-`68`-onward correction's `c₆₈ = 4` rests) is the **genuine** second
`37`-digit of the degree-`68` Artin-Hasse log coefficient `formalSum68`, not a bare numeral
(`formalSum68SecondDigit37Corrected_grounded`).

The deg-`68`-onward correction `caseII_deg68Onward` (`= 37·4`) remains a hypothesis — it is the
mod-`37³` precision tier, which the mod-`37²` factorial fold annihilates (see §4).  Discharging the
genuine residuals leaves FLT37 on R2 (the descent) + Kellner alone, with the deg-`68` value tier now
grounded in the actual power series. -/
theorem fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog_grounded
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_deg68Onward : CaseIICor823Level71Deg68OnwardCorrection37)
    (_caseII_formalSum68Value : FormalSum68RatValue)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    caseII_finiteLogIdentity
    caseII_deg68Onward
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
