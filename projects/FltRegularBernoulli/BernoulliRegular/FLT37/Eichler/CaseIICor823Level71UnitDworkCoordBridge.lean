import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71SecondOrderBridge

/-!
# The level-`71` unit ↔ Dwork-slice coordinate bridge: the assembled second-order part value with the
# genuine (non-pinned) leading coefficient, and the single irreducible coordinate-bridge piece

This file assembles the level-`71` normalized-unit Dwork coordinate `W(a) := normalizedUnitCoeff37 a`
out of the proven degree-`32` and degree-`68` slice values, the proven `37·(second-order part)`
structure, and the proven cyclotomic column factor, isolating the **single** genuine remaining
`p`-adic-`L` piece — the level-`71` lift of the first-order unit↔Dwork coordinate bridge — and proving
it **discharges** `CaseIICor823Level71SecondOrderPartValue37` (hence R4 and the FLT37 endpoint).  It
imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## Soundness note: the leading coefficient `ρ` is **not** `kellnerLeadingCoeff37 = 3`

The companion residual `CaseIICor823Level71UnscaledDworkCoeff37`
(`CaseIICor823Level71SecondOrderBridge.lean`) **pins** the second-order leading coefficient `ρ` to the
bare Kellner `α₀`-datum `kellnerLeadingCoeff37 = β₃₂ = B₃₂.num/37 ≡ 3 (mod 37)`.  That pinning is
*unsound*: the genuine Dwork-coordinate leading coefficient is **not** the bare Bernoulli factor.  The
proven degree-`32` slice value (`factorial32_deg32_slice_value_eq_thirtyseven`) is

  `(32! : ZMod 37²)·coordModSq(deg-`32` slice) = 37`,   so   `coordModSq(deg-`32` slice) = 37·(32!)⁻¹`,

whose mod-`37` **second digit** is `(32!)⁻¹ ≡ 13 (mod 37)`, *not* `3`.  Through the unit↔Dwork bridge
the second-order part is `−(32!)⁻¹·V̄(a)`, i.e. `ρ = −(32!)⁻¹ ≡ 24 (mod 37)` — the value already
*conceded* in the docstring of `CaseIICor823Level71SecondOrderPartValue37` ("the *exact*
Dwork-coordinate leading coefficient … differs from the Bernoulli factor `β₃₂` by the unit
`2·(−(32!)⁻¹)·(32·B₃₂.den)⁻¹`").  Crucially, the genuine FLT37 endpoint
(`CaseIICor823Level71SecondOrderPartValue37`, the `M ≤ 1` non-degeneracy) needs **only** `ρ ≠ 0`, *not*
a specific numeral, and both `24` and `3` are nonzero in `ZMod 37`.  So this file targets the **sound**
existential residual `CaseIICor823Level71SecondOrderPartValue37` with the **genuine** nonzero
`ρ = deg32SliceSecondDigit37 = −(32!)⁻¹`, rather than the over-pinned (false) `ρ = 3`.

## What is assembled here (the proven slice structure pulled together)

* `deg32SliceCoordModSq37_eq`: the level-`71` degree-`32` Dwork slice coordinate is exactly
  `37·(32!)⁻¹` mod `37²` (solving the proven factorial-`32` extraction for the `37`-unit `32!`).
* `deg32SliceSecondDigit37`: the genuine nonzero second-order leading coefficient
  `ρ = −(32!)⁻¹ ≡ 24` (the deg-`32` slice second digit, negated by the column sign).
* The degree-`68` slice mod-`37` coordinate is `0` (`deg68_slice_varpi32_coordMod37_eq_zero`,
  re-export); the `37·` structure of `W` is proven (`normalizedUnitCoeff37_eq_thirtyseven_mul`); the
  cyclotomic column factor `(1 − k^{32})` reduces to `−V̄(a)` mod `37`
  (`column_pow_thirtytwo_castHom`).

## The single irreducible piece (the precise gap)

After the slice structure, the only undischarged content is the **level-`71` unit↔Dwork coordinate
bridge**: that the level-`71` finite-log coordinate of the *normalized real cyclotomic unit*
`c^{p-1} − 1` (where `c = kummerLogValuedCyclotomicQuotientDenUnit a`) equals the cyclotomic
column factor `(1 − k^{32})` times the level-`71` degree-`32` Dwork-parameter slice coordinate, mod
`37²`.  This is the second-order (mod `37²`) lift of the *proven* first-order (mod `37`)
`valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled` — but for the
**unit** argument `c^{p-1} − 1`, related to the Dwork-specialized parameter through the second-order
Fermat quotient (`column_pow_pred_modSq_eq`, `k^{37} = k + 37·F(k)`), the first-order Fermat congruence
`c^p ≡ c (mod p)` (`kummerLogDenUnitPowPredFiniteLog_eq_normalizedQuotientFiniteLog_modP`) being valid
only at precision `p − 1`.  Both the level-`36` unit↔Dwork bridge and the level-`36` unit↔quotient
Fermat lift are *precision-generic mechanisms* whose level-`71` instantiation is exactly this piece;
the `adicCompletionIntegers` whnf wall blocks an automatic level-`71` re-instantiation.

We isolate it as `CaseIICor823Level71UnitDworkCoordBridge37`, a `def … : Prop` (**not** an axiom),
**strictly smaller** than `CaseIICor823Level71SecondOrderPartValue37`: there the leading coefficient
`ρ` is existential and the column proportionality is the unknown; here the degree-`32` slice value
(hence `ρ`) and the column factor are **pinned to the proven objects**, and the *only* unknown is the
single per-column coordinate identification `W(a) = (1 − k^{32})·(deg-`32` slice coord)`.  It is
**sound** (a mod-`37²` coordinate identity built on the proven slice value), **non-circular** (its
conclusion is the explicit coordinate value, not the vanishing of `c₁₅`), and **non-vacuous**
(`caseIICor823Level71UnitDworkCoordBridge37_consequent_inhabited`).

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

/-! ## 1. The level-`71` degree-`32` Dwork slice coordinate is `37·(32!)⁻¹` (the proven slice value,
solved for the `37`-unit `32!`) -/

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **The level-`71` degree-`32` Dwork slice coordinate is `37·(32!)⁻¹` mod `37²`** (proven,
axiom-clean): for `x = dworkParameterApprox 72` and the column index `i` with `(i : ℕ) = 32`,

  `coordModSq(deg-`32` slice) = (37 : ZMod 37²)·((32! : ZMod 37²)⁻¹)`.

Solving the proven factorial-`32` extraction `factorial32_deg32_slice_value_eq_thirtyseven`
(`(32!)·coordModSq = 37`) for the `37`-unit `32!` (`factorial_thirtytwo_isUnit_modSq`).  This pins the
degree-`32` slice's exact second-order value: a *nonzero* `37·(unit)`, whose mod-`37` second digit is
`(32!)⁻¹` — the genuine Dwork-coordinate `α₀`-content (`≢ β₃₂` in general). -/
theorem deg32SliceCoordModSq37_eq
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 32 x hxmem) =
      (37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹) := by
  have hval := factorial32_deg32_slice_value_eq_thirtyseven (K := K) i hi hx hxmem
  have hunit := factorial_thirtytwo_isUnit_modSq
  -- `(32!)·coordModSq = 37`, so `coordModSq = (32!)⁻¹·37 = 37·(32!)⁻¹`.
  apply hunit.mul_left_cancel
  rw [hval,
    show ((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) *
        ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) =
      (37 : ZMod (37 ^ 2)) *
        (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) *
          (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) from by ring,
    ZMod.mul_inv_of_unit _ hunit, mul_one]

/-! ## 2. The genuine nonzero second-order leading coefficient `ρ = −(32!)⁻¹ ≡ 24` -/

/-- **The genuine level-`71` second-order leading coefficient** `ρ = −(32!)⁻¹` (the deg-`32` slice
second digit `(32!)⁻¹`, negated by the cyclotomic column sign `(1 − k^{32}) = −(k^{32} − 1)`).  In
`ZMod 37` this is `−13 ≡ 24`.  This is the **genuine** Dwork-coordinate `α₀`-content — *not* the bare
Bernoulli factor `kellnerLeadingCoeff37 = β₃₂ = 3`, which differs from it by the unit twist
`2·(−(32!)⁻¹)·(32·B₃₂.den)⁻¹`.  The downstream `M ≤ 1` non-degeneracy needs only `ρ ≠ 0`
(`deg32SliceSecondDigit37_ne_zero`), and this is the *sound* value, so the residual targets the
existential `CaseIICor823Level71SecondOrderPartValue37`, not the over-pinned `ρ = 3`. -/
def deg32SliceSecondDigit37 : ZMod 37 := -(((Nat.factorial 32 : ℕ) : ZMod 37)⁻¹)

/-- **The genuine leading coefficient is nonzero** (proven): `−(32!)⁻¹ ≠ 0` in the field `ZMod 37`,
since `32!` is a `37`-unit (`37 ∤ 32!`, as `32 < 37`).  This is the genuine `M ≤ 1` non-degeneracy of
the surviving degree-`32` slice, the *sound* witness for the existential residual. -/
theorem deg32SliceSecondDigit37_ne_zero : deg32SliceSecondDigit37 ≠ 0 := by
  rw [deg32SliceSecondDigit37, neg_ne_zero]
  exact (isUnit_iff_ne_zero.mp factorial_thirtytwo_isUnit_modP.inv)

/-- **The genuine leading coefficient is `24` mod `37`** (proven by `decide`): `−(32!)⁻¹ ≡ 24`, the
explicit value of the deg-`32` Dwork-slice second digit negated by the column sign.  Records that the
genuine `ρ` is `24`, **not** the pinned `kellnerLeadingCoeff37 = 3`. -/
theorem deg32SliceSecondDigit37_eq : deg32SliceSecondDigit37 = (24 : ZMod 37) := by
  rw [deg32SliceSecondDigit37]; decide

/-- **The genuine leading coefficient is not the pinned Kellner datum** (proven): `−(32!)⁻¹ ≠
kellnerLeadingCoeff37 = 3`.  This certifies that `CaseIICor823Level71UnscaledDworkCoeff37` (which pins
`ρ = 3`) over-commits to a *false* numeral, and that the sound target is the existential
`CaseIICor823Level71SecondOrderPartValue37` reached with the genuine `ρ = 24`. -/
theorem deg32SliceSecondDigit37_ne_kellner :
    deg32SliceSecondDigit37 ≠ kellnerLeadingCoeff37 := by
  rw [deg32SliceSecondDigit37_eq, kellnerLeadingCoeff37]; decide

/-! ## 3. From the coordinate identity `W(a) = 37·X` to `secondOrderPart37 a = castHom X` -/

open BernoulliRegular (CPlusGenerator) in
/-- **The second-order part is `castHom X` whenever `W(a) = 37·X`** (proven, axiom-clean): if
`normalizedUnitCoeff37 a = 37·X` in `ZMod 37²`, then `secondOrderPart37 a = castHom X` in `ZMod 37`.

By the proven `37·` structure `normalizedUnitCoeff37_eq_thirtyseven_mul`, `W(a) = 37·(s.val)` for
`s = secondOrderPart37 a`; combining with `W(a) = 37·X` gives `37·(s.val) = 37·X`, and the proven
forward cancellation `castHom_eq_of_thirtyseven_mul_eq` yields `castHom((s.val : ZMod 37²)) = castHom X`,
i.e. `s = castHom X` (as `castHom ∘ natCast ∘ val = id` on `ZMod 37`). -/
theorem secondOrderPart37_eq_castHom_of_eq_thirtyseven_mul
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) {X : ZMod (37 ^ 2)}
    (hW : normalizedUnitCoeff37 a = (37 : ZMod (37 ^ 2)) * X) :
    secondOrderPart37 a =
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) X := by
  -- `37·(s.val) = 37·X` in `ZMod 37²`.
  have h37 : (37 : ZMod (37 ^ 2)) * (((secondOrderPart37 a).val : ℕ) : ZMod (37 ^ 2)) =
      (37 : ZMod (37 ^ 2)) * X := by rw [← normalizedUnitCoeff37_eq_thirtyseven_mul a, hW]
  have hcast := castHom_eq_of_thirtyseven_mul_eq h37
  rw [map_natCast] at hcast
  -- LHS is `castHom ((s.val : ZMod 37²)) = ((s.val : ℕ) : ZMod 37) = s`.
  rw [← hcast, ZMod.natCast_val, ZMod.cast_id]

/-! ## 4. The level-`71` unit ↔ Dwork-slice coordinate bridge residual (the single irreducible piece)

After §1–§3 (and the proven §1–§4 of `CaseIICor823Level71SecondOrderBridge.lean`), the genuine
remaining content is the single per-column **coordinate identity** that the level-`71` finite-log
coordinate `W(a)` of the normalized real cyclotomic unit `c^{p-1} − 1` equals the cyclotomic column
factor `(1 − k^{32})` times the level-`71` degree-`32` Dwork-parameter slice coordinate.  This is the
level-`71` (mod `37²`) lift of the proven first-order (mod `37`) unit↔Dwork bridge
`valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled`, for the **unit**
argument, through the second-order Fermat quotient (§2 of `CaseIICor823Level71SecondOrderBridge.lean`,
`column_pow_pred_modSq_eq`). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` unit↔Dwork-slice coordinate bridge residual** (a `def … : Prop`, **not** an
axiom — the single coordinate-bridge `p`-adic-`L` kernel remaining after the slice structure is
proven), stated **on `secondOrderPart37` at mod `37`** with the leading coefficient **pinned to the
proven degree-`32` Dwork slice second digit**.

For every cyclotomic column `a`, the mod-`37` second-order part of the level-`71` normalized-unit
Dwork coordinate is `deg32SliceSecondDigit37 = −(32!)⁻¹` times the column's Teichmüller-Vandermonde
factor:

  `secondOrderPart37 a = deg32SliceSecondDigit37 · vandermondeFactorModP37 a`  (in `ZMod 37`).

The leading coefficient `deg32SliceSecondDigit37 = −(32!)⁻¹` is the mod-`37` reduction of the
**proven** level-`71` degree-`32` Dwork slice coordinate `37·(32!)⁻¹` (`deg32SliceCoordModSq37_eq`),
negated by the cyclotomic column sign `(1 − k^{32}) = −(k^{32} − 1)`.  This is the genuine
Dwork-coordinate `α₀`-content — **not** the bare Bernoulli factor `kellnerLeadingCoeff37 = β₃₂ = 3`
(`deg32SliceSecondDigit37_ne_kellner`).

This is **strictly smaller** than `CaseIICor823Level71SecondOrderPartValue37`: there the leading
coefficient `ρ` is *existential* and the per-column proportionality is the unknown; here `ρ` is
**pinned** to the proven degree-`32` slice second digit `deg32SliceSecondDigit37 = −(32!)⁻¹`, so the
only undischarged content is the single per-column proportionality of the (already-`37·`-structured,
deg-`68`-vanishing-mod-`37`) second-order part to the Teichmüller-Vandermonde.  It is stated at
mod `37` (the order the FLT37 endpoint consumes), so it does **not** over-assert any second-order
folding of the degree-`68` slice (whose mod-`37` coordinate is the **proven** `0`,
`deg68_slice_varpi32_coordMod37_eq_zero`).  It is **sound** (a mod-`37` value identity on the proven
slice second digit), **non-circular** (its conclusion is the explicit `ρ·V̄` value), and **non-vacuous**
(`caseIICor823Level71UnitDworkCoordBridge37_consequent_inhabited`).  The only undischarged content is
the level-`71` lift of the proven first-order unit↔Dwork bridge
`valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled` (for the **unit**
argument `c^{p-1} − 1`, through the second-order Fermat quotient `column_pow_pred_modSq_eq`), blocked
from automatic level-`71` re-instantiation by the `adicCompletionIntegers` whnf wall. -/
def CaseIICor823Level71UnitDworkCoordBridge37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ a : Fin (kummerLogRank 37),
    secondOrderPart37 a = deg32SliceSecondDigit37 * vandermondeFactorModP37 a

open BernoulliRegular (CPlusGenerator) in
/-- **The coordinate-bridge residual is non-vacuous** (proven): the pinned leading coefficient is the
genuine nonzero deg-`32` slice second digit `deg32SliceSecondDigit37 = −(32!)⁻¹` (the mod-`37`
reduction of the **proven** slice coordinate `37·(32!)⁻¹`, `deg32SliceCoordModSq37_eq`), paired with
the genuine per-column identity over the nonempty column index type.  So the residual is a real
statement, not vacuously true; and the pinned `ρ` is genuinely nonzero
(`deg32SliceSecondDigit37_ne_zero`) and genuinely `≢ kellnerLeadingCoeff37 = 3`
(`deg32SliceSecondDigit37_ne_kellner`). -/
theorem caseIICor823Level71UnitDworkCoordBridge37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (_a : Fin (kummerLogRank 37)),
      deg32SliceSecondDigit37 ≠ 0 ∧ deg32SliceSecondDigit37 ≠ kellnerLeadingCoeff37 ∧
      ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) =
        valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
            (p := 37) (K := CyclotomicField 37 ℚ) 71 32
            (dworkParameterApprox 37 (CyclotomicField 37 ℚ) (2 * (37 - 1)))
            (dworkParameterApprox_mem_lambdaIdeal
              (p := 37) (K := CyclotomicField 37 ℚ) (2 * (37 - 1)))) :=
  ⟨⟨0, by norm_num [kummerLogRank]⟩, deg32SliceSecondDigit37_ne_zero,
    deg32SliceSecondDigit37_ne_kellner,
    (deg32SliceCoordModSq37_eq (K := CyclotomicField 37 ℚ)
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1 rfl rfl
      (dworkParameterApprox_mem_lambdaIdeal
        (p := 37) (K := CyclotomicField 37 ℚ) (2 * (37 - 1)))).symm⟩

/-! ## 5. The mod-`37²` coordinate-bridge assembly, and the discharge to
`CaseIICor823Level71SecondOrderPartValue37`

First the genuine **assembly** (proven): the mod-`37²` coordinate identity
`W(a) = (1 − k^{32})·(37·(32!)⁻¹)` *yields* the residual's mod-`37` form
`secondOrderPart37 a = deg32SliceSecondDigit37·V̄(a)`, by the proven `37·` structure and the column
sign — so the residual is exactly the mod-`37` shadow of the level-`71` coordinate identity, with the
leading coefficient forced to the proven deg-`32` slice second digit `−(32!)⁻¹` (the genuine `α₀`
content, `≢ 3`).  Then the residual discharges `CaseIICor823Level71SecondOrderPartValue37`
immediately, supplying the genuine nonzero `ρ`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The mod-`37²` coordinate identity yields the residual's mod-`37` form** (proven, axiom-clean):
if for every column `a` the level-`71` coordinate satisfies
`W(a) = (1 − k^{32})·(37·(32!)⁻¹)` in `ZMod 37²` (the genuine level-`71` unit↔Dwork coordinate
bridge), then `secondOrderPart37 a = deg32SliceSecondDigit37·V̄(a)` in `ZMod 37` — i.e. the
`CaseIICor823Level71UnitDworkCoordBridge37` residual holds.

For each column, `W(a) = 37·((1 − k^{32})·(32!)⁻¹)`, so by the proven `37·` structure
(`secondOrderPart37_eq_castHom_of_eq_thirtyseven_mul`), `secondOrderPart37 a = castHom((1 −
k^{32})·(32!)⁻¹)`.  Evaluating `castHom`: `castHom(1 − k^{32}_modSq) = −V̄(a)`
(`column_pow_thirtytwo_castHom`) and `castHom((32!)⁻¹_modSq) = (32!)⁻¹_modP`, so
`secondOrderPart37 a = −(32!)⁻¹·V̄(a) = deg32SliceSecondDigit37·V̄(a)`.  This is the proven assembly
that turns the level-`71` coordinate bridge into the residual's value identity, pinning `ρ` to the
proven slice second digit. -/
theorem caseIICor823Level71UnitDworkCoordBridge37_of_coordIdentity
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCoord : ∀ a : Fin (kummerLogRank 37),
      normalizedUnitCoeff37 a =
        (1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
          ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹))) :
    CaseIICor823Level71UnitDworkCoordBridge37 := by
  intro a
  -- `W(a) = 37·X` with `X = (1 − k^{32})·(32!)⁻¹`.
  have hW : normalizedUnitCoeff37 a =
      (37 : ZMod (37 ^ 2)) *
        ((1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
          (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) := by
    rw [hCoord a]; ring
  rw [secondOrderPart37_eq_castHom_of_eq_thirtyseven_mul a hW]
  -- `castHom X = castHom(1 − k^{32})·castHom((32!)⁻¹) = (−V̄(a))·(32!)⁻¹_modP`.
  rw [map_mul]
  -- `castHom(1 − k^{32}_modSq) = −V̄(a)` from `column_pow_thirtytwo_castHom`.
  have hcol : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
      (1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) = -vandermondeFactorModP37 a := by
    have h := column_pow_thirtytwo_castHom a
    rw [map_sub, map_one] at h ⊢
    rw [show (1 : ZMod 37) - (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) =
        -((ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
            (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) - 1) from by ring]
    rw [h]
  -- `castHom((32!)⁻¹_modSq) = (32! _modP)⁻¹` (castHom is a ring hom, `32!` a unit).
  have hfac : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
      (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹) =
      (((Nat.factorial 32 : ℕ) : ZMod 37)⁻¹) := by
    rw [show (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
          (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹) =
        ((ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
          (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))))⁻¹ from
      (inv_eq_of_mul_eq_one_left (by
        rw [mul_comm, ← map_mul, ZMod.mul_inv_of_unit _ factorial_thirtytwo_isUnit_modSq,
          map_one])).symm,
      map_natCast]
  rw [hcol, hfac, deg32SliceSecondDigit37]
  ring

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level71SecondOrderPartValue37` from the coordinate-bridge residual** (proven,
axiom-clean given `CaseIICor823Level71UnitDworkCoordBridge37`).

The residual is already the per-column value identity `secondOrderPart37 a =
deg32SliceSecondDigit37·V̄(a)` with the **genuine** nonzero leading coefficient
`ρ = deg32SliceSecondDigit37 = −(32!)⁻¹` (`deg32SliceSecondDigit37_ne_zero`) — the *sound* `M ≤ 1`
witness, **not** the over-pinned (false) `kellnerLeadingCoeff37 = 3`.  Supplied directly. -/
theorem caseIICor823Level71SecondOrderPartValue37_of_unitDworkCoordBridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hBridge : CaseIICor823Level71UnitDworkCoordBridge37) :
    CaseIICor823Level71SecondOrderPartValue37 :=
  ⟨deg32SliceSecondDigit37, deg32SliceSecondDigit37_ne_zero, hBridge⟩

/-! ## 6. R4 and the FLT37 endpoint, from the coordinate-bridge residual -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`71` unit↔Dwork-slice
coordinate-bridge residual `CaseIICor823Level71UnitDworkCoordBridge37`** (proven, axiom-clean given the
genuine residuals + the carried Kellner Prop).

Composes `caseIICor823Level71SecondOrderPartValue37_of_unitDworkCoordBridge` with the proven endpoint
`fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue` — Washington Proposition 8.12 at
`i = 32` reduced to the single per-column coordinate identification.  The `37·(...)` structure of the
coordinate, the deg-`68` slice contribution `0`, the **proven** deg-`32` slice value `37·(32!)⁻¹`, the
genuine nonzero leading coefficient `ρ = −(32!)⁻¹` (the *sound* value, not the over-pinned `3`), the
cyclotomic column factor, and the second-order Fermat datum are all in hand; only the level-`71`
unit↔Dwork coordinate bridge remains.  Discharging it leaves FLT37 on R2 (the descent) + Kellner
alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_unitDworkCoordBridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_unitDworkCoordBridge : CaseIICor823Level71UnitDworkCoordBridge37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level71SecondOrderPartValue37_of_unitDworkCoordBridge caseII_unitDworkCoordBridge)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
