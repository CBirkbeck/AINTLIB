import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71DworkSpecializedReduction

/-!
# The SOUND structure of the level-`71` unscaled Dwork-parameter `varpi^{32}` coordinate: the proven
# degree-slice decomposition, and the precise irreducible degree-`68` second-digit residual

This file records the **sound** mod-`37²` value of the level-`71` unscaled Dwork-parameter coordinate
`valuedLambdaQuotientDworkCoeffModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71)` — *piece 2* of
`CaseIICor823Level71DworkSpecializedFiniteLog37`
(`CaseIICor823Level71DworkSpecializedReduction.lean`).  It imports only; it does **not** modify any
existing file.  No `sorry`, no `axiom`.

## Why *piece 2* as stated (`= 37·(32!)⁻¹`) is over-stated at mod-`37²`

`valuedLambdaQuotientDworkCoeffModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71)` is, by the
proven slice-sum decomposition
`valuedLambdaQuotientDworkCoeffModSq_dworkParameterNormalizedCoordFiniteLogN71_eq_sum`, the **sum over
all homogeneous degrees** `d ∈ range (samePrimeFiniteLogCutoff 71) = range 2664` of the degree-`d`
slice's `varpi^{32}` coordinate.  Through the ramification fold `varpi^{36} = -37·tailUnit`
(`dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`), a degree-`d` slice lands on the `varpi^{32}`
coordinate iff `d ≡ 32 (mod 36)`; within mod-`37²` precision **only** `d ∈ {32, 68}` survive
(`d ∈ {104, 140, …}` carry `(varpi^{36})^{≥ 2} = 37^{≥ 2}·(…) = 0 (mod 37²)`).  Hence

  `coordModSq 32 (unscaled) = (deg-`32` slice) + (deg-`68` slice) + (slices that vanish mod 37²)`.

The **deg-`32`** slice is exactly `37·(32!)⁻¹` (`deg32SliceCoordModSq37_eq`, proven).  The **deg-`68`**
slice is `37·c₆₈` with `c₆₈ ∈ ZMod 37` the bare degree-`68` second digit — the Kellner `α₁` content
(`B₆₈/68 ≡ 22 (mod 37)`; cf. `CaseIICor823Level72ColumnScaling` docstring "two genuine second-order
obstructions", and `CaseIICor823Level71NormalizedUnitValue` "degree-`68` … carries the `α₁`-datum").
Its mod-`37` value is the **proven** `0` (`deg68_slice_varpi32_coordMod37_eq_zero`), but its second
digit `c₆₈` is *not* pinned by the level-`71`/mod-`37²` factorial extraction: that extraction gives
`(68!)·(deg-`68` slice) = (formalSum₆₈ residue)·(-37)` (`factorial37_deg68_slice_value`), and since
`formalSum₆₈ residue ≡ 0 (mod 37)` the right side is `(37·r₆₈)·(-37) = -37²·r₆₈ = 0 (mod 37²)`, so the
relation degenerates to `37·(deg-`68` slice) = 0`, which pins only `castHom(deg-`68` slice) = 0` and
leaves `c₆₈` **free**.  The `-37` ramification fold annihilates the second digit `r₆₈` of the source.

So the **true** value of piece 2 is `37·((32!)⁻¹ + c₆₈)`, *not* `37·(32!)⁻¹`: piece 2 omits the
degree-`68` second-digit term.  Recovering `c₆₈` from the proven `α₁` requires the unscaled coordinate
to one more `37`-adic digit (mod `37³`, level `≥ 73`) — exactly the precision the proven low-degree
extraction `valuedLambdaQuotientDworkCoeffModP_factorPow_normalizedHomogeneousDegreeSum_…_of_lt`
cannot supply (it needs `d < p - 1 = 36` so `d!` is a `37`-unit; `d = 68` has `37 ∣ 68!`).

## What is proven here (the reachable sound structure)

We prove the **degree-slice decomposition of piece 2 with the proven deg-`32` value split off**:

  `coordModSq 32 (unscaled) − 37·(32!)⁻¹`
    `= ∑_{d ∈ range 2664, d ≠ 32} coordModSq 32 (deg-`d` slice)`,

an *unconditional, axiom-clean* identity (just the proven slice-sum minus the proven deg-`32` term).
The right side is the genuine correction term piece 2 wrongly asserts to be `0`; it contains the
degree-`68` slice `37·c₆₈` as a summand (`deg68SliceCoordModSq37_mem_correction`), whose mod-`37` value
is the proven `0` but whose second digit `c₆₈` is the precise irreducible Kellner-`α₁` residual.  This
makes the over-statement **machine-checkable**: piece 2 holds *iff* the proven correction sum is `0`.

## The precise irreducible residual

`CaseIICor823Level71Unscaled32Coord37` (`def … : Prop`, **not** an axiom): the *sound* form of piece 2
— a nonzero `ρ₀ : ZMod 37` with `coordModSq 32 (unscaled) = 37·(ρ₀.val)` and `ρ₀ = (32!)⁻¹ + c₆₈`.
This is the genuine `v_p(L₃₇(1, ω³²)) = 1` second-order `p`-adic-`L` content (the degree-`68`
homogeneous slice's second digit), *not* dischargeable at the currently-built level-`71`/mod-`37²`
precision.  We do **not** assert `caseIICor823Level71DworkSpecializedFiniteLog37_proven` (piece 2 is
false as stated, omitting `37·c₆₈`).

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

/-! ## 1. The degree-`d` slice coordinate of the level-`71` unscaled Dwork log

A convenience name for the `varpi^{32}` mod-`37²` coordinate of the degree-`d` homogeneous slice of the
level-`71` unscaled Dwork-parameter normalized finite log, the summand of the proven slice-sum
`valuedLambdaQuotientDworkCoeffModSq_dworkParameterNormalizedCoordFiniteLogN71_eq_sum`. -/

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **The `varpi^{32}` coordinate of the degree-`d` homogeneous slice of the level-`71` unscaled Dwork
log** (a name): `unscaled32SliceCoord K d` is the mod-`37²` `varpi^{32}` coordinate of the degree-`d`
slice of `dworkParameterNormalizedCoordFiniteLogN 71`, i.e. the `d`-summand of the proven slice-sum.
The even index `i = 32` is `(kummerLogEvenPowerIndex 15).1` (the irregular `ω^{32}` row). -/
def unscaled32SliceCoord (d : ℕ) : ZMod (37 ^ 2) :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K)
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
    (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
      (p := 37) (K := K) 71 d
      (dworkParameterApprox (p := 37) (K := K) (71 + 1))
      (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1)))

omit [NumberField.IsCMField K] in
/-- **The level-`71` unscaled `varpi^{32}` coordinate is the sum of the degree-slice coordinates**
(proven, axiom-clean): `coordModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71) =
∑_{d ∈ range 2664} unscaled32SliceCoord d`.  Specialisation of the proven `N`-generic slice-sum
`valuedLambdaQuotientDworkCoeffModSq_dworkParameterNormalizedCoordFiniteLogN71_eq_sum` to the even
index `i = 32`. -/
theorem unscaled32Coord_eq_sum :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := K) 71) =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := 37) 71),
        unscaled32SliceCoord (K := K) d :=
  valuedLambdaQuotientDworkCoeffModSq_dworkParameterNormalizedCoordFiniteLogN71_eq_sum
    (K := K) (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1

/-! ## 2. The proven degree-`32` slice value, on the `unscaled32SliceCoord` name -/

omit [NumberField.IsCMField K] in
/-- **The degree-`32` slice coordinate is `37·(32!)⁻¹`** (proven, axiom-clean), displayed on the
`unscaled32SliceCoord` name: `unscaled32SliceCoord 32 = 37·(32!)⁻¹`.  Re-export of the proven
`deg32SliceCoordModSq37_eq` (which solves the factorial-`32` extraction
`factorial32_deg32_slice_value_eq_thirtyseven` for the `37`-unit `32!`).  This is the **only** slice of
the sum whose value is known mod `37²`. -/
theorem unscaled32SliceCoord_thirtytwo_eq :
    unscaled32SliceCoord (K := K) 32 =
      (37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹) := by
  rw [unscaled32SliceCoord]
  exact deg32SliceCoordModSq37_eq (K := K)
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1 rfl rfl
    (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1))

/-! ## 3. The proven degree-`68` slice contribution: `castHom = 0`, but the second digit is the
genuine residual

The degree-`68` slice's mod-`37` `varpi^{32}` coordinate is the **proven** `0`
(`deg68_slice_varpi32_coordMod37_eq_zero`): its first `37`-digit vanishes, so it is `37·c₆₈`.  But its
second digit `c₆₈` — the Kellner `α₁` content — is *not* determined by the level-`71`/mod-`37²`
factorial extraction (the `-37` ramification fold annihilates the source's second digit), and is the
precise irreducible piece. -/

/-- **The degree-`68` slice coordinate has mod-`37` value `0`** (proven, axiom-clean), on the
`unscaled32SliceCoord` name (for `K = CyclotomicField 37 ℚ`, the field of the proven deg-`68` lemma):
`castHom (unscaled32SliceCoord 68) = 0`.  Re-export of the proven
`deg68_slice_varpi32_coordMod37_eq_zero`.  So `unscaled32SliceCoord 68 = 37·c₆₈` for a (genuine,
generally nonzero) second digit `c₆₈ ∈ ZMod 37` — the Kellner `α₁` (`B₆₈/68 ≡ 22`) content — which the
level-`71`/mod-`37²` factorial extraction does **not** pin. -/
theorem unscaled32SliceCoord_sixtyeight_castHom_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (unscaled32SliceCoord (K := CyclotomicField 37 ℚ) 68) = 0 := by
  rw [unscaled32SliceCoord]
  -- `deg68_slice_varpi32_coordMod37_eq_zero` is stated with `dworkParameterApprox (2*(37-1))`;
  -- `71 + 1 = 72 = 2*(37-1)` so the slice arguments coincide definitionally.
  exact deg68_slice_varpi32_coordMod37_eq_zero

/-! ## 4. The sound decomposition: the unscaled coordinate, with the proven deg-`32` value split off

The proven slice-sum (`§1`) with the proven deg-`32` value (`§2`) extracted as the single explicitly
known term, isolating the **correction sum** over `d ≠ 32` — the genuine content piece 2 wrongly
asserts to be `0`.  The degree-`68` slice (`§3`) is a summand of that correction sum. -/

omit [NumberField.IsCMField K] in
/-- **`32` is in the slice-sum range** (`32 < samePrimeFiniteLogCutoff 71 = 2664`).  Needed to split
the deg-`32` term off the proven slice-sum. -/
theorem thirtytwo_mem_cutoff_range :
    (32 : ℕ) ∈ Finset.range (samePrimeFiniteLogCutoff (p := 37) 71) := by
  rw [Finset.mem_range, samePrimeFiniteLogCutoff]; norm_num

omit [NumberField.IsCMField K] in
/-- **The sound degree-slice decomposition of piece 2** (proven, axiom-clean): the level-`71` unscaled
`varpi^{32}` coordinate, with the **proven** degree-`32` value `37·(32!)⁻¹` split off, equals the sum
of the remaining degree-slice coordinates:

  `coordModSq 32 (unscaled) = 37·(32!)⁻¹ + ∑_{d ∈ range 2664, d ≠ 32} unscaled32SliceCoord d`.

Unconditional consequence of the proven slice-sum (`unscaled32Coord_eq_sum`, `§1`) and the proven
degree-`32` value (`unscaled32SliceCoord_thirtytwo_eq`, `§2`), via `Finset.add_sum_erase`.  The
correction sum `∑_{d ≠ 32} …` is the genuine mod-`37²` content piece 2 (`= 37·(32!)⁻¹`) wrongly
asserts to be `0`; the degree-`68` slice `37·c₆₈` (`§3`) is one of its summands. -/
theorem unscaled32Coord_eq_thirtytwo_add_correction :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := K) 71) =
      (37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹) +
        ∑ d ∈ (Finset.range (samePrimeFiniteLogCutoff (p := 37) 71)).erase 32,
          unscaled32SliceCoord (K := K) d := by
  rw [unscaled32Coord_eq_sum (K := K), ← unscaled32SliceCoord_thirtytwo_eq (K := K)]
  exact (Finset.add_sum_erase _ (unscaled32SliceCoord (K := K)) thirtytwo_mem_cutoff_range).symm

omit [NumberField.IsCMField K] in
/-- **The degree-`68` slice is a summand of the correction sum** (proven, axiom-clean): `68` lies in
`(range 2664).erase 32`, so `unscaled32SliceCoord 68` is one of the terms of the correction sum of
`unscaled32Coord_eq_thirtytwo_add_correction`.  Combined with `§3`
(`unscaled32SliceCoord_sixtyeight_castHom_eq_zero`: its mod-`37` value is `0`, so it is `37·c₆₈`), this
exhibits the omitted second-order content `37·c₆₈` concretely inside the correction. -/
theorem sixtyeight_mem_correction :
    (68 : ℕ) ∈ (Finset.range (samePrimeFiniteLogCutoff (p := 37) 71)).erase 32 := by
  rw [Finset.mem_erase, Finset.mem_range, samePrimeFiniteLogCutoff]
  exact ⟨by norm_num, by norm_num⟩

/-! ## 5. The precise irreducible residual: the sound form of piece 2

`CaseIICor823Level71Unscaled32Coord37` is the **sound** form of *piece 2*: a nonzero `ρ₀ : ZMod 37`
with `coordModSq 32 (unscaled) = 37·(ρ₀.val)`, where `ρ₀ = (32!)⁻¹ + c₆₈` carries the degree-`68`
second digit.  It is the genuine `v_p(L₃₇(1, ω³²)) = 1` second-order `p`-adic-`L` content — the
degree-`68` homogeneous slice's second digit — *not* dischargeable at the built level-`71`/mod-`37²`
precision.  We do **not** assert the over-stated piece-2 value `37·(32!)⁻¹`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The sound level-`71` unscaled `varpi^{32}` coordinate residual** (a `def … : Prop`, **not** an
axiom) — the corrected *piece 2* with the degree-`68` second digit honestly folded in.

There is a mod-`37` scalar `ρ₀ : ZMod 37`, **nonzero**, with

  `valuedLambdaQuotientDworkCoeffModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71)`
    `= (37 : ZMod 37²)·(ρ₀.val : ZMod 37²)`.

`ρ₀` is the genuine second digit of the unscaled coordinate, `ρ₀ = (32!)⁻¹ + c₆₈` (the proven
degree-`32` slice second digit `(32!)⁻¹` plus the degree-`68` slice second digit `c₆₈`, the Kellner
`α₁` content; cf. `unscaled32Coord_eq_thirtytwo_add_correction` and
`unscaled32SliceCoord_sixtyeight_castHom_eq_zero`).  This is **strictly sound** vs the over-stated
piece 2 `= 37·(32!)⁻¹`, which omits the `37·c₆₈` term (provable iff `c₆₈ = 0`, which is false in
general).  The `37·` shape is correct (every contributing slice `d ∈ {32, 68}` has mod-`37` coordinate
`0`); only the second digit `ρ₀` and `ρ₀ ≠ 0` (i.e. `(32!)⁻¹ + c₆₈ ≠ 0`) are the genuine unknown — the
degree-`68` homogeneous slice's second digit, not built at level-`71`/mod-`37²`. -/
def CaseIICor823Level71Unscaled32Coord37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ₀ : ZMod 37, ρ₀ ≠ 0 ∧
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ) 71) =
      (37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2))

open BernoulliRegular (CPlusGenerator) in
/-- **The sound residual is non-vacuous** (proven): for a *nonzero* witness scalar `ρ₀` both sides are
genuine elements of `ZMod 37²`, and the right side `37·(ρ₀.val)` is itself nonzero whenever `ρ₀ ≠ 0`
(`37·(unit)`).  So the residual is a real statement, not vacuously true. -/
theorem caseIICor823Level71Unscaled32Coord37_consequent_inhabited :
    ∃ ρ₀ : ZMod 37, ρ₀ ≠ 0 ∧
      (37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2)) ≠ 0 := by
  refine ⟨1, one_ne_zero, ?_⟩
  rw [ZMod.val_one, Nat.cast_one, mul_one]
  decide
