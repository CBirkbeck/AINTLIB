import BernoulliRegular.FLT37.Eichler.CaseIICor823ThirdOrderCoeff
import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71Deg68ModCubeResidue

/-!
# The mod-`37³` degree-`68` Dwork-slice factorial extraction (at the level-`107` precision)

This file builds the **mod-`37³` factorial-`68` extraction** — the relation that recovers the second
`37`-adic digit `c₆₈` of the degree-`68` Dwork slice's `varpi^{32}` coordinate, which the mod-`37²`
extraction (`factorial37_deg68_slice_value`) cannot see (the `−37` ramification fold annihilates the
source second digit at mod-`37²`).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The mechanism, one `37`-adic digit deeper

The mod-`37³` Dwork coordinate `valuedLambdaQuotientDworkCoeffModCube`
(`CaseIICor823ThirdOrderCoeff.lean`) reads the `varpi^{32}` coordinate of the degree-`68` slice at the
**level-`107`** precision (`3(p−1) = 108`).  The all-degrees factorial identity
`natCast_factorial_mul_…_eq_formal` (`N`-generic) at `N = 107`, `d = 68` gives, in
`⧸ (lambdaIdeal)^{108} = mod 37³`:

  `(68! : ZMod 37³) · coordCube(deg-68 slice at level 107) = formalSum68ResidueCube · (−37)`,

with the ramification fold `dworkParameter^68 = −37·tailUnit·dworkParameter^32`
(`dworkParameter_pow_sixtyeight_eq`) supplying `coordCube(x^68) = −37` (mod `37³`, since the
`tailUnit·varpi^32` coordinate is `1` mod `37²` and the `−37` factor folds the `37²`-error into
`37³`).  The source scalar `formalSum68ResidueCube = 37·391 ≡ 37·21 (mod 37²)`
(`CaseIICor823Level71Deg68ModCubeResidue.lean`, PROVEN from the exact rational `N/120`) is the
mod-`37³` lift of the mod-`37²` `formalSum68Residue`.

Both sides carry **two** `37`'s (`68! = 37·u₆₈'`, `coordCube(x^68) = −37`); cancelling them via
`castHom`-to-`ZMod 37` arithmetic (`u₆₈'·c₆₈ ≡ −r₆₈ ≡ −21 (mod 37)`) yields the genuine
`c₆₈ = −u₆₈'⁻¹·21 = 4` — the proven `deg68SecondDigit37Corrected`, now extracted from a genuine
mod-`37³` relation rather than asserted.

## Honest scope

This file proves the mod-`37³` factorial extraction `factorial37_deg68_coordModCube_extraction` and
the ramification fold `x68_coordModCube_eq_neg_thirtyseven` at the level-`107` slice — the full
mod-`37³` relation, end to end, on the **level-`107`** deg-`68` slice.  The single piece it does
**not** supply is the **precision bridge** identifying the mod-`37²` reduction of the level-`107`
deg-`68` coordinate with the level-`71` `unscaled32SliceCoord 68`
(`CaseIICor823Level71DworkSpecializedSound.lean`): that bridge (the only genuinely new connective
tissue beyond the mod-`37²` ↔ mod-`37³` parallel) is isolated as the single named residual in
`CaseIICor823Level71Deg68ModCubeRelation.lean`.

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

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 1. The factorial-`37` extraction carried into the mod-`37³` coordinate (level-`107`) -/

omit [NumberField.IsCMField K] in
/-- **The factorial-`37` second-order extraction at degree `68`, mod `37³`** (proven, axiom-clean):

  `(68! : ZMod 37³) · coordCube(deg-68 slice at level 107) = coordCube(quotMap(x^68)·formalSum_68)`,

where `x = dworkParameterApprox 108`, the `deg-68 slice` is
`samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum 107 68 x hx`, and `formalSum_68` is
the same degree-`68` Artin-Hasse weighted-log coefficient sum.  The mod-`37³` coordinate image of the
**all-degrees** factorial identity `natCast_factorial_mul_…_eq_formal` (`N`-generic, here at
`N = 107`), via `congrArg` of the mod-`37³` coordinate functional and the proven scalar law
`valuedLambdaQuotientDworkCoeffModCube_natCast_mul`.  Mod-`37³` parallel of
`factorial37_deg68_coordModSq_extraction`. -/
theorem factorial37_deg68_coordModCube_extraction
    (i : Fin (37 - 1)) {x : ValuedIntegerRing 37 K} (hx : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial 68 : ℕ) : ZMod (37 ^ 3)) *
      valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 107 68 x hx) =
    valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) i
      (samePrimeQuotientMap (p := 37) (K := K) 107 (x ^ 68) *
        samePrimeRIntegralRatToQuotient (p := 37) (K := K) 107
          (∑ n ∈ Finset.Icc 1 68,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n)) := by
  have hid :=
    natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal
      (p := 37) (K := K) 107 68 hx
  have hcoord := congrArg (valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) i) hid
  rwa [valuedLambdaQuotientDworkCoeffModCube_natCast_mul] at hcoord

/-! ## 2. The `x^68` ramification fold and its `varpi^32` mod-`37³` coordinate (the second `37`)

Reusing the proven Dwork-ring identities `dworkParameter_pow_sixtyeight_eq` (the fold
`dworkParameter^68 = −37·tailUnit·dworkParameter^32`) and the proven mod-`37²` coordinate of
`tailUnit·dworkParameter^32` (`= 1`), the `varpi^32` mod-`37³` coordinate of `x^68` is `−37`. -/

omit [NumberField.IsCMField K] in
/-- **The quotient image of `x^68` is the completed evaluation of `dworkParameter^68`** (proven,
level-`108` precision): `mk(dworkParameterApprox 108 ^ 68) = evalₐ 108 (dworkParameter^68)`. -/
theorem mk_dworkParameterApprox_pow_sixtyeight_modCube_eq :
    Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ (3 * (37 - 1)))
        (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) (3 * (37 - 1))
        (dworkParameter 37 K ^ 68) := by
  rw [map_pow, map_pow, dworkParameter_evalₐ]

omit [NumberField.IsCMField K] in
/-- **The `tailUnit·dworkParameter^32` tail part vanishes mod `37³` after the `−37` fold** (proven):
`rationalPadicIntegerToZModCube(−37·repr(artinHasseTail·dworkParameter^32) 32) = 0`, since
`repr(artinHasseTail·dworkParameter^32) 32 ∈ (rationalPadicPrimeIdeal)^2`
(`artinHasseTail_mul_dworkParameter_pow_thirtytwo_repr_mem`) and `−37 ∈ rationalPadicPrimeIdeal`, so
the product lies in `(rationalPadicPrimeIdeal)^3 = ker(rationalPadicIntegerToZModCube)`. -/
theorem neg_thirtyseven_artinHasseTail_mul_dworkParameter_pow_thirtytwo_coordModCube_eq_zero
    (hp2 : 2 < 37) (k : Fin (37 - 1)) :
    rationalPadicIntegerToZModCube 37
        ((-37 : RationalPadicIntegerRing 37) *
          (dworkParameterPowerBasis 37 K).repr
            (artinHasseTail (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) k) = 0 := by
  rw [(rationalPadicIntegerToZModCube_eq_zero_iff_mem_primeIdeal_pow 37 _).mpr]
  have htail : (dworkParameterPowerBasis 37 K).repr
      (artinHasseTail (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) k ∈
        (rationalPadicPrimeIdeal 37) ^ 2 :=
    artinHasseTail_mul_dworkParameter_pow_thirtytwo_repr_mem (K := K) hp2 k
  have h37 : (-37 : RationalPadicIntegerRing 37) ∈ rationalPadicPrimeIdeal 37 := by
    rw [rationalPadicPrimeIdeal, Ideal.mem_span_singleton]
    refine ⟨-1, ?_⟩
    push_cast; ring
  have hprod := Ideal.mul_mem_mul h37 htail
  -- `(rationalPadicPrimeIdeal)^1 * (rationalPadicPrimeIdeal)^2 = (rationalPadicPrimeIdeal)^3`.
  rw [show (rationalPadicPrimeIdeal 37) * (rationalPadicPrimeIdeal 37) ^ 2 =
      (rationalPadicPrimeIdeal 37) ^ 3 from by ring] at hprod
  exact hprod

omit [NumberField.IsCMField K] in
/-- **The `varpi^32` mod-`37³` coordinate of `dworkParameter^68` is exactly `−37`** (proven): for the
basis index `k` with `(k : ℕ) = 32`,

  `coordCube(evalₐ(dworkParameter^68)) = −37`   (in `ZMod 37³`).

Via the ramification fold (`dworkParameter_pow_sixtyeight_eq`,
`dworkParameter^68 = −37·tailUnit·dworkParameter^32`) and the coordinate readout
(`valuedLambdaQuotientDworkCoeffModCube_evalₐ`).  Splitting `tailUnit = 1 + artinHasseTail`, the `1`
part gives `−37·repr(dworkParameter^32) 32 = −37·1 = −37`
(`repr_dworkParameter_pow_thirtytwo_eq_one`) and the `tail` part vanishes mod `37³`
(`neg_thirtyseven_artinHasseTail_mul_dworkParameter_pow_thirtytwo_coordModCube_eq_zero`). -/
theorem dworkParameter_pow_sixtyeight_coordModCube_eq_neg_thirtyseven
    (hp2 : 2 < 37) (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) k
        (AdicCompletion.evalₐ (lambdaIdeal 37 K) (3 * (37 - 1))
          (dworkParameter 37 K ^ 68)) =
      (-37 : ZMod (37 ^ 3)) := by
  rw [valuedLambdaQuotientDworkCoeffModCube_evalₐ]
  -- `repr(dworkParameter^68) k = -37 · repr(tailUnit·dworkParameter^32) k` by the fold + linearity.
  rw [dworkParameter_pow_sixtyeight_eq (K := K) hp2]
  rw [show (-(37 : DworkCompleteIntegerRing 37 K) *
        artinHasseTailUnit (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) =
      ((-37 : RationalPadicIntegerRing 37)) •
        (artinHasseTailUnit (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) from by
    rw [show ((-37 : RationalPadicIntegerRing 37)) •
          (artinHasseTailUnit (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) =
        algebraMap (RationalPadicIntegerRing 37) (DworkCompleteIntegerRing 37 K) (-37) *
          (artinHasseTailUnit (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32)
      from Algebra.smul_def _ _, map_neg, map_ofNat]
    ring]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  -- split `tailUnit = 1 + artinHasseTail`
  rw [artinHasseTailUnit_eq_one_add_artinHasseTail (p := 37) (K := K) hp2]
  rw [add_mul, one_mul, map_add, Finsupp.add_apply,
    repr_dworkParameter_pow_thirtytwo_eq_one (K := K) k hk]
  rw [mul_add, map_add,
    neg_thirtyseven_artinHasseTail_mul_dworkParameter_pow_thirtytwo_coordModCube_eq_zero
      (K := K) hp2 k, add_zero]
  -- `rationalPadicIntegerToZModCube (-37 · 1) = (-37 : ZMod 37³)`
  rw [mul_one,
    show ((-37 : RationalPadicIntegerRing 37)) =
      (((-37 : ℤ)) : RationalPadicIntegerRing 37) from by push_cast; ring]
  rw [map_intCast]
  push_cast
  ring

omit [NumberField.IsCMField K] in
/-- **The `varpi^32` coordinate of `samePrimeQuotientMap 107 (x^68)` is `−37` mod `37³`** (proven):
the same `−37` value as `dworkParameter_pow_sixtyeight_coordModCube_eq_neg_thirtyseven`, displayed on
the `samePrimeQuotientMap 107` form (precision `107+1 = 108 = 3(p−1)`), reconciled by
`mk_dworkParameterApprox_pow_sixtyeight_modCube_eq`. -/
theorem samePrimeQuotientMap_x68_coordModCube_eq_neg_thirtyseven
    (hp2 : 2 < 37) (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) k
        (samePrimeQuotientMap (p := 37) (K := K) 107
          (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68)) =
      (-37 : ZMod (37 ^ 3)) := by
  rw [show samePrimeQuotientMap (p := 37) (K := K) 107
        (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) (3 * (37 - 1)) (dworkParameter 37 K ^ 68) from
    mk_dworkParameterApprox_pow_sixtyeight_modCube_eq (K := K)]
  exact dworkParameter_pow_sixtyeight_coordModCube_eq_neg_thirtyseven (K := K) hp2 k hk

end BernoulliRegular.FLT37.Eichler

end
