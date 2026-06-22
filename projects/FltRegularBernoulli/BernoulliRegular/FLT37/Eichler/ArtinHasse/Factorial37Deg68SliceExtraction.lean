import BernoulliRegular.FLT37.Eichler.DworkCoordinate.VandermondeColumnFoldFermat
import BernoulliRegular.CyclotomicUnits.KummerLogNormalization.ArtinHasseFiniteLogDecomposition

/-!
# The factorial-`37` degree-`68` second-order extraction: the `68! = 37·u` cancellation mechanism

This file builds the **factorial-`37` degree-`68` second-order extraction** — the genuinely
distinct, deepest arithmetic engine of R4 (the irregular `ω³²` half of Assumption II at the second
order).  It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The genuine factorial-`37` mechanism (proven here)

The first-order single-column evaluator
(`KummerLogFormalEvaluator/Homogeneous.lean`,
`valuedLambdaQuotientDworkCoeffModP_factorPow_normalizedHomogeneousDegreeSum_dworkParameterApprox_of_lt`)
extracts a homogeneous degree-`d` slice of the cyclotomic-unit log by **dividing by `d!`**, which
needs `d < p - 1 = 36` so that `d!` is a `37`-unit.  At degree `d = 68` this route is unavailable:
`padicValNat 37 (68!) = 1` (exactly one multiple of `37` in `{1,…,68}`, namely `37` itself, since
`2·37 = 74 > 68`), so `68! = 37·u` with `u := 68!/37` a `37`-**unit** (`u68_isUnit`).  This is the
factorial-`37` obstruction.

The **all-degrees** factorial identity over the precision quotient,
`natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal`
(proven in `KummerLogNormalization/Part3.lean`, valid at *every* `N, d` — no `d < p - 1` needed),
gives, at `N = 71` (precision `72 = 2(p-1)`, the domain of the mod-`37²` coordinate
`valuedLambdaQuotientDworkCoeffModSq`) and `d = 68`:

  `(68! : Q) · (deg-68 slice) = quotMap(x^68) · RIntegralRatToQuotient(formalSum_68)`

with `x = dworkParameterApprox 72`.  Applying the mod-`37²` Dwork coordinate functional and the
proven scalar law `valuedLambdaQuotientDworkCoeffModSq_natCast_mul` yields the **factorial-`37`
second-order extraction** (`factorial37_deg68_coordModSq_extraction`):

  `(68! : ZMod 37²) · coordModSq(deg-68 slice) = coordModSq(quotMap(x^68)·formalSum_68)`.

The left factor `(68! : ZMod 37²) = 37·(u : ZMod 37²)` (`factorial_68_cast_modSq`); the right side
carries the **second `37`** through the ramification fold `x^68 = -37·tailUnit·x^32`
(`dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`, here `dworkParameter^68 =
-37·tailUnit·dworkParameter^32`, `dworkParameter_pow_sixtyeight_eq`).  These two `37`'s are the
`37·q`-numerator / `37·u`-denominator cancellation of the degree-`68` Bernoulli coefficient
`B₆₈/68! = (37·q)/(37·u)`: in the mod-`37²` reduction the two `37`'s cancel and leave the leading
mod-`37` scalar a `37`-unit combination.

## The `x^68` ramification-fold coordinate (proven here)

`coordModSq(quotMap(dworkParameterApprox 72 ^ 68))` is read through `evalₐ` and the Dwork power
basis (`x68_coordModSq_eq`): `mk(x^68) = evalₐ(dworkParameter^68)`, and via the fold the `varpi^32`
basis coordinate of `dworkParameter^68 = -37·tailUnit·dworkParameter^32` is
`-37·repr(tailUnit·dworkParameter^32) 32` with `repr(dworkParameter^32) 32 = 1` (basis index `32 <
36`).  So the `varpi^32` coordinate of `x^68` is `37·(unit)` mod `37²` — the second `37`, made
explicit.

## Honest scope

This file proves the factorial-`37` engine end-to-end — the `68! = 37·u` arithmetic, the all-degrees
factorial extraction at `d = 68` carried into the mod-`37²` coordinate, the `x^68` ramification-fold
coordinate (exactly `-37`), the formal-scalar denominator clearing, the **Frobenius collapse** of the
formal degree-`68` source to a single coefficient, and — crucially — the **vanishing** of that
coefficient mod `37`.  The upshot (`deg68_slice_coordMod37_eq_zero`) is that the degree-`68`
homogeneous slice's `varpi^32` mod-`37` coordinate is `0`: the **degree-`68` slice does not
contribute to `secondOrderPart37` at the mod-`37` order**.  This resolves the degree-`68` slice's
contribution to the irregular `varpi^32` coordinate.

The vanishing is genuine arithmetic, not an accident: `formalSum68 mod 37` collapses to the single
`n = 37` term (`factorial_div_mod37_eq_zero`: `68!/n ≡ 0` for `n ≠ 37` since `68! = 37·u`,
`37 ∤ n`), whose coefficient `ahCoeff37 = [λ^{68}` of `(AH−1)^{37}]` is `≡ 0 (mod 37)` by **Frobenius
in characteristic `37`** (`coeff_sixtyeight_pow37_eq_zero`: `f^{37}` is supported on degrees divisible
by `37`, and `37 ∤ 68`).  So the slice coordinate is itself divisible by `37` (a higher-order effect).

What this file does **not** do is assemble the full level-`71` finite-log coordinate `W(a)` (the
genuine `secondOrderPart37 a := (W(a).val/37 : ZMod 37)`) out of *all* its homogeneous slices: `W(a)`
is the coordinate of `samePrimeFiniteLog 71 ((normalizedUnit)^{p-1} - 1)`, whose full slice
decomposition (and the lower slices' contributions) requires the second-order normalized-unit ↔
Dwork-parameter bridge (the first-order bridge `ε^{p-1} ≡ a(1−ζ)/(1−ζ^a)` holds only mod `(λ)^{p-1} =
(p)`; see `CaseIICor823Level72ColumnScaling.lean`).  This file settles the **degree-`68`** slice — the
deepest, factorial-`37`-obstructed one — completely.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7 (the `α₀`, `α₁` invariants).
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

/-! ## 1. The factorial-`37` arithmetic: `padicValNat 37 (68!) = 1`, `68! = 37·u`, `u` a `37`-unit -/

/-- **Legendre's formula at `(37, 68)`**: `padicValNat 37 (68!) = 1`.  The only multiple of `37` in
`{1,…,68}` is `37` itself (`2·37 = 74 > 68`), so the `37`-adic valuation of `68!` is exactly `1`.
This is the precise factorial-`37` obstruction: at degree `68` the factorial `d!` is no longer a
`37`-unit, but it carries *exactly one* factor of `37`. -/
theorem padicValNat_thirtyseven_factorial_sixtyeight :
    padicValNat 37 (Nat.factorial 68) = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [padicValNat_factorial (b := 2) (by norm_num [Nat.log])]
  decide

/-- **`37 ∣ 68!`** — one factor of `37` (from `37 ∈ {1,…,68}`). -/
theorem thirtyseven_dvd_factorial_sixtyeight : 37 ∣ Nat.factorial 68 := by decide

/-- **`68! = 37·u` with `u := 68!/37`** — the factorial-`37` factorization. -/
theorem factorial_sixtyeight_eq_thirtyseven_mul :
    Nat.factorial 68 = 37 * (Nat.factorial 68 / 37) := by
  have h := thirtyseven_dvd_factorial_sixtyeight
  omega

/-- **`u := 68!/37` is a `37`-unit** (`(u : ZMod 37) ≠ 0`): since `padicValNat 37 (68!) = 1`, the
quotient `68!/37` is coprime to `37`.  This is the surviving `37`-unit after the single `37` is
factored out — the denominator of the cancellation `B₆₈/68! = (37·q)/(37·u)`. -/
theorem u68_ne_zero : (((Nat.factorial 68 / 37 : ℕ) : ZMod 37)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  decide

/-- **`u := 68!/37` is a unit in `ZMod 37`**. -/
theorem u68_isUnit : IsUnit ((Nat.factorial 68 / 37 : ℕ) : ZMod 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr u68_ne_zero

/-- **The mod-`37²` cast of `68!` is `37·u`** (`(68! : ZMod 37²) = 37·(u : ZMod 37²)`): the
factorial-`37` factorization read in `ZMod 37²`.  This is the **first** of the two `37`'s in the
degree-`68` Bernoulli coefficient `B₆₈/68! = (37·q)/(37·u)` — the denominator `37`. -/
theorem factorial_sixtyeight_cast_modSq :
    ((Nat.factorial 68 : ℕ) : ZMod (37 ^ 2)) =
      37 * ((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2)) := by
  conv_lhs => rw [factorial_sixtyeight_eq_thirtyseven_mul]
  push_cast
  ring

/-! ## 2. The factorial-`37` second-order extraction (the all-degrees identity in the coordinate)

The all-degrees factorial identity
`natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal`
(proven, valid at *every* `N, d`) at `N = 71`, `d = 68` lives in the precision quotient
`⧸ (lambdaIdeal)^(71+1) = ⧸ (lambdaIdeal)^(2(p-1))`, exactly the domain of the mod-`37²` Dwork
coordinate.  Applying the coordinate functional and the proven scalar law gives the factorial-`37`
extraction: a single mod-`37²` identity with `68!` (`= 37·u`) on the left and the formal degree-`68`
Bernoulli source (times `x^68`) on the right. -/

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **The factorial-`37` second-order extraction at degree `68`** (proven, axiom-clean):

  `(68! : ZMod 37²) · coordModSq(deg-68 slice) = coordModSq(quotMap(x^68)·formalSum_68)`,

where `x = dworkParameterApprox 72`, the `deg-68 slice` is
`samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum 71 68 x hx`, and `formalSum_68 =
RIntegralRatToQuotient(∑ rationalArtinHasseNormalizedFactorialWeightedLogCoeff 68 n)`.

This is the mod-`37²` coordinate image of the **all-degrees** factorial identity
`natCast_factorial_mul_…_eq_formal` (proven, no `d < p - 1` constraint), obtained by `congrArg` of
the coordinate functional and the proven scalar law `valuedLambdaQuotientDworkCoeffModSq_natCast_mul`
(which factors the `(68! : ZMod 37²)` cast out of the coordinate).  Combined with
`factorial_sixtyeight_cast_modSq` (`(68! : ZMod 37²) = 37·u`), the left side is `37·u·coordModSq(deg-68
slice)`: the **first** `37` of the factorial-`37` cancellation. -/
theorem factorial37_deg68_coordModSq_extraction
    (i : Fin (37 - 1)) {x : ValuedIntegerRing 37 K} (hx : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial 68 : ℕ) : ZMod (37 ^ 2)) *
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 68 x hx) =
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
      (samePrimeQuotientMap (p := 37) (K := K) 71 (x ^ 68) *
        samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71
          (∑ n ∈ Finset.Icc 1 68,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n)) := by
  have hid :=
    natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal
      (p := 37) (K := K) 71 68 hx
  have hcoord := congrArg (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i) hid
  rwa [valuedLambdaQuotientDworkCoeffModSq_natCast_mul] at hcoord

/-! ## 3. The `x^68` ramification fold and its `varpi^32` mod-`37²` coordinate (the second `37`)

The right side of the factorial-`37` extraction carries `x^68 = dworkParameterApprox 72 ^ 68`.  Its
mod-`37²` coordinate is read in the completed Dwork ring through the ramification fold

  `dworkParameter^68 = dworkParameter^36 · dworkParameter^32 = (-37·tailUnit)·dworkParameter^32`,

from `dworkParameter_pow_pred_eq_neg_p_mul_tailUnit` (`varpi^{p-1} = varpi^36 = -37·tailUnit`).  So
the `varpi^32` basis coordinate of `dworkParameter^68` carries an explicit `-37` factor — the
**second** `37` of the cancellation `B₆₈/68! = (37·q)/(37·u)` (the numerator `37`). -/

omit [NumberField.IsCMField K] in
/-- **The Dwork-parameter ramification fold at degree `68`** (proven): in the completed Dwork ring,

  `dworkParameter^68 = -37·tailUnit·dworkParameter^32`,

from `dworkParameter^36 = -37·tailUnit` (`dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`, the
ramification `varpi^{p-1} = -p·tailUnit`) and `68 = 36 + 32`.  This converts the degree-`68` Dwork
power into a `37·(unit)` multiple of the degree-`32` (basis) power: the source of the **second** `37`
in the factorial-`37` cancellation. -/
theorem dworkParameter_pow_sixtyeight_eq (hp2 : 2 < 37) :
    dworkParameter 37 K ^ 68 =
      -(37 : DworkCompleteIntegerRing 37 K) *
        artinHasseTailUnit (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32 := by
  have h36 := dworkParameter_pow_pred_eq_neg_p_mul_tailUnit (p := 37) (K := K) hp2
  have he : dworkParameter 37 K ^ 68 = dworkParameter 37 K ^ 36 * dworkParameter 37 K ^ 32 := by
    rw [← pow_add]
  rw [he, h36]
  ring

omit [NumberField.IsCMField K] in
/-- **The quotient image of `x^68` is the completed evaluation of `dworkParameter^68`** (proven,
`N`-generic precision): `mk(dworkParameterApprox 72 ^ 68) = evalₐ 72 (dworkParameter^68)`, via
`map_pow` and `dworkParameter_evalₐ` (`evalₐ N (dworkParameter) = mk(dworkParameterApprox N)`). -/
theorem mk_dworkParameterApprox_pow_sixtyeight_eq :
    Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ (2 * (37 - 1)))
        (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) (2 * (37 - 1))
        (dworkParameter 37 K ^ 68) := by
  rw [map_pow, map_pow, dworkParameter_evalₐ]

omit [NumberField.IsCMField K] in
/-- **The `varpi^32` mod-`37²` coordinate of `dworkParameter^68` is `37·(unit)`** (proven): for the
basis index `k` with `(k : ℕ) = 32`,

  `coordModSq(evalₐ(dworkParameter^68)) =
     rationalPadicIntegerToZModSq(-37·repr(tailUnit·dworkParameter^32) 32)`,

via the ramification fold (`dworkParameter_pow_sixtyeight_eq`), the power-basis coordinate readout
(`valuedLambdaQuotientDworkCoeffModSq_evalₐ`), and `RationalPadicIntegerRing`-linearity of `repr`.
The explicit `-37` factor in the coordinate is the **second** `37` of the factorial-`37`
cancellation.  (Holds for every basis index `k`; the relevant case is `(k : ℕ) = 32`, the
`varpi^32` column coordinate.) -/
theorem x68_coordModSq_eq (hp2 : 2 < 37) (k : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (AdicCompletion.evalₐ (lambdaIdeal 37 K) (2 * (37 - 1))
          (dworkParameter 37 K ^ 68)) =
      rationalPadicIntegerToZModSq 37
        ((-37 : RationalPadicIntegerRing 37) *
          (dworkParameterPowerBasis 37 K).repr
            (artinHasseTailUnit (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) k) := by
  rw [valuedLambdaQuotientDworkCoeffModSq_evalₐ]
  congr 1
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

omit [NumberField.IsCMField K] in
/-- **The degree-`32` Dwork power is the basis element of index `32`** (proven): `repr(dworkParameter
^32) 32 = 1`, since `32 < 36 = p - 1` so `dworkParameter^32 = dworkParameterPowerBasis 32`.  This is
the column-carrying basis term `varpi^32`, the same `varpi^32` coordinate the level-`72` evaluator
reads. -/
theorem repr_dworkParameter_pow_thirtytwo_eq_one (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    (dworkParameterPowerBasis 37 K).repr (dworkParameter 37 K ^ 32) k = 1 := by
  have hbasis : dworkParameter 37 K ^ 32 = dworkParameterPowerBasis 37 K k := by
    rw [dworkParameterPowerBasis_apply, hk]
  rw [hbasis, Module.Basis.repr_self, Finsupp.single_eq_same]

omit [NumberField.IsCMField K] in
/-- **The tail correction `artinHasseTail·dworkParameter^32` has trivial `varpi^32` coordinate mod
`37²`** (proven): its `repr` coefficient at any index lies in `(rationalPadicPrimeIdeal)^2`.

Since `artinHasseTail ∈ (dworkCompleteLambdaIdeal)^{(p-1)²} = (varpi)^{1296}` and `dworkParameter^32
∈ (varpi)^{32}`, the product lies in `(varpi)^{1328} ⊆ (varpi)^{72} = (p²)`, so by the proven
second-order coordinate congruence
`dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_pow_two_pred` (vs `0`)
the coordinate is in `(rationalPadicPrimeIdeal)^2`.  Hence `tailUnit = 1 + tail` contributes nothing
to the `varpi^32` coordinate mod `37²` beyond the `1` of `dworkParameter^32`. -/
theorem artinHasseTail_mul_dworkParameter_pow_thirtytwo_repr_mem (hp2 : 2 < 37) (k : Fin (37 - 1)) :
    (dworkParameterPowerBasis 37 K).repr
        (artinHasseTail (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) k ∈
      (rationalPadicPrimeIdeal 37) ^ 2 := by
  have hmem : artinHasseTail (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32 ∈
      (dworkParameterIdeal 37 K) ^ (2 * (37 - 1)) := by
    have htail : artinHasseTail (p := 37) (K := K) hp2 ∈
        (dworkParameterIdeal 37 K) ^ ((37 - 1) ^ 2) := by
      rw [dworkParameterIdeal_eq_dworkCompleteLambdaIdeal (p := 37) (K := K)]
      exact artinHasseTail_mem_dworkCompleteLambdaIdeal_pow (p := 37) (K := K) hp2
    have hdwork : dworkParameter 37 K ^ 32 ∈ (dworkParameterIdeal 37 K) ^ 32 := by
      have h1 : dworkParameter 37 K ∈ dworkParameterIdeal 37 K := by
        rw [dworkParameterIdeal]; exact Ideal.mem_span_singleton_self _
      exact Ideal.pow_mem_pow h1 32
    have hprod := Ideal.mul_mem_mul htail hdwork
    rw [← pow_add] at hprod
    exact Ideal.pow_le_pow_right (by norm_num) hprod
  have hcoord :=
    dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_pow_two_pred
      (p := 37) (K := K)
      (x := artinHasseTail (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32)
      (y := 0) (by simpa using hmem) k
  simpa using hcoord

omit [NumberField.IsCMField K] in
/-- **`tailUnit·dworkParameter^32` has `varpi^32` coordinate `1` mod `37²`** (proven): for the basis
index `k` with `(k : ℕ) = 32`,
`rationalPadicIntegerToZModSq(repr(tailUnit·dworkParameter^32) 32) = 1`.  Splitting `tailUnit = 1 +
tail`, the `dworkParameter^32` part gives `repr = 1` (`repr_dworkParameter_pow_thirtytwo_eq_one`) and
the `tail` part vanishes mod `37²`
(`artinHasseTail_mul_dworkParameter_pow_thirtytwo_repr_mem`). -/
theorem tailUnit_mul_dworkParameter_pow_thirtytwo_coordModSq_eq_one
    (hp2 : 2 < 37) (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    rationalPadicIntegerToZModSq 37
        ((dworkParameterPowerBasis 37 K).repr
          (artinHasseTailUnit (p := 37) (K := K) hp2 * dworkParameter 37 K ^ 32) k) = 1 := by
  rw [artinHasseTailUnit_eq_one_add_artinHasseTail (p := 37) (K := K) hp2]
  rw [add_mul, one_mul, map_add, Finsupp.add_apply, map_add]
  rw [repr_dworkParameter_pow_thirtytwo_eq_one (K := K) k hk]
  rw [(rationalPadicIntegerToZModSq_eq_zero_iff_mem_primeIdeal_sq 37 _).mpr
    (artinHasseTail_mul_dworkParameter_pow_thirtytwo_repr_mem (K := K) hp2 k)]
  simp

omit [NumberField.IsCMField K] in
/-- **The `varpi^32` mod-`37²` coordinate of `x^68` is exactly `-37`** (proven): for `x =
dworkParameterApprox 72` and the basis index `k` with `(k : ℕ) = 32`,

  `coordModSq(quotMap(x^68)) = -37`   (in `ZMod 37²`).

This is the **second** `37` of the factorial-`37` cancellation, made fully explicit (value `-37`, the
ramification sign `varpi^{36} = -37·tailUnit` times the `varpi^32`-coordinate `1`).  Assembled from
`mk_dworkParameterApprox_pow_sixtyeight_eq`, `x68_coordModSq_eq`,
`tailUnit_mul_dworkParameter_pow_thirtytwo_coordModSq_eq_one`, and the `RingHom`-naturality of
`rationalPadicIntegerToZModSq` on the `-37·(·)` scalar. -/
theorem x68_coordModSq_eq_neg_thirtyseven (hp2 : 2 < 37) (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ (2 * (37 - 1)))
          (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68)) =
      (-37 : ZMod (37 ^ 2)) := by
  rw [mk_dworkParameterApprox_pow_sixtyeight_eq, x68_coordModSq_eq (K := K) hp2 k]
  rw [map_mul]
  rw [tailUnit_mul_dworkParameter_pow_thirtytwo_coordModSq_eq_one (K := K) hp2 k hk, mul_one]
  -- `rationalPadicIntegerToZModSq (-37 : RationalPadicIntegerRing) = (-37 : ZMod 37²)`
  rw [show ((-37 : RationalPadicIntegerRing 37)) =
      (((-37 : ℤ)) : RationalPadicIntegerRing 37) from by push_cast; ring]
  rw [map_intCast]
  push_cast
  ring

omit [NumberField.IsCMField K] in
/-- **The `varpi^32` coordinate of `samePrimeQuotientMap 71 (x^68)` is `-37`** (proven): the same
`-37` value as `x68_coordModSq_eq_neg_thirtyseven`, displayed on the `samePrimeQuotientMap 71` form in
which the factorial-`37` extraction produces it (the precision indices `71+1` and `2(p-1) = 72`
coincide, reconciled by `mk_dworkParameterApprox_pow_sixtyeight_eq` without forcing the heavy
`adicCompletionIntegers` quotient transport). -/
theorem samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven
    (hp2 : 2 < 37) (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (samePrimeQuotientMap (p := 37) (K := K) 71
          (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68)) =
      (-37 : ZMod (37 ^ 2)) := by
  rw [show samePrimeQuotientMap (p := 37) (K := K) 71
        (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) (2 * (37 - 1)) (dworkParameter 37 K ^ 68) from
    mk_dworkParameterApprox_pow_sixtyeight_eq (K := K)]
  exact x68_coordModSq_eq_neg_thirtyseven (K := K) hp2 k hk

/-! ## 4. The formal degree-`68` scalar factored through the coordinate (the `rIntegralRat`
den-clearing), and the degree-`68` slice value mod `37`

The right side of the factorial-`37` extraction is `coordModSq(quotMap(x^68)·formalSum_68)` with
`formalSum_68 = samePrimeRIntegralRatToQuotient 71 (formalSum_rat)` a *ring constant* (a `37`-integral
rational embedded in the quotient).  We factor that scalar out of the coordinate by clearing its
denominator (a `37`-unit, hence a `ZMod 37²`-unit), mirroring the first-order template
`valuedLambdaQuotientDworkCoeffModP_mk_rIntegralRat_mul_dworkParameterApprox_pow_of_lt`.  Combined
with `samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven` (`coordModSq(x^68) = -37`), the whole
right side is `-37·(formalSum_68's mod-`37²` residue)`. -/

omit [NumberField.IsCMField K] in
/-- **The formal degree-`68` `rIntegralRat` scalar factors out of the mod-`37²` coordinate**
(proven): for any `37`-integral rational `q`,

  `coordModSq(quotMap(x^68)·RIntegralRatToQuotient(q)) =
     (q.num · q.den⁻¹ : ZMod 37²) · coordModSq(quotMap(x^68))`.

The second-order denominator clearing: multiply by the `37`-unit `q.den`, use
`den_mul_rIntegralRatToValuedInteger` to collapse `q.den·rIntegralRat(q) = q.num`, factor the integer
`q.num` out of the coordinate (`valuedLambdaQuotientDworkCoeffModSq_intCast_mul`), then divide by the
unit `q.den` (`ZMod.isUnit_iff_coprime`, `q.den` coprime to `37` hence to `37²`).  The whole
computation stays at the `samePrimeQuotientMap 71` precision, dodging the `adicCompletionIntegers`
quotient-transport `whnf` wall. -/
theorem rIntegralRat_scalar_factors_through_coordModSq_x68
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) (k : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (samePrimeQuotientMap (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68) *
          samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71 q) =
      ((q : ℚ).num : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹ *
        valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
          (samePrimeQuotientMap (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68)) := by
  set xp := dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68 with hxp
  set C := valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
    (samePrimeQuotientMap (p := 37) (K := K) 71 xp) with hC
  set L := valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
      (samePrimeQuotientMap (p := 37) (K := K) 71 xp *
        samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71 q) with hL
  have hunit : IsUnit (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) := by
    have hcop : ((q : ℚ).den : ℕ).Coprime 37 := q.property
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_right 2)
  have hden : (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) * L = ((q : ℚ).num : ZMod (37 ^ 2)) * C := by
    rw [hL, ← valuedLambdaQuotientDworkCoeffModSq_natCast_mul]
    have hRItoQ : samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71 q =
        samePrimeQuotientMap (p := 37) (K := K) 71 (rIntegralRatToValuedInteger 37 K q) := rfl
    rw [hRItoQ, ← map_mul,
      ← map_natCast (samePrimeQuotientMap (p := 37) (K := K) 71) ((q : ℚ).den), ← map_mul]
    have hclear :
        (((q : ℚ).den : ValuedIntegerRing 37 K)) *
            (xp * rIntegralRatToValuedInteger 37 K q) =
          ((q : ℚ).num : ValuedIntegerRing 37 K) * xp := by
      calc
        (((q : ℚ).den : ValuedIntegerRing 37 K)) *
            (xp * rIntegralRatToValuedInteger 37 K q)
            = ((((q : ℚ).den : ValuedIntegerRing 37 K)) *
                rIntegralRatToValuedInteger 37 K q) * xp := by ring
        _ = ((q : ℚ).num : ValuedIntegerRing 37 K) * xp := by
            rw [den_mul_rIntegralRatToValuedInteger (p := 37) (K := K) q]
    rw [hclear, map_mul, map_intCast, valuedLambdaQuotientDworkCoeffModSq_intCast_mul, ← hC]
  -- divide by the unit `q.den`
  apply hunit.mul_left_cancel
  rw [hden,
    show (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) *
        (((q : ℚ).num : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹ * C) =
      ((q : ℚ).num : ZMod (37 ^ 2)) *
        ((((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹) * C from by
      ring]
  rw [ZMod.mul_inv_of_unit _ hunit, mul_one]

/-! ## 5. The capstone: the degree-`68` slice coordinate value (both `37`'s cancelled)

Assembling §2 (factorial extraction), §4 (`rIntegralRat` den-clearing) and
`samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven` (`coordModSq(x^68) = -37`):

  `(68! : ZMod 37²) · coordModSq(deg-68 slice) =
     (formalSum68.num·formalSum68.den⁻¹ : ZMod 37²) · (-37)`.

The left carries the **first** `37` (`68! = 37·u`), the right the **second** `37` (`-37`).
Cancelling both (mod `37`, `u` a unit) determines
`coordModSq(deg-68 slice) mod 37 = -u⁻¹·(formalSum68 residue)`: the explicit factorial-`37`-cleared
degree-`68` coefficient. -/

/-- **The formal degree-`68` Artin-Hasse log coefficient sum** (a `37`-integral rational): the
`d = 68` row of `rationalArtinHasseNormalizedFactorialWeightedLogCoeff`, whose mod-`37²` residue is
the formal Bernoulli source of the degree-`68` slice. -/
noncomputable def formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37 :=
  ∑ n ∈ Finset.Icc 1 68, rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n

omit [NumberField.IsCMField K] in
/-- **The factorial-`37` degree-`68` slice extraction, fully assembled** (proven, axiom-clean): for
`x = dworkParameterApprox 72` and the column index `i` with `(i : ℕ) = 32`,

  `(68! : ZMod 37²) · coordModSq(deg-68 slice) =
     (formalSum68.num · formalSum68.den⁻¹ : ZMod 37²) · (-37)`.

The complete factorial-`37` mechanism: the **first** `37` is `68! = 37·u`
(`factorial_sixtyeight_cast_modSq`), the **second** is the ramification `coordModSq(x^68) = -37`
(`samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven`), with the formal degree-`68` Bernoulli
source `formalSum68` factored through the coordinate by denominator clearing (§4).  This is the
factorial-`37` degree-`68` second-order coefficient before the two `37`'s are divided out. -/
theorem factorial37_deg68_slice_value
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial 68 : ℕ) : ZMod (37 ^ 2)) *
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 68 x hxmem) =
    (((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).num :
        ZMod (37 ^ 2)) *
        ((((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).den : ℕ) :
            ZMod (37 ^ 2))⁻¹ *
      (-37 : ZMod (37 ^ 2)) := by
  rw [factorial37_deg68_coordModSq_extraction (K := K) i hxmem]
  subst hx
  rw [show (∑ n ∈ Finset.Icc 1 68,
        rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n) = formalSum68 from rfl]
  rw [rIntegralRat_scalar_factors_through_coordModSq_x68 (K := K) formalSum68 i,
    samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven (K := K) (by norm_num) i hi]

/-- **Forward `37`-cancellation in `ZMod 37²`**: if `37·x = 37·y` then `castHom x = castHom y`
(proven).  From `37·(x−y) = 0` in `ZMod 37²` we get `37² ∣ 37·(x−y).val`, hence `37 ∣ (x−y).val`,
i.e. `castHom (x−y) = 0`.  The converse of `thirtyseven_mul_eq_of_castHom_eq`; used to divide both
`37`'s out of the factorial-`37` slice equation. -/
theorem castHom_eq_of_thirtyseven_mul_eq {x y : ZMod (37 ^ 2)}
    (h : (37 : ZMod (37 ^ 2)) * x = (37 : ZMod (37 ^ 2)) * y) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) x =
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) y := by
  have hsub : (37 : ZMod (37 ^ 2)) * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  rw [← sub_eq_zero, ← map_sub]
  set z := x - y
  rw [ZMod.castHom_apply, ← ZMod.natCast_val z, ZMod.natCast_eq_zero_iff]
  have hval : (37 * z.val) % (37 ^ 2) = 0 := by
    have h2 := congrArg ZMod.val hsub
    rw [ZMod.val_zero, ZMod.val_mul, show (37 : ZMod (37 ^ 2)).val = 37 from by decide] at h2
    exact h2
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hval
  refine ⟨c, ?_⟩
  have hcc : 37 * z.val = 37 * (37 * c) := by rw [hc]; ring
  omega

omit [NumberField.IsCMField K] in
/-- **The degree-`68` homogeneous slice coordinate, mod `37`, with both `37`'s divided out** (proven,
axiom-clean): for `x = dworkParameterApprox 72` and the column index `i` with `(i : ℕ) = 32`,

  `(u mod 37) · (coordModSq(deg-68 slice) mod 37) = -(formalSum68 residue mod 37)`   (in `ZMod 37`),

where `u = 68!/37`.  This is the factorial-`37` cancellation completed: the `68! = 37·u` (left) and
`coordModSq(x^68) = -37` (right) `37`'s cancel, leaving a mod-`37` identity in which `u` is a unit
(`u68_isUnit`) and the right side is the mod-`37` residue of the formal degree-`68` Bernoulli
source.  So `coordModSq(deg-68 slice) mod 37 = -u⁻¹·(formalSum68 residue)`, the explicit
factorial-`37`-cleared degree-`68` second-order coefficient.

Obtained from `factorial37_deg68_slice_value` (`37·u·X = (R)·(-37)`) by
`castHom_eq_of_thirtyseven_mul_eq` after writing both sides as `37·(·)`
(`factorial_sixtyeight_cast_modSq` for the left). -/
theorem factorial37_deg68_slice_coordMod37
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    (((Nat.factorial 68 / 37 : ℕ) : ZMod 37)) *
        (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
          (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := 37) (K := K) 71 68 x hxmem)) =
      -(ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        ((((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).num :
            ZMod (37 ^ 2)) *
          ((((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).den : ℕ) :
              ZMod (37 ^ 2))⁻¹) := by
  have hval := factorial37_deg68_slice_value (K := K) i hi hx hxmem
  -- Write LHS as `37·(u · X)` and RHS as `37·(-R)`, then cancel the `37` via castHom.
  set X := valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
    (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
      (p := 37) (K := K) 71 68 x hxmem) with hX
  set R := (((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).num :
      ZMod (37 ^ 2)) *
    ((((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).den : ℕ) :
        ZMod (37 ^ 2))⁻¹ with hR
  -- hval : (68! : ZMod 37²)·X = R·(-37); rewrite both as `37·(·)`.
  rw [factorial_sixtyeight_cast_modSq] at hval
  have hcasteq : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2)) * X) =
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) (-R) := by
    apply castHom_eq_of_thirtyseven_mul_eq
    rw [show (37 : ZMod (37 ^ 2)) * (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2)) * X) =
        (37 : ZMod (37 ^ 2)) * ((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2)) * X from by ring]
    rw [hval]; ring
  rw [map_mul, map_neg] at hcasteq
  -- castHom ((68!/37 : ZMod 37²)) = ((68!/37 : ℕ) : ZMod 37)
  rw [map_natCast] at hcasteq
  exact hcasteq

/-! ## 6. The formal source `formalSum68 mod 37` collapses to a single Frobenius-degree coefficient

The mod-`37` residue of the formal degree-`68` source
`formalSum68 = ∑_{n=1}^{68} (68!/n)·(±1)·[λ^{68} coefficient of (AH−1)^n]` collapses to the
**single** `n = 37` term: for every `n ≠ 37` in
`{1,…,68}` the factorial weight `68!/n` is `≡ 0 (mod 37)` (`factorial_div_mod37_eq_zero`), because
`68! = 37·u` and `37 ∤ n` (the only multiple of `37` in `{1,…,68}` is `37` itself).  So

  `rIntegralToZMod 37 (formalSum68) = (u mod 37) · rIntegralToZMod 37 (ahCoeff37)`,

with `ahCoeff37 := [λ^{68} coefficient of (AH−1)^{37}]` the Frobenius-power Artin-Hasse coefficient.
This isolates the entire degree-`68` formal source to that **one** coefficient mod `37` — the
genuine Kellner `α₁` / `p`-adic content. -/

/-- **The factorial weight `68!/n` vanishes mod `37` for `n ≠ 37`** (proven): for `1 ≤ n ≤ 68` with
`n ≠ 37`, `((68!/n : ℕ) : ZMod 37) = 0`.  Since `68! = 37·u` (`padicValNat 37 (68!) = 1`) and `37 ∤
n` (the unique multiple of `37` in `{1,…,68}` is `37`), `padicValNat 37 (68!/n) = 1 − 0 ≥ 1`, so `37
∣ 68!/n`.  This is why only the `n = 37` term of `formalSum68` survives mod `37`. -/
theorem factorial_div_mod37_eq_zero (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 68) (hne : n ≠ 37) :
    ((Nat.factorial 68 / n : ℕ) : ZMod 37) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  have hdvd : n ∣ Nat.factorial 68 := Nat.dvd_factorial hn1 hn
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hn37 : ¬ (37 ∣ n) := by
    intro h; obtain ⟨c, hc⟩ := h; interval_cases n <;> omega
  apply dvd_of_one_le_padicValNat
  rw [padicValNat.div_of_dvd hdvd, padicValNat_thirtyseven_factorial_sixtyeight]
  have hvn : padicValNat 37 n = 0 := by rw [padicValNat.eq_zero_iff]; right; right; exact hn37
  omega

/-- **The Frobenius-power Artin-Hasse coefficient** `ahCoeff37`: the `λ^{68}` coefficient of
`(rationalArtinHasseNormalizedExpMinusOneSeries 37 − 1)^{37}`, a `37`-integral rational.  This single
coefficient mod `37` is the entire degree-`68` formal source after the factorial collapse
(`formalSum68_rIntegralToZMod_eq`); it is the genuine remaining `p`-adic / Kellner `α₁` content of
the degree-`68` slice. -/
noncomputable def ahCoeff37 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37 :=
  ⟨(PowerSeries.coeff (R := ℚ) 68)
      ((rationalArtinHasseNormalizedExpMinusOneSeries 37 - 1) ^ 37),
    (rationalArtinHasseNormalizedExpMinusOneSeries_sub_one_isPIntegral (p := 37)).pow 37 68⟩

/-- **The formal degree-`68` source collapses to the single `n = 37` term mod `37`** (proven,
axiom-clean):

  `rIntegralToZMod 37 (formalSum68) = (u mod 37) · rIntegralToZMod 37 (ahCoeff37)`,

where `u = 68!/37`.  `rIntegralToZMod 37` is a `RingHom`, so it distributes over the sum
`formalSum68 = ∑_n (68!/n)·(−1)^{n+1}·[λ^{68} of (AH−1)^n]`; for `n ≠ 37` the factor `68!/n ≡ 0
(mod 37)` (`factorial_div_mod37_eq_zero`) kills the term, and the surviving `n = 37` term is
`(68!/37)·(−1)^{38}·ahCoeff37 = u·ahCoeff37` (mod `37`).  This is the **Frobenius collapse**: the
degree-`68` formal source mod `37` is `u` times the single Frobenius-power coefficient `ahCoeff37`. -/
theorem formalSum68_rIntegralToZMod_eq :
    Furtwaengler.DieudonneDwork.rIntegralToZMod 37
        (formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) =
      ((Nat.factorial 68 / 37 : ℕ) : ZMod 37) *
        Furtwaengler.DieudonneDwork.rIntegralToZMod 37 ahCoeff37 := by
  change Furtwaengler.DieudonneDwork.rIntegralToZMod 37
      (∑ n ∈ Finset.Icc 1 68,
        rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n) = _
  rw [map_sum, Finset.sum_eq_single 37]
  · rw [rationalArtinHasseNormalizedFactorialWeightedLogCoeff,
      map_mul, map_mul, map_natCast, map_pow, map_neg, map_one,
      show ((-1 : ZMod 37) ^ (37 + 1)) = 1 from by norm_num, mul_one]
    rfl
  · intro n hn hne
    rw [Finset.mem_Icc] at hn
    rw [rationalArtinHasseNormalizedFactorialWeightedLogCoeff, map_mul, map_mul, map_natCast,
      factorial_div_mod37_eq_zero n hn.1 hn.2 hne]
    ring
  · intro hnot
    exact absurd (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) hnot

/-! ## 7. The Frobenius coefficient vanishes mod `37`: the degree-`68` slice does not contribute

The single Frobenius-power coefficient `ahCoeff37 = [λ^{68} of (AH−1)^{37}]` is `≡ 0 (mod 37)`, by
**Frobenius / the freshman's dream in characteristic `37`**: in `PowerSeries (ZMod 37)`, `f^{37} =
(expand 37 f).map(frobenius)` collects only the degrees divisible by `37`, so the degree-`68`
coefficient of `f^{37}` is `0` (since `37 ∤ 68`).  Reducing `(AH−1)^{37}` coefficientwise mod `37`
(`toZModPS`, `toZModPS_pow`) and applying this collapses `ahCoeff37 mod 37` to `0`.

Consequently `formalSum68 mod 37 = u·0 = 0` (`formalSum68_rIntegralToZMod_eq`), and the degree-`68`
homogeneous slice's `varpi^32` mod-`37` coordinate is `0` (`deg68_slice_coordMod37_eq_zero`): the
degree-`68` slice does **not** contribute to `secondOrderPart37` at the mod-`37` order — it is itself
divisible by `37` (a higher-order effect).  This *resolves* the degree-`68` slice's contribution to
the irregular `varpi^32` coordinate. -/

/-- **Frobenius vanishing in `PowerSeries (ZMod 37)`**: for any `f`, `coeff_{68}(f^{37}) = 0`
(proven).  Since `ZMod 37` has expchar `37`, `f^{37} = (expand 37 f).map(frobenius)` (the
freshman's dream, `MvPowerSeries.map_frobenius_expand`), and `expand 37` is supported on degrees
divisible by `37`; as `37 ∤ 68`, `coeff_{68}(expand 37 f) = 0` (`coeff_expand_of_not_dvd`), so
`coeff_{68}(f^{37}) = frobenius(0) = 0`. -/
theorem coeff_sixtyeight_pow37_eq_zero (f : PowerSeries (ZMod 37)) :
    (PowerSeries.coeff (R := ZMod 37) 68) (f ^ 37) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  haveI : ExpChar (ZMod 37) 37 := ExpChar.prime (by norm_num)
  have hfrob :
      (PowerSeries.expand 37 (by norm_num) f).map (frobenius (ZMod 37) 37) = f ^ 37 :=
    MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 37) 37 (by norm_num) (f := f)
  rw [← hfrob, PowerSeries.coeff_map,
    PowerSeries.coeff_expand_of_not_dvd 37 (by norm_num) f (by norm_num : ¬ (37 ∣ 68)), map_zero]

/-- **The Frobenius coefficient `ahCoeff37` vanishes mod `37`** (proven, axiom-clean):
`rIntegralToZMod 37 (ahCoeff37) = 0`.

`rIntegralToZMod 37 (ahCoeff37) = toZMod([λ^{68} of (AH−1)^{37}])`, which by the coefficientwise
reduction `toZModPS` (`coeff_toZModPS`) equals `coeff_{68}` of the mod-`37` reduction of `(AH−1)^{37}
= ((AH−1) reduced)^{37}` (`toZModPS_pow`), and that is `0` by `coeff_sixtyeight_pow37_eq_zero` (the
Frobenius vanishing, `37 ∤ 68`).  So the entire degree-`68` formal source vanishes mod `37`. -/
theorem ahCoeff37_rIntegralToZMod_eq_zero :
    Furtwaengler.DieudonneDwork.rIntegralToZMod 37 ahCoeff37 = 0 := by
  have hpI : Furtwaengler.DieudonneDwork.IsRIntegralPS 37
      (rationalArtinHasseNormalizedExpMinusOneSeries 37 - 1) :=
    rationalArtinHasseNormalizedExpMinusOneSeries_sub_one_isPIntegral (p := 37)
  rw [Furtwaengler.DieudonneDwork.rIntegralToZMod_apply]
  have hval : (ahCoeff37 : ℚ) = (PowerSeries.coeff (R := ℚ) 68)
      ((rationalArtinHasseNormalizedExpMinusOneSeries 37 - 1) ^ 37) := rfl
  have key : Furtwaengler.DieudonneDwork.IsRIntegralRat.toZMod
        ((PowerSeries.coeff (R := ℚ) 68)
          ((rationalArtinHasseNormalizedExpMinusOneSeries 37 - 1) ^ 37))
        ((hpI.pow 37) 68) = 0 := by
    rw [← Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_toZModPS (hpI.pow 37) 68,
      Furtwaengler.DieudonneDwork.IsRIntegralPS.toZModPS_pow hpI 37]
    exact coeff_sixtyeight_pow37_eq_zero hpI.toZModPS
  simp only [Furtwaengler.DieudonneDwork.IsRIntegralRat.toZMod] at key ⊢
  rw [hval]
  exact key

/-- **The formal degree-`68` source vanishes mod `37`** (proven): `rIntegralToZMod 37 (formalSum68) =
0`.  Combines the Frobenius collapse `formalSum68_rIntegralToZMod_eq` (`= u · rIntegralToZMod 37
ahCoeff37`) with `ahCoeff37_rIntegralToZMod_eq_zero` (`= 0`). -/
theorem formalSum68_rIntegralToZMod_eq_zero :
    Furtwaengler.DieudonneDwork.rIntegralToZMod 37
        (formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) = 0 := by
  rw [formalSum68_rIntegralToZMod_eq, ahCoeff37_rIntegralToZMod_eq_zero, mul_zero]

/-- **`castHom` of `q.num·q.den⁻¹` over `ZMod 37²` is `rIntegralToZMod 37 q`** (proven): for a
`37`-integral rational `q`, `castHom((q.num : ZMod 37²)·(q.den : ZMod 37²)⁻¹) = (q.num : ZMod
37)·(q.den : ZMod 37)⁻¹ = rIntegralToZMod 37 q`, since `castHom` is a ring hom commuting with the
integer/nat casts and (as `q.den` is a `37`-unit) with the inverse, and the result is exactly
`IsRIntegralRat.toZMod`.  Bridges the mod-`37²` residue's `castHom` to the first-order
`rIntegralToZMod` used in the Frobenius collapse. -/
theorem castHom_num_den_eq_rIntegralToZMod
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (((q : ℚ).num : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹) =
      Furtwaengler.DieudonneDwork.rIntegralToZMod 37 q := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hunit2 : IsUnit (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) := by
    have hcop : ((q : ℚ).den : ℕ).Coprime 37 := q.property
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_right 2)
  rw [map_mul, map_intCast,
    show (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        ((((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹) =
      ((ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)))⁻¹ from
      (inv_eq_of_mul_eq_one_left (by rw [mul_comm, ← map_mul,
        ZMod.mul_inv_of_unit _ hunit2, map_one])).symm,
    map_natCast, Furtwaengler.DieudonneDwork.rIntegralToZMod_apply,
    Furtwaengler.DieudonneDwork.IsRIntegralRat.toZMod]

omit [NumberField.IsCMField K] in
/-- **The degree-`68` homogeneous slice has zero `varpi^32` coordinate mod `37`** (proven,
axiom-clean): for `x = dworkParameterApprox 72` and the column index `i` with `(i : ℕ) = 32`,

  `castHom (coordModSq(deg-68 slice)) = 0`   (in `ZMod 37`),

i.e. the slice's `varpi^32` mod-`37²` coordinate is divisible by `37`.  From
`factorial37_deg68_slice_coordMod37` (`u·(coord mod 37) = -(formalSum68 residue mod 37)`): the right
side is `-castHom((formalSum68.num)·(formalSum68.den)⁻¹) = -rIntegralToZMod 37 formalSum68 = 0`
(`castHom_num_den_eq_rIntegralToZMod`, `formalSum68_rIntegralToZMod_eq_zero`); since `u` is a unit
(`u68_isUnit`), `coord mod 37 = 0`.  **The degree-`68` slice does not contribute to
`secondOrderPart37` at the mod-`37` order** — it is itself divisible by `37`. -/
theorem deg68_slice_coordMod37_eq_zero
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
            (p := 37) (K := K) 71 68 x hxmem)) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hcoord := factorial37_deg68_slice_coordMod37 (K := K) i hi hx hxmem
  rw [castHom_num_den_eq_rIntegralToZMod formalSum68,
    formalSum68_rIntegralToZMod_eq_zero, neg_zero] at hcoord
  exact (u68_isUnit.mul_right_eq_zero).mp hcoord

end BernoulliRegular.FLT37.Eichler

end
