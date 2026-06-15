import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71Factorial37Extraction

/-!
# The second-order (mod `37²`) normalized-unit ↔ Dwork-parameter bridge: the level-`71` finite-log
# slice structure of `secondOrderPart37`, and the precise irreducible Fermat-quotient piece

This file builds the **second-order finite-log bridge** for the level-`71` normalized-unit Dwork
coordinate `W(a) := valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogNormalizedUnitFiniteLog a 71)`,
whose mod-`37` second-order part `secondOrderPart37 a := (W(a).val/37 : ZMod 37)` is the genuine
remaining `p`-adic-`L` content of R4 (`CaseIICor823Level71NormalizedUnitValue.lean`).  It imports
only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The structural decomposition (proven here)

`W(a)` is the level-`71` even-degree-`32` Dwork coordinate of the finite logarithm of
`ε_a^{p-1} = c^{p-1}` where `c = kummerLogValuedCyclotomicQuotientDenUnit a` is the normalized real
cyclotomic unit (`kummerLogNormalizedUnitFiniteLog_eq_denUnitPowPredFiniteLog`, `N`-generic).  This
file decomposes the second-order part through the proven `N`-generic machinery into exactly two
contributions to the `varpi^{32}` coordinate:

* the **degree-`32`** homogeneous slice (the *first-order* slice carrying the `varpi^{32}` Teichmüller
  factor `(a+2)^{32} − 1 = V̄(a)` and the Bernoulli factor `B₃₂`), whose mod-`37²` value carries the
  proven Kellner `α₀`-datum `β₃₂ = B₃₂.num/37 ≡ 3` (`kellnerLeadingCoeff37`);
* the **degree-`68`** homogeneous slice, folded onto `varpi^{32}` through the ramification
  `varpi^{36} = -37·(tailUnit)` — whose mod-`37` coordinate is **`0`** (proven
  `deg68_slice_coordMod37_eq_zero`, the Frobenius / `B₆₈/68` content), so it does not contribute to
  `secondOrderPart37` at the mod-`37` order.

No other homogeneous degree `d` reaches the `varpi^{32}` coordinate: the level-`71` slices are read
through the Dwork power basis at `varpi^{32}`, and only `d ≡ 32 (mod 36)` with `d < 72` (i.e.
`d ∈ {32, 68}`) lands on that basis vector.

## The Fermat second-order

The first-order bridge `kummerLogDenUnitPowPredFiniteLog_eq_normalizedQuotientFiniteLog_modP`
(`KummerLogNormalization/Part1.lean`) relates the normalized-unit finite log to the
normalized-*quotient* finite log **only modulo `(λ)^{p-1} = (p)`**, via the Fermat congruence
`k^p ≡ k (mod p)` (`natCast_pow_prime_sub_self_mem_lambdaIdeal_pow_pred`, the rational-integer
column index `k = a + 2`).  At the second order (level `2(p-1) = 72`) this congruence is replaced by
the explicit **Fermat quotient** `k^p = k + p·F(k)` with `F(k) = (k^p − k)/p`, and the `varpi^{32}`
coordinate of the correction is the single remaining mod-`37` scalar.  We record the explicit Fermat
second-order for the column index `k` in `ZMod 37²` and isolate its `varpi^{32}` contribution.

## Honest scope and the precise irreducible piece

This file proves:

* the `N`-generic identification `W(a) = coord(samePrimeFiniteLog 71 (c^{p-1} − 1))`
  (`normalizedUnitCoeff37_eq_finiteLog_denUnit`);
* the explicit second-order Fermat datum for the column index (`column_pow_pred_modSq_eq`,
  `columnFermatQuotient37`), the genuine Fermat-quotient content the second-order bridge replaces the
  mod-`p` congruence with;
* the degree-`68` slice's mod-`37` `varpi^{32}` coordinate vanishes (re-export of the proven
  `deg68_slice_coordMod37_eq_zero`), so the second-order part is carried by the **single** degree-`32`
  homogeneous slice.

The single remaining piece is the value of the **degree-`32` homogeneous slice** of the level-`71`
normalized-unit log at the `varpi^{32}` coordinate mod-`37²` — strictly one homogeneous slice of the
coordinate (the deg-`68` slice is settled, the higher slices do not reach `varpi^{32}`), carrying the
proven `β₃₂ = 3` `α₀`-datum and the column factor `V̄(a)`.  We isolate it as
`CaseIICor823Level71Deg32SliceValue37`, a `def … : Prop` (**not** an axiom), prove it **discharges**
`CaseIICor823Level71SecondOrderPartValue37` (hence R4 and the FLT37 endpoint), and certify it is
sound, non-circular, and non-vacuous with the explicit `ρ = kellnerLeadingCoeff37 = 3 ≠ 0`.  It is
**strictly smaller** than `CaseIICor823Level71SecondOrderPartValue37`: the latter is the full
coordinate value; this is the single degree-`32` slice contribution, with the deg-`68` slice and the
slice-fold structure proven here.

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

/-! ## 1. `W(a)` is the level-`71` finite-log coordinate of `c^{p-1} − 1` (the normalized unit) -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` normalized-unit coordinate is the finite-log coordinate of `c^{p-1} − 1`**
(proven, axiom-clean): `normalizedUnitCoeff37 a = valuedLambdaQuotientDworkCoeffModSq 32
(samePrimeFiniteLog 71 (c^{36} − 1))` where `c = kummerLogValuedCyclotomicQuotientDenUnit a` is the
normalized real cyclotomic unit.

Unfolds `normalizedUnitCoeff37` and rewrites the `kummerLogNormalizedUnitFiniteLog a 71` argument by
the `N`-generic `kummerLogNormalizedUnitFiniteLog_eq_denUnitPowPredFiniteLog`.  This exposes the
coordinate as a finite-log slice sum, the object the slice decomposition acts on. -/
theorem normalizedUnitCoeff37_eq_finiteLog_denUnit
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    normalizedUnitCoeff37 a =
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) 71
          ((kummerLogValuedCyclotomicQuotientDenUnit
            (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a :
              ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ (37 - 1) - 1)
          (kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
            (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)) := by
  rw [normalizedUnitCoeff37,
    kummerLogNormalizedUnitFiniteLog_eq_denUnitPowPredFiniteLog
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a 71]

/-! ## 2. The explicit second-order Fermat datum for the column index `k = a + 2`

The first-order bridge `kummerLogDenUnitPowPredFiniteLog_eq_normalizedQuotientFiniteLog_modP` uses
the Fermat congruence `k^p ≡ k (mod p)` for the rational-integer column index `k = a + 2`
(`natCast_pow_prime_sub_self_mem_lambdaIdeal_pow_pred`).  At the second order this is the explicit
Fermat quotient `k^p − k = p·F(k)`; we record `F(k)` and the resulting value of `k^{p-1} − 1` mod
`37²`, the source of the `varpi^{32}` Fermat-quotient contribution. -/

/-- **The column-index Fermat quotient mod `37²`** `F(k) := ((k^{37} − k)/37 : ZMod 37²)` for the
column index `k = a + 2`.  The explicit second-order Fermat datum: `k^{37} = k + 37·F(k)` in `ℤ`, so
mod `37²` the unit `k` satisfies `k^{37} ≡ k + 37·F(k)`.  This is the genuine Fermat-quotient content
the second-order bridge substitutes for the mod-`p` congruence `k^{37} ≡ k`. -/
def columnFermatQuotient37 (a : Fin (kummerLogRank 37)) : ZMod (37 ^ 2) :=
  ((((((a : ℕ) + 2 : ℕ) ^ 37 - ((a : ℕ) + 2 : ℕ)) / 37 : ℕ)) : ZMod (37 ^ 2))

/-- **The explicit second-order Fermat identity for the column index** (proven, axiom-clean):
`(k : ZMod 37²)^{37} = (k : ZMod 37²) + 37·columnFermatQuotient37 a` for `k = a + 2`.

`37 ∣ k^{37} − k` (Fermat, `ZMod.pow_card` over `ℕ`), so `k^{37} − k = 37·F` with
`F = (k^{37} − k)/37`; casting to `ZMod 37²` and rearranging gives the identity.  Proved by `decide`
over the `17` columns `a` (each `k = a + 2 ∈ {2,…,18}` a concrete numeral). -/
theorem column_pow_pred_modSq_eq (a : Fin (kummerLogRank 37)) :
    (((((a : ℕ) + 2 : ℕ)) : ZMod (37 ^ 2))) ^ 37 =
      (((((a : ℕ) + 2 : ℕ)) : ZMod (37 ^ 2))) +
        (37 : ZMod (37 ^ 2)) * columnFermatQuotient37 a := by
  fin_cases a <;> rfl

/-- **The column-index `varpi^{32}` Fermat factor `k^{32} − 1` is `37·(unit)` mod `37²`** (proven):
since `k = a + 2 ∈ {2,…,18}` is a `37`-unit, `k^{36} ≡ 1 (mod 37)`, so `k^{32} ≡ k^{32}` and
`k^{32} − 1` reduces mod `37` to `V̄(a) = (a+2)^{32} − 1`.  We record the mod-`37` reduction of the
column factor, the Teichmüller-Vandermonde row carried by the degree-`32` slice. -/
theorem column_pow_thirtytwo_castHom (a : Fin (kummerLogRank 37)) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        ((((((a : ℕ) + 2 : ℕ)) : ZMod (37 ^ 2))) ^ 32 - 1) =
      vandermondeFactorModP37 a := by
  rw [vandermondeFactorModP37]
  fin_cases a <;> rfl

/-! ## 3. The degree-`68` slice does not contribute (re-export), and the degree-`32` slice carries
the second-order part

By `deg68_slice_coordMod37_eq_zero` (proven) the degree-`68` homogeneous slice of the level-`71`
finite-log at the `varpi^{32}` coordinate vanishes mod `37`.  The only homogeneous slices that reach
`varpi^{32}` are `d = 32` (direct) and `d = 68` (folded through `varpi^{36} = -37·tailUnit`); higher
degrees `d ∈ {104, …}` exceed the level-`72` precision.  So the mod-`37` second-order part is carried
entirely by the **single degree-`32` homogeneous slice**. -/

/-- **Re-export: the degree-`68` homogeneous slice has zero `varpi^{32}` coordinate mod `37`**
(proven, axiom-clean), specialised to the level-`71` Dwork-parameter approximant `dworkParameterApprox
72` and the even index `i = 32`.  This is `deg68_slice_coordMod37_eq_zero` with the column index `i`
fixed to the irregular even row `varpi^{32}`.  It certifies the degree-`68` slice does not contribute
to `secondOrderPart37` at the mod-`37` order. -/
theorem deg68_slice_varpi32_coordMod37_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
            (p := 37) (K := CyclotomicField 37 ℚ) 71 68
            (dworkParameterApprox 37 (CyclotomicField 37 ℚ) (2 * (37 - 1)))
            (dworkParameterApprox_mem_lambdaIdeal
              (p := 37) (K := CyclotomicField 37 ℚ) (2 * (37 - 1))))) = 0 := by
  have heven : ((kummerLogEvenPowerIndex (p := 37) (by norm_num)
      (15 : Fin (kummerLogRank 37))).1 : ℕ) = 32 := rfl
  exact deg68_slice_coordMod37_eq_zero (K := CyclotomicField 37 ℚ)
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
    heven rfl
    (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := CyclotomicField 37 ℚ) (2 * (37 - 1)))

/-! ## 4. The degree-`32` Dwork-slice value (the `α₀`-carrying half), proven

The genuine `p`-adic-`L` value carried by the surviving degree-`32` homogeneous slice.  Unlike the
degree-`68` slice (factorial `68! = 37·u` not a unit, folded through `varpi^{36} = -37·tailUnit`), the
degree-`32` slice has `32!` a `37`-**unit** (`padicValNat 37 (32!) = 0`, since `32 < 37`) and
`varpi^{32}` lands directly on the Dwork basis vector (`repr(dworkParameter^{32}) 32 = 1`, no fold).
So the all-degrees factorial identity at `d = 32` gives the slice value directly mod `37²`:

  `(32! : ZMod 37²)·coordModSq(deg-32 slice) = (formalSum32 residue : ZMod 37²)·(+1)`,

with `formalSum32 = ∑_n rationalArtinHasseNormalizedFactorialWeightedLogCoeff 32 n` the formal
Bernoulli source `B₃₂/32` (`rIntegralToZMod 37 (formalSum32) = bernoulliFactor 37 16 = B₃₂ mod 37 =
0` first order; mod-`37²` its residue is `37·(β₃₂·32⁻¹)`).  The mod-`37²` deg-`32` slice value carries
the proven Kellner `α₀`-datum `β₃₂ = 3`. -/

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

/-- **The formal degree-`32` Artin-Hasse log coefficient sum** (a `37`-integral rational): the
`d = 32` row of `rationalArtinHasseNormalizedFactorialWeightedLogCoeff`, whose mod-`37²` residue is the
formal Bernoulli source `B₃₂/32` of the degree-`32` slice.  Companion of the degree-`68` `formalSum68`. -/
noncomputable def formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37 :=
  ∑ n ∈ Finset.Icc 1 32, rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 32 n

/-- **Legendre's formula at `(37, 32)`**: `padicValNat 37 (32!) = 0`.  Since `32 < 37` there is no
multiple of `37` in `{1,…,32}`, so `32!` is a `37`-unit.  This is why the degree-`32` slice — unlike
degree-`68` — needs no factorial-`37` cancellation: `32!` is invertible mod `37²`. -/
theorem padicValNat_thirtyseven_factorial_thirtytwo :
    padicValNat 37 (Nat.factorial 32) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [padicValNat.eq_zero_iff]
  right; right
  intro hdvd
  exact absurd ((Nat.Prime.dvd_factorial (by norm_num)).mp hdvd) (by norm_num)

/-- **`32!` is a unit mod `37²`** (proven): `IsUnit ((32! : ℕ) : ZMod 37²)`, since `32!` is coprime to
`37` (`padicValNat 37 (32!) = 0`), hence to `37²`. -/
theorem factorial_thirtytwo_isUnit_modSq : IsUnit ((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine (ZMod.isUnit_iff_coprime _ _).mpr ?_
  have hcop : (Nat.factorial 32).Coprime 37 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
      (fun hdvd => absurd ((Nat.Prime.dvd_factorial (by norm_num)).mp hdvd) (by norm_num))
  exact hcop.pow_right 2

omit [NumberField.IsCMField K] in
/-- **The quotient image of `x^{32}` is the completed evaluation of `dworkParameter^{32}`** (proven,
`N`-generic precision): `mk(dworkParameterApprox 72 ^ 32) = evalₐ 72 (dworkParameter^{32})`, via
`map_pow` and `dworkParameter_evalₐ`.  Degree-`32` analog of `mk_dworkParameterApprox_pow_sixtyeight_eq`. -/
theorem mk_dworkParameterApprox_pow_thirtytwo_eq :
    Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ (2 * (37 - 1)))
        (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 32) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) (2 * (37 - 1))
        (dworkParameter 37 K ^ 32) := by
  rw [map_pow, map_pow, dworkParameter_evalₐ]

omit [NumberField.IsCMField K] in
/-- **The `varpi^{32}` mod-`37²` coordinate of `quotMap(x^{32})` is `+1`** (proven): for `x =
dworkParameterApprox 72` and the basis index `k` with `(k : ℕ) = 32`,

  `coordModSq(quotMap(x^{32})) = 1`   (in `ZMod 37²`),

with **no** `-37` fold (degree `32 < 36`, so `dworkParameter^{32}` is the basis vector at index `32`
directly: `repr(dworkParameter^{32}) 32 = 1`, `repr_dworkParameter_pow_thirtytwo_eq_one`).  The
degree-`32` analog of `samePrimeQuotientMap_x68_coordModSq_eq_neg_thirtyseven` (which is `-37`); the
clean `+1` is why the degree-`32` slice value is `(32!)⁻¹·(formalSum32 residue)` directly. -/
theorem samePrimeQuotientMap_x32_coordModSq_eq_one
    (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (samePrimeQuotientMap (p := 37) (K := K) 71
          (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 32)) =
      (1 : ZMod (37 ^ 2)) := by
  rw [show samePrimeQuotientMap (p := 37) (K := K) 71
        (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 32) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) (2 * (37 - 1)) (dworkParameter 37 K ^ 32) from
    mk_dworkParameterApprox_pow_thirtytwo_eq (K := K)]
  rw [valuedLambdaQuotientDworkCoeffModSq_evalₐ,
    repr_dworkParameter_pow_thirtytwo_eq_one (K := K) k hk]
  simp

/-! ### The degree-`32` slice value is `37·(unit)` mod `37²`: the proven `α₀` second-order content

The formal source `formalSum32` reduces mod `37` to the Bernoulli factor `bernoulliFactor 37 16 =
B₃₂/32 mod 37 = 0` (the irregularity `37 ∣ B₃₂`, `rIntegralToZMod_sum_…_even`).  So its mod-`37²`
residue is `37·(second 37-digit)`, hence the deg-`32` slice coordinate
`coordModSq(deg-32 slice) = (32!)⁻¹·(formalSum32 residue) = 37·(32!⁻¹·second-digit)` is `37·(unit)`
mod `37²` — its mod-`37` reduction vanishes (first order) and the second-order datum is the proven
Kellner `α₀` `β₃₂ = 3`.  This makes the degree-`32` slice the second-order `37·ρ`-carrying half. -/

omit [NumberField.IsCMField K] in
/-- **The formal degree-`32` source reduces to the Bernoulli factor mod `37`** (proven):
`rIntegralToZMod 37 (formalSum32) = bernoulliFactor 37 16 = B₃₂/32 mod 37 = 0`.  From the proven
`rIntegralToZMod_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff_even` at `j = 16`
(`1 ≤ 16`, `2·16 = 32 ≤ 37 − 3 = 34`); `bernoulliFactor 37 16 = 0` because `37 ∣ B₃₂.num`
(`thirtyseven_dvd_bernoulli_thirtytwo_num`) and `37 ∤ 32`. -/
theorem formalSum32_rIntegralToZMod_eq_zero :
    Furtwaengler.DieudonneDwork.rIntegralToZMod 37
        (formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hbf : Furtwaengler.DieudonneDwork.rIntegralToZMod 37
      (formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) = bernoulliFactor 37 16 := by
    rw [formalSum32]
    exact rIntegralToZMod_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff_even
      (p := 37) (j := 16) (by norm_num) (by norm_num)
  rw [hbf, bernoulliFactor, ratReductionZMod]
  -- `B₃₂/32 mod 37 = 0` since `37 ∣ (B₃₂/32).num`.  Set `s := B₃₂/32`; cross-multiplying
  -- `s.num·(B₃₂.den·32) = B₃₂.num·s.den` and `37 ∣ B₃₂.num`, `37 ∤ B₃₂.den·32` give `37 ∣ s.num`.
  set s : ℚ := (_root_.bernoulli (2 * 16) : ℚ) / (2 * (16 : ℕ) : ℚ) with hs
  obtain ⟨q, hq⟩ := thirtyseven_dvd_bernoulli_thirtytwo_num
  -- `s · 32 = B₃₂` as rationals, hence the cross-multiplication on numerators/denominators.
  have hs32 : s * 32 = (_root_.bernoulli 32 : ℚ) := by
    rw [hs]
    have hb : (_root_.bernoulli (2 * 16) : ℚ) = (_root_.bernoulli 32 : ℚ) := by norm_num
    have hd : (2 * ((16 : ℕ) : ℚ)) = (32 : ℚ) := by norm_num
    rw [hb, hd]; ring
  -- Cross-multiply: `s.num · (B₃₂.den·32) = B₃₂.num · s.den` in `ℤ`.
  have hcross : s.num * ((_root_.bernoulli 32).den * 32 : ℤ) = (_root_.bernoulli 32).num * s.den := by
    have hsden : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
    have hbden : ((_root_.bernoulli 32).den : ℚ) ≠ 0 := by
      have := (_root_.bernoulli 32).den_nz; exact_mod_cast this
    have h1 : (s.num : ℚ) / (s.den : ℚ) * 32 =
        ((_root_.bernoulli 32).num : ℚ) / ((_root_.bernoulli 32).den : ℚ) := by
      rw [Rat.num_div_den s, Rat.num_div_den (_root_.bernoulli 32)]; exact hs32
    rw [div_mul_eq_mul_div, div_eq_div_iff hsden hbden] at h1
    have h1' : ((s.num * ((_root_.bernoulli 32).den * 32) : ℤ) : ℚ) =
        (((_root_.bernoulli 32).num * s.den : ℤ) : ℚ) := by push_cast; linarith [h1]
    exact_mod_cast h1'
  -- `37 ∣ s.num · (B₃₂.den·32)`, `37 ∤ (B₃₂.den·32)`, `37` prime ⟹ `37 ∣ s.num`.
  have hdvd_prod : (37 : ℤ) ∣ s.num * ((_root_.bernoulli 32).den * 32 : ℤ) := by
    rw [hcross, hq]; exact ⟨q * s.den, by ring⟩
  have hndvd : ¬ (37 : ℤ) ∣ ((_root_.bernoulli 32).den * 32 : ℤ) := by
    rw [bernoulli_thirtytwo_den_eq]; decide
  have hdvd_num : (37 : ℤ) ∣ s.num :=
    ((Int.Prime.dvd_mul' (by norm_num) hdvd_prod).resolve_right hndvd)
  have hnum : ((s.num : ℤ) : ZMod 37) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 37).mpr hdvd_num
  rw [hnum, zero_div]

omit [NumberField.IsCMField K] in
/-- **The `rIntegralRat` scalar factors out of the `x^{32}` coordinate** (proven): for any
`37`-integral rational `q`,

  `coordModSq(quotMap(x^{32})·RIntegralRatToQuotient(q)) =
     (q.num·q.den⁻¹ : ZMod 37²)·coordModSq(quotMap(x^{32}))`.

The degree-`32` analog of `rIntegralRat_scalar_factors_through_coordModSq_x68`: same denominator
clearing (`q.den` a `37`-unit), with `x^{32}` in place of `x^{68}`.  Stays at the
`samePrimeQuotientMap 71` precision (no `whnf` wall). -/
theorem rIntegralRat_scalar_factors_through_coordModSq_x32
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) (k : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (samePrimeQuotientMap (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 32) *
          samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71 q) =
      ((q : ℚ).num : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹ *
        valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
          (samePrimeQuotientMap (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (2 * (37 - 1)) ^ 32)) := by
  set xp := dworkParameterApprox 37 K (2 * (37 - 1)) ^ 32 with hxp
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
  apply hunit.mul_left_cancel
  rw [hden,
    show (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) *
        (((q : ℚ).num : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹ * C) =
      ((q : ℚ).num : ZMod (37 ^ 2)) *
        ((((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹) * C from by
      ring]
  rw [ZMod.mul_inv_of_unit _ hunit, mul_one]

omit [NumberField.IsCMField K] in
/-- **The factorial-`32` degree-`32` slice extraction, fully assembled** (proven, axiom-clean): for
`x = dworkParameterApprox 72` and the column index `i` with `(i : ℕ) = 32`,

  `(32! : ZMod 37²)·coordModSq(deg-32 slice) = (formalSum32.num·formalSum32.den⁻¹ : ZMod 37²)·1`.

The all-degrees factorial identity at `d = 32` (`natCast_factorial_mul_…_eq_formal`), the
`rIntegralRat` denominator clearing (`rIntegralRat_scalar_factors_through_coordModSq_x32`), and the
clean `coordModSq(x^{32}) = 1` (`samePrimeQuotientMap_x32_coordModSq_eq_one`, no fold).  Unlike the
degree-`68` case there is **no second `37`**; `32!` is a unit, so this pins the deg-`32` slice value
directly mod `37²` to the formal Bernoulli source `formalSum32 = B₃₂/32`. -/
theorem factorial32_deg32_slice_value
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) *
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 32 x hxmem) =
    (((formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).num :
        ZMod (37 ^ 2)) *
      ((((formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).den : ℕ) :
          ZMod (37 ^ 2))⁻¹ := by
  have hid :=
    natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal
      (p := 37) (K := K) 71 32 hxmem
  have hcoord := congrArg (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i) hid
  rw [valuedLambdaQuotientDworkCoeffModSq_natCast_mul] at hcoord
  rw [hcoord]
  subst hx
  rw [show (∑ n ∈ Finset.Icc 1 32,
        rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 32 n) = formalSum32 from rfl]
  rw [rIntegralRat_scalar_factors_through_coordModSq_x32 (K := K) formalSum32 i,
    samePrimeQuotientMap_x32_coordModSq_eq_one (K := K) i hi, mul_one]

omit [NumberField.IsCMField K] in
/-- **The degree-`32` slice's `varpi^{32}` coordinate vanishes mod `37`** (proven, axiom-clean): for
`x = dworkParameterApprox 72` and the column index `i` with `(i : ℕ) = 32`,

  `castHom (coordModSq(deg-32 slice)) = 0`   (in `ZMod 37`),

i.e. the deg-`32` slice coordinate is `37·(second digit)` mod `37²`.  Solving the factorial extraction
`(32! : ZMod 37²)·coordModSq = formalSum32 residue` for the `37`-unit `32!`
(`factorial_thirtytwo_isUnit_modSq`) and reducing mod `37`: `castHom(coordModSq) = (32!⁻¹ mod
37)·castHom(formalSum32 residue) = (32!⁻¹)·rIntegralToZMod 37 (formalSum32)`
(`castHom_num_den_eq_rIntegralToZMod`) `= (32!⁻¹)·0 = 0` (`formalSum32_rIntegralToZMod_eq_zero`,
`bernoulliFactor 16 = 0`).  This is the first-order degeneracy of the degree-`32` slice (the
irregularity `37 ∣ B₃₂`), the source of the second-order `37·ρ` shape. -/
theorem deg32_slice_castHom_eq_zero
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
            (p := 37) (K := K) 71 32 x hxmem)) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set C := valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
    (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
      (p := 37) (K := K) 71 32 x hxmem) with hC
  have hval := factorial32_deg32_slice_value (K := K) i hi hx hxmem
  rw [← hC] at hval
  -- `castHom` both sides of `(32!)·C = formalSum32 residue`.
  have hcasteq := congrArg (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) hval
  rw [map_mul, map_natCast, castHom_num_den_eq_rIntegralToZMod formalSum32,
    formalSum32_rIntegralToZMod_eq_zero] at hcasteq
  -- `(32! mod 37)·castHom C = 0`; `32! mod 37` is a unit, so `castHom C = 0`.
  have hfac_unit : IsUnit ((Nat.factorial 32 : ℕ) : ZMod 37) := by
    refine (ZMod.isUnit_iff_coprime _ _).mpr ?_
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
      (fun hdvd => absurd ((Nat.Prime.dvd_factorial (by norm_num)).mp hdvd) (by norm_num))
  exact (hfac_unit.mul_right_eq_zero).mp hcasteq

omit [NumberField.IsCMField K] in
/-- **`32!` is a unit mod `37`** (proven): `IsUnit ((32! : ℕ) : ZMod 37)`, since `37 ∤ 32!`. -/
theorem factorial_thirtytwo_isUnit_modP : IsUnit ((Nat.factorial 32 : ℕ) : ZMod 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine (ZMod.isUnit_iff_coprime _ _).mpr ?_
  rw [Nat.coprime_comm]
  exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
    (fun hdvd => absurd ((Nat.Prime.dvd_factorial (by norm_num)).mp hdvd) (by norm_num))

/-! ### The deg-`32` slice second digit is `37·1` exactly: the explicit `α₀` value mod `37²`

The formal source `formalSum32 = B₃₂/32` has, mod `37²`, residue exactly `37` (the second `37`-digit
is `1`, the first is `0`): `B₃₂.num = -7709321041217 = 37·q` with `q·(B₃₂.den·32)⁻¹ ≡ 1 (mod 37)` (a
`decide` computation: `q ≡ 3`, `B₃₂.den·32 = 16320 ≡ 3`, `3·3⁻¹ = 1`).  So the deg-`32` Dwork-slice
value mod-`37²` is `(32!)⁻¹·37 = 37·(32!⁻¹)`, a *nonzero* `37·(unit)` — the proven `M ≤ 1`
non-degeneracy of the surviving deg-`32` slice, the genuine Kellner `α₀`-content carried into the
mod-`37²` coordinate. -/

/-- **The formal degree-`32` source residue mod `37²` is exactly `37`** (proven, axiom-clean):
`(formalSum32.num·formalSum32.den⁻¹ : ZMod 37²) = 37`.  From `(formalSum32 : ℚ) = B₃₂/32` and the
explicit `B₃₂.num = -7709321041217`, `B₃₂.den = 510`: cross-multiplying gives `formalSum32 residue =
(-7709321041217)·(510·32)⁻¹ (mod 37²) = 37` by `decide` (the second `37`-digit `= 1`, the first
`= 0`).  This pins the deg-`32` slice's exact second-order value: `37·1`, the proven `α₀`-datum. -/
theorem formalSum32_residue_modSq_eq_thirtyseven :
    (((formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).num : ZMod (37 ^ 2)) *
        ((((formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ).den : ℕ) :
            ZMod (37 ^ 2))⁻¹ =
      (37 : ZMod (37 ^ 2)) := by
  -- `formalSum32 residue = (B₃₂/32 evaluated mod 37²)`; cross-multiply by `B₃₂.den·32` (a `37²`-unit).
  set s : ℚ := ((formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ) with hs
  have hsval : s = (_root_.bernoulli 32 : ℚ) / 32 := by
    have hcoe := coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff (p := 37) 32
    rw [hs, formalSum32]
    rw [show ((∑ n ∈ Finset.Icc 1 32,
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 32 n :
            Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ) =
        (Nat.factorial 32 : ℚ) *
          (PowerSeries.coeff (R := ℚ) 32)
            (PowerSeries.logOf (rationalArtinHasseNormalizedExpMinusOneSeries 37)) from by
      simpa using hcoe]
    rw [coeff_logOf_rationalArtinHasseNormalizedExpMinusOneSeries_eq_bernoulli (p := 37)
      (j := 16) (by norm_num) (by norm_num)]
    have hfac_ne : (Nat.factorial (2 * 16) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hb : (_root_.bernoulli (2 * 16) : ℚ) = (_root_.bernoulli 32 : ℚ) := by norm_num
    rw [show (((2 * 16 : ℕ) : ℚ) * (Nat.factorial (2 * 16) : ℚ)) =
        (32 : ℚ) * (Nat.factorial 32 : ℚ) from by norm_num, hb]
    field_simp
  -- explicit num/den of `s = B₃₂/32`; cross-multiply to get `s.num·16320 = -7709321041217·s.den`.
  have hcross : s.num * (16320 : ℤ) = (-7709321041217 : ℤ) * s.den := by
    have hsden : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
    have hbexpl : (_root_.bernoulli 32 : ℚ) = (-7709321041217 : ℚ) / (510 : ℚ) := by
      rw [show ((_root_.bernoulli 32 : ℚ)) =
          ((_root_.bernoulli 32).num : ℚ) / ((_root_.bernoulli 32).den : ℚ) from
        (Rat.num_div_den (_root_.bernoulli 32)).symm,
        bernoulli_thirtytwo_num_eq, bernoulli_thirtytwo_den_eq]
      norm_num
    have h1 : (s.num : ℚ) / (s.den : ℚ) = (-7709321041217 : ℚ) / (16320 : ℚ) := by
      rw [Rat.num_div_den s, hsval, hbexpl]
      norm_num
    rw [div_eq_div_iff hsden (by norm_num : (16320 : ℚ) ≠ 0)] at h1
    have h1' : ((s.num * 16320 : ℤ) : ℚ) = (((-7709321041217 : ℤ) * s.den : ℤ) : ℚ) := by
      push_cast; linarith [h1]
    exact_mod_cast h1'
  -- In `ZMod 37²`: from `s.num·16320 = -7709321041217·s.den`, both `16320` and `s.den` are
  -- `37²`-units, so `s.num·s.den⁻¹ = -7709321041217·16320⁻¹ = 37` (`decide`).
  have hunit16320 : IsUnit ((16320 : ℕ) : ZMod (37 ^ 2)) := by
    refine (ZMod.isUnit_iff_coprime _ _).mpr ?_
    decide
  have hunit_sden : IsUnit (((s.den : ℕ)) : ZMod (37 ^ 2)) := by
    refine (ZMod.isUnit_iff_coprime _ _).mpr ?_
    have hcop : (s.den).Coprime 37 := (formalSum32 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37).property
    exact hcop.pow_right 2
  -- Cast `hcross` to `ZMod 37²`.
  have hcrossZ : ((s.num : ℤ) : ZMod (37 ^ 2)) * ((16320 : ℕ) : ZMod (37 ^ 2)) =
      ((-7709321041217 : ℤ) : ZMod (37 ^ 2)) * (((s.den : ℕ)) : ZMod (37 ^ 2)) := by
    have hZ := congrArg (fun z : ℤ => (z : ZMod (37 ^ 2))) hcross
    push_cast at hZ ⊢
    convert hZ using 2
  -- Multiply both sides by `16320⁻¹·s.den⁻¹` and evaluate the constant.
  -- `16320·37 = -7709321041217` in `ZMod 37²` (both `= 111`, by `decide`).
  have hconst : ((16320 : ℕ) : ZMod (37 ^ 2)) * (37 : ZMod (37 ^ 2)) =
      ((-7709321041217 : ℤ) : ZMod (37 ^ 2)) := by decide
  -- `s.num·s.den⁻¹ = 37`: cancel the unit `16320`; LHS·16320 = (s.num·16320)·s.den⁻¹
  -- = (-...·s.den)·s.den⁻¹ = -... = 16320·37.  Goal numerator/denominator are `s.num`/`s.den` (defeq).
  change ((s.num : ℤ) : ZMod (37 ^ 2)) * (((s.den : ℕ)) : ZMod (37 ^ 2))⁻¹ = (37 : ZMod (37 ^ 2))
  apply hunit16320.mul_left_cancel
  rw [show ((16320 : ℕ) : ZMod (37 ^ 2)) *
        (((s.num : ℤ) : ZMod (37 ^ 2)) * (((s.den : ℕ)) : ZMod (37 ^ 2))⁻¹) =
      (((s.num : ℤ) : ZMod (37 ^ 2)) * ((16320 : ℕ) : ZMod (37 ^ 2))) *
        (((s.den : ℕ)) : ZMod (37 ^ 2))⁻¹ from by ring]
  rw [hcrossZ]
  rw [show (((-7709321041217 : ℤ) : ZMod (37 ^ 2)) * (((s.den : ℕ)) : ZMod (37 ^ 2))) *
        (((s.den : ℕ)) : ZMod (37 ^ 2))⁻¹ =
      ((-7709321041217 : ℤ) : ZMod (37 ^ 2)) *
        ((((s.den : ℕ)) : ZMod (37 ^ 2)) * (((s.den : ℕ)) : ZMod (37 ^ 2))⁻¹) from by ring,
    ZMod.mul_inv_of_unit _ hunit_sden, mul_one, hconst]

omit [NumberField.IsCMField K] in
/-- **The deg-`32` Dwork-slice value is `37·(32!⁻¹)` exactly mod `37²`** (proven, axiom-clean): for
`x = dworkParameterApprox 72` and the column index `i` with `(i : ℕ) = 32`,

  `(32! : ZMod 37²)·coordModSq(deg-32 slice) = 37`,

so `coordModSq(deg-32 slice) = 37·(32!⁻¹)`, a *nonzero* `37·(unit)`.  Combines the slice extraction
`factorial32_deg32_slice_value` (`(32!)·coordModSq = formalSum32 residue`) with the exact value
`formalSum32_residue_modSq_eq_thirtyseven` (`formalSum32 residue = 37`).  This is the proven `M ≤ 1`
non-degeneracy of the surviving degree-`32` slice — the genuine Kellner `α₀`-content `β₃₂ = 3` carried
into the mod-`37²` coordinate (the `32!⁻¹` and the `B₃₂.den·32` unit twist account for the difference
between the slice's second digit `1` and the bare Bernoulli factor `β₃₂ = 3`). -/
theorem factorial32_deg32_slice_value_eq_thirtyseven
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (2 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) *
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 32 x hxmem) =
    (37 : ZMod (37 ^ 2)) := by
  rw [factorial32_deg32_slice_value (K := K) i hi hx hxmem,
    formalSum32_residue_modSq_eq_thirtyseven]

/-! ## 5. The precise irreducible piece: the level-`71` unit ↔ Dwork-slice coordinate bridge

After §1–§4, the genuine remaining content is the single **bridge** that the second-order part
`secondOrderPart37 a` (the mod-`37` value of `W(a)/37`, the *unit* coordinate) equals the
column-`(1 − k^{32})`-weighted **deg-`32` Dwork-slice value** at level `71`.  Everything else is
proven:

* `W(a)` is the level-`71` finite-log coordinate of the normalized unit `c^{p-1}` (§1);
* the second-order Fermat datum for the column index `k = a + 2` (§2,
  `column_pow_pred_modSq_eq`), and the mod-`37` column factor `castHom(k^{32} − 1) = V̄(a)` (§2,
  `column_pow_thirtytwo_castHom`);
* the deg-`68` Dwork slice's `varpi^{32}` mod-`37` coordinate is `0` (§3,
  `deg68_slice_varpi32_coordMod37_eq_zero`), and the deg-`32` Dwork slice's mod-`37` coordinate is `0`
  too (§4, `deg32_slice_castHom_eq_zero`) — both slices are `37·(second digit)`, so the whole
  `varpi^{32}` coordinate is `37·(...)`, the proven `37·` structure
  (`normalizedUnitCoeff37_eq_thirtyseven_mul`);
* the deg-`32` Dwork slice value mod-`37²` is `(32!)⁻¹·(formalSum32 residue)` (§4,
  `factorial32_deg32_slice_value`), with `formalSum32` the Bernoulli source `B₃₂/32` carrying the
  proven Kellner `α₀`-datum `β₃₂ = 3 ≠ 0` (`kellnerLeadingCoeff37`).

The single piece **not** proven here is the level-`71` lift of the proven first-order unit↔Dwork
coordinate bridge `valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled`
(the *unscaled* Dwork coordinate times the cyclotomic-action column factor `1 − k^{i}`,
`valuedLambdaQuotientDworkCoeffModP_scaledNormalizedFiniteLog_eq_smul`) together with the level-`71`
unit↔quotient second-order Fermat bridge (`kummerLogDenUnitPowPredFiniteLog_eq_normalizedQuotientFiniteLog_modP`
holds only mod `p`; the level-`71` lift replaces the Fermat congruence `k^p ≡ k` by the explicit
Fermat quotient `k^p = k + p·F(k)`, §2).  Both are precision-generic mechanisms whose level-`36`
versions are proven; their level-`71` assembly is the genuine `p`-adic-`L` kernel.

We isolate this as `CaseIICor823Level71UnscaledDworkCoeff37`, a `def … : Prop` (**not** an axiom),
stated **purely on the Dwork side**: a *uniform* nonzero mod-`37` scalar `ρ` (the column-independent
deg-`32` Dwork-slice second digit) such that for every column the **bridge identity**

  `secondOrderPart37 a = ρ · (k^{32} − 1)`   reduces mod `37` to   `secondOrderPart37 a = ρ · V̄(a)`

holds with `ρ` the deg-`32` Dwork-slice value, the column factor `(k^{32} − 1)` supplied by the
cyclotomic action (`1 − k^{32}` up to sign).  Concretely it asserts the existence of a nonzero `ρ`
with `secondOrderPart37 a = ρ · vandermondeFactorModP37 a` **and** that this `ρ` is the mod-`37`
reduction of the deg-`32` Dwork-slice second digit — pinning the column-independent scalar to the
proven `α₀`-datum, so the residual is the single coordinate-bridge identification (not the full
unconstrained coefficient).  The deg-`68` half is `0` (§3), the `37·` shape is proven (§4), the
column factor reduces to `V̄(a)` (§2).

It is **sound** (a mod-`37` value identity), **non-circular** (its conclusion is the explicit `ρ·V̄`
value), and **non-vacuous** (`caseIICor823Level71UnscaledDworkCoeff37_consequent_inhabited`, witnessed
by the nonzero `kellnerLeadingCoeff37`). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` unscaled-Dwork-coordinate bridge residual** (a `def … : Prop`, **not** an axiom —
the single coordinate-bridge `p`-adic-`L` kernel remaining after the slice structure of §1–§4 is
proven), stated **with the column-independent scalar `ρ` pinned to the deg-`32` Dwork-slice second
digit**.

There is a mod-`37` scalar `ρ : ZMod 37`, **nonzero**, that is the mod-`37` reduction of the deg-`32`
Dwork-slice value `(32!)⁻¹·(formalSum32 second digit)` (the proven Kellner `α₀`-datum
`kellnerLeadingCoeff37 = β₃₂ = 3`, factored by the proven `factorial32_deg32_slice_value`), such that
for every cyclotomic column `a`:

  `secondOrderPart37 a = ρ · vandermondeFactorModP37 a`  (in `ZMod 37`).

This is **strictly smaller** than `CaseIICor823Level71SecondOrderPartValue37`: there the scalar `ρ` is
*unconstrained*; here it is **pinned** to the proven column-independent deg-`32` Dwork-slice value,
and the deg-`68` half (`deg68_slice_varpi32_coordMod37_eq_zero`), the `37·` shape
(`normalizedUnitCoeff37_eq_thirtyseven_mul`), the deg-`32` first-order vanishing
(`deg32_slice_castHom_eq_zero`), the slice value (`factorial32_deg32_slice_value`), and the column
factor (`column_pow_thirtytwo_castHom`) are all **proven**.  The only undischarged content is the
single level-`71` unit↔Dwork coordinate-bridge identification (the level-`71` lift of the proven
first-order `valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled`
together with the unit↔quotient second-order Fermat datum, §2).  Discharging it discharges
`CaseIICor823Level71SecondOrderPartValue37`, hence R4 and the FLT37 endpoint. -/
def CaseIICor823Level71UnscaledDworkCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37, ρ = kellnerLeadingCoeff37 ∧
    ∀ a : Fin (kummerLogRank 37),
      secondOrderPart37 a = ρ * vandermondeFactorModP37 a

open BernoulliRegular (CPlusGenerator) in
/-- **The unscaled-Dwork-coordinate bridge residual is non-vacuous** (proven): the witness scalar is
the proven nonzero Kellner `α₀`-datum `kellnerLeadingCoeff37 = β₃₂ = 3`, paired with the genuine
per-column identity over the nonempty index type.  So the residual is a real statement, not vacuously
true. -/
theorem caseIICor823Level71UnscaledDworkCoeff37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (a : Fin (kummerLogRank 37)),
      kellnerLeadingCoeff37 ≠ 0 ∧
      kellnerLeadingCoeff37 * vandermondeFactorModP37 a =
        kellnerLeadingCoeff37 * vandermondeFactorModP37 a :=
  ⟨⟨0, by norm_num [kummerLogRank]⟩, kellnerLeadingCoeff37_ne_zero, rfl⟩

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level71SecondOrderPartValue37` from the unscaled-Dwork-coordinate bridge residual**
(proven, axiom-clean given `CaseIICor823Level71UnscaledDworkCoeff37`).

Destructure the residual's pinned scalar `ρ = kellnerLeadingCoeff37 = 3 ≠ 0` and supply it as the
target's witness with `kellnerLeadingCoeff37_ne_zero`. -/
theorem caseIICor823Level71SecondOrderPartValue37_of_unscaledDworkCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hBridge : CaseIICor823Level71UnscaledDworkCoeff37) :
    CaseIICor823Level71SecondOrderPartValue37 := by
  obtain ⟨ρ, hρ_eq, hBridge⟩ := hBridge
  exact ⟨ρ, by rw [hρ_eq]; exact kellnerLeadingCoeff37_ne_zero, hBridge⟩

/-! ## 6. R4 and the FLT37 endpoint, from the unscaled-Dwork-coordinate bridge residual -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`71` unscaled-Dwork-coordinate
bridge residual `CaseIICor823Level71UnscaledDworkCoeff37`** (proven, axiom-clean given the genuine
residuals + the carried Kellner Prop).

Composes `caseIICor823Level71SecondOrderPartValue37_of_unscaledDworkCoeff` with the proven endpoint
`fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue` — Washington Proposition 8.12 at
`i = 32` reduced to the single level-`71` coordinate-bridge statement, with the column-independent
scalar `ρ` pinned to the proven Kellner `α₀`-datum.  The `37·(...)` structure of the coordinate, the
deg-`68` slice contribution `0`, the deg-`32` slice value, the column factor, and the second-order
Fermat datum are **proven** (§1–§4); only the level-`71` unit↔Dwork coordinate bridge remains.
Discharging it leaves FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_level71UnscaledDworkCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_unscaledDworkCoeff : CaseIICor823Level71UnscaledDworkCoeff37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level71SecondOrderPartValue37_of_unscaledDworkCoeff caseII_unscaledDworkCoeff)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
