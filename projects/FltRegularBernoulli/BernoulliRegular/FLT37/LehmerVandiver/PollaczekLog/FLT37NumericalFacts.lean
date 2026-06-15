module

public import BernoulliRegular.FLT37.LehmerVandiver.Certificate
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# FLT37-specific numerical residue facts (LV004g-6)

For the FLT37 certificate tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`, this
file provides the two decide-able numerical facts needed to close
`Q(pollaczekUnit p K i)^k ≠ 1` in the residue field `ZMod 149`.

## Mathematical context

After the term-wise residue substitution (LV004g-4) and transport via the
residue-field isomorphism (LV004g-5), the residue of `pollaczekUnit^k` in
`ZMod ℓ` evaluates to

  `Q(pollaczekUnit^k) = (-1)^{kS} · lehmerVandiverProduct / (1 - t^k)^{kS}`,

where `S = ∑_{b=1}^{(p-1)/2} b^{p-1-i}`. For FLT37 we have `kS = 4·432345 =
1729380 = 148·11685`, so by Fermat the denominator `(1 - 16)^{kS}` is `1` in
`ZMod 149` and the sign `(-1)^{kS}` is `1` (kS even). Hence

  `Q(pollaczekUnit^k) = lehmerVandiverProduct = 107 (mod 149) ≠ 1`,

which combined with the cyclic-criterion `IsPthPower pollaczekUnit ↔
Q(pollaczekUnit^k) = 1` (LV004g main, already shipped) gives
`¬IsPthPower pollaczekUnit` for FLT37.

## Why not the LV001/2 certificate

Note this chain does **not** route through the Washington-style certificate
`prefactor ≠ product` of `LehmerVandiver/Certificate.lean`. That certificate
encodes Washington's `Q_i^k ≢ 1`, where `Q_i = t^{-k·d_i/2} · ∏ (t^{kb}-1)^{b^E}`
is associated to the auxiliary unit `R_i` (Washington's `R_i`, which differs
from our `pollaczekUnit` by a `ζ`-power normalization). The decide-able
facts here close the `pollaczekUnit` chain directly.

## Main results

* `lehmerVandiverProduct_thirtyseven_ne_one`: `lehmerVandiverProduct
  37 32 149 2 4 ≠ 1` in `ZMod 149` (its actual value is 107).
* `one_sub_two_pow_four_pow_kS_eq_one`: `(1 - 2^4)^{4·432345} = 1` in
  `ZMod 149`. Fermat-trivial because `4·432345 = 148·11685` and Fermat
  gives `(1 - 2^4)^{148} = 1`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer GTM 83),
  §8.3 (Pollaczek units), Theorem 9.5 (p. 176).
* `BernoulliRegular/FLT37/LehmerVandiver/Certificate.lean` — definitions of
  `lehmerVandiverProduct` and `lehmerVandiverPrefactor`, plus the LV001/2
  certificate `lehmerVandiverNonTrivial_thirtyseven`.
-/

@[expose] public section

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

section FLT37NumericalFacts

set_option maxRecDepth 4000000
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000

/-- **`lehmerVandiverProduct ≠ 1` for FLT37.** Numerical fact in `ZMod 149`:
the LV001/2 product side `∏_{b=1}^{18} (2^{4b}-1)^{4·b^4}` is not `1`. Its
actual value is `107 (mod 149)`. Combined with the residue substitution
`Q(pollaczekUnit^k) = lehmerVandiverProduct` (LV004g-7 assembly), this gives
`Q(pollaczekUnit^k) ≠ 1` and hence `¬IsPthPower pollaczekUnit` via the
cyclic criterion.

Proved by kernel `decide` with bumped `maxRecDepth` and `maxHeartbeats`,
matching the convention of `lehmerVandiverNonTrivial_thirtyseven`. -/
theorem lehmerVandiverProduct_thirtyseven_ne_one :
    lehmerVandiverProduct 37 32 149 2 4 ≠ 1 := by
  unfold lehmerVandiverProduct
  decide

/-- **Fermat-trivial residue identity for FLT37.** In `ZMod 149`,
`(1 - 2^4)^{4·432345} = 1`. Because `4·432345 = 148·11685` and
`(1 - 2^4)^{148} = 1` by Fermat's little theorem (`1 - 2^4 = -15 ≢ 0
(mod 149)`).

This is the structural fact that lets us drop the `(1 - t^k)^{kS}`
denominator from `Q(pollaczekUnit^k)` for FLT37: in the chain

  `Q(pollaczekUnit^k) = (-1)^{kS} · lehmerVandiverProduct / (1 - t^k)^{kS}`,

the denominator equals `1`, leaving `Q(pollaczekUnit^k) =
lehmerVandiverProduct` (the sign factor `(-1)^{kS}` is `1` because `kS`
is even). -/
theorem one_sub_two_pow_four_pow_kS_eq_one :
    ((1 : ZMod 149) - 2 ^ 4) ^ (4 * 432345) = 1 := by
  have h148 : ((1 : ZMod 149) - 2 ^ 4) ^ 148 = 1 := by decide
  rw [show (4 * 432345 : ℕ) = 148 * 11685 by norm_num, pow_mul, h148, one_pow]

end FLT37NumericalFacts

end LehmerVandiver

end FLT37

end BernoulliRegular

end
