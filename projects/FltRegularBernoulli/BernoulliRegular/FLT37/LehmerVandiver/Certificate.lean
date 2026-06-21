module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lehmer-Vandiver certificate (Washington 9.5)

For an irregular prime `p` with irregular index `i ∈ {2, 4, …, p-3}` (i.e. an
even `i` with `p ∣ num(B_i)`), an auxiliary prime `ℓ ≡ 1 (mod p)` with
`ℓ < p² - p`, write `ℓ = k · p + 1`, and choose `t ∈ ℤ` with
`gcd(t, ℓ) = 1` and `t^k ≢ 1 (mod ℓ)`. Define

  Q_i := t^{-k·d_i/2} · ∏_{b=1}^{(p-1)/2} (t^{kb} - 1)^{b^{p-1-i}}    in ZMod ℓ,

where `d_i := ∑_{a=1}^{(p-1)/2} a^{p-i}`. Washington Theorem 9.5 then says
that if `Q_i^k ≢ 1 (mod ℓ)` for every irregular index `i`, then
`p ∤ h⁺(ℚ(ζ_p))`.

To keep everything `decide`-able (avoiding the noncomputable `⁻¹` on
`ZMod`), we encode the test in the equivalent multiplied-through form:

  Q_i^k ≢ 1 (mod ℓ)  ⟺  (t^{k²·d_i/2}) · 1 ≢ ∏_{b=1}^{(p-1)/2} (t^{kb}-1)^{k·b^{p-1-i}}

i.e. the prefactor and the product disagree as elements of `ZMod ℓ`.

This file provides:

* `lehmerVandiverDPow p i` — the partial power sum
  `d_i := ∑_{a=1}^{(p-1)/2} a^{p-i}`.
* `lehmerVandiverPrefactor p i ℓ t k : ZMod ℓ` — the value `t^{k²·d_i/2}`.
* `lehmerVandiverProduct p i ℓ t k : ZMod ℓ` — the value
  `∏_{b=1}^{(p-1)/2} (t^{kb}-1)^{k·b^{p-1-i}}`.
* `lehmerVandiverNonTrivial p i ℓ t k : Prop` — the predicate
  `lehmerVandiverPrefactor ≠ lehmerVandiverProduct`, equivalent to
  `Q_i^k ≢ 1 (mod ℓ)`.
* `lehmerVandiverNonTrivial_thirtyseven` — the central numerical fact for
  `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`, proved by `decide`.
* `two_pow_four_ne_one_mod_one_hundred_forty_nine` — admissibility of
  `t = 2`: `2^4 ≢ 1 (mod 149)`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer GTM 83,
  Theorem 9.5 (p. 176).
* Vandiver, "Fermat's last theorem and the second factor in the cyclotomic
  class number," Bull. AMS 40 (1934) 118-126.
-/

@[expose] public section

open Finset

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

/-- The Washington-9.5 partial power sum `d_i := ∑_{a=1}^{(p-1)/2} a^{p-i}`,
viewed as a natural number. Used as the exponent of the prefactor in the
Lehmer-Vandiver certificate. -/
def lehmerVandiverDPow (p i : ℕ) : ℕ :=
  ∑ a ∈ Ico 1 ((p - 1) / 2 + 1), a ^ (p - i)

/-- Prefactor side of the Lehmer-Vandiver certificate equation:
`t^{k²·d_i/2}` viewed in `ZMod ℓ`. The certificate `Q_i^k ≡ 1 (mod ℓ)`
iff `lehmerVandiverPrefactor = lehmerVandiverProduct`.

The natural-number exponent is reduced modulo `ℓ - 1` (Fermat's little
theorem) to keep `decide` tractable; this is valid as long as the base
`t mod ℓ` is nonzero, which holds whenever `gcd(t, ℓ) = 1`. -/
def lehmerVandiverPrefactor (p i ℓ t k : ℕ) : ZMod ℓ :=
  (t : ZMod ℓ) ^ ((k * k * lehmerVandiverDPow p i / 2) % (ℓ - 1))

/-- Product side of the Lehmer-Vandiver certificate equation:

  ∏_{b=1}^{(p-1)/2} (t^{kb} - 1)^{k·b^{p-1-i}}     in `ZMod ℓ`.

Each per-`b` exponent is reduced modulo `ℓ - 1` (Fermat's little theorem)
to keep `decide` tractable; this is valid as long as the base
`(t^{kb} - 1) mod ℓ` is nonzero, which holds in our intended use case
(`gcd(t, ℓ) = 1` and `b · k < ℓ - 1`).

The certificate `Q_i^k ≡ 1 (mod ℓ)` iff `lehmerVandiverPrefactor =
lehmerVandiverProduct`. -/
def lehmerVandiverProduct (p i ℓ t k : ℕ) : ZMod ℓ :=
  ∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
    ((t : ZMod ℓ) ^ ((k * b) % (ℓ - 1)) - 1) ^ ((k * b ^ (p - 1 - i)) % (ℓ - 1))

/-- The Lehmer-Vandiver non-triviality predicate:
`lehmerVandiverPrefactor p i ℓ t k ≠ lehmerVandiverProduct p i ℓ t k`,
equivalent to `Q_i^k ≢ 1 (mod ℓ)` in Washington's notation. -/
def lehmerVandiverNonTrivial (p i ℓ t k : ℕ) : Prop :=
  lehmerVandiverPrefactor p i ℓ t k ≠ lehmerVandiverProduct p i ℓ t k

/-- **Admissibility of `t = 2` for the Lehmer-Vandiver test at `ℓ = 149,
k = 4`:** `2^4 ≢ 1 (mod 149)`. Required by the hypotheses of Washington
Theorem 9.5. -/
theorem two_pow_four_ne_one_mod_one_hundred_forty_nine :
    (2 : ZMod 149) ^ 4 ≠ 1 := by
  decide

section CertificateProof

set_option maxRecDepth 4000000
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000

/-- **Numerical Lehmer-Vandiver certificate at `(37, 32, 149, 2, 4)`:**
the prefactor `2^{16·d_{32}/2} mod 149` differs from the product
`∏_{b=1}^{18} (2^{4b}-1)^{4b^4} mod 149`, equivalently `Q_{32}^4 ≢ 1 (mod 149)`.

The actual certificate value is `81 (mod 149)` (verified externally);
what we need formally is just non-equality with `1`, packaged here as
non-equality of the prefactor and product sides.

This is the single numerical input feeding Washington Corollary 8.19
(via Proposition 8.18 / Pollaczek's log identity in `LV004` / `LV005`)
and ultimately discharging `Vandiver37PlusCoprime` (`LV006`).

Proved by kernel `decide` with bumped `maxRecDepth` and `maxHeartbeats`
(matching the convention used by `bernoulli_decide` in this project).
This avoids any `native_decide` axiom and keeps the axiom set at the
standard `[propext, Classical.choice, Quot.sound]`. -/
theorem lehmerVandiverNonTrivial_thirtyseven :
    lehmerVandiverNonTrivial 37 32 149 2 4 := by
  unfold lehmerVandiverNonTrivial
  decide

end CertificateProof

end LehmerVandiver

end FLT37

end BernoulliRegular

end
