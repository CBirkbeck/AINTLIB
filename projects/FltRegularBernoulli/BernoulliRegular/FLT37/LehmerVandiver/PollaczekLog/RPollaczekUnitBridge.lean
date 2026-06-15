module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekUnit

/-!
# `R_i ↔ pollaczekUnit²` bridge (LV004g-1)

This file isolates the algebraic identity bridging the half-range
cyclotomic-unit product
`∏_b (ζ^b - 1)^{2 b^E}` from LV004e to the cyclotomic Pollaczek unit
`pollaczekUnit p K i` of `BernoulliRegular/FLT37/LehmerVandiver/PollaczekUnit.lean`.

## Main theorem

`zeta_pow_sub_one_prod_eq_pollaczekUnit_sq_mul_zeta_sub_one_pow`

  ∏_{b=1}^{(p-1)/2} (ζ^b - 1)^{2 b^E}
    = (ζ - 1)^{2 ∑_{b=1}^{(p-1)/2} b^E}  ·  pollaczekUnit p K i ^ 2,

with `E = p - 1 - i`.

## Proof outline

Term-wise, `ζ^b - 1 = (ζ - 1) · cyclotomicUnit p K b` (this is
`zeta_sub_one_mul_cyclotomicUnit` from `BernoulliRegular/FLT37/PrimaryUnits.lean`).
Raising to the power `2·b^E` and distributing over `b ∈ Ico 1 ((p-1)/2 + 1)`:

  ∏_b (ζ^b - 1)^{2 b^E}
    = ∏_b ((ζ - 1) · cyclotomicUnit p K b)^{2 b^E}
    = (ζ - 1)^{2 ∑ b^E} · ∏_b (cyclotomicUnit p K b)^{2 b^E}.

The second factor is `pollaczekUnit p K i ^ 2` (the value-cast of the unit
squared, after `Finset.prod_attach` to switch between attached and bare
indexing). Since `(b^E)^2 = (b^E) · 2 = 2 · b^E` morally as an exponent,
we collect the `2` outside.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section RPollaczekUnitBridge

/-- **Cyclotomic-unit product `∏ cyclotomicUnit^(b^E)` equals
the value-cast of `pollaczekUnit`.** Translates the unit-level definition
of `pollaczekUnit p K i` (using attached indexing) to a bare-Finset product
of cyclotomic-unit values, the form needed for the bridge identity. -/
theorem prod_cyclotomicUnit_pow_eq_pollaczekUnit_val (i : ℕ) :
    (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (cyclotomicUnit p K b) ^ (b : ℕ) ^ (p - 1 - i)) =
      ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) := by
  unfold pollaczekUnit
  rw [Units.coe_prod]
  rw [show (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K b ^ (b : ℕ) ^ (p - 1 - i)) =
      ∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
        cyclotomicUnit p K (b.1 : ℕ) ^ ((b.1 : ℕ) : ℕ) ^ (p - 1 - i) from
    (Finset.prod_attach (Finset.Ico 1 ((p - 1) / 2 + 1))
      (fun b => cyclotomicUnit p K b ^ (b : ℕ) ^ (p - 1 - i))).symm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Units.val_pow_eq_pow_val, pollaczekFactor_val]

/-- **Per-term factorisation `(ζ^b - 1)^{2·b^E} = (ζ - 1)^{2·b^E} · cyclotomicUnit^{2·b^E}`.**
Expands a single factor of the half-range main product, using the
defining identity `ζ^b - 1 = (ζ - 1) · cyclotomicUnit p K b`. -/
theorem zeta_pow_sub_one_pow_two_mul_eq (b i : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (2 * b ^ (p - 1 - i)) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ (2 * b ^ (p - 1 - i)) *
        (cyclotomicUnit p K b) ^ (2 * b ^ (p - 1 - i)) := by
  rw [← mul_pow, zeta_sub_one_mul_cyclotomicUnit]

/-- **R_i ↔ pollaczekUnit² bridge identity (LV004g-1).** The half-range
cyclotomic-unit product factorises as

  ∏_b (ζ^b - 1)^{2 b^E} = (ζ - 1)^{2 ∑ b^E} · pollaczekUnit p K i ^ 2,

with `E = p - 1 - i`. This is the algebraic identity bridging LV004e's
half-range main product to the Pollaczek cyclotomic unit `pollaczekUnit p K i`,
needed for the `IsPthPower R_i ↔ IsPthPower E_i` reduction in the LV004g
final assembly.

Proof: term-wise factorisation `ζ^b - 1 = (ζ - 1) · cyclotomicUnit p K b`
(via `zeta_sub_one_mul_cyclotomicUnit`), raise to `2·b^E`, distribute the
product, and identify the cyclotomic-unit factor with `pollaczekUnit p K i ^ 2`
through `Finset.prod_attach`. The hypothesis `hp_odd` is not directly used
in the algebra (the identity is purely formal in `𝓞 K`), but is preserved
in the statement to match the calling convention of LV004e. -/
theorem zeta_pow_sub_one_prod_eq_pollaczekUnit_sq_mul_zeta_sub_one_pow
    (hp_odd : p ≠ 2) (i : ℕ) :
    (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (2 * b ^ (p - 1 - i))) =
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^
          (2 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      ((pollaczekUnit p K i : 𝓞 K) ^ 2) := by
  -- The hypothesis `hp_odd` is preserved in the calling convention but not
  -- used in the algebraic identity itself.
  let _ := hp_odd
  -- Step 1: per-term factorisation `(ζ^b - 1)^{2·b^E} = (ζ-1)^{2·b^E} · cycl^{2·b^E}`.
  rw [Finset.prod_congr rfl (fun b (_ : b ∈ Ico 1 ((p - 1) / 2 + 1)) =>
        zeta_pow_sub_one_pow_two_mul_eq p K b i),
    Finset.prod_mul_distrib]
  -- Step 2: collect the `(ζ-1)`-prefactor into a single power of the sum.
  congr 1
  · -- ∏ (ζ-1)^(2·b^E) = (ζ-1)^(2 ∑ b^E)
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  · -- ∏ cyclotomicUnit^(2·b^E) = pollaczekUnit²
    rw [Finset.prod_congr rfl (fun b (_ : b ∈ Ico 1 ((p - 1) / 2 + 1)) =>
      show cyclotomicUnit p K b ^ (2 * b ^ (p - 1 - i)) =
        (cyclotomicUnit p K b ^ b ^ (p - 1 - i)) ^ 2 from by
      rw [show (2 * b ^ (p - 1 - i) : ℕ) = b ^ (p - 1 - i) * 2 from by ring, pow_mul])]
    rw [Finset.prod_pow]
    congr 1
    exact prod_cyclotomicUnit_pow_eq_pollaczekUnit_val p K i

end RPollaczekUnitBridge

end FLT37

end BernoulliRegular

end
