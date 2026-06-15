module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PollaczekIdentity

/-!
# Factor-wise σ_a-twist for cyclotomic-unit factors (LV005c1a)

For the standard cyclotomic Galois automorphism `σ_a := cyclotomicSigmaOfUnit
p K a` indexed by `a ∈ (ZMod p)ˣ`, the cyclotomic unit
`cyclotomicUnit p K b = (1 + ζ + ⋯ + ζ^{b-1}) = (ζ^b - 1)/(ζ - 1)` transforms
under `σ_a` according to the identity

  `σ_a(cyclotomicUnit p K b) · cyclotomicUnit p K (a : ZMod p).val =
   cyclotomicUnit p K (((a : ZMod p) * b).val)`

in `𝓞 K`. (Equivalently
`σ_a(cyclotomicUnit p K b) = cyclotomicUnit p K ((a · b).val) /
cyclotomicUnit p K a.val`, but the multiplicative form avoids inversion.)

Proof strategy: multiply both sides by `(ζ - 1)`. Apply σ_a to
`(ζ - 1) · cyclotomicUnit b = ζ^b - 1` to get
`(ζ^{a.val} - 1) · σ_a(cyclotomicUnit b) = ζ^{a.val · b} - 1`. Then use
`ζ^{a.val · b} = ζ^{((a · b).val)}` (`ζ` has order `p`) and
`ζ^{a.val} - 1 = (ζ - 1) · cyclotomicUnit a.val` to rewrite the equation as
`σ_a(cyclotomicUnit b) · cyclotomicUnit a.val · (ζ - 1) =
cyclotomicUnit ((a · b).val) · (ζ - 1)`. Cancel `(ζ - 1) ≠ 0`.

This file's main result is the building block for LV005c1b's aggregate
σ-twist on `pollaczekUnit p K i` mod `p`-th powers.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer GTM
  83), Lemma 8.4 (p. 156).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section CyclotomicUnitTwist

/-- **Auxiliary: `(ζ^{a.val} - 1) · σ_a(cyclotomicUnit b) = ζ^{a.val · b} - 1`
in `𝓞 K`.**

Apply σ_a as a ring homomorphism to the defining equation
`(ζ - 1) · cyclotomicUnit b = ζ^b - 1`, then use
`σ_a(ζ - 1) = ζ^{a.val} - 1` (from
`cyclotomicSigmaOfUnit_smul_zeta_pow_sub_one` at `b = 1`) and
`σ_a(ζ^b - 1) = ζ^{a.val · b} - 1`. -/
theorem cyclotomicSigmaOfUnit_smul_cyclotomicUnit_mul_zeta_pow_sub_one
    (a : (ZMod p)ˣ) (b : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((a : ZMod p).val) - 1) *
        (cyclotomicSigmaOfUnit (p := p) K a • cyclotomicUnit p K b) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((a : ZMod p).val * b) - 1 := by
  -- Apply σ_a as a ring hom to (ζ - 1) · cyclotomicUnit b = ζ^b - 1.
  set σ : 𝓞 K →+* 𝓞 K :=
    MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K)
      (cyclotomicSigmaOfUnit (p := p) K a)
  have h_eq := zeta_sub_one_mul_cyclotomicUnit p K b
  have h_apply := congrArg σ h_eq
  -- σ is a ring hom; propagate over · and -; reduce ζ^b under σ.
  simp only [map_mul, map_sub, map_one, map_pow] at h_apply
  -- h_apply : (σ ζ - 1) · σ(cyclotomicUnit b) = σ(ζ)^b - 1.
  -- σ(ζ) = ζ^{a.val} (cyclotomicSigmaOfUnit_smul_zetaInteger).
  have hσζ : σ ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((a : ZMod p).val) := by
    change cyclotomicSigmaOfUnit (p := p) K a •
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((a : ZMod p).val)
    rw [show ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
      cyclotomicZetaInteger (p := p) K from rfl,
      cyclotomicSigmaOfUnit_smul_zetaInteger]
  rw [hσζ, ← pow_mul] at h_apply
  exact h_apply

/-- **`a.val · b` and `((a · b).val)` are congruent mod `p` for `a : (ZMod p)ˣ`.**
A clean form of the defining identity for ZMod multiplication. -/
private theorem val_mul_eq_val_mul_mod (a : (ZMod p)ˣ) (b : ℕ) :
    (a : ZMod p).val * b ≡ ((a : ZMod p) * b).val [MOD p] := by
  -- Both sides reduce to (a.val * b) mod p in ZMod p.
  -- Use ZMod.val_natCast and ZMod.cast_id.
  have h1 : ((((a : ZMod p).val * b : ℕ) : ZMod p)) =
      (a : ZMod p) * (b : ZMod p) := by
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]
  have h2 : ((((a : ZMod p) * b).val : ℕ) : ZMod p) =
      (a : ZMod p) * (b : ZMod p) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  -- So the two natural numbers cast to the same element in ZMod p, i.e.,
  -- they are congruent mod p.
  have h_eq : (((a : ZMod p).val * b : ℕ) : ZMod p) =
      ((((a : ZMod p) * b).val : ℕ) : ZMod p) := h1.trans h2.symm
  rwa [ZMod.natCast_eq_natCast_iff'] at h_eq

/-- **Factor-wise σ-twist for cyclotomic units (ring-level)**: for
`a ∈ (ZMod p)ˣ` and `b : ℕ`,
`σ_a(cyclotomicUnit p K b) · cyclotomicUnit p K (a : ZMod p).val =
 cyclotomicUnit p K (((a : ZMod p) * b).val)` in `𝓞 K`.

Multiplicative form (no inverse): the σ-twisted cyclotomic unit at index
`b`, multiplied by the cyclotomic unit at the index `a.val`, equals the
cyclotomic unit at the product index `(a · b).val`. -/
theorem cyclotomicSigmaOfUnit_smul_cyclotomicUnit_mul_cyclotomicUnit
    (a : (ZMod p)ˣ) (b : ℕ) :
    (cyclotomicSigmaOfUnit (p := p) K a • cyclotomicUnit p K b) *
        cyclotomicUnit p K ((a : ZMod p).val) =
      cyclotomicUnit p K (((a : ZMod p) * b).val) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  have hζ_sub_one_ne_zero : (ζ - 1 : 𝓞 K) ≠ 0 :=
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
  -- Multiply both sides by (ζ - 1) and cancel using IsDomain.
  refine mul_right_cancel₀ hζ_sub_one_ne_zero ?_
  have h_aux :=
    cyclotomicSigmaOfUnit_smul_cyclotomicUnit_mul_zeta_pow_sub_one p K a b
  have h_lhs_zsub : (ζ - 1) * cyclotomicUnit p K ((a : ZMod p).val) =
      ζ ^ ((a : ZMod p).val) - 1 :=
    zeta_sub_one_mul_cyclotomicUnit p K _
  have h_rhs_zsub : (ζ - 1) * cyclotomicUnit p K (((a : ZMod p) * b).val) =
      ζ ^ (((a : ZMod p) * b).val) - 1 :=
    zeta_sub_one_mul_cyclotomicUnit p K _
  -- ζ has order p, so ζ^{m} = ζ^{n} when m ≡ n (mod p).
  have hζ_p : ζ ^ p = 1 := by
    have hζ_prim : IsPrimitiveRoot ζ p := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
    exact hζ_prim.pow_eq_one
  have hmod := val_mul_eq_val_mul_mod p a b
  -- ζ^{a.val · b} = ζ^{((a · b).val)} via mod-p exponent reduction.
  have h_pow_eq :
      ζ ^ ((a : ZMod p).val * b) = ζ ^ (((a : ZMod p) * b).val) := by
    -- Use: ζ^m = ζ^{m % p} via ζ^p = 1 (apply iteratively to both sides).
    have h_lhs : ζ ^ ((a : ZMod p).val * b) =
        ζ ^ (((a : ZMod p).val * b) % p) := by
      conv_lhs => rw [← Nat.mod_add_div ((a : ZMod p).val * b) p, pow_add,
        pow_mul, hζ_p, one_pow, mul_one]
    have h_rhs : ζ ^ (((a : ZMod p) * b).val) =
        ζ ^ ((((a : ZMod p) * b).val) % p) := by
      rw [Nat.mod_eq_of_lt ((a : ZMod p) * b).val_lt]
    rw [h_lhs, h_rhs, hmod]
  -- Now compute LHS · (ζ - 1).
  calc (cyclotomicSigmaOfUnit (p := p) K a • cyclotomicUnit p K b) *
          cyclotomicUnit p K ((a : ZMod p).val) * (ζ - 1)
      = (cyclotomicSigmaOfUnit (p := p) K a • cyclotomicUnit p K b) *
          ((ζ - 1) * cyclotomicUnit p K ((a : ZMod p).val)) := by ring
    _ = (cyclotomicSigmaOfUnit (p := p) K a • cyclotomicUnit p K b) *
          (ζ ^ ((a : ZMod p).val) - 1) := by rw [h_lhs_zsub]
    _ = (ζ ^ ((a : ZMod p).val) - 1) *
          (cyclotomicSigmaOfUnit (p := p) K a • cyclotomicUnit p K b) := by ring
    _ = ζ ^ ((a : ZMod p).val * b) - 1 := h_aux
    _ = ζ ^ (((a : ZMod p) * b).val) - 1 := by rw [h_pow_eq]
    _ = (ζ - 1) * cyclotomicUnit p K (((a : ZMod p) * b).val) := h_rhs_zsub.symm
    _ = cyclotomicUnit p K (((a : ZMod p) * b).val) * (ζ - 1) := by ring

end CyclotomicUnitTwist

end FLT37

end BernoulliRegular

end
