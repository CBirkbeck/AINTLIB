module

public import BernoulliRegular.Stickelberger

/-!
# Integrality of the corrected Stickelberger element (T032a)

For any unit `c ∈ (ZMod p)ˣ`, the element
  `(c.val • 1 - σ_c) · θ_p ∈ ℚ[(ZMod p)ˣ]`
has integer coefficients, where
* `c.val : ℕ` is the canonical lift of `c` to `{1, …, p-1}`,
* `σ_c = MonoidAlgebra.single c 1` in the group algebra,
* `θ_p = stickelbergerElement p` is the rational Stickelberger element.

This is the coefficient-level integrality statement underlying the
Stickelberger annihilation theorem.

## Main definitions

* `stickelbergerCorrectedCoeff p c b`: the integer coefficient at `σ_{b⁻¹}`
  of `(c.val • 1 - σ_c) · θ_p`, equal to
  `(c.val * b.val - (c * b).val) / p`.
* `stickelbergerCorrectedInt p c`: the integer-valued "corrected"
  Stickelberger element, i.e., the ℤ[G] element whose image under the
  coefficient cast ℤ → ℚ equals `(c.val • 1 - σ_c) · θ_p`.

## References

* Washington, *Introduction to Cyclotomic Fields*, Lemma 6.9.
* Diekmann, *FLT for regular primes*, §4.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Finset MonoidAlgebra

variable (p : ℕ) [hp : Fact p.Prime]

section Integrality

/-- The integer coefficient at `σ_{b⁻¹}` of `(c.val • 1 - σ_c) · θ_p`.

Equals `(c.val * b.val - (c * b).val) / p`, which is integral since
`c.val * b.val ≡ (c * b).val (mod p)`. -/
def stickelbergerCorrectedCoeff (c b : (ZMod p)ˣ) : ℤ :=
  ((c : ZMod p).val * (b : ZMod p).val - ((c * b : (ZMod p)ˣ) : ZMod p).val : ℤ) / p

/-- The integer-valued "corrected" Stickelberger element `(c.val • 1 - σ_c) · θ_p`,
packaged as an element of `ℤ[(ZMod p)ˣ]`. -/
def stickelbergerCorrectedInt (c : (ZMod p)ˣ) : MonoidAlgebra ℤ (ZMod p)ˣ :=
  ∑ b : (ZMod p)ˣ,
    stickelbergerCorrectedCoeff p c b • MonoidAlgebra.single b⁻¹ (1 : ℤ)

/-- `c.val * b.val ≡ (c * b).val (mod p)`, hence the difference is divisible by `p`. -/
lemma val_mul_sub_val_mul_dvd (c b : (ZMod p)ˣ) :
    (p : ℤ) ∣ ((c : ZMod p).val * (b : ZMod p).val -
        ((c * b : (ZMod p)ˣ) : ZMod p).val : ℤ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  ring

/-- `p * (stickelbergerCorrectedCoeff c b) = c.val * b.val - (c * b).val`. -/
lemma stickelbergerCorrectedCoeff_mul_p (c b : (ZMod p)ˣ) :
    (p : ℤ) * stickelbergerCorrectedCoeff p c b =
      ((c : ZMod p).val * (b : ZMod p).val -
        ((c * b : (ZMod p)ˣ) : ZMod p).val : ℤ) := by
  unfold stickelbergerCorrectedCoeff
  exact Int.mul_ediv_cancel' (val_mul_sub_val_mul_dvd p c b)

/-- Rational form: the coefficient difference equals `p * (corrected coeff : ℚ)`. -/
lemma rat_stickelbergerCorrectedCoeff (c b : (ZMod p)ˣ) :
    ((c : ZMod p).val * (b : ZMod p).val : ℚ) - (((c * b : (ZMod p)ˣ) : ZMod p).val : ℚ)
      = (p : ℚ) * (stickelbergerCorrectedCoeff p c b : ℚ) := by
  have h : ((p : ℤ) * stickelbergerCorrectedCoeff p c b : ℚ) =
      (((c : ZMod p).val * (b : ZMod p).val -
        ((c * b : (ZMod p)ˣ) : ZMod p).val : ℤ) : ℚ) := by
    exact_mod_cast stickelbergerCorrectedCoeff_mul_p p c b
  push_cast at h ⊢
  linarith

/-- Multiplying `single c 1` into `stickelbergerScaled p` reindexes the sum. -/
lemma single_mul_stickelbergerScaled (c : (ZMod p)ˣ) :
    MonoidAlgebra.single c (1 : ℤ) * stickelbergerScaled p =
      ∑ b : (ZMod p)ˣ, (((b * c : (ZMod p)ˣ) : ZMod p).val : ℤ) •
        MonoidAlgebra.single b⁻¹ (1 : ℤ) := by
  rw [stickelbergerScaled_def, Finset.mul_sum]
  -- Re-index a ↦ a * c⁻¹ (bijection on G). Then:
  -- single c 1 * (a.val • single a⁻¹ 1) = a.val • single (c * a⁻¹) 1
  -- With substitution a = b * c: c * a⁻¹ = b⁻¹, a.val = (b * c).val.
  apply Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => a * c⁻¹)
  · intros; exact Finset.mem_univ _
  · intro a _ a' _ h
    have : a * c⁻¹ * c = a' * c⁻¹ * c := by rw [h]
    group at this; exact this
  · intro b _; exact ⟨b * c, Finset.mem_univ _, by group⟩
  · intro a _
    have hb : a * c⁻¹ * c = a := by group
    change MonoidAlgebra.single c (1 : ℤ) *
        (((a : ZMod p).val : ℤ) • MonoidAlgebra.single a⁻¹ (1 : ℤ))
      = ((((a * c⁻¹) * c : (ZMod p)ˣ) : ZMod p).val : ℤ) •
        MonoidAlgebra.single (a * c⁻¹)⁻¹ (1 : ℤ)
    rw [hb, mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul]
    rw [show c * a⁻¹ = (a * c⁻¹)⁻¹ from by group]

/-- Expanding `(c.val • 1) * stickelbergerScaled p`. -/
lemma smul_one_mul_stickelbergerScaled (c : (ZMod p)ˣ) :
    (((c : ZMod p).val : ℤ) • (1 : MonoidAlgebra ℤ (ZMod p)ˣ)) * stickelbergerScaled p =
      ∑ a : (ZMod p)ˣ, (((c : ZMod p).val : ℤ) * ((a : ZMod p).val : ℤ)) •
        MonoidAlgebra.single a⁻¹ (1 : ℤ) := by
  rw [stickelbergerScaled_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_one_mul, smul_smul]

/-- The key identity: `p · stickelbergerCorrectedInt p c =
    (c.val • 1 - σ_c) * stickelbergerScaled p` in `ℤ[(ZMod p)ˣ]`.

This is the integer-coefficient form of the Stickelberger integrality statement:
the integer element `stickelbergerCorrectedInt p c` maps under `ℤ → ℚ` to
`(c.val • 1 - σ_c) * θ_p`. -/
theorem p_smul_stickelbergerCorrectedInt (c : (ZMod p)ˣ) :
    (p : ℤ) • stickelbergerCorrectedInt p c =
      (((c : ZMod p).val : ℤ) • (1 : MonoidAlgebra ℤ (ZMod p)ˣ) -
        MonoidAlgebra.single c (1 : ℤ)) * stickelbergerScaled p := by
  unfold stickelbergerCorrectedInt
  rw [sub_mul, smul_one_mul_stickelbergerScaled, single_mul_stickelbergerScaled]
  rw [show ((p : ℤ) • ∑ b : (ZMod p)ˣ,
      stickelbergerCorrectedCoeff p c b • MonoidAlgebra.single b⁻¹ (1 : ℤ)) =
      ∑ b : (ZMod p)ˣ, (p : ℤ) •
        (stickelbergerCorrectedCoeff p c b • MonoidAlgebra.single b⁻¹ (1 : ℤ)) from
      Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul, ← sub_smul]
  congr 1
  have hmul := stickelbergerCorrectedCoeff_mul_p p c b
  rw [show (b * c : (ZMod p)ˣ) = c * b from mul_comm _ _]
  push_cast at hmul ⊢
  linarith

/-- The image of `stickelbergerScaled p` under `ℤ → ℚ` equals `p • stickelbergerElement p`. -/
lemma mapRangeRingHom_stickelbergerScaled :
    MonoidAlgebra.mapRingHom (ZMod p)ˣ (Int.castRingHom ℚ) (stickelbergerScaled p) =
      (p : ℚ) • stickelbergerElement p := by
  rw [smul_stickelbergerElement, stickelbergerScaled_def, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_zsmul, MonoidAlgebra.mapRingHom_single, map_one]
  change ((((a : ZMod p).val : ℤ) : ℚ)) • MonoidAlgebra.single a⁻¹ (1 : ℚ) = _
  push_cast
  rfl

/-- **T032a**: The corrected Stickelberger element `(c.val • 1 - σ_c) · θ_p` has integer
coefficients: it equals the image of `stickelbergerCorrectedInt p c ∈ ℤ[(ZMod p)ˣ]`
under the coefficient cast `ℤ → ℚ`. -/
theorem mapRangeRingHom_stickelbergerCorrectedInt (c : (ZMod p)ˣ) :
    MonoidAlgebra.mapRingHom (ZMod p)ˣ (Int.castRingHom ℚ)
        (stickelbergerCorrectedInt p c) =
      (((c : ZMod p).val : ℚ) • (1 : MonoidAlgebra ℚ (ZMod p)ˣ) -
        MonoidAlgebra.single c (1 : ℚ)) * stickelbergerElement p := by
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  -- Multiply both sides by p and use p_smul_stickelbergerCorrectedInt.
  apply smul_right_injective (MonoidAlgebra ℚ (ZMod p)ˣ) hp_ne
  change (p : ℚ) • MonoidAlgebra.mapRingHom (ZMod p)ˣ (Int.castRingHom ℚ)
      (stickelbergerCorrectedInt p c) =
    (p : ℚ) • ((((c : ZMod p).val : ℚ) • (1 : MonoidAlgebra ℚ (ZMod p)ˣ) -
      MonoidAlgebra.single c (1 : ℚ)) * stickelbergerElement p)
  rw [show ((p : ℚ) • MonoidAlgebra.mapRingHom (ZMod p)ˣ (Int.castRingHom ℚ)
      (stickelbergerCorrectedInt p c)) =
    MonoidAlgebra.mapRingHom (ZMod p)ˣ (Int.castRingHom ℚ)
      ((p : ℤ) • stickelbergerCorrectedInt p c) from by rw [map_zsmul]; rfl]
  rw [p_smul_stickelbergerCorrectedInt]
  rw [map_mul, map_sub, map_zsmul, map_one, MonoidAlgebra.mapRingHom_single,
    map_one, mapRangeRingHom_stickelbergerScaled, ← mul_smul_comm]
  rfl

end Integrality

end BernoulliRegular
