module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Units
public import BernoulliRegular.Idempotents

/-!
# The Stickelberger element for cyclotomic fields of prime conductor

For a prime `p`, the Stickelberger element is the classical group-ring element

`θ_p := (1/p) · ∑_{a ∈ (ZMod p)ˣ} (a.val : ℚ) • single a⁻¹ (1 : ℚ)
       ∈ ℚ[(ZMod p)ˣ]`

where we identify `(ZMod p)ˣ` with `Gal(ℚ(ζ_p)/ℚ)` via `σ_a(ζ_p) = ζ_p^a`
and `a.val` is the canonical lift of `a ∈ (ZMod p)ˣ` to `{1, …, p-1}`.

## Main definitions

* `BernoulliRegular.stickelbergerElement p`: the Stickelberger element
  `θ_p ∈ ℚ[(ZMod p)ˣ]`.
* `BernoulliRegular.stickelbergerScaled p`: the `p`-scaled version
  `p · θ_p = ∑_a (a.val : ℤ) • single a⁻¹ 1 ∈ ℤ[(ZMod p)ˣ]`, which has
  integer coefficients.

## Main results

* `BernoulliRegular.stickelbergerScaled_coe_eq_p_smul_stickelberger`: the
  algebraMap from the integer-coefficient to the rational-coefficient form
  sends `stickelbergerScaled` to `p · stickelbergerElement`.

## References

* Diekmann, *FLT for regular primes*, §4 (definition 52 region).
* Washington, *Introduction to Cyclotomic Fields*, Chapter 6.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Finset MonoidAlgebra

section Stickelberger

variable (p : ℕ) [hp : Fact p.Prime]

/-- Package a coefficient vector indexed by `(ZMod p)ˣ` as an integer
group-ring element in the Stickelberger convention: the coefficient attached to
`a` is stored on the basis element `single a⁻¹`. -/
def stickelbergerCoefficientPackage (c : (ZMod p)ˣ → ℤ) :
    MonoidAlgebra ℤ (ZMod p)ˣ :=
  ∑ a : (ZMod p)ˣ, MonoidAlgebra.single a⁻¹ (c a)

/-- The coefficient at `a⁻¹` in the Stickelberger coefficient package. -/
@[simp] lemma stickelbergerCoefficientPackage_apply_inv
    (c : (ZMod p)ˣ → ℤ) (a : (ZMod p)ˣ) :
    (stickelbergerCoefficientPackage (p := p) c).coeff a⁻¹ = c a := by
  rw [stickelbergerCoefficientPackage, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hb
    simp [hb, inv_inj]

/-- The Stickelberger element `θ_p ∈ ℚ[(ZMod p)ˣ]`:
`θ_p := (1/p) · ∑_{a ∈ (ZMod p)ˣ} (a.val : ℚ) • single a⁻¹ 1`. -/
def stickelbergerElement : MonoidAlgebra ℚ (ZMod p)ˣ :=
  (p : ℚ)⁻¹ •
    ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) • MonoidAlgebra.single a⁻¹ (1 : ℚ)

/-- The integer-coefficient `p`-scaled Stickelberger element:
`p · θ_p = ∑_{a ∈ (ZMod p)ˣ} (a.val : ℤ) • single a⁻¹ 1 ∈ ℤ[(ZMod p)ˣ]`. -/
def stickelbergerScaled : MonoidAlgebra ℤ (ZMod p)ˣ :=
  ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℤ) • MonoidAlgebra.single a⁻¹ (1 : ℤ)

/-- Unfolding `stickelbergerElement`. -/
@[simp] lemma stickelbergerElement_def :
    stickelbergerElement p =
      (p : ℚ)⁻¹ •
        ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) • MonoidAlgebra.single a⁻¹ (1 : ℚ) :=
  rfl

/-- Unfolding `stickelbergerScaled`. -/
@[simp] lemma stickelbergerScaled_def :
    stickelbergerScaled p =
      ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℤ) • MonoidAlgebra.single a⁻¹ (1 : ℤ) :=
  rfl

/-- The scaled Stickelberger element is the coefficient package attached to
the canonical integer lifts of units. -/
lemma stickelbergerScaled_eq_stickelbergerCoefficientPackage :
    stickelbergerScaled p =
      stickelbergerCoefficientPackage (p := p)
        (fun a : (ZMod p)ˣ ↦ ((a : ZMod p).val : ℤ)) := by
  simp only [stickelbergerScaled, stickelbergerCoefficientPackage]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [MonoidAlgebra.smul_single]; simp

/-- The coefficient at `a⁻¹` in `p · θ_p`. -/
@[simp] lemma stickelbergerScaled_apply_inv (a : (ZMod p)ˣ) :
    (stickelbergerScaled p).coeff a⁻¹ = ((a : ZMod p).val : ℤ) := by
  rw [stickelbergerScaled_eq_stickelbergerCoefficientPackage]
  simp

/-- The coefficient function for `p · θ_p`: casting `stickelbergerScaled` into `ℚ`
via the canonical ring homomorphism gives `p • stickelbergerElement p`. -/
theorem smul_stickelbergerElement :
    (p : ℚ) • stickelbergerElement p =
      ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) • MonoidAlgebra.single a⁻¹ (1 : ℚ) := by
  rw [stickelbergerElement_def, smul_smul,
    mul_inv_cancel₀ (mod_cast hp.out.ne_zero : (p : ℚ) ≠ 0), one_smul]

end Stickelberger

end BernoulliRegular
