module

public import BernoulliRegular.Stickelberger
public import BernoulliRegular.BernoulliGeneralized
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Eigenspace projection of the Stickelberger element (T033)

For a prime `p`, the idempotent associated to a rational character
`χ : MulChar (ZMod p)ˣ ℚ` projects the Stickelberger element `θ_p` to a scalar
multiple of the idempotent itself. The scalar is the explicit sum

  `(1/p) · ∑_{a ∈ (ZMod p)ˣ} (a.val : ℚ) * χ(a⁻¹)`.

The scalar is then identified with the generalized Bernoulli number
`B_{1,χ⁻¹}` attached to the Dirichlet character induced by `χ⁻¹`.

## Main definitions

* `stickelbergerEigenvalue p χ`: the scalar `(1/p) ∑_a a.val * χ(a⁻¹)`.
* `unitMulCharDirichlet p χ`: the Dirichlet character modulo `p` induced by
  a character on `(ZMod p)ˣ`.

## Main results

* `charIdempotent_mul_single`: for any `CommGroup G` and `CommRing R` with `|G|`
  invertible, `ε_χ · single c 1 = χ(c) • ε_χ`. This is the right-multiplication
  counterpart to `single_mul_charIdempotent`, proved directly to avoid the
  `IsDomain`/`HasEnoughRootsOfUnity` constraints of the latter.
* `charIdempotent_mul_stickelbergerElement`: **T033a**, the reduction
  `ε_χ · θ_p = stickelbergerEigenvalue p χ • ε_χ`.
* `stickelbergerEigenvalue_eq_BernoulliGen`: **T033b**, the identification
  `stickelbergerEigenvalue p χ = B_{1,χ⁻¹}` for nontrivial `χ`.
* `charIdempotent_mul_stickelbergerElement_eq_BernoulliGen`: the projected
  Stickelberger formula with the Bernoulli scalar.

## References

* Diekmann, *FLT for regular primes*, §4 Lemma 53.
* Washington, *Introduction to Cyclotomic Fields*, Chapter 6.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Finset MonoidAlgebra MulChar

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

section Basic

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
variable {R : Type*} [CommRing R] [Invertible ((Fintype.card G : R))]

/-- Right multiplication of the character idempotent `ε_χ` by `single c 1`
scales it by the eigenvalue `χ c`. Dual to `single_mul_charIdempotent`, proved
directly (without `IsDomain`/`HasEnoughRootsOfUnity`) via the reindex
`σ ↦ σ * c` in a commutative group. -/
lemma charIdempotent_mul_single (χ : MulChar G R) (c : G) :
    charIdempotent χ * MonoidAlgebra.single c (1 : R) = χ c • charIdempotent χ := by
  rw [charIdempotent_def, smul_mul_assoc, smul_comm (χ c) (⅟((Fintype.card G : R)))]
  congr 1
  calc (∑ σ : G, χ σ • MonoidAlgebra.single σ⁻¹ (1 : R)) *
      MonoidAlgebra.single c (1 : R)
      = ∑ σ : G, χ σ • MonoidAlgebra.single (σ⁻¹ * c) (1 : R) := by
        simp_rw [Finset.sum_mul, smul_mul_assoc, MonoidAlgebra.single_mul_single, one_mul]
    _ = ∑ σ : G, χ (σ * c) • MonoidAlgebra.single ((σ * c)⁻¹ * c) (1 : R) :=
        ((Group.mulRight_bijective c).sum_comp
          (fun σ => χ σ • MonoidAlgebra.single (σ⁻¹ * c) (1 : R))).symm
    _ = ∑ σ : G, (χ σ * χ c) • MonoidAlgebra.single σ⁻¹ (1 : R) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [map_mul, show (σ * c)⁻¹ * c = σ⁻¹ from by
          rw [mul_comm σ c, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]]
    _ = χ c • ∑ σ : G, χ σ • MonoidAlgebra.single σ⁻¹ (1 : R) := by
        simp_rw [Finset.smul_sum, smul_smul, mul_comm (χ _) (χ c)]

end Basic

section Stickelberger

variable (p : ℕ) [hp : Fact p.Prime]

/-- `Invertible` instance for `|(ZMod p)ˣ| = p - 1` viewed in `ℚ`, needed to
build `charIdempotent` over `ℚ` for characters on `(ZMod p)ˣ`. -/
instance invertible_card_units_rat : Invertible ((Fintype.card (ZMod p)ˣ : ℚ)) := by
  rw [ZMod.card_units]
  exact invertibleOfNonzero <| by
    exact_mod_cast (Nat.sub_pos_of_lt hp.out.one_lt).ne'

/-- The Stickelberger eigenvalue on the `χ`-eigenspace:

  `(1/p) · ∑_{a ∈ (ZMod p)ˣ} (a.val : ℚ) · χ(a⁻¹)`.

This is the scalar by which `θ_p` acts on `ε_χ · ℚ[(ZMod p)ˣ]`. Its
identification with the generalized Bernoulli number `B_{1,χ⁻¹}` is the
content of `T033b`. -/
def stickelbergerEigenvalue (χ : MulChar (ZMod p)ˣ ℚ) : ℚ :=
  (p : ℚ)⁻¹ * ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) * χ a⁻¹

/-- Unfolding lemma for `stickelbergerEigenvalue`. -/
lemma stickelbergerEigenvalue_def (χ : MulChar (ZMod p)ˣ ℚ) :
    stickelbergerEigenvalue p χ =
      (p : ℚ)⁻¹ * ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) * χ a⁻¹ :=
  rfl

/-- **T033a**: Projecting the Stickelberger element `θ_p` onto the `χ`-eigenspace
yields the scalar `stickelbergerEigenvalue p χ` times the idempotent `ε_χ`. -/
theorem charIdempotent_mul_stickelbergerElement (χ : MulChar (ZMod p)ˣ ℚ) :
    charIdempotent χ * stickelbergerElement p =
      stickelbergerEigenvalue p χ • charIdempotent χ := by
  rw [stickelbergerEigenvalue_def, stickelbergerElement_def, mul_smul_comm, Finset.mul_sum]
  simp_rw [mul_smul_comm, charIdempotent_mul_single, smul_smul]
  rw [← Finset.sum_smul, smul_smul]

/-- The Dirichlet character modulo `p` obtained by extending a character on
`(ZMod p)ˣ` by zero away from units. -/
def unitMulCharDirichlet (χ : MulChar (ZMod p)ˣ ℚ) : DirichletCharacter ℚ p :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (toUnits (G := (ZMod p)ˣ)).toMonoidHom)

@[simp]
lemma unitMulCharDirichlet_apply_unit (χ : MulChar (ZMod p)ˣ ℚ) (a : (ZMod p)ˣ) :
    unitMulCharDirichlet p χ (a : ZMod p) = χ a := by
  simp [unitMulCharDirichlet]

@[simp]
lemma unitMulCharDirichlet_one :
    unitMulCharDirichlet p (1 : MulChar (ZMod p)ˣ ℚ) = 1 := by
  ext a
  simp [unitMulCharDirichlet, MulChar.one_apply (R' := ℚ) (Group.isUnit a)]

lemma unitMulCharDirichlet_ne_one {χ : MulChar (ZMod p)ˣ ℚ} (hχ : χ ≠ 1) :
    unitMulCharDirichlet p χ ≠ 1 := by
  intro h
  apply hχ
  apply MulChar.equivToUnitHom.injective
  ext a
  have hunit :
      (unitMulCharDirichlet p χ).toUnitHom (a : (ZMod p)ˣ) =
        (1 : DirichletCharacter ℚ p).toUnitHom (a : (ZMod p)ˣ) := by
    rw [h]
  have hunit_val := congrArg Units.val hunit
  simpa [unitMulCharDirichlet] using hunit_val

/-- Summing a unit-induced Dirichlet character against `a.val` over all residues
is the same as summing the original unit character over `(ZMod p)ˣ`; the zero
residue contributes zero. -/
lemma sum_unitMulCharDirichlet_eq_sum_units (χ : MulChar (ZMod p)ˣ ℚ) :
    ∑ a : ZMod p, unitMulCharDirichlet p χ a * (a.val : ℚ) =
      ∑ a : (ZMod p)ˣ, χ a * ((a : ZMod p).val : ℚ) := by
  let F : ZMod p → ℚ := fun a => unitMulCharDirichlet p χ a * (a.val : ℚ)
  have hsplit :
      ∑ a : ZMod p, F a = F 0 + ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne F (0 : ZMod p)
  have hnonzero :
      ∑ a : {a : ZMod p // a ≠ 0}, F a.1 =
        ∑ u : (ZMod p)ˣ, F (u : ZMod p) := by
    simpa using
      (Fintype.sum_equiv unitsEquivNeZero
        (fun u : (ZMod p)ˣ => F (u : ZMod p))
        (fun a : {a : ZMod p // a ≠ 0} => F a.1)
        (fun u => rfl)).symm
  calc
    ∑ a : ZMod p, unitMulCharDirichlet p χ a * (a.val : ℚ) =
        ∑ a : ZMod p, F a := rfl
    _ = F 0 + ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := hsplit
    _ = ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := by
      simp [F]
    _ = ∑ a : (ZMod p)ˣ, F (a : ZMod p) := hnonzero
    _ = ∑ a : (ZMod p)ˣ, χ a * ((a : ZMod p).val : ℚ) := by
      simp [F]

/-- **T033b**: the Stickelberger eigenvalue is the generalized Bernoulli number
`B_{1,χ⁻¹}` for the Dirichlet character induced by `χ⁻¹`. -/
theorem stickelbergerEigenvalue_eq_BernoulliGen {χ : MulChar (ZMod p)ˣ ℚ}
    (hχ : χ ≠ 1) :
    stickelbergerEigenvalue p χ =
      BernoulliGen (unitMulCharDirichlet p χ⁻¹) 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hχinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hB := natCast_mul_BernoulliGen_one_of_ne_one
    (R := ℚ) (N := p) (χ := unitMulCharDirichlet p χ⁻¹)
    (unitMulCharDirichlet_ne_one (p := p) hχinv)
  apply (mul_right_injective₀ hp_ne)
  calc
    (p : ℚ) * stickelbergerEigenvalue p χ =
        ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) * χ a⁻¹ := by
      rw [stickelbergerEigenvalue_def, ← mul_assoc, mul_inv_cancel₀ hp_ne, one_mul]
    _ = ∑ a : (ZMod p)ˣ, χ⁻¹ a * ((a : ZMod p).val : ℚ) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [MulChar.inv_apply_eq_inv', ← map_inv]
      ring
    _ = ∑ a : ZMod p, unitMulCharDirichlet p χ⁻¹ a * (a.val : ℚ) := by
      rw [sum_unitMulCharDirichlet_eq_sum_units]
    _ = (p : ℚ) * BernoulliGen (unitMulCharDirichlet p χ⁻¹) 1 := hB.symm

/-- The Stickelberger projection with its eigenvalue written as the generalized
Bernoulli number `B_{1,χ⁻¹}`. -/
theorem charIdempotent_mul_stickelbergerElement_eq_BernoulliGen
    {χ : MulChar (ZMod p)ˣ ℚ} (hχ : χ ≠ 1) :
    charIdempotent χ * stickelbergerElement p =
      BernoulliGen (unitMulCharDirichlet p χ⁻¹) 1 • charIdempotent χ := by
  rw [charIdempotent_mul_stickelbergerElement, stickelbergerEigenvalue_eq_BernoulliGen p hχ]

end Stickelberger

end BernoulliRegular
