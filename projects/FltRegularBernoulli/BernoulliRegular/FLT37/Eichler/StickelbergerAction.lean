module

public import BernoulliRegular.Reflection.ClassGroupModP.GalAction
public import BernoulliRegular.Stickelberger.Eigenspaces
public import BernoulliRegular.Stickelberger.Integrality
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Stickelberger action on `ClassGroupModP K p` (Eichler / easy Herbrand, foundational leaf)

The cyclotomic Galois group `Δ ≃ (ZMod p)ˣ` acts on
`V := Additive (ClassGroupModP K p)` by `ZMod p`-linear endomorphisms
(`cyclotomicGalActionLinearModP`, built in
`BernoulliRegular.Reflection.ClassGroupModP.GalAction`). This file turns that
multiplicative `G`-action into a **group-ring module structure** and proves the
**Stickelberger eigenvalue action**: on a `χ`-eigenvector the integral
Stickelberger element acts as the scalar `B_{1,χ⁻¹}` (the generalized Bernoulli
number) reduced mod `p`.

## Main definitions

* `BernoulliRegular.FLT37.Eichler.classGroupModPGroupRingAction`: the algebra
  homomorphism
  `MonoidAlgebra (ZMod p) (ZMod p)ˣ →ₐ[ZMod p] Module.End (ZMod p) V`
  obtained from a `CyclotomicGalAction` via the universal property
  `MonoidAlgebra.lift`.

## Main results

* `classGroupModPGroupRingAction_single`: the action agrees with the `G`-action
  on `single a 1`.
* `classGroupModPGroupRingAction_apply_eigenvector`: the abstract eigenvalue
  lemma — if `v` is a `ψ`-eigenvector (`ρ a v = ψ a • v` for all `a`), then any
  group-ring element `x` acts as the scalar `x.sum fun a b ↦ b * ψ a`.
* `stickelbergerCorrectedInt_action_eigenvector`: the integral Stickelberger
  element `stickelbergerCorrectedInt c` (mapped `ℤ → ZMod p`) acts on a
  `ψ`-eigenvector by the explicit Stickelberger scalar.
* `stickelbergerCorrectedScalar_eq` / `stickelbergerCorrectedScalar_eq_BernoulliGen`:
  identification of the (rational) corrected Stickelberger eigenvalue scalar with
  `(c.val - χ c) · stickelbergerEigenvalue χ`, resp. `(c.val - χ c) · B_{1,χ⁻¹}`
  (the easy-Herbrand eigenvalue), for the matching `ℚ`-valued character `χ`.

## References

* Diekmann, *FLT for regular primes*, §4 (Stickelberger / Herbrand).
* Washington, *Introduction to Cyclotomic Fields*, Chapters 6, 10.
-/

@[expose] public section

noncomputable section

open NumberField Finset MonoidAlgebra
open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace Eichler

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Abbreviation for the `ZMod p`-module on which the cyclotomic Galois group
acts. -/
abbrev ClassGroupModPMod (p : ℕ) [Fact p.Prime] (K : Type u) [Field K]
    [NumberField K] : Type u :=
  Additive (ClassGroupModP K p)

/-- **Group-ring action.** A multiplicative `(ZMod p)ˣ`-action on
`V = Additive (ClassGroupModP K p)` (i.e. a `CyclotomicGalAction p K`, a monoid
hom into `Module.End (ZMod p) V`) extends, by the universal property of the
group algebra (`MonoidAlgebra.lift`), to an algebra homomorphism

  `MonoidAlgebra (ZMod p) (ZMod p)ˣ →ₐ[ZMod p] Module.End (ZMod p) V`.

This makes `V` a module over the group ring `(ZMod p)[(ZMod p)ˣ]`, which is the
setting in which the Stickelberger element acts. -/
def classGroupModPGroupRingAction (ρ : CyclotomicGalAction p K) :
    MonoidAlgebra (ZMod p) (CyclotomicUnitDelta p) →ₐ[ZMod p]
      Module.End (ZMod p) (ClassGroupModPMod p K) :=
  MonoidAlgebra.lift (ZMod p) (Module.End (ZMod p) (ClassGroupModPMod p K))
    (CyclotomicUnitDelta p) ρ

omit [IsCyclotomicExtension {p} ℚ K] in
/-- The group-ring action agrees with the `G`-action on `single a 1`. -/
@[simp]
theorem classGroupModPGroupRingAction_single (ρ : CyclotomicGalAction p K)
    (a : CyclotomicUnitDelta p) :
    classGroupModPGroupRingAction (p := p) (K := K) ρ (MonoidAlgebra.single a 1) =
      ρ a := by
  rw [classGroupModPGroupRingAction, MonoidAlgebra.lift_single, one_smul]

/-- The group-ring action via the canonical cyclotomic action instance agrees
with `cyclotomicGalActionLinearModP` on `single a 1`. -/
@[simp]
theorem classGroupModPGroupRingAction_instance_single
    (a : CyclotomicUnitDelta p) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K))
        (MonoidAlgebra.single a 1) =
      cyclotomicGalActionLinearModP (p := p) (K := K) a := by
  rw [classGroupModPGroupRingAction_single]
  rfl

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Abstract eigenvalue lemma.** Let `v` be a `ψ`-eigenvector for the
`G`-action `ρ`, i.e. `ρ a v = ψ a • v` for every `a` (where
`ψ : (ZMod p)ˣ → ZMod p` is multiplicative — typically a `ZMod p`-valued
character of `(ZMod p)ˣ`). Then any group-ring element `x` acts on `v` as the
scalar `∑ over the support of x, x(a) · ψ(a)`. -/
theorem classGroupModPGroupRingAction_apply_eigenvector
    (ρ : CyclotomicGalAction p K) {ψ : CyclotomicUnitDelta p → ZMod p}
    {v : ClassGroupModPMod p K} (hv : ∀ a, ρ a v = ψ a • v)
    (x : MonoidAlgebra (ZMod p) (CyclotomicUnitDelta p)) :
    classGroupModPGroupRingAction (p := p) (K := K) ρ x v =
      (x.sum fun a b ↦ b * ψ a) • v := by
  rw [classGroupModPGroupRingAction, MonoidAlgebra.lift_apply, LinearMap.finsupp_sum_apply,
    Finsupp.sum, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [LinearMap.smul_apply, hv a, smul_smul]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Eigenvalue action of the integral Stickelberger element.** For a unit
`c : (ZMod p)ˣ` and a `ψ`-eigenvector `v`, the integral corrected Stickelberger
element `stickelbergerCorrectedInt c` (mapped along `ℤ → ZMod p`) acts on `v` by
the explicit Stickelberger scalar

  `∑_b (corrCoeff c b : ZMod p) · ψ(b⁻¹)`.

This is the integral, mod-`p` form of `ε_χ · θ_p = (eigenvalue) · ε_χ`: the
action of `(c.val - σ_c) θ_p` on a `ψ`-eigenvector is scalar multiplication. -/
theorem stickelbergerCorrectedInt_action_eigenvector
    (ρ : CyclotomicGalAction p K) {ψ : CyclotomicUnitDelta p → ZMod p}
    {v : ClassGroupModPMod p K} (hv : ∀ a, ρ a v = ψ a • v)
    (c : (ZMod p)ˣ) :
    classGroupModPGroupRingAction (p := p) (K := K) ρ
        (MonoidAlgebra.mapRingHom (CyclotomicUnitDelta p) (Int.castRingHom (ZMod p))
          (stickelbergerCorrectedInt p c)) v =
      (∑ b : (ZMod p)ˣ,
        ((stickelbergerCorrectedCoeff p c b : ℤ) : ZMod p) * ψ b⁻¹) • v := by
  rw [stickelbergerCorrectedInt, map_sum, map_sum, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [map_zsmul, MonoidAlgebra.mapRingHom_single, map_one, map_zsmul,
    classGroupModPGroupRingAction_single, LinearMap.smul_apply, hv b⁻¹, mul_smul,
    Int.cast_smul_eq_zsmul]

/-- The `χ`-eigenvalue scalar of the corrected Stickelberger element
`(c.val - σ_c) θ_p`, written with `ℚ`-valued coefficients:

  `∑_b (corrCoeff c b : ℚ) · χ(b⁻¹)`.

This is the rational shadow of the mod-`p` scalar appearing in
`stickelbergerCorrectedInt_action_eigenvector`; the two agree under reduction
`ℤ → ZMod p` when `χ` reduces to `ψ`. -/
def stickelbergerCorrectedScalar (χ : MulChar (ZMod p)ˣ ℚ) (c : (ZMod p)ˣ) : ℚ :=
  ∑ b : (ZMod p)ˣ, ((stickelbergerCorrectedCoeff p c b : ℤ) : ℚ) * χ b⁻¹

/-- **Eigenvalue of the corrected Stickelberger element.** The `χ`-eigenvalue of
`(c.val - σ_c) θ_p` is `(c.val - χ c) · (eigenvalue of θ_p)`, where the
eigenvalue of `θ_p` is `stickelbergerEigenvalue p χ`. -/
theorem stickelbergerCorrectedScalar_eq (χ : MulChar (ZMod p)ˣ ℚ) (c : (ZMod p)ˣ) :
    stickelbergerCorrectedScalar (p := p) χ c =
      (((c : ZMod p).val : ℚ) - χ c) * stickelbergerEigenvalue p χ := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  apply mul_left_cancel₀ hp_ne
  rw [stickelbergerCorrectedScalar, Finset.mul_sum, stickelbergerEigenvalue_def]
  rw [show (p : ℚ) * ((((c : ZMod p).val : ℚ) - χ c) *
        ((p : ℚ)⁻¹ * ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) * χ a⁻¹)) =
      (((c : ZMod p).val : ℚ) - χ c) *
        ((p : ℚ) * (p : ℚ)⁻¹ * ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) * χ a⁻¹) from by
      ring]
  rw [mul_inv_cancel₀ hp_ne, one_mul]
  rw [show (∑ b : (ZMod p)ˣ, (p : ℚ) * (((stickelbergerCorrectedCoeff p c b : ℤ) : ℚ) * χ b⁻¹))
        = ∑ b : (ZMod p)ˣ, ((p : ℚ) * ((stickelbergerCorrectedCoeff p c b : ℤ) : ℚ)) * χ b⁻¹ from
      Finset.sum_congr rfl fun b _ ↦ by ring]
  simp_rw [show ∀ b : (ZMod p)ˣ, (p : ℚ) * ((stickelbergerCorrectedCoeff p c b : ℤ) : ℚ) =
      ((c : ZMod p).val * (b : ZMod p).val : ℚ) - (((c * b : (ZMod p)ˣ) : ZMod p).val : ℚ) from
    fun b ↦ by rw [rat_stickelbergerCorrectedCoeff p c b]]
  rw [show (∑ b : (ZMod p)ˣ, (((c : ZMod p).val * (b : ZMod p).val : ℚ) -
        (((c * b : (ZMod p)ˣ) : ZMod p).val : ℚ)) * χ b⁻¹)
      = (∑ b : (ZMod p)ˣ, ((c : ZMod p).val : ℚ) * (((b : ZMod p).val : ℚ) * χ b⁻¹))
        - ∑ b : (ZMod p)ˣ, (((c * b : (ZMod p)ˣ) : ZMod p).val : ℚ) * χ b⁻¹ from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ ↦ by push_cast; ring]
  rw [← Finset.mul_sum, sub_mul]
  congr 1
  rw [show (χ c * ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) * χ a⁻¹)
      = ∑ a : (ZMod p)ˣ, ((a : ZMod p).val : ℚ) * (χ c * χ a⁻¹) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by ring]
  rw [← (Group.mulLeft_bijective c).sum_comp
    (fun a : (ZMod p)ˣ ↦ (((a : (ZMod p)ˣ) : ZMod p).val : ℚ) * (χ c * χ a⁻¹))]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  rw [show ((c * b : (ZMod p)ˣ))⁻¹ = b⁻¹ * c⁻¹ from by rw [mul_inv_rev], map_mul]
  rw [show χ c * (χ b⁻¹ * χ c⁻¹) = (χ c * χ c⁻¹) * χ b⁻¹ from by ring,
    ← map_mul, mul_inv_cancel, map_one, one_mul]

/-- **The Stickelberger eigenvalue is the generalized Bernoulli number.** For a
nontrivial character `χ`, the `χ`-eigenvalue of the corrected Stickelberger
element `(c.val - σ_c) θ_p` equals `(c.val - χ c) · B_{1,χ⁻¹}`. -/
theorem stickelbergerCorrectedScalar_eq_BernoulliGen {χ : MulChar (ZMod p)ˣ ℚ}
    (hχ : χ ≠ 1) (c : (ZMod p)ˣ) :
    stickelbergerCorrectedScalar (p := p) χ c =
      (((c : ZMod p).val : ℚ) - χ c) * BernoulliGen (unitMulCharDirichlet p χ⁻¹) 1 := by
  rw [stickelbergerCorrectedScalar_eq, stickelbergerEigenvalue_eq_BernoulliGen p hχ]

end Eichler

end FLT37

end BernoulliRegular
