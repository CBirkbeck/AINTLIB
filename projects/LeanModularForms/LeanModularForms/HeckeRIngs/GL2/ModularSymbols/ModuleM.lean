/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.CoefficientSystem
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The integral modular-symbol module `𝕄 N k`

This file assembles the two coefficient systems of `CoefficientSystem.lean` into the integral
modular-symbol module.

## Main definitions

* `HeckeRing.GL2.ModularSymbols.fullModSymRep R m` : the diagonal tensor representation of
  `SL(2, ℤ)` on `Div0 R ⊗[R] SymPow R m`, where `g` acts as `div0Rep R g ⊗ symRep R m g`.
* `HeckeRing.GL2.ModularSymbols.modSymRep N m` : the restriction of `fullModSymRep ℤ m` to the
  congruence subgroup `Γ₁(N)`.
* `HeckeRing.GL2.ModularSymbols.𝕄 N k` : the integral modular-symbol module of weight `k` and
  level `N`, defined as the `Γ₁(N)`-coinvariants of `modSymRep N (k - 2).toNat`.
* `HeckeRing.GL2.ModularSymbols.𝕄.mk N k` : the canonical surjection from the tensor module onto
  `𝕄 N k`.

The diagonal tensor representation is built **manually** as a `MonoidHom`, rather than via
`Representation.tprod`, to avoid an instance diamond: `Representation.tprod` lands in a tensor type
carrying `TensorProduct.addCommMonoid`, whereas `Representation.Coinvariants` requires an
`AddCommGroup` on the underlying module. By packaging the action
`g ↦ TensorProduct.map (div0Rep R g)
(symRep R m g)` directly into the literal tensor type `Div0 R ⊗[R] SymPow R m`, the canonical
`AddCommGroup`/`Module R` instances (the tensor product of two submodules of `AddCommGroup`s) are
found by instance resolution and `Coinvariants` elaborates cleanly.
-/

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups TensorProduct

universe u

/-! ## `fullModSymRep` — the diagonal tensor representation -/

/-- The diagonal tensor representation of `SL(2, ℤ)` on `Div0 R ⊗[R] SymPow R m`: a matrix `g` acts
by `div0Rep R g ⊗ symRep R m g`.  Built manually as a `MonoidHom` (not via `Representation.tprod`)
so that the codomain is the literal tensor type, whose `AddCommGroup` instance is found by instance
resolution — this is what lets `Representation.Coinvariants` elaborate later. -/
noncomputable def fullModSymRep (R : Type u) [CommRing R] (m : ℕ) :
    Representation R SL(2, ℤ) (Div0 R ⊗[R] SymPow R m) where
  toFun g := TensorProduct.map (div0Rep R g) (symRep R m g)
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, TensorProduct.map_id]
  map_mul' := fun g h => by
    rw [map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      TensorProduct.map_comp, Module.End.mul_eq_comp]

@[simp]
theorem fullModSymRep_apply (R : Type u) [CommRing R] (m : ℕ) (g : SL(2, ℤ))
    (d : Div0 R) (s : SymPow R m) :
    fullModSymRep R m g (d ⊗ₜ s) = (div0Rep R g d) ⊗ₜ (symRep R m g s) :=
  rfl

/-! ## `modSymRep` — restriction to `Γ₁(N)` -/

/-- The restriction of the diagonal tensor representation `fullModSymRep ℤ m` to the congruence
subgroup `Γ₁(N) ≤ SL(2, ℤ)`. -/
noncomputable def modSymRep (N : ℕ) [NeZero N] (m : ℕ) :
    Representation ℤ (CongruenceSubgroup.Gamma1 N) (Div0 ℤ ⊗[ℤ] SymPow ℤ m) :=
  (fullModSymRep ℤ m).comp (CongruenceSubgroup.Gamma1 N).subtype

/-! ## `𝕄 N k` — the integral modular-symbol module -/

/-- The integral modular-symbol module of weight `k` and level `N`: the `Γ₁(N)`-coinvariants of the
diagonal tensor representation on `Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2)`. -/
def 𝕄 (N : ℕ) [NeZero N] (k : ℤ) : Type :=
  Representation.Coinvariants (modSymRep N (k - 2).toNat)

noncomputable instance (N : ℕ) [NeZero N] (k : ℤ) : AddCommGroup (𝕄 N k) :=
  inferInstanceAs <| AddCommGroup (Representation.Coinvariants (modSymRep N (k - 2).toNat))

noncomputable instance (N : ℕ) [NeZero N] (k : ℤ) : Module ℤ (𝕄 N k) :=
  inferInstanceAs <| Module ℤ (Representation.Coinvariants (modSymRep N (k - 2).toNat))

/-- The canonical surjection from the tensor module onto the modular-symbol module `𝕄 N k`. -/
noncomputable def 𝕄.mk (N : ℕ) [NeZero N] (k : ℤ) :
    (Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) →ₗ[ℤ] 𝕄 N k :=
  Representation.Coinvariants.mk (modSymRep N (k - 2).toNat)

theorem 𝕄.mk_surjective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Surjective (𝕄.mk N k) :=
  Representation.Coinvariants.mk_surjective (modSymRep N (k - 2).toNat)

end HeckeRing.GL2.ModularSymbols
