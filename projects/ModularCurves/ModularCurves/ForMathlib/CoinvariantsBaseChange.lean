import ModularCurves.ForMathlib.HopfGalois
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Base change of a co-action along the co-invariants

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B3]`; Stacks
`groupoids-lemma-invariants-base-change`, tag 03BK): for a co-action `ρ : B → B ⊗[R] A`
with co-invariants `C := coinvariants ρ` and a `C`-algebra `C'`, the co-action base
changes to `ρ' : C' ⊗[C] B → (C' ⊗[C] B) ⊗[R] A` — `ρ` is `C`-linear
(`coactionOverCoinvariants`), so `id_{C'} ⊗ ρ` makes sense, reassociated through the
heterobasic `Algebra.TensorProduct.assoc`.

* `coactionBaseChange` — the base-changed co-action `ρ'`;
* `coactionBaseChange_tmul` — `ρ'(c' ⊗ b) = (c' ⊗ b₍₀₎) ⊗ b₍₁₎` on expansions;
* (later increments) `IsCoaction (coactionBaseChange …)`, and — the 03BK(3) content —
  for **flat** `C → C'` the co-invariants of `ρ'` are exactly the image of `C'`
  (`AlgHom.tensorEqualizerEquiv`).

This is the gadget the `[HG-B6]` bootstrap uses at each localized invariant ring: base
change along `C → (LocalPolynomialExtension (Localization.AtPrime p))` preserves the
co-invariants, so the semi-local heart (03C1 + 03C8) applies upstairs and its conclusions
descend.
-/

open scoped TensorProduct

namespace ModularCurves

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]
variable (ρ : B →ₐ[R] B ⊗[R] A)
variable (C' : Type*) [CommRing C'] [Algebra R C']
variable [Algebra (coinvariants ρ) C'] [IsScalarTower R (coinvariants ρ) C']

/-- The heterobasic associator specialized to the base-change situation:
`(C' ⊗[C] B) ⊗[R] A ≃ C' ⊗[C] (B ⊗[R] A)`. -/
noncomputable def baseChangeAssoc :
    ((C' ⊗[coinvariants ρ] B) ⊗[R] A) ≃ₐ[C'] C' ⊗[coinvariants ρ] (B ⊗[R] A) :=
  Algebra.TensorProduct.assoc R (coinvariants ρ) C' C' B A

/-- **The base-changed co-action**: `ρ' : C' ⊗[C] B → (C' ⊗[C] B) ⊗[R] A`, the map
`id_{C'} ⊗ ρ` (using the `C`-linearity of `ρ`) reassociated. -/
noncomputable def coactionBaseChange :
    (C' ⊗[coinvariants ρ] B) →ₐ[R] (C' ⊗[coinvariants ρ] B) ⊗[R] A :=
  ((baseChangeAssoc R A ρ C').symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id C' C') (coactionOverCoinvariants ρ))).restrictScalars R

@[simp]
theorem coactionBaseChange_tmul (c' : C') (b : B) :
    coactionBaseChange R A ρ C' (c' ⊗ₜ[coinvariants ρ] b)
      = (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] ρ b) := rfl

end ModularCurves
