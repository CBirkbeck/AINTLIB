import ModularCurves.ForMathlib.HopfGaloisBootstrap
import ModularCurves.ForMathlib.CoinvariantsPoints
import ModularCurves.ForMathlib.CoinvariantsBaseChange
import ModularCurves.ForMathlib.FlatLocalInfiniteResidue
import ModularCurves.ForMathlib.SemilocalBasis
import ModularCurves.ForMathlib.FaithfullyFlatEqualizer
import ModularCurves.ForMathlib.FaithfullyFlatFiniteDescent

/-!
# The Hopf–Galois theorem for co-actions of finite free Hopf algebras

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B6]`; Stacks 03BM =
SGA 3 Exp. V Théorème 4.1, affine case, comodule form): for a co-action
`ρ : B →ₐ[R] B ⊗[R] A` of a finite free commutative Hopf algebra such that the
product map `B ⊗[R] B → B ⊗[R] A`, `b ⊗ b' ↦ (b ⊗ 1)·ρ(b')` is surjective (the
action-pair is a closed immersion — e.g. a free translation action), `B` is a
Hopf–Galois extension of its co-invariants: the canonical Galois map is bijective
and `B` is faithfully flat over `coinvariants ρ`.

The proof is the per-prime bootstrap of the decomposition appendix `[HG-B6]`:
localize the co-invariants at a maximal ideal, pass to the flat local extension
with infinite residue field (`LocalPolynomialExtension`), base-change the
co-action, harvest the shifted basis via semi-locality + the semi-local basis
selection, conclude Galois upstairs by the bootstrap, and descend.
-/

namespace ModularCurves

open TensorProduct

section GeneralizedGalois

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]
variable (C₀ : Type*) [CommRing C₀] [Algebra C₀ B] [SMulCommClass R C₀ B]

/-- A co-action, re-based to scalars `C₀` mapping into the co-invariants (the `C₀`-algebra
structure on `B ⊗[R] A` is `Algebra.TensorProduct.leftAlgebra` through the left factor). -/
noncomputable def coactionOver (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A)) :
    B →ₐ[C₀] B ⊗[R] A where
  toRingHom := ρ.toRingHom
  commutes' := fun c => by
    show ρ (algebraMap C₀ B c) = algebraMap C₀ (B ⊗[R] A) c
    rw [hcoinv c, Algebra.TensorProduct.algebraMap_apply]

@[simp]
theorem coactionOver_apply (ρ : B →ₐ[R] B ⊗[R] A) (hcoinv) (b : B) :
    coactionOver R A C₀ ρ hcoinv b = ρ b := rfl

/-- The generalized Galois product map over `C₀`: `b ⊗ b' ↦ (b ⊗ 1) · ρ(b')`. -/
noncomputable def galoisProductMap (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A)) :
    (B ⊗[C₀] B) →ₐ[C₀] B ⊗[R] A :=
  Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.includeLeft (S := C₀))
    (coactionOver R A C₀ ρ hcoinv)

@[simp]
theorem galoisProductMap_tmul (ρ : B →ₐ[R] B ⊗[R] A) (hcoinv) (b b' : B) :
    galoisProductMap R A C₀ ρ hcoinv (b ⊗ₜ[C₀] b')
      = (b ⊗ₜ[R] (1 : A)) * ρ b' := by
  rw [galoisProductMap, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.includeLeft_apply, coactionOver_apply]

/-- The generalized Galois product map as a left `B`-linear map. -/
noncomputable def galoisProductLinear (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A)) :
    (B ⊗[C₀] B) →ₗ[B] B ⊗[R] A where
  toFun := galoisProductMap R A C₀ ρ hcoinv
  map_add' := map_add _
  map_smul' := by
    intro b y
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [show (algebraMap B (B ⊗[C₀] B)) b = b ⊗ₜ[C₀] (1 : B) from rfl,
      galoisProductMap_tmul, map_one, mul_one]
    rfl

/-- **Generalized bootstrap conclusion** (the `C₀`-form of Stacks 03C8's second half):
if `(x i)` is a `C₀`-basis of `B` and the `ρ (x i)` form a left `B`-basis of `B ⊗[R] A`,
the generalized Galois product map over `C₀` is bijective. -/
theorem bijective_galoisProductMap_of_basis
    {ι' : Type*} [Fintype ι'] (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A))
    (hb : Module.Basis ι' B (B ⊗[R] A)) (bx : Module.Basis ι' C₀ B)
    (hx : ∀ i, hb i = ρ (bx i)) :
    Function.Bijective (galoisProductMap R A C₀ ρ hcoinv) := by
  classical
  set bT := bx.baseChange B with hbT
  have hmap : galoisProductLinear R A C₀ ρ hcoinv
      = (bT.equiv hb (Equiv.refl ι')).toLinearMap := by
    refine bT.ext (fun i => ?_)
    show galoisProductMap R A C₀ ρ hcoinv (bT i) = (bT.equiv hb (Equiv.refl ι')) (bT i)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply, hbT, Module.Basis.baseChange_apply]
    rw [galoisProductMap_tmul, hx i,
      show ((1 : B) ⊗ₜ[R] (1 : A)) = (1 : B ⊗[R] A) from rfl, one_mul]
  have hbij : Function.Bijective (galoisProductLinear R A C₀ ρ hcoinv) := by
    rw [hmap]
    exact (bT.equiv hb (Equiv.refl ι')).bijective
  exact hbij

end GeneralizedGalois

end ModularCurves
