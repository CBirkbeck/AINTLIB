/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Co-invariants of a co-action

Construction support for `T-G3d-infra` Piece 3 (`.mathlib-quality/decomposition-g3d-piece3.md`): the
central object of the affine-local quotient's deep crux. For a **co-action** `ρ : B →ₐ[R] B ⊗[R] A`
(the structure-sheaf dual of the translation action `G ×_S E → E`, `A = O_G`), the **co-invariants**
`B^{coρ} = {b : ρ b = b ⊗ 1}` are the functions on the affine chart of the quotient `E/G`; the
affine quotient map is `Spec B ⟶ Spec B^{coρ}` (cf. `ForMathlib/SpecEqualizer.lean`). Absent from
mathlib (only representation-coinvariants exist, the wrong object), so built here as an
`R`-subalgebra via the `AlgHom.equalizer` of `ρ` and the "trivial co-action" `b ↦ b ⊗ 1`
(`Algebra.TensorProduct.includeLeft`).

The remaining crux — `B` is *faithfully flat* over `B^{coρ}` (the torsor / Hopf-Galois property),
whence `Spec B → Spec B^{coρ}` is the affine coequalizer via
`isRegularEpi_of_flat_of_surjective_of_isAffine` — is deferred (multi-week, mathlib-gap-filling).
-/

open scoped TensorProduct

namespace ModularCurves

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The **co-invariants** of a co-action `ρ : B →ₐ[R] B ⊗[R] A`: the `R`-subalgebra
`{b : ρ b = b ⊗ₜ 1}` where `ρ` agrees with the trivial co-action `b ↦ b ⊗ₜ 1`. On `Spec`, these are
the functions on the quotient chart. -/
def coinvariants (ρ : B →ₐ[R] B ⊗[R] A) : Subalgebra R B :=
  AlgHom.equalizer ρ Algebra.TensorProduct.includeLeft

@[simp]
theorem mem_coinvariants {ρ : B →ₐ[R] B ⊗[R] A} {b : B} :
    b ∈ coinvariants ρ ↔ ρ b = b ⊗ₜ[R] 1 := by
  rw [coinvariants, AlgHom.mem_equalizer, Algebra.TensorProduct.includeLeft_apply]

/-- The restriction of the co-action to the co-invariants is the trivial co-action `b ↦ b ⊗ₜ 1`. -/
theorem coinvariants_coaction (ρ : B →ₐ[R] B ⊗[R] A) (b : coinvariants ρ) :
    ρ b = (b : B) ⊗ₜ[R] 1 :=
  mem_coinvariants.mp b.2

/-- **Functoriality of co-invariants across a (possibly base-changing) equivariant square.**
If `φB` intertwines the two co-actions through *any* comparison map `T` of the tensor sides
that carries `b ⊗ 1` to `φB b ⊗ 1`, then `φB` maps co-invariants to co-invariants. (`T` is
data: at the chart-restriction instantiation it is the tensor of the two section
restrictions, and the square is the geometric equivariance of the restricted action —
`[HG-C4c]`.) -/
theorem mem_coinvariants_of_map {R' A' B' : Type*} [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R' A'] [Algebra R' B'] {ρ : B →ₐ[R] B ⊗[R] A} {ρ' : B' →ₐ[R'] B' ⊗[R'] A'}
    (φB : B →+* B') (T : B ⊗[R] A →+* B' ⊗[R'] A')
    (hsq : ∀ b, ρ' (φB b) = T (ρ b)) (hT1 : ∀ b : B, T (b ⊗ₜ[R] 1) = φB b ⊗ₜ[R'] 1)
    {b : B} (hb : b ∈ coinvariants ρ) : φB b ∈ coinvariants ρ' := by
  rw [mem_coinvariants] at hb ⊢
  rw [hsq, hb, hT1]

end ModularCurves
