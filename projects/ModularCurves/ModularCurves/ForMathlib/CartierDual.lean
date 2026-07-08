import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Cartier duality and Deligne's order theorem (BB-DELIGNE)

This file develops the abstract Hopf-algebraic layer (Layer A of `plan-deligne.md`) of
**Deligne's theorem**: a finite locally free commutative group scheme of rank `N` is killed
by `N`. The route is Tate's, from J. Tate, *Finite flat group schemes* (in Cornell–Silverman–
Stevens, *Modular Forms and Fermat's Last Theorem*), §3.8, book pp. 143–145.

The mathematical content of §3.8, in the affine/Hopf-algebra picture `G = Spec A`, `R` the base
ring, `A` a finite locally free `R`-Hopf algebra of rank `n`:

* `A' := Hom_R(A, R)` is the **Cartier dual** — itself a commutative `R`-Hopf algebra when `A` is
  cocommutative (equivalently `G` commutative), finite locally free of the same rank `n`.
* A `B`-point of `G`, i.e. an `R`-algebra map `A → B`, is a **group-like** element of `A'_B := A' ⊗_R B`.
* The free rank-`n` left `A'`-module `A' ⊗_R A` carries two operators whose ratio realises the
  scalar `λ · Iₙ` (multiplication by a group-like `λ`) as a **commutator** in `GLₙ(A')`
  (Prop 3.8.1).
* Since `A'` is commutative, `det : GLₙ(A') → (A')ˣ` kills commutators, so `det(λ · Iₙ) = λⁿ = 1`.

This file proves the pieces bottom-up. The determinant step (Layer A leaf **T-D5f**) is pure
matrix algebra over a commutative ring and is proved first; the Cartier-dual algebra (**T-D5a**),
its finiteness (**T-D5b**), the points↔group-like dictionary (**T-D5c**), the operator/commutator
package (**T-D5d/e**) and the final group-like assembly (**T-D5g**) follow. The geometric bridge
(Layer B) lives in `ModularCurves.GroupScheme.DeligneOrder`.

See `.mathlib-quality/plan-deligne.md` for the full ticket board and verbatim source quotes.
-/

open scoped Matrix

namespace ModularCurves.CartierDual

universe u v

/-! ## Layer A leaf T-D5f — the determinant step

The determinant homomorphism `GLₙ(S) → Sˣ` over a *commutative* ring `S` kills commutators;
applied to the scalar matrix `λ · Iₙ = A B A⁻¹ B⁻¹` this gives `λⁿ = 1`. In Deligne's proof
`S = A'_B` is the (commutative) Cartier dual, `λ` the group-like element attached to a point,
and `n` the rank of `G` — so this leaf is exactly the last two sentences of Tate §3.8 (p. 144):
"we can use the determinant homomorphism `GLₙ(A') → (A')*` to conclude that `λⁿ = 1`." -/

/-- The determinant of a `unit` matrix and of its inverse multiply to `1`: `det ↑A · det ↑A⁻¹ = 1`.
A packaging of `Matrix.det_mul` + `Units.mul_inv` used repeatedly below. -/
theorem det_val_mul_det_val_inv {S : Type u} [CommRing S] {n : ℕ}
    (A : (Matrix (Fin n) (Fin n) S)ˣ) :
    (↑A : Matrix (Fin n) (Fin n) S).det * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det = 1 := by
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

/-- **(T-D5f — determinant step, Tate §3.8 p. 144.)** Over a commutative ring `S`, if the scalar
matrix `λ • Iₙ` is a commutator `A · B · A⁻¹ · B⁻¹` of invertible `n × n` matrices, then `λⁿ = 1`.

Proof: `det` is multiplicative and `S` is commutative, so `det(A B A⁻¹ B⁻¹) = 1`; and
`det(λ • Iₙ) = λⁿ` by `Matrix.det_smul`. This is the leaf discharged purely from mathlib
(`Matrix.det_smul`, `Matrix.det_mul`, `Matrix.det_one`, `Units.mul_inv`). -/
theorem pow_eq_one_of_smul_one_eq_commutator {S : Type u} [CommRing S] {n : ℕ}
    (lam : S) (A B : (Matrix (Fin n) (Fin n) S)ˣ)
    (h : lam • (1 : Matrix (Fin n) (Fin n) S) = ↑(A * B * A⁻¹ * B⁻¹)) :
    lam ^ n = 1 := by
  -- Take determinants of both sides.
  have key := congrArg Matrix.det h
  -- LHS: det (λ • 1) = λ ^ n.
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at key
  rw [key]
  -- RHS: det of the commutator is 1.
  simp only [Units.val_mul]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  -- goal: det↑A * det↑B * det↑A⁻¹ * det↑B⁻¹ = 1
  calc (↑A : Matrix (Fin n) (Fin n) S).det * (↑B : Matrix (Fin n) (Fin n) S).det
          * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det * (↑B⁻¹ : Matrix (Fin n) (Fin n) S).det
      = ((↑A : Matrix (Fin n) (Fin n) S).det * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det)
          * ((↑B : Matrix (Fin n) (Fin n) S).det * (↑B⁻¹ : Matrix (Fin n) (Fin n) S).det) := by
        ring
    _ = 1 * 1 := by rw [det_val_mul_det_val_inv, det_val_mul_det_val_inv]
    _ = 1 := by ring

end ModularCurves.CartierDual
