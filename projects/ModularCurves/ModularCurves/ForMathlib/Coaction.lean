/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.ComoduleCoinvariants
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Co-actions of a bialgebra (comodule algebras)

Construction support for `T-G3d-infra` Piece 3: the algebraic structure underlying the affine-local
quotient `Spec B → Spec B^{coρ}` (`.mathlib-quality/decomposition-g3d-piece3.md`). A **co-action**
of an `R`-bialgebra `A` on an `R`-algebra `B` is an algebra map `ρ : B →ₐ[R] B ⊗[R] A` — the
structure-sheaf dual of a group-scheme action `G ×_S X → X` (`A = O_G`, `B = O_X`) — satisfying
**counitality** and **coassociativity** (`IsCoaction`). This is the comodule-algebra structure;
mathlib has `Coalgebra`/`Bialgebra`/`HopfAlgebra` but **no comodule class** (only
`RepresentationTheory.Coinvariants`, the module-quotient — the wrong object), so it is built here.

The counit/coassoc axioms are stated as equalities of `R`-algebra maps, reconciled through the
tensor coherence isos `Algebra.TensorProduct.{rid, assoc}`; element-level forms follow by
`AlgHom.congr_fun`. The trivial co-action `b ↦ b ⊗ 1` (`Algebra.TensorProduct.includeLeft`) is a
co-action (`isCoaction_includeLeft`) — the dual of the trivial action — validating the definition.

`IsCoaction` is the route-independent foundation of the deep crux (`B` faithfully flat over
`B^{coρ}`, the Hopf-Galois / torsor property): both the general finite-flat route and the E[N] étale
shortcut factor through it; only the crux *proof* differs.
-/

open scoped TensorProduct

namespace ModularCurves

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R B] [Bialgebra R A]

/-- The **co-action axioms** for an algebra map `ρ : B →ₐ[R] B ⊗[R] A` (`A` an `R`-bialgebra): `ρ`
is *counital* — `(id ⊗ ε) ∘ ρ = id` under `B ⊗ R ≅ B` — and *coassociative* —
`(ρ ⊗ id) ∘ ρ = (id ⊗ Δ) ∘ ρ` under `(B ⊗ A) ⊗ A ≅ B ⊗ (A ⊗ A)`. This makes `B` a right
comodule algebra over `A`, i.e. an affine `A`-scheme with a `G`-action (`A = O_G`). -/
structure IsCoaction (ρ : B →ₐ[R] B ⊗[R] A) : Prop where
  /-- Counitality: `(id ⊗ ε) ∘ ρ`, followed by `B ⊗ R ≅ B`, is the identity. -/
  counit : (Algebra.TensorProduct.rid R R B).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R A)).comp ρ)
      = AlgHom.id R B
  /-- Coassociativity: `(ρ ⊗ id) ∘ ρ`, moved across the associator, equals `(id ⊗ Δ) ∘ ρ`. -/
  coassoc : (Algebra.TensorProduct.assoc R R R B A A).toAlgHom.comp
      ((Algebra.TensorProduct.map ρ (AlgHom.id R A)).comp ρ)
      = (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.comulAlgHom R A)).comp ρ

namespace IsCoaction

variable {ρ : B →ₐ[R] B ⊗[R] A}

/-- Element form of counitality: applying `(id ⊗ ε)` to `ρ b` and contracting `B ⊗ R ≅ B` recovers
`b`. -/
theorem counit_apply (h : IsCoaction ρ) (b : B) :
    Algebra.TensorProduct.rid R R B
        (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R A) (ρ b)) = b := by
  simpa using AlgHom.congr_fun h.counit b

/-- Element form of coassociativity: `(ρ ⊗ id)(ρ b)` moved across the associator equals
`(id ⊗ Δ)(ρ b)`. -/
theorem coassoc_apply (h : IsCoaction ρ) (b : B) :
    Algebra.TensorProduct.assoc R R R B A A
        (Algebra.TensorProduct.map ρ (AlgHom.id R A) (ρ b))
      = Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.comulAlgHom R A) (ρ b) := by
  simpa using AlgHom.congr_fun h.coassoc b

end IsCoaction

/-- The **trivial co-action** `b ↦ b ⊗ 1` (`Algebra.TensorProduct.includeLeft`) is a co-action — the
structure-sheaf dual of the trivial `G`-action. Validates `IsCoaction`; its co-invariants are all of
`B`. -/
theorem isCoaction_includeLeft :
    IsCoaction (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] A) where
  counit := by ext b; simp
  coassoc := by ext b; simp [Algebra.TensorProduct.one_def]

/-- The co-invariants of the trivial co-action `b ↦ b ⊗ 1` are all of `B` — the dual statement that
the trivial `G`-action has quotient `X` itself. -/
theorem coinvariants_includeLeft :
    coinvariants (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] A) = ⊤ := by
  ext b
  simp [Algebra.TensorProduct.includeLeft_apply]

end ModularCurves
