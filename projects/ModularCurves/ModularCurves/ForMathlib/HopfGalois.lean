/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.Coaction
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The canonical Galois map and the Hopf-Galois / torsor property

Construction support for `T-G3d-infra` Piece 3 (`.mathlib-quality/decomposition-g3d-piece3.md`): the
**precise, route-independent statement of the deep crux**. For a co-action `ρ : B →ₐ[R] B ⊗[R] A`
with co-invariants `S = B^{coρ}` (`ForMathlib/ComoduleCoinvariants.lean`), the **canonical Galois
map** is
`β : B ⊗_S B → B ⊗_R A,   b ⊗ b' ↦ (b ⊗ 1) · ρ(b')`,
the affine dual of the "action + projection" map `G ×_S X → X ×_{X/G} X`. Its well-definedness over
`S` is *exactly* the co-invariant property: `ρ` and `b ↦ b ⊗ 1` are both `S`-algebra maps (for `ρ`,
`S`-linearity says `ρ s = s ⊗ 1` for `s ∈ S`, which is the definition of `S = B^{coρ}`), so `β` is
their `Algebra.TensorProduct.lift`.

`IsHopfGalois ρ` bundles the crux: `β` bijective (**the action is free and transitive on fibres**)
together with `B` faithfully flat over `S` (**the quotient map `Spec B → Spec S` is flat +
surjective**). By `isRegularEpi_of_flat_of_surjective_of_isAffine` (`@[stacks 023Q]`),
`IsHopfGalois` gives the affine-local `Spec B → Spec B^{coρ}` as the coequalizer of the groupoid —
discharging the `SubgroupQuotient` pins through `isInvariant_iff_coequalizes`.

This statement is **route-independent**: the general finite-flat route and the E[N] étale shortcut
both target `IsHopfGalois`; only its *proof* (finite-flat-group-scheme torsor theory vs. étale
descent) differs, and that proof is the multi-week, mathlib-absent core (no Hopf-Galois / torsor
infrastructure exists in mathlib).
-/

open scoped TensorProduct

namespace ModularCurves

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The co-action `ρ`, viewed as an algebra map over the co-invariants `S = B^{coρ}`. Its
`S`-linearity is precisely the co-invariant property `ρ s = s ⊗ 1` for `s ∈ S`. -/
noncomputable def coactionOverCoinvariants (ρ : B →ₐ[R] B ⊗[R] A) :
    B →ₐ[coinvariants ρ] (B ⊗[R] A) where
  toFun := ρ
  map_one' := map_one ρ
  map_mul' := map_mul ρ
  map_zero' := map_zero ρ
  map_add' := map_add ρ
  commutes' := fun r => by
    simpa [Subalgebra.algebraMap_def, Algebra.TensorProduct.algebraMap_apply]
      using coinvariants_coaction ρ r

/-- The inclusion `b ↦ b ⊗ 1`, viewed as an algebra map over the co-invariants `S = B^{coρ}`. -/
noncomputable def includeLeftOverCoinvariants (ρ : B →ₐ[R] B ⊗[R] A) :
    B →ₐ[coinvariants ρ] (B ⊗[R] A) :=
  (Algebra.ofId B (B ⊗[R] A)).restrictScalars (coinvariants ρ)

@[simp]
theorem includeLeftOverCoinvariants_apply (ρ : B →ₐ[R] B ⊗[R] A) (b : B) :
    includeLeftOverCoinvariants ρ b = b ⊗ₜ[R] 1 := rfl

@[simp]
theorem coactionOverCoinvariants_apply (ρ : B →ₐ[R] B ⊗[R] A) (b : B) :
    coactionOverCoinvariants ρ b = ρ b := rfl

/-- The **canonical Galois map** `β : B ⊗_S B → B ⊗_R A`, `b ⊗ b' ↦ (b ⊗ 1) · ρ(b')`, where
`S = B^{coρ}`. The affine dual of `G ×_S X → X ×_{X/G} X`; the extension `B / B^{coρ}` is
*Hopf-Galois* exactly when `β` is bijective. -/
noncomputable def canonicalGaloisMap (ρ : B →ₐ[R] B ⊗[R] A) :
    (B ⊗[coinvariants ρ] B) →ₐ[coinvariants ρ] (B ⊗[R] A) :=
  Algebra.TensorProduct.lift (includeLeftOverCoinvariants ρ) (coactionOverCoinvariants ρ)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem canonicalGaloisMap_tmul (ρ : B →ₐ[R] B ⊗[R] A) (b b' : B) :
    canonicalGaloisMap ρ (b ⊗ₜ[coinvariants ρ] b') = (b ⊗ₜ[R] 1) * ρ b' := rfl

/-- `β ∘ (b ↦ b ⊗ 1) = (b ↦ b ⊗ 1)`: the canonical Galois map sends the left inclusion of `B ⊗_S B`
to the left inclusion of `B ⊗_R A`. On `Spec` this identifies one kernel-pair projection with the
`SpecEqualizer` cofork's `Spec includeLeft` leg. -/
theorem canonicalGaloisMap_comp_includeLeft (ρ : B →ₐ[R] B ⊗[R] A) :
    (canonicalGaloisMap ρ).comp Algebra.TensorProduct.includeLeft
      = includeLeftOverCoinvariants ρ := by
  ext b
  show canonicalGaloisMap ρ (b ⊗ₜ[coinvariants ρ] 1) = b ⊗ₜ[R] 1
  rw [canonicalGaloisMap_tmul, map_one, mul_one]

/-- `β ∘ (b ↦ 1 ⊗ b) = ρ`: the canonical Galois map sends the right inclusion of `B ⊗_S B` to the
co-action `ρ`. On `Spec` this identifies the other kernel-pair projection with the `SpecEqualizer`
cofork's `Spec ρ` leg. -/
theorem canonicalGaloisMap_comp_includeRight (ρ : B →ₐ[R] B ⊗[R] A) :
    (canonicalGaloisMap ρ).comp Algebra.TensorProduct.includeRight
      = coactionOverCoinvariants ρ := by
  ext b
  show canonicalGaloisMap ρ ((1 : B) ⊗ₜ[coinvariants ρ] b) = ρ b
  rw [canonicalGaloisMap_tmul, ← Algebra.TensorProduct.one_def, one_mul]

/-- The **Hopf-Galois / torsor property** of a co-action `ρ`, the precise form of the `T-G3d-infra`
Piece 3 crux. Both conditions are needed to realise `Spec B → Spec B^{coρ}` as the affine
coequalizer of the translation groupoid via `@[stacks 023Q]`:

* `galois`: the canonical Galois map `β` is bijective — the action `G ×_S X ⇉ X` is *free and
  transitive on fibres* (its kernel pair is the graph of the action);
* `faithfullyFlat`: `B` is faithfully flat over `S = B^{coρ}` — the quotient map is *flat and
  surjective*, so `023Q` gives it as a regular epi (= coequalizer).

This is the route-independent target; its proof for the translation co-action of a
finite-locally-free group scheme is the multi-week, mathlib-absent core. -/
structure IsHopfGalois (ρ : B →ₐ[R] B ⊗[R] A) : Prop where
  /-- The canonical Galois map `β : B ⊗_S B → B ⊗_R A` is bijective. -/
  galois : Function.Bijective (canonicalGaloisMap ρ)
  /-- `B` is faithfully flat over its co-invariants `S = B^{coρ}`. -/
  faithfullyFlat : Module.FaithfullyFlat (coinvariants ρ) B

namespace IsHopfGalois

variable {ρ : B →ₐ[R] B ⊗[R] A}

/-- The **Galois isomorphism** `B ⊗_S B ≃ B ⊗_R A` packaged from the bijective canonical Galois map.
This is the algebra dual of the groupoid iso `Spec B ×_{Spec S} Spec B ≅ G ×_S Spec B` (the action
is an equivalence relation); on `Spec` it identifies the kernel pair of the quotient map with the
translation groupoid, the input to the `@[stacks 023Q]` coequalizer. -/
noncomputable def galoisEquiv (h : IsHopfGalois ρ) :
    (B ⊗[coinvariants ρ] B) ≃ₐ[coinvariants ρ] (B ⊗[R] A) :=
  AlgEquiv.ofBijective (canonicalGaloisMap ρ) h.galois

@[simp]
theorem galoisEquiv_tmul (h : IsHopfGalois ρ) (b b' : B) :
    h.galoisEquiv (b ⊗ₜ[coinvariants ρ] b') = (b ⊗ₜ[R] 1) * ρ b' := rfl

end IsHopfGalois

end ModularCurves
