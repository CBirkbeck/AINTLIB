/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Fibrewise finiteness of a quotient

`Module.Finite R (A ⧸ I)` says the closed subscheme `V(I) ⊆ Spec A` is **finite over the
base**. For a relative effective Cartier divisor `D ⊂ C` on a relative curve `C/S` this is
true *globally* (`D ⟶ S` is finite) but **false on a general chart**: a chart cuts `D` down
to an open piece, and an open piece of a finite scheme is only *clopen*-locally finite. The
standard counterexample is `ℤ[1/2]` over `ℤ`, which is `Γ` of a basic open of the finite
`ℤ`-scheme `Spec ℤ`, and is not a finite `ℤ`-module.

What survives — and what every consumer actually uses — is the **fibrewise** statement:

* `ModularCurves.HasFiniteFibres R A I` — for every field `K` over `R`, the base change
  `K ⊗[R] (A ⧸ I)` is a finite `K`-module.

This is exactly "every fibre of `V(I) ⟶ Spec R` is a finite scheme", and unlike finiteness
it *is* inherited by charts: `K ⊗[ℤ] ℤ[1/2]` is `K` or `0`. The mechanism is
`module_finite_tensor_of_localizationAway`: after base change to `K` the ambient finite
algebra becomes Artinian, and a localization of an Artinian ring is a quotient of it
(`IsArtinianRing.localization_surjective`), hence still finite.
-/

universe u

open TensorProduct

namespace ModularCurves

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- `A ⧸ I` **has finite fibres** over `R`: for every field `K` over `R` the base change
`K ⊗[R] (A ⧸ I)` is a finite `K`-module, i.e. every fibre of `V(I) ⟶ Spec R` is a finite
scheme. Weaker than `Module.Finite R (A ⧸ I)`, and — unlike it — stable under passing to a
chart. -/
def HasFiniteFibres (I : Ideal A) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K], Module.Finite K (K ⊗[R] (A ⧸ I))

/-- Finite ⟹ fibrewise finite (base change of a finite module). -/
theorem hasFiniteFibres_of_finite (I : Ideal A) (hfin : Module.Finite R (A ⧸ I)) :
    HasFiniteFibres R A I := fun _ _ _ => by
  haveI := hfin
  infer_instance

/-- Fibrewise finiteness only depends on the `R`-algebra `A ⧸ I` up to isomorphism. -/
theorem hasFiniteFibres_of_algEquiv {I : Ideal A} (Q : Type u) [CommRing Q] [Algebra R Q]
    (e : Q ≃ₐ[R] A ⧸ I)
    (h : ∀ (K : Type u) [Field K] [Algebra R K], Module.Finite K (K ⊗[R] Q)) :
    HasFiniteFibres R A I := fun K _ _ => by
  haveI := h K
  exact Module.Finite.equiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) e).toLinearEquiv

/-- **The chart mechanism.** A localization away from an element, of a *module-finite*
algebra, still has finite fibres: `K ⊗[R] B` is a finite `K`-algebra, hence Artinian, and a
localization of an Artinian ring is a quotient of it.

This is what lets a relative effective Cartier divisor be read off on an arbitrary basic-open
chart, where it is no longer finite over the base. -/
theorem module_finite_tensor_of_localizationAway (B K Bb : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Field K] [Algebra R K] (b : B) [CommRing Bb] [Algebra R Bb]
    [Algebra B Bb] [IsScalarTower R B Bb] [IsLocalization.Away b Bb] :
    Module.Finite K (K ⊗[R] Bb) := by
  haveI hfinKB : Module.Finite K (K ⊗[R] B) := inferInstance
  haveI : IsArtinianRing (K ⊗[R] B) := IsArtinianRing.of_finite K (K ⊗[R] B)
  haveI : Module.Finite K (Localization.Away ((1 : K) ⊗ₜ[R] b)) :=
    Module.Finite.of_surjective
      (IsScalarTower.toAlgHom K (K ⊗[R] B)
        (Localization.Away ((1 : K) ⊗ₜ[R] b))).toLinearMap
      (IsArtinianRing.localization_surjective (Submonoid.powers ((1 : K) ⊗ₜ[R] b)) _)
  exact Module.Finite.equiv
    (IsLocalization.Away.tensorProductEquivTMulRight R K b Bb).symm.toLinearEquiv

end ModularCurves
