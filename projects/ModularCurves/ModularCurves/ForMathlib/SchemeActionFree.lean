/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.SchemeQuotient
import ModularCurves.ForMathlib.InvariantTorsor

/-!
# Geometric freeness ⟹ algebraic freeness (the T-Q2 bridge)

`ForMathlib/InvariantTorsor.lean` proves the Katz–Mazur A7.1.1 package (finite, unramified,
étale, torsor, base change) from `IsFreeAlgebraAction G R A` — KM's *"for any non-zero
`R`-algebra `R'`, and any `g ≠ 1`, `g` operates without fixed points on
`Hom_{R-alg}(A, R')`"*.

`ForMathlib/SchemeQuotient.lean` proves the quotient `X/G` from a *geometric* freeness
statement: no `γ ≠ 1` fixes a `T`-point of `X` over a nonempty `T`.

This file is the bridge: on a `G`-stable **affine** open, geometric freeness gives
`IsFreeAlgebraAction` on the section ring. It is the input that turns the local quotient
`V ⟶ Spec Γ(X,V)ᴳ` into a finite étale `G`-torsor.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

namespace SchemeAction

variable {G : Type*} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)

/-- **(T-Q2 bridge)** If no `γ ≠ 1` fixes a `T`-point of `X` over a nonempty `T`, then on every
`G`-stable affine open `U` the induced action on the section ring `Γ(X, U)` is free in the sense
of Katz–Mazur A7.1.1 (`IsFreeAlgebraAction`).

Given a ring point `φ : Γ(X, U) →ₐ[ℤ] R'` with `R'` nontrivial and `φ ∘ (γ • ·) = φ`, the
morphism `t : Spec R' ⟶ Spec Γ(X, U) ≅ U ↪ X` is `γ`-fixed (`specSMul_isoSpec_inv` is exactly the
statement that `Spec` of the ring action *is* the restricted geometric action), so `Spec R'` is
empty — impossible, since a nontrivial ring has a prime ideal. -/
theorem isFreeAlgebraAction_of_free {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    IsFreeAlgebraAction G ℤ ↑Γ(X, U) := by
  letI := σ.gammaMulSemiringAction hU
  intro γ hγ R' _ _ _ φ
  by_contra hcon
  push_neg at hcon
  -- `φ` is `γ`-invariant, hence `Spec φ` equalises the action
  have hring : (CommRingCat.ofHom (MulSemiringAction.toRingHom G (↑Γ(X, U)) γ)) ≫
      CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom φ.toRingHom := by
    ext a
    exact hcon a
  have hspec : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specSMul γ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    show Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G (↑Γ(X, U)) γ)) = _
    rw [← Spec.map_comp, hring]
  -- the resulting point of `X` is `γ`-fixed
  set t : Spec (CommRingCat.of R') ⟶ X :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hUa.isoSpec.inv ≫ U.ι with ht
  have h1 : U.ι ≫ σ.hom γ = (σ.hom γ).resLE U U (hU.le_preimage γ) ≫ U.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have h2 : hUa.isoSpec.inv ≫ (σ.hom γ).resLE U U (hU.le_preimage γ) =
      specSMul γ ≫ hUa.isoSpec.inv := (specSMul_isoSpec_inv σ hU hUa γ).symm
  have hfix : t ≫ σ.hom γ = t := by
    rw [ht]
    simp only [Category.assoc]
    rw [h1, ← Category.assoc hUa.isoSpec.inv, h2, Category.assoc,
      ← Category.assoc (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specSMul γ), hspec]
  -- but `Spec R'` is nonempty
  haveI hE : IsEmpty (Spec (CommRingCat.of R')) := hfree γ hγ _ t hfix
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
  exact hE.false p

/-- **(T-Q2 on a chart)** On a `G`-stable affine open of a scheme with a free `G`-action, the
section ring is a finite module over its invariants (KM A7.1.1, finiteness part). -/
theorem finite_gamma_of_free [Finite G] {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    Module.Finite (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) := by
  letI := σ.gammaMulSemiringAction hU
  exact Module.Finite.of_isFreeAlgebraAction G ℤ _ (σ.isFreeAlgebraAction_of_free hU hUa hfree)

/-- **(T-Q2 on a chart)** The torsor identity `Γ(X,U) ⊗_{Γ(X,U)ᴳ} Γ(X,U) ≅ ∏_G Γ(X,U)`
(KM A7.1.1, torsor part; SGA III Exp. V 4.1 (iv)) holds on every `G`-stable affine open of a
scheme with a free `G`-action. Geometrically: `U ⟶ U/G` is a `G`-torsor. -/
theorem torsorMul_bijective_of_free [Finite G] {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    Function.Bijective (MulSemiringAction.torsorMul G ℤ (↑Γ(X, U))) := by
  letI := σ.gammaMulSemiringAction hU
  exact torsorMul_bijective_of_isFreeAlgebraAction G ℤ _
    (σ.isFreeAlgebraAction_of_free hU hUa hfree)

end SchemeAction

end AlgebraicGeometry
