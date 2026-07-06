/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q5 (leaf T-Q5a).
-/
import ModularCurves.ForMathlib.SpecGroupAction

/-!
# Group actions on schemes: vocabulary for the quotient construction

A `G`-action on a scheme `X` is recorded as a bare family `σ : G → (X ⟶ X)` with
the covariant composition laws (`SchemeAction`), matching the convention of
`AlgebraicGeometry.specSMul`. This file provides:

* `SchemeAction` — the two-law action structure, with `IsIso (σ.hom g)`;
* `SchemeAction.spec` — the tautological action on `Spec B` by `specSMul`;
* `SchemeAction.IsStableOpen` — `G`-stable opens (`(σ.hom g) ⁻¹ᵁ U = U`);
* `SchemeAction.gammaMulSemiringAction` — the induced ring action on the sections
  `Γ(X, U)` over a stable open, via `Scheme.Hom.appLE` (T-Q5a's Γ-bridge: over a
  stable *affine* open this reconnects to the affine quotient theory of
  `SpecGroupAction.lean`/`AffineQuotient.lean`).

This is the vocabulary layer of the quotient of a scheme by a finite group
([Loeffler, *Modular curves*, Prop 3.6.1]; the gluing itself is tickets T-Q5b–d).
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

variable (G : Type*) [Group G]

/-- An action of a group `G` on a scheme `X`, as a family of endomorphisms with the
covariant composition laws (each `hom g` is automatically an isomorphism,
`SchemeAction.isIso_hom`). The composition convention matches `specSMul`:
`hom (g * h) = hom g ≫ hom h`. -/
structure SchemeAction (X : Scheme.{u}) where
  /-- The endomorphism attached to `g`. -/
  hom : G → (X ⟶ X)
  hom_one : hom 1 = 𝟙 X
  hom_mul : ∀ g h : G, hom (g * h) = hom g ≫ hom h

namespace SchemeAction

variable {G}
variable {X : Scheme.{u}} (σ : SchemeAction G X)

instance isIso_hom (g : G) : IsIso (σ.hom g) :=
  ⟨σ.hom g⁻¹, by rw [← σ.hom_mul, mul_inv_cancel, σ.hom_one],
    by rw [← σ.hom_mul, inv_mul_cancel, σ.hom_one]⟩

variable (G) in
/-- The tautological action on `Spec B` induced by a ring action (`specSMul`). -/
noncomputable def spec (B : Type u) [CommRing B] [MulSemiringAction G B] :
    SchemeAction G (Spec (CommRingCat.of B)) where
  hom g := specSMul g
  hom_one := specSMul_one
  hom_mul := specSMul_mul

@[simp]
theorem spec_hom (B : Type u) [CommRing B] [MulSemiringAction G B] (g : G) :
    (spec G B).hom g = specSMul g := rfl

/-- A `G`-stable open of `X`: each `σ g` restricts to it. -/
def IsStableOpen (U : X.Opens) : Prop :=
  ∀ g : G, (σ.hom g) ⁻¹ᵁ U = U

theorem IsStableOpen.le_preimage {σ : SchemeAction G X} {U : X.Opens}
    (hU : σ.IsStableOpen U) (g : G) : U ≤ (σ.hom g) ⁻¹ᵁ U :=
  (hU g).ge

/-- The induced action on the sections over a `G`-stable open, through
`Scheme.Hom.appLE` (no `eqToHom` transport). Over a stable *affine* open this is
the bridge back to the affine quotient theory. Not an instance (it depends on the
stability hypothesis): bring it into scope with `letI`. -/
@[implicit_reducible]
noncomputable def gammaMulSemiringAction {U : X.Opens} (hU : σ.IsStableOpen U) :
    MulSemiringAction G ↑Γ(X, U) where
  smul g s := ((σ.hom g).appLE U U (hU.le_preimage g)).hom s
  one_smul s := by
    show ((σ.hom 1).appLE U U (hU.le_preimage 1)).hom s = s
    simp only [σ.hom_one]
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    have h1 : (homOfLE (show U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U from σ.hom_one ▸
        hU.le_preimage 1)).op = 𝟙 (Opposite.op U) := rfl
    rw [h1]
    erw [X.presheaf.map_id]
    rfl
  mul_smul g h s := by
    show ((σ.hom (g * h)).appLE U U (hU.le_preimage (g * h))).hom s =
      ((σ.hom g).appLE U U (hU.le_preimage g)).hom
        (((σ.hom h).appLE U U (hU.le_preimage h)).hom s)
    simp only [σ.hom_mul]
    rw [← Scheme.Hom.appLE_comp_appLE (σ.hom g) (σ.hom h) U U U
      (hU.le_preimage h) (hU.le_preimage g)]
    rfl
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

@[simp]
theorem gammaMulSemiringAction_smul_def {U : X.Opens} (hU : σ.IsStableOpen U)
    (g : G) (s : ↑Γ(X, U)) :
    (gammaMulSemiringAction σ hU).smul g s =
      ((σ.hom g).appLE U U (hU.le_preimage g)).hom s := rfl

end SchemeAction

end AlgebraicGeometry
