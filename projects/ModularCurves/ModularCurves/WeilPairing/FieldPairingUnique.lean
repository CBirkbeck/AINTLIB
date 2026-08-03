/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.EtaleDescent

/-!
# The field-level Weil pairing is unique (WP-D3c, step 1)

`exists_weilPairingHom_of_field` (`WeilPairing/GlobalFibreChart.lean`) produces the field-level
pairing as an **existence** statement characterised by its values on the `k̄`-points. To use it
as the independent input of the DS4 root construction one needs it to be *canonical*: the root
`ζ` attached to two different components of the universal base must be comparable, and that
comparison is naturality under a change of the base field — which is meaningless until the
pairing is pinned down uniquely.

The pin is faithfulness of the fibre functor of the Galois category of finite étale
`k`-algebras: a morphism of finite étale `k`-algebras is determined by the induced map on
`k^sep`-points. This is the exact dual of the *fullness* statement
`exists_finiteEtaleHom_of_galoisEquivariant` (`WeilPairing/EtaleDescent.lean`) that produced
the pairing in the first place.
-/

universe u

open CategoryTheory

namespace ModularCurves

/-- **(WP-D3c step 1)** A morphism of finite étale `k`-algebras is determined by the map it
induces on `k^sep`-points: the fibre functor of a Galois category is faithful.

Dual to `exists_finiteEtaleHom_of_galoisEquivariant`, which is its fullness. -/
theorem finiteEtaleHom_unique {k : Type u} [Field k]
    (A B : CommAlgCat.FiniteEtale.{u} k) (w₁ w₂ : A ⟶ B)
    (h : ∀ x : (B : Type u) →ₐ[k] SeparableClosure k,
      x.comp w₁.hom.hom = x.comp w₂.hom.hom) :
    w₁ = w₂ := by
  have hmap : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}).map w₁.op =
      (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
        (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}).map w₂.op :=
    FintypeCat.hom_ext _ _ h
  have := (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}).map_injective hmap
  exact Opposite.op_injective this

/-- **(WP-D3c-CLOSURE)** A `k`-algebra equivalence of geometric points induces a natural
isomorphism of the corresponding fibre functors: postcomposition with the equivalence is a
bijection `(A →ₐ[k] Ω₁) ≃ (A →ₐ[k] Ω₂)`, natural in `A`.

Stated for an arbitrary equivalence, not just `SeparableClosure k ≃ₐ[k] AlgebraicClosure k`:
the field-change naturality of the Weil pairing needs the same transport. -/
@[simps!]
noncomputable def fiberIsoOfAlgEquiv {k : Type u} [Field k] {Ω₁ Ω₂ : Type u} [Field Ω₁]
    [Field Ω₂] [Algebra k Ω₁] [Algebra k Ω₂] (e : Ω₁ ≃ₐ[k] Ω₂) :
    (CommAlgCat.FiniteEtale.fiber.{u} k Ω₁ :
        (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}) ≅
      CommAlgCat.FiniteEtale.fiber.{u} k Ω₂ :=
  NatIso.ofComponents
    (fun A => FintypeCat.equivEquivIso
      (show (((A.unop : CommAlgCat.FiniteEtale.{u} k) : Type u) →ₐ[k] Ω₁) ≃
          (((A.unop : CommAlgCat.FiniteEtale.{u} k) : Type u) →ₐ[k] Ω₂) from
        { toFun := fun x => e.toAlgHom.comp x
          invFun := fun y => e.symm.toAlgHom.comp y
          left_inv := fun x => AlgHom.ext fun a => e.symm_apply_apply (x a)
          right_inv := fun y => AlgHom.ext fun a => e.apply_symm_apply (y a) }))
    (fun _ => rfl)

/-- **(WP-D3c-CLOSURE)** Faithfulness of a fibre functor transports along an equivalence of
geometric points. -/
theorem faithful_fiber_of_algEquiv {k : Type u} [Field k] {Ω₁ Ω₂ : Type u} [Field Ω₁]
    [Field Ω₂] [Algebra k Ω₁] [Algebra k Ω₂] (e : Ω₁ ≃ₐ[k] Ω₂)
    [(CommAlgCat.FiniteEtale.fiber.{u} k Ω₁ :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}).Faithful] :
    (CommAlgCat.FiniteEtale.fiber.{u} k Ω₂ :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}).Faithful :=
  Functor.Faithful.of_iso (fiberIsoOfAlgEquiv e)

/- The uniqueness statement read at `AlgebraicClosure k` — which is the geometric point
`exists_weilPairingHom_of_field`'s characterisation clause actually quantifies over — does
**not** follow by the same three lines: the `PreGaloisCategory.FiberFunctor` instance in
`ForMathlib/FiniteEtaleFiberFunctor.lean:662` is registered at `SeparableClosure k` only, so
`Faithful (CommAlgCat.FiniteEtale.fiber k (AlgebraicClosure k))` is not synthesised
(measured). Over a perfect field the two closures agree —
`IsSepClosure.of_isAlgClosure_of_perfectField` (`FieldTheory/IsSepClosed.lean:252`) plus
uniqueness of separable closures gives `SeparableClosure k ≃ₐ[k] AlgebraicClosure k` — so the
missing step is a natural isomorphism of the two fibre functors along that equivalence. See
the board's [WP-D3c-CLOSURE]. -/

end ModularCurves
