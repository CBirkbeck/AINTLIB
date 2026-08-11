/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Stalk

/-!
ForMathlib (OURS, not vendored): upstream candidate.

# The function field pullback of a dominant morphism

For a dominant morphism `f : X ⟶ Y` of irreducible schemes, the generic point of `X` maps to the
generic point of `Y` (`genericPoint_eq_of_isDominant`, the dense-range generalisation of mathlib's
`genericPoint_eq_of_isOpenImmersion`), so `f`'s stalk map at the generic point is the induced
pullback on function fields `Scheme.Hom.functionFieldMap : Y.functionField ⟶ X.functionField`.

This is the scheme-morphism → function-field functoriality that mathlib currently lacks (it only
packages `germToFunctionField`), and the substrate for the finrank ↔ function-field-degree bridge
(`[N]`'s scheme fibre rank = its function-field extension degree).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- **(dense-range generic point)** A dominant morphism of irreducible schemes carries the generic
point to the generic point. Generalises `genericPoint_eq_of_isOpenImmersion` from open immersions to
arbitrary dominant morphisms — the image of the generic point is a generic point of `closure (range f)
= univ`, hence *the* generic point of the irreducible target. -/
theorem genericPoint_eq_of_isDominant (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  have h := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_eq] at h

/-- **(function field pullback of a dominant morphism)** The map on function fields induced by a
dominant morphism `f : X ⟶ Y` of irreducible schemes: the stalk map of `f` at the generic point of
`X` (whose image is the generic point of `Y` by `genericPoint_eq_of_isDominant`). For an open
immersion this is an isomorphism; in general it is the field extension `K(Y) ↪ K(X)` pulled back
along `f`. -/
noncomputable def Scheme.Hom.functionFieldMap (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    Y.functionField ⟶ X.functionField :=
  eqToHom (show Y.functionField = Y.presheaf.stalk (f.base (genericPoint X)) from
      congrArg (Y.presheaf.stalk) (genericPoint_eq_of_isDominant f).symm) ≫
    f.stalkMap (genericPoint X)

/-- The function field pullback of a dominant morphism of **integral** schemes is injective — it is a
homomorphism of fields `K(Y) → K(X)`, hence the field extension `K(Y) ↪ K(X)`. -/
theorem functionFieldMap_injective (f : X ⟶ Y) [IsDominant f] [IsIntegral X] [IsIntegral Y] :
    Function.Injective f.functionFieldMap.hom :=
  f.functionFieldMap.hom.injective

/-- `X`'s function field as an algebra over `Y`'s, via the dominant-morphism pullback
`functionFieldMap` — the field extension `K(Y) → K(X)` along `f`, whose degree is the
generic-fibre degree of `f`. -/
noncomputable abbrev functionFieldAlgebra (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    Algebra Y.functionField X.functionField :=
  f.functionFieldMap.hom.toAlgebra

/-- The generic point of `X` lies in the preimage of any nonempty open of `Y` under a dominant `f`
(its image is the generic point of `Y`, which lies in every nonempty open). -/
theorem genericPoint_mem_preimage (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] (U : Y.Opens) [hU : Nonempty U] :
    genericPoint X ∈ f ⁻¹ᵁ U := by
  show f.base (genericPoint X) ∈ U
  rw [genericPoint_eq_of_isDominant f]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- **(germ transport along a point equality)** Applying the stalk isomorphism `eqToHom` induced by
an equality of points `a = b` to the germ of a section at `a` yields its germ at `b`. This is the
elementary transport lemma that lets one move a germ between two *equal* points; it is what turns the
abstract `eqToHom` in `functionFieldMap` into a concrete germ at the generic point. -/
theorem germ_eqToHom_stalk_apply (Z : Scheme.{u}) (U : Z.Opens) {a b : Z} (hab : a = b)
    (ha : a ∈ U) (hb : b ∈ U) (s : Γ(Z, U)) :
    (eqToHom (congrArg (Z.presheaf.stalk) hab)) (Z.presheaf.germ U a ha s)
      = Z.presheaf.germ U b hb s := by
  subst hab
  simp

/-- **(function field pullback = section pullback on germs)** `functionFieldMap f` sends the class in
`K(Y)` of a section `s ∈ Γ(Y, U)` to the class in `K(X)` of its pullback `f.app U s ∈ Γ(X, f⁻¹U)`.
This is the concrete action of the abstract stalk-map `functionFieldMap`: it computes `f`'s
function-field pullback on any regular function, the substrate for identifying it with an explicit
coordinate/rational-function formula. -/
theorem functionFieldMap_germToFunctionField (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] (U : Y.Opens) [Nonempty U] (s : Γ(Y, U)) :
    f.functionFieldMap (Y.germToFunctionField U s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (genericPoint_mem_preimage f U) (f.app U s) := by
  have hx : f.base (genericPoint X) ∈ U := genericPoint_mem_preimage f U
  rw [Scheme.Hom.functionFieldMap, CommRingCat.comp_apply,
    germ_eqToHom_stalk_apply Y U (genericPoint_eq_of_isDominant f).symm _ hx s]
  exact Scheme.Hom.germ_stalkMap_apply f U (genericPoint X) hx s

/-- **(function field pullback = fraction-field extension of the section map)** The commuting square
identifying `functionFieldMap f` as the fraction-field extension of the section pullback `f.app U`:
`germToFunctionField U ≫ functionFieldMap f = f.app U ≫ germToFunctionField (f⁻¹U)`. Morphism-level
form of `functionFieldMap_germToFunctionField`. Since `germToFunctionField` is the localisation
`Γ(Y,U) → K(Y)` (`IsFractionRing`, for `U` affine), this says `functionFieldMap f` is *the* extension
of `f.app U` to fraction fields — the compatibility that turns `finrank Γ(Y,U) Γ(X,f⁻¹U)` into the
function-field degree `finrank K(Y) K(X)` (the scalar-tower input for `finrank_of_isFractionRing`). -/
theorem functionFieldMap_comp_germToFunctionField (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ f.functionFieldMap = f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  ext s
  show f.functionFieldMap (Y.germToFunctionField U s) = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s)
  rw [functionFieldMap_germToFunctionField f U s]

/-- **(functoriality)** The function-field pullback of a composite of dominant morphisms of
irreducible schemes is the composite of the pullbacks. The eqToHom bookkeeping rides on
`genericPoint_eq_of_isDominant`. -/
theorem functionFieldMap_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsDominant f] [IsDominant g] [IrreducibleSpace X] [IrreducibleSpace Y]
    [IrreducibleSpace Z] [IsDominant (f ≫ g)] :
    (f ≫ g).functionFieldMap = g.functionFieldMap ≫ f.functionFieldMap := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  haveI hU : Nonempty U := ⟨⟨genericPoint Z, hxU⟩⟩
  haveI : Nonempty (g ⁻¹ᵁ U) := ⟨⟨genericPoint Y, genericPoint_mem_preimage g U⟩⟩
  ext s
  show (f ≫ g).functionFieldMap (Z.germToFunctionField U s) =
    f.functionFieldMap (g.functionFieldMap (Z.germToFunctionField U s))
  have hsec : (f ≫ g).app U s = f.app (g ⁻¹ᵁ U) (g.app U s) := by
    rw [Scheme.Hom.comp_app]
    rfl
  rw [functionFieldMap_germToFunctionField (f ≫ g) U s,
    functionFieldMap_germToFunctionField g U s, hsec]
  exact (functionFieldMap_germToFunctionField f (g ⁻¹ᵁ U) (g.app U s)).symm

/-- The function-field pullback of the identity is the identity. -/
theorem functionFieldMap_id [IrreducibleSpace X] :
    (𝟙 X : X ⟶ X).functionFieldMap = 𝟙 (CommRingCat.of X.functionField) := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  haveI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  ext s
  show (𝟙 X : X ⟶ X).functionFieldMap (X.germToFunctionField U s) =
    X.germToFunctionField U s
  rw [functionFieldMap_germToFunctionField (𝟙 X) U s]
  rfl

/-- `functionFieldMap` is a congruence in the morphism (the `IsDominant` instances ride along by
proof irrelevance). -/
theorem functionFieldMap_congr {f g : X ⟶ Y} [IsDominant f] [IsDominant g]
    [IrreducibleSpace X] [IrreducibleSpace Y] (h : f = g) :
    f.functionFieldMap = g.functionFieldMap := by
  subst h; rfl

/-- **(invariance under a deck-style automorphism)** If `τ ≫ f = f` (e.g. `f = [N]` and `τ` a
translation by an `N`-torsion section), the function-field pullback of `τ` fixes the image of
`f.functionFieldMap` pointwise. One-line consequence of `functionFieldMap_comp`. -/
theorem functionFieldMap_apply_functionFieldMap_of_comp_eq
    (f : X ⟶ Y) (τ : X ⟶ X) [IsDominant f] [IsDominant τ]
    [IrreducibleSpace X] [IrreducibleSpace Y] (h : τ ≫ f = f) (z : Y.functionField) :
    τ.functionFieldMap.hom (f.functionFieldMap.hom z) = f.functionFieldMap.hom z := by
  haveI : IsDominant (τ ≫ f) := by rw [h]; infer_instance
  refine Eq.trans (congrArg (fun m => (CommRingCat.Hom.hom m) z)
    (functionFieldMap_comp τ f)).symm ?_
  exact congrArg (fun m => (CommRingCat.Hom.hom m) z) (functionFieldMap_congr h)

end AlgebraicGeometry
