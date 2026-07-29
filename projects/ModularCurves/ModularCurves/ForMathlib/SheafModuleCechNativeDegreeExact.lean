/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverBicomplex

/-!
# Exactness in a fixed degree of a native module-valued Cech complex

A fixed degree of a native Cech complex is a product over tuple
intersections. Products of pointwise exact pairs are exact in modules, and
products of pointwise monomorphisms are monic.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable {κ : Type u}

/-- The concrete linear equivalence from a fixed native Cech degree to the
product over its tuple intersections. -/
noncomputable def moduleNativeCechDegreeLinearEquiv
    (G : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (V : κ → Opens X) (p : ℕ) :
    ((cechComplexFunctor V).obj G).X p ≃ₗ[R]
      ((i : Fin (p + 1) → κ) →
        G.obj (op (∏ᶜ fun k : Fin (p + 1) => V (i k)))) :=
  (ModuleCat.piIsoPi _).toLinearEquiv

/-- The concrete fixed-degree comparison sends a mapped Cech element to the
pointwise images of its tuple components. -/
theorem moduleNativeCechDegreeLinearEquiv_map
    {G H : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (f : G ⟶ H) (V : κ → Opens X) (p : ℕ)
    (x : ((cechComplexFunctor V).obj G).X p)
    (i : Fin (p + 1) → κ) :
    moduleNativeCechDegreeLinearEquiv H V p
        (((cechComplexFunctor V).map f).f p x) i =
      f.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k)))
        (moduleNativeCechDegreeLinearEquiv G V p x i) := by
  simp only [moduleNativeCechDegreeLinearEquiv]
  exact ConcreteCategory.congr_hom
    (Pi.map_π (fun i => f.app
      (op (∏ᶜ fun k : Fin (p + 1) => V (i k)))) i) x

/-- The fixed degree of the Cech images of a composable zero pair. -/
noncomputable def moduleNativeCechMapShortComplex
    {G H K : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (f : G ⟶ H) (g : H ⟶ K) (h : f ≫ g = 0)
    (V : κ → Opens X) (p : ℕ) :
    ShortComplex (ModuleCat.{u} R) := by
  refine ShortComplex.mk
    (((cechComplexFunctor V).map f).f p)
    (((cechComplexFunctor V).map g).f p) ?_
  change (((cechComplexFunctor V).map f) ≫
    ((cechComplexFunctor V).map g)).f p = 0
  rw [← Functor.map_comp, h, Functor.map_zero]
  rfl

/-- Pointwise exactness on every tuple intersection implies exactness after
taking the product defining a fixed native Cech degree. -/
theorem moduleNativeCechMapShortComplex_exact
    {G H K : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (f : G ⟶ H) (g : H ⟶ K) (h : f ≫ g = 0)
    (V : κ → Opens X) (p : ℕ)
    (hexact : ∀ i : Fin (p + 1) → κ,
      (ShortComplex.mk
        (f.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k))))
        (g.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k))))
        (congrArg (fun t => t.app
          (op (∏ᶜ fun k : Fin (p + 1) => V (i k)))) h)).Exact) :
    (moduleNativeCechMapShortComplex f g h V p).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  change ((cechComplexFunctor V).map g).f p y = 0 at hy
  let ey := moduleNativeCechDegreeLinearEquiv H V p y
  have hcycle : ∀ i : Fin (p + 1) → κ,
      g.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k))) (ey i) = 0 := by
    intro i
    calc
      _ = moduleNativeCechDegreeLinearEquiv K V p
          (((cechComplexFunctor V).map g).f p y) i :=
        (moduleNativeCechDegreeLinearEquiv_map g V p y i).symm
      _ = moduleNativeCechDegreeLinearEquiv K V p 0 i :=
        congrArg (fun z =>
          moduleNativeCechDegreeLinearEquiv K V p z i) hy
      _ = 0 := by simp
  have hpreimage : ∀ i : Fin (p + 1) → κ,
      ∃ x, f.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k))) x = ey i := by
    intro i
    exact ((ShortComplex.moduleCat_exact_iff _).mp (hexact i))
      (ey i) (hcycle i)
  let xcoord := fun i : Fin (p + 1) → κ => (hpreimage i).choose
  let x := (moduleNativeCechDegreeLinearEquiv G V p).symm xcoord
  refine ⟨x, ?_⟩
  change ((cechComplexFunctor V).map f).f p x = y
  apply (moduleNativeCechDegreeLinearEquiv H V p).injective
  funext i
  rw [moduleNativeCechDegreeLinearEquiv_map]
  change f.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k)))
      ((moduleNativeCechDegreeLinearEquiv G V p)
        ((moduleNativeCechDegreeLinearEquiv G V p).symm xcoord) i) =
    ey i
  rw [(moduleNativeCechDegreeLinearEquiv G V p).apply_symm_apply]
  exact (hpreimage i).choose_spec

/-- Pointwise monicity on every tuple intersection implies monicity after
taking the product defining a fixed native Cech degree. -/
theorem moduleNativeCechMap_mono
    {G H : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (f : G ⟶ H) (V : κ → Opens X) (p : ℕ)
    (hmono : ∀ i : Fin (p + 1) → κ,
      Mono (f.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k))))) :
    Mono (((cechComplexFunctor V).map f).f p) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  apply (moduleNativeCechDegreeLinearEquiv G V p).injective
  funext i
  apply ((ModuleCat.mono_iff_injective
    (f.app (op (∏ᶜ fun k : Fin (p + 1) => V (i k))))).mp (hmono i))
  have hi := congrArg
    (fun z => moduleNativeCechDegreeLinearEquiv H V p z i) hxy
  rwa [moduleNativeCechDegreeLinearEquiv_map,
    moduleNativeCechDegreeLinearEquiv_map] at hi

end TopCat.Sheaf
