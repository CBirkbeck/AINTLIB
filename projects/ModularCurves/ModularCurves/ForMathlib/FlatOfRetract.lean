/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness is stable under retracts of schemes over a base

**[KM-W0 / F3-flat] ForMathlib brick (candidate mathlib PR).** If `X` is a retract of
`Y` over `S` (morphisms `i : X ⟶ Y`, `r : Y ⟶ X` over `S` with `i ≫ r = 𝟙 X`) and
`Y ⟶ S` is flat, then `X ⟶ S` is flat.

Route: the stalkwise criterion (`AlgebraicGeometry.Flat.of_stalkMap` /
`Flat.stalkMap`) plus `Module.Flat.of_retract` — at each `x : X` the stalk
`𝒪_{X,x}` is a module retract of `𝒪_{Y, i x}` over `𝒪_{S, s}` via the stalk maps of
`i` and `r`, whose composite is the identity by `i ≫ r = 𝟙`.

KM (print p. 27, the use site): *"the sheaf of `S`-algebras defining `G[N₁]` is an
`S`-direct factor of that defining `G`, so flat over `S`."*
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-- **Ring-level input**: if `φ : R →+* A` is flat and `B` is a ring retract of `A`
compatibly over `R` (`ψ ∘ ρ = id`, `ρ ∘ ψ ∘ φ = φ`), then `ψ ∘ φ` is flat. Pure
algebra — the scheme-level statement reduces to this at stalks. -/
theorem _root_.RingHom.Flat.of_retract {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] (φ : R →+* A) (ψ : A →+* B) (ρ : B →+* A)
    (hψρ : ψ.comp ρ = RingHom.id B) (hρφ : ρ.comp (ψ.comp φ) = φ)
    (hφ : φ.Flat) : (ψ.comp φ).Flat := by
  letI : Algebra R A := φ.toAlgebra
  letI : Algebra R B := (ψ.comp φ).toAlgebra
  haveI hFA : Module.Flat R A := hφ
  let ψₗ : A →ₗ[R] B :=
    { toFun := ψ
      map_add' := map_add ψ
      map_smul' := fun r a => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul]
        congr 1 }
  let ρₗ : B →ₗ[R] A :=
    { toFun := ρ
      map_add' := map_add ρ
      map_smul' := fun r b => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul]
        congr 1
        exact DFunLike.congr_fun hρφ r }
  have hcomp : ψₗ.comp ρₗ = LinearMap.id := by
    ext b
    exact DFunLike.congr_fun hψρ b
  exact Module.Flat.of_retract ρₗ ψₗ hcomp

/-- **Flatness descends along retracts over a base.** If `i : X ⟶ Y` and `r : Y ⟶ X`
are morphisms over `S` with `i ≫ r = 𝟙 X`, and `g : Y ⟶ S` is flat, then
`f : X ⟶ S` is flat. -/
theorem Flat.of_retract_over {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X)
    (hi : i ≫ g = f) (hr : r ≫ f = g) [Flat g] : Flat f := by
  subst hi
  apply AlgebraicGeometry.Flat.of_stalkMap
  intro x
  rw [Scheme.Hom.stalkMap_comp]
  haveI hA : ((g.stalkMap (i x)).hom).Flat := AlgebraicGeometry.Flat.stalkMap g (i x)
  -- the point identity and the packaged retract equation
  have hpt : (i ≫ r) x = x := by rw [hir]; rfl
  have hretr : r.stalkMap (i x) ≫ i.stalkMap x
      = (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom := by
    rw [← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom (i ≫ r) (𝟙 X) hir x, Scheme.Hom.stalkMap_id]
    exact Category.comp_id _
  have hpt' : r (i x) = x := hpt
  -- apply the ring-level retract lemma
  refine RingHom.Flat.of_retract (g.stalkMap (i x)).hom (i.stalkMap x).hom
    (((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).inv ≫ r.stalkMap (i x))).hom
    ?_ ?_ hA
  · -- ψ ∘ ρ = id
    have h : ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).inv ≫ r.stalkMap (i x))
        ≫ i.stalkMap x = 𝟙 _ := by
      calc ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).inv ≫ r.stalkMap (i x))
            ≫ i.stalkMap x
          = (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).inv
            ≫ (r.stalkMap (i x) ≫ i.stalkMap x) := Category.assoc _ _ _
        _ = (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).inv
            ≫ (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom :=
          congrArg (fun m => (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).inv ≫ m) hretr
        _ = 𝟙 _ := Iso.inv_hom_id _
    exact congrArg CommRingCat.Hom.hom h
  · -- ρ ∘ ψ ∘ φ = φ : the hr-choreography
    have h1 := Scheme.Hom.stalkMap_congr_hom (r ≫ (i ≫ g)) g hr (i x)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h1
    have h3 := Scheme.Hom.stalkMap_congr_point (f := i) (r (i x)) x hpt'
    have hiy : i (r (i x)) = i x := congrArg (fun y => i y) hpt'
    have h4 := Scheme.Hom.stalkMap_congr_point (f := g) (i (r (i x))) (i x) hiy
    -- solve for the transported stalk maps (casts inherited, not re-spelled)
    have h3' : i.stalkMap (r (i x))
        = ((Y.presheaf.stalkCongr _).hom ≫ i.stalkMap x)
          ≫ (X.presheaf.stalkCongr (.of_eq hpt')).inv :=
      (CategoryTheory.Iso.eq_comp_inv _).mpr h3
    have h4' : g.stalkMap (i (r (i x)))
        = ((S.presheaf.stalkCongr _).hom ≫ g.stalkMap (i x))
          ≫ (Y.presheaf.stalkCongr (.of_eq hiy)).inv :=
      (CategoryTheory.Iso.eq_comp_inv _).mpr h4
    rw [h3', h4'] at h1
    -- bridge the two proof-spellings of the Y-cast, then collapse
    have hbridge : ∀ (h₁ h₂ : Inseparable (i (r (i x))) (i x)) {Z : CommRingCat}
        (m : Y.presheaf.stalk (i x) ⟶ Z),
        (Y.presheaf.stalkCongr h₂).inv ≫ (Y.presheaf.stalkCongr h₁).hom ≫ m = m := by
      intro h₁ h₂ Z m
      rw [Subsingleton.elim h₁ h₂, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    try simp only [Category.assoc] at h1
    rw [hbridge] at h1
    try simp only [Category.assoc] at h1
    -- cancel the S-cast generically over its proof spellings
    have hcancelS : ∀ (h₁ h₂ : Inseparable (g (i (r (i x)))) (g (i x)))
        {Z : CommRingCat} (m m' : S.presheaf.stalk (g (i x)) ⟶ Z),
        (S.presheaf.stalkCongr h₁).hom ≫ m = (S.presheaf.stalkCongr h₂).hom ≫ m' →
          m = m' := by
      intro h₁ h₂ Z m m' hmm'
      rw [Subsingleton.elim h₁ h₂] at hmm'
      exact (cancel_epi _).mp hmm'
    have h1' : (S.presheaf.stalkCongr (.of_eq (congrArg (fun y => g y) hiy))).hom
          ≫ (g.stalkMap (i x) ≫ i.stalkMap x
            ≫ (X.presheaf.stalkCongr (.of_eq hpt')).inv ≫ r.stalkMap (i x))
        = (S.presheaf.stalkCongr (.of_eq (congrArg (fun y => g y) hiy))).hom
          ≫ g.stalkMap (i x) := by
      exact h1
    have h5 := hcancelS _ _ _ _ h1'
    exact congrArg CommRingCat.Hom.hom h5

end ModularCurves
