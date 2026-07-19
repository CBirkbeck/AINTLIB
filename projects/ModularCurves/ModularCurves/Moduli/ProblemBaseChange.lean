/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.EllCategory

/-!
# Base change of moduli problems ([B4]/[T-E5f] recollement infrastructure)

`EllObj.restrictScalars ρ : EllObj R' ⥤ EllObj R` (an `Ell/R'`-object viewed over `R` via
`Spec.map ρ`) and `ModuliProblem.baseChange ρ P : ModuliProblem R'` (precompose `P` with it).
The foundational plumbing for the Katz–Mazur recollement of `representable_iff` ⇐ over the
Zariski cover `Spec R = D(2) ∪ D(3)` (KM 4.7.0 SCHOLIE, over `ℤ[1/6]`).
-/

open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace ModularCurves

variable {R R' : CommRingCat.{u}} (ρ : R ⟶ R')

/-- **Restriction of scalars** along a ring map `ρ : R ⟶ R'`: an `Ell/R'`-object is an
`Ell/R`-object with structure map post-composed with `Spec.map ρ` (the same base scheme, the
same curve). -/
@[simps]
noncomputable def EllObj.restrictScalars : EllObj R' ⥤ EllObj R where
  obj X := { base := X.base, structMap := X.structMap ≫ Spec.map ρ, curve := X.curve }
  map {X Y} f :=
    { baseHom := f.baseHom
      base_w := by rw [← Category.assoc, f.base_w]
      top := f.top
      isPullback := f.isPullback
      zero_w := f.zero_w }
  map_id X := rfl
  map_comp f g := rfl

/-- **Base change of a moduli problem** along `ρ : R ⟶ R'`: the `Ell/R'`-functor obtained by
precomposing `P` with restriction of scalars. Its value on `X : Ell/R'` is `P` at the same
data viewed over `R`. -/
noncomputable def ModuliProblem.baseChange (P : ModuliProblem R) : ModuliProblem R' :=
  (EllObj.restrictScalars ρ).op ⋙ P

@[simp]
theorem ModuliProblem.baseChange_obj (P : ModuliProblem R) (X : (EllObj R')ᵒᵖ) :
    (P.baseChange ρ).obj X = P.obj (op ((EllObj.restrictScalars ρ).obj X.unop)) := rfl


/-- Restriction of scalars is faithful (it preserves `baseHom` and `top`, which determine an
`EllHom`). -/
instance : (EllObj.restrictScalars ρ).Faithful where
  map_injective {X Y} {f g} h := by
    have hb : f.baseHom = g.baseHom := congrArg (·.baseHom) h
    have ht : f.top = g.top := congrArg (·.top) h
    exact EllHom.ext hb ht

/-- **Rigidity transfers forward under base change**: if `P` is rigid, so is `P.baseChange ρ`. -/
theorem ModuliProblem.Rigid.baseChange {P : ModuliProblem R} (hP : P.Rigid) :
    (P.baseChange ρ).Rigid := by
  intro X e hb hne a hfix
  refine hP ((EllObj.restrictScalars ρ).obj X) ((EllObj.restrictScalars ρ).mapIso e) hb ?_ a hfix
  intro hrefl
  apply hne
  apply Iso.ext
  apply (EllObj.restrictScalars ρ).map_injective
  have h1 := congrArg Iso.hom hrefl
  simpa using h1

/-- **Noetherian-local rigidity transfers forward under base change**: if `P` is
`RigidNoeth`, so is `P.baseChange ρ`. `restrictScalars` leaves the base scheme unchanged
(`restrictScalars_obj_base`), so the `IsLocallyNoetherian` hypothesis carries through to
the `P`-side rigidity call. This is the `:324` recollement's transfer of the engine's
rigidity input to the `D(2)` / `D(3)` loci. -/
theorem ModuliProblem.RigidNoeth.baseChange {P : ModuliProblem R} (hP : P.RigidNoeth) :
    (P.baseChange ρ).RigidNoeth := by
  intro X hXnoeth e hb hne a hfix
  refine hP ((EllObj.restrictScalars ρ).obj X) hXnoeth
    ((EllObj.restrictScalars ρ).mapIso e) hb ?_ a hfix
  intro hrefl
  apply hne
  apply Iso.ext
  apply (EllObj.restrictScalars ρ).map_injective
  have h1 := congrArg Iso.hom hrefl
  simpa using h1


/-- **Relative representability transfers under base change**: the same representing datum works
(the `Ell/R'`-pullbacks agree, over `R`, with the `Ell/R`-pullbacks — `rfl`). -/
theorem ModuliProblem.RelativelyRepresentable.baseChange {P : ModuliProblem R}
    (hP : P.RelativelyRepresentable) : (P.baseChange ρ).RelativelyRepresentable := by
  intro X'
  obtain ⟨Z, f, eqv, hnat⟩ := hP ((EllObj.restrictScalars ρ).obj X')
  exact ⟨Z, f, eqv, hnat⟩

/-- **Affine-over-`(Ell)` transfers under base change** (same affine representing morphism). -/
theorem ModuliProblem.AffineOverEll.baseChange {P : ModuliProblem R}
    (hP : P.AffineOverEll) : (P.baseChange ρ).AffineOverEll := by
  intro X'
  obtain ⟨Z, f, haff, eqv, hnat⟩ := hP ((EllObj.restrictScalars ρ).obj X')
  exact ⟨Z, f, haff, eqv, hnat⟩

end ModularCurves
