/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Two-element covers by basic opens (W1 i11)

The chord identity is proved on two chart families — `D(conj)`, where the conjugate is
invertible, and `D(g₁g₂g₃)`, where all three vertical generators are (so the chord is
itself a unit). Non-degeneracy says the two loci have empty intersection, i.e. the two
functions generate the unit ideal, and then the two basic opens cover the curve.

This file provides that cover in the shape the trivialization criteria consume: an
`ι`-indexed family with `iSup = ⊤`, together with the unit restrictions on each member.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace ModularCurves

variable {X : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[i11] Two functions generating the unit ideal cover the scheme.** -/
theorem sup_basicOpen_eq_top_of_span_pair (f g : Γ(X, (⊤ : X.Opens)))
    (h : Ideal.span ({f, g} : Set Γ(X, (⊤ : X.Opens))) = ⊤) :
    X.basicOpen f ⊔ X.basicOpen g = (⊤ : X.Opens) := by
  have hcov := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top
    (X := X) (⊤ : X.Opens) {f, g} h
  refine le_antisymm le_top ?_
  refine le_trans (le_of_eq hcov.symm) ?_
  · refine iSup₂_le ?_
    rintro i (rfl | rfl)
    · exact le_sup_left
    · exact le_sup_right

/-- **[i11] The two-element family.** -/
noncomputable def pairCover (f g : Γ(X, (⊤ : X.Opens))) :
    ULift.{u} (Fin 2) → X.Opens :=
  fun i => if i.down = 0 then X.basicOpen f else X.basicOpen g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[i11] The two-element family covers the scheme.** This is the `iSup W = ⊤`
hypothesis of the trivialization criteria, supplied by non-degeneracy. -/
theorem iSup_pairCover_eq_top (f g : Γ(X, (⊤ : X.Opens)))
    (h : Ideal.span ({f, g} : Set Γ(X, (⊤ : X.Opens))) = ⊤) :
    iSup (pairCover f g) = (⊤ : X.Opens) := by
  rw [← sup_basicOpen_eq_top_of_span_pair f g h]
  apply le_antisymm
  · refine iSup_le ?_
    intro i
    by_cases hi : i.down = 0
    · simp only [pairCover, hi, if_pos]
      exact le_sup_left
    · simp only [pairCover, hi, if_neg, if_false]
      exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_trans (le_of_eq (by simp [pairCover])) (le_iSup (pairCover f g) ⟨0⟩)
    · exact le_trans (le_of_eq (by simp [pairCover])) (le_iSup (pairCover f g) ⟨1⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[i11] On its own basic open, a function is a unit.** Mathlib's ringed-space
statement, in the `Scheme` spelling the chart calculus uses. -/
theorem isUnit_res_basicOpen (f : Γ(X, (⊤ : X.Opens))) :
    IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
  X.toRingedSpace.isUnit_res_basicOpen f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[i11/i13] No common zero means the unit ideal.** Non-degeneracy is a statement
about points — the conjugate and the generator product never vanish together, because
that would put a reflected point on top of one of `P, Q, R`. This converts it into the
`Ideal.span {f, g} = ⊤` hypothesis the cover lemma consumes. -/
theorem span_pair_eq_top_of_no_common_maximal {A : Type u} [CommRing A] (f g : A)
    (h : ∀ m : Ideal A, m.IsMaximal → ¬(f ∈ m ∧ g ∈ m)) :
    Ideal.span ({f, g} : Set A) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  exact h m hm ⟨hle (Ideal.subset_span (by simp)),
    hle (Ideal.subset_span (by simp))⟩

end ModularCurves
