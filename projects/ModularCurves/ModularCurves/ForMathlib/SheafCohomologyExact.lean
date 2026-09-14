import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Exact sequences in sheaf cohomology

The connecting morphism `H.δ`, the six-term window `H.longSequence` of the long exact sequence
and its elementwise exactness lemmas are in mathlib
(`Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences`, upstreamed from #36218).
This file adds further consequences for a short exact sequence of additive sheaves.
-/

open CategoryTheory Abelian AddCommGrpCat

universe w' w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

namespace H

/-- The connecting map followed by the next cohomology map is zero. -/
lemma longSequence_comp_zero₁ (x : H S.X₃ n₀) :
    map S.f n₁ (δ hS n₀ n₁ h x) = 0 := by
  change (x.comp hS.extClass h).comp (Ext.mk₀ S.f) (add_zero n₁) = 0
  simp only [Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_comp, Ext.comp_zero]

/-- The previous cohomology map followed by the connecting map is zero. -/
lemma longSequence_comp_zero₃ (x : H S.X₂ n₀) :
    δ hS n₀ n₁ h (map S.g n₀ x) = 0 := by
  change (x.comp (Ext.mk₀ S.g) (add_zero n₀)).comp hS.extClass h = 0
  simp only [Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- Consecutive cohomology maps induced by a short complex compose to zero. -/
lemma longSequence_comp_zero₂ (n : ℕ) (x : H S.X₁ n) :
    map S.g n (map S.f n x) = 0 := by
  simp only [map_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    ShortComplex.zero, Ext.mk₀_zero, Ext.comp_zero]

include hS in
/-- In a short exact sequence, vanishing of the same cohomology degree at the
two ends implies vanishing at the middle. -/
lemma subsingleton_H_X₂_of_shortExact (n : ℕ)
    (hleft : Subsingleton (H S.X₁ n))
    (hright : Subsingleton (H S.X₃ n)) :
    Subsingleton (H S.X₂ n) := by
  letI : Subsingleton (H S.X₁ n) := hleft
  letI : Subsingleton (H S.X₃ n) := hright
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₁, hx₁⟩ := longSequence_exact₂ hS x (Subsingleton.elim _ _)
  rw [Subsingleton.elim x₁ 0, map_zero] at hx₁
  exact hx₁.symm

include hS in
/-- In a short exact sequence, vanishing of `H^q` of the right term and
`H^(q+1)` of the middle term implies vanishing of `H^(q+1)` of the left
term. -/
lemma subsingleton_H_X₁_succ_of_shortExact (q : ℕ)
    (hright : Subsingleton (H S.X₃ q))
    (hmiddle : Subsingleton (H S.X₂ (q + 1))) :
    Subsingleton (H S.X₁ (q + 1)) := by
  letI : Subsingleton (H S.X₃ q) := hright
  letI : Subsingleton (H S.X₂ (q + 1)) := hmiddle
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ := longSequence_exact₁
    hS x (Subsingleton.elim _ _) (n₀ := q) rfl
  rw [Subsingleton.elim x₃ 0, map_zero] at hx₃
  exact hx₃.symm

include hS in
/-- In a short exact sequence, surjectivity on `H^q` from the middle to the
right and vanishing of `H^(q+1)` of the middle imply vanishing of
`H^(q+1)` of the left term. -/
lemma subsingleton_H_X₁_succ_of_shortExact_of_surjective (q : ℕ)
    (hsurj : Function.Surjective (map S.g q))
    (hmiddle : Subsingleton (H S.X₂ (q + 1))) :
    Subsingleton (H S.X₁ (q + 1)) := by
  letI : Subsingleton (H S.X₂ (q + 1)) := hmiddle
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ := longSequence_exact₁
    hS x (Subsingleton.elim _ _) (n₀ := q) rfl
  obtain ⟨x₂, hx₂⟩ := hsurj x₃
  rw [← hx₃, ← hx₂, longSequence_comp_zero₃]

variable {T : C} (hT : Limits.IsTerminal T)

open Opposite

include hS hT in
/-- Degree-zero exactness at the middle sheaf, expressed using sections over a
terminal object. -/
lemma longSequence_equiv₀_exact₂ (x₂ : S.X₂.obj.obj (op T))
    (hx₂ : S.g.hom.app (op T) x₂ = 0) :
    ∃ x₁ : S.X₁.obj.obj (op T), S.f.hom.app (op T) x₁ = x₂ := by
  let y₂ := (equiv₀ S.X₂ hT).symm x₂
  have hy₂ : map S.g 0 y₂ = 0 := by
    rw [equiv₀_symm_naturality, hx₂]
    exact map_zero _
  obtain ⟨y₁, hy₁⟩ := longSequence_exact₂ hS y₂ hy₂
  refine ⟨equiv₀ S.X₁ hT y₁, ?_⟩
  rw [equiv₀_naturality, hy₁]
  simp [y₂]

include hS hT in
/-- If `H¹` of the first sheaf vanishes, the map on terminal-object sections is
surjective. -/
lemma longSequence_surjective_of_subsingleton_H [Subsingleton (S.X₁.H 1)] :
    Function.Surjective (S.g.hom.app (op T)) :=
  fun x₃ ↦ longSequence_equiv₀_exact₃ hS hT x₃ (Subsingleton.elim _ _)

end H

end CategoryTheory.Sheaf
