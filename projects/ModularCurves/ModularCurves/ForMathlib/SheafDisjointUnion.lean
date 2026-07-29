/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Register-box support (T-D3/T-D1).
-/
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sections of a sheaf over a disjoint union of opens

For a sheaf `F` on a topological space (valued in a concrete category with limits whose
forgetful functor preserves limits and reflects isomorphisms) and a *pairwise disjoint*
family of opens `U : ι → Opens X`, restriction assembles into a bijection
`F(V) ≃ Π i, F(U i)` for any open `V` with `U i ≤ V ≤ ⨆ i, U i`.

This is the sheaf condition in its simplest form: on a disjoint family every family of
local sections is compatible (the pairwise intersections are empty, and sections over the
empty open form a subsingleton), so gluing is a bijection onto the full product.

Used for the finiteness of sums of relative effective Cartier divisors (KM 1.2.3): the
subscheme attached to a product of section ideals decomposes, over a suitable affine
base, into finitely many disjoint affine pieces, and its ring of functions is computed
as the product of the rings of the pieces.
-/

universe x

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable [Limits.HasLimitsOfSize.{x, x} C]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [Limits.PreservesLimitsOfSize.{x, x} (CategoryTheory.forget C)]
variable {X : TopCat.{x}} (F : Sheaf C X)

/-- Sections of a sheaf over the empty open form a subsingleton. -/
theorem subsingleton_toType_obj_bot : Subsingleton (ToType (F.1.obj (op (⊥ : Opens X)))) := by
  obtain ⟨s, -, hs⟩ := F.existsUnique_gluing' (fun i : PEmpty.{x + 1} ↦ i.elim) ⊥
    (fun i ↦ i.elim) bot_le (fun i ↦ i.elim) (fun i ↦ i.elim)
  exact ⟨fun a b ↦ (hs a fun i ↦ i.elim).trans (hs b fun i ↦ i.elim).symm⟩

open scoped Function in
/-- For a pairwise disjoint family of opens `U : ι → Opens X` and an open `V` with
`U i ≤ V ≤ ⨆ i, U i`, restriction of sections is a bijection `F(V) ≃ Π i, F(U i)`. -/
theorem bijective_restrict_pi_of_pairwise_disjoint {ι : Type*} (U : ι → Opens X)
    (V : Opens X) (hle : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hdisj : Pairwise (Disjoint on U)) :
    Function.Bijective fun (s : ToType (F.1.obj (op V))) (i : ι) ↦
      F.1.map (homOfLE (hle i)).op s := by
  have hcompat : ∀ sf : ∀ i, ToType (F.1.obj (op (U i))), Presheaf.IsCompatible F.1 U sf := by
    intro sf i j
    rcases eq_or_ne i j with rfl | hij
    · rw [Subsingleton.elim (Opens.infLELeft (U i) (U i)) (Opens.infLERight (U i) (U i))]
    · have hbot : U i ⊓ U j = ⊥ := disjoint_iff.mp (hdisj hij)
      have : Subsingleton (ToType (F.1.obj (op (U i ⊓ U j)))) := by
        rw [hbot]; exact F.subsingleton_toType_obj_bot
      exact Subsingleton.elim _ _
  constructor
  · intro a b hab
    obtain ⟨s, -, hs⟩ := F.existsUnique_gluing' U V (fun i ↦ homOfLE (hle i)) hcover
      (fun i ↦ F.1.map (homOfLE (hle i)).op a) (hcompat _)
    exact (hs a fun i ↦ rfl).trans (hs b fun i ↦ (congrFun hab i).symm).symm
  · intro t
    obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U V (fun i ↦ homOfLE (hle i)) hcover t
      (hcompat t)
    exact ⟨s, funext hs⟩

/-- If two opens cover the space and sections on the second open and the overlap are
subsingletons, then restriction to the first open is bijective. -/
theorem bijective_restrict_of_sup_eq_top_of_subsingleton
    {U V : Opens X} (hcover : U ⊔ V = ⊤)
    [Nonempty (ToType (F.1.obj (op V)))]
    [Subsingleton (ToType (F.1.obj (op V)))]
    [Subsingleton (ToType (F.1.obj (op (U ⊓ V))))] :
    Function.Bijective fun s : ToType (F.1.obj (op (⊤ : Opens X))) ↦
      F.1.map (homOfLE le_top : U ⟶ ⊤).op s := by
  constructor
  · intro a b hab
    apply F.eq_of_locally_eq₂ (homOfLE (le_top : U ≤ ⊤))
      (homOfLE (le_top : V ≤ ⊤)) (by rw [hcover]) a b hab
    exact Subsingleton.elim _ _
  · intro a
    let W : Fin 2 → Opens X := ![U, V]
    let s : ∀ i, ToType (F.1.obj (op (W i)))
      | 0 => a
      | 1 => by
          simpa only [W, Matrix.cons_val_one, Matrix.cons_val_zero] using
            (Classical.choice (inferInstance : Nonempty (ToType (F.1.obj (op V)))))
    have hcompatible : Presheaf.IsCompatible F.1 W s := by
      simp only [Presheaf.IsCompatible, Fin.forall_fin_two, W,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      refine ⟨⟨rfl, ?_⟩, ?_, rfl⟩
      · exact Subsingleton.elim _ _
      · haveI : Subsingleton (ToType (F.1.obj (op (V ⊓ U)))) := by
          rw [inf_comm]
          infer_instance
        exact Subsingleton.elim _ _
    have hcover' : (⊤ : Opens X) ≤ iSup W := by
      rw [← hcover]
      apply sup_le
      · simpa only [W, Matrix.cons_val_zero] using le_iSup W 0
      · simpa only [W, Matrix.cons_val_one, Matrix.cons_val_zero] using le_iSup W 1
    obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' W ⊤ (fun _ ↦ homOfLE le_top)
      hcover' s hcompatible
    refine ⟨t, ?_⟩
    convert ht 0 using 1 <;>
      simp only [W, s, Matrix.cons_val_zero] <;> rfl

end TopCat.Sheaf
