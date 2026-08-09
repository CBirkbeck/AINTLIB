/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DualPullback.LocalTrivialization
import ModularCurves.Picard.DualPullback.Map
import ModularCurves.WeilPairing.UnitSheaf

/-!
# `f_{i,j} ∘ [N] = h_i / h_j` — the existence half (ticket AP-D5)

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 88: after trivializing an invertible sheaf
`ℒ` on `E` over the preimages `π⁻¹(U_i)` of a base cover, the transition units `f_{i,j}` form a
cocycle; *because `[N]^*ℒ` is trivial in `Pic`*, the pulled-back cocycle `f_{i,j} ∘ [N]` is a
**coboundary**, so units `h_i` on `π⁻¹(U_i)` with `f_{i,j} ∘ [N] = h_i / h_j` exist. The
uniqueness half is already in `WeilPairing/UnitSheaf.lean` (`eq_one_of_mem_kUnits`,
`eq_of_div_mem_kUnits`, from `AP-D2`); **this file is the existence half only**.

Everything is stated for an arbitrary morphism of schemes `f : Y ⟶ X` and an arbitrary
`𝒪_X`-module `M`, since none of the argument uses the elliptic curve: `[N]` enters only through
the hypothesis `Pic.map f L = 1`, which for `f = [N]` and `L = κ(Q)` is exactly the `⊆` half of
AP-D4 (`picMap_mulByHom_kappa_eq_one`, `Picard/SelfAdjointN.lean`, proved and axiom-clean).

## Main results

* `trivializationTransitionUnit_localPullbackTrivialization` — **`f_{i,j} ∘ [N]`, formalized**:
  the transition unit of two *pulled-back* trivializations is the pullback of their transition
  unit, `t(f^*e, f^*g) = f^# (t(e,g))`. The pullback of a trivialization is the tree's existing
  `localPullbackTrivializationT` (`Picard/DualPullback/LocalTrivialization.lean`); only the
  transition-unit computation is new.
* `restrict_localPullbackTrivialization` — pulling back commutes with restricting to a smaller
  open. Proved from `localDualPullback_restrictD` (`Picard/DualPullback/Map.lean`) through
  `localDualPullback_trivialization_homT`; this is what lets the `h_i` be defined on all of
  `f ⁻¹ᵁ (W i)` rather than only on the pairwise overlaps.
* `transitionUnit_restrictOn_eq_mul_inv` — **the coboundary**: over a module trivialized on the
  top open, the transition unit of two local trivializations on a common open is `h₁ · h₂⁻¹`,
  where `h_k = globalComparisonUnit` compares the `k`-th trivialization with the global one.
  This is KM's `f_{i,j} = h_i / h_j` for the module whose cocycle is being split.
* `exists_pullback_transitionUnit_eq_mul_inv` — **the assembled AP-D5 existence statement**:
  given a family of trivializations `e_i` of `M` over opens `W i` and a trivialization of `f^*M`
  over the top open, there are units `h_i` on `f ⁻¹ᵁ (W i)` with
  `f^# (f_{i,j}) = h_i · h_j⁻¹` on `f ⁻¹ᵁ (W i ⊓ W j)`. Literally KM's `f_{i,j} ∘ [N] = h_i/h_j`.
* `exists_transitionUnit_eq_mul_inv_of_picMap_eq_one` — the same with the global trivialization
  replaced by its Picard-theoretic source, `Pic.map f L = 1` for a class `L` represented by `M`.
  Supporting bridges: `exists_toSkeleton_eq`, `nonempty_unitObj_iso_of_picMap_eq_one`,
  `overTrivializationOfUnitObjIso`.

## Degenerate cases

Nothing here needs the index type to be nonempty, the `W i` to cover `X`, or `N ≠ 0`: the
splitting is a statement about one overlap at a time and is vacuously true on an empty cover.
All the `N`-dependence of the KM construction sits in the input `Pic.map (mulByN E t N) L = 1`.
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

variable {X Y : Scheme.{u}}

/-! ## `f_{i,j} ∘ [N]`: transition units are natural under pullback

`localPullbackTrivializationT` (`Picard/DualPullback/LocalTrivialization.lean`) pulls a
trivialization of `M` on the over-site of `U` back to a trivialization of `f^*M` on the over-site
of `f ⁻¹ᵁ U`. What is new here is that this operation transforms transition units by `f^#`, which
is what makes the tree's `trivializationTransitionUnit` the `f_{i,j} ∘ [N]` of KM p. 88. -/

theorem overEquiv_map_localPullbackTrivialization_hom (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (overEquiv (f ⁻¹ᵁ U)).functor.map (localPullbackTrivializationT f M U e).hom =
      (localPullbackModuleIso f M U).inv ≫
        (pullback (f ∣_ U)).map ((overEquiv U).functor.map e.hom) ≫
        (localPullbackUnitIso f U).hom := by
  simp only [localPullbackTrivializationT, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]

theorem overEquiv_map_localPullbackTrivialization_inv (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (overEquiv (f ⁻¹ᵁ U)).functor.map (localPullbackTrivializationT f M U e).inv =
      (localPullbackUnitIso f U).inv ≫
        (pullback (f ∣_ U)).map ((overEquiv U).functor.map e.inv) ≫
        (localPullbackModuleIso f M U).hom := by
  simp only [localPullbackTrivializationT, Functor.FullyFaithful.preimageIso_inv,
    Functor.FullyFaithful.map_preimage, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Category.assoc]

/-- The comparison map between two pulled-back trivializations is multiplication by the pullback
of their transition unit. -/
theorem localPullbackTrivialization_inv_comp_hom (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (localPullbackTrivializationT f M U e).inv ≫ (localPullbackTrivializationT f M U g).hom =
      ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf (f ⁻¹ᵁ U)
        ((f.app U).hom (trivializationTransitionUnit U e g : Γ(X, U))) := by
  apply (overEquiv (f ⁻¹ᵁ U)).functor.map_injective
  rw [Functor.map_comp, overEquiv_map_localPullbackTrivialization_hom,
    overEquiv_map_localPullbackTrivialization_inv]
  have hcomp : (pullback (f ∣_ U)).map ((overEquiv U).functor.map e.inv) ≫
      (pullback (f ∣_ U)).map ((overEquiv U).functor.map g.hom) =
      (pullback (f ∣_ U)).map ((overEquiv U).functor.map
        (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
          (trivializationTransitionUnit U e g : Γ(X, U)))) := by
    rw [overUnitScalarEnd_transitionUnit, Functor.map_comp, Functor.map_comp]
  calc ((localPullbackUnitIso f U).inv ≫
        (pullback (f ∣_ U)).map ((overEquiv U).functor.map e.inv) ≫
        (localPullbackModuleIso f M U).hom) ≫
      ((localPullbackModuleIso f M U).inv ≫
        (pullback (f ∣_ U)).map ((overEquiv U).functor.map g.hom) ≫
        (localPullbackUnitIso f U).hom)
      = (localPullbackUnitIso f U).inv ≫
          ((pullback (f ∣_ U)).map ((overEquiv U).functor.map e.inv) ≫
            (pullback (f ∣_ U)).map ((overEquiv U).functor.map g.hom)) ≫
          (localPullbackUnitIso f U).hom := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (localPullbackUnitIso f U).inv ≫
          (pullback (f ∣_ U)).map ((overEquiv U).functor.map
            (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
              (trivializationTransitionUnit U e g : Γ(X, U)))) ≫
            (localPullbackUnitIso f U).hom := by
        rw [hcomp]
    _ = (localPullbackUnitIso f U).inv ≫ (localPullbackUnitIso f U).hom ≫
          (overEquiv (f ⁻¹ᵁ U)).functor.map
            (ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf (f ⁻¹ᵁ U)
              ((f.app U).hom (trivializationTransitionUnit U e g : Γ(X, U)))) := by
        rw [localPullbackUnitIso_scalar]
    _ = (overEquiv (f ⁻¹ᵁ U)).functor.map
          (ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf (f ⁻¹ᵁ U)
            ((f.app U).hom (trivializationTransitionUnit U e g : Γ(X, U)))) := by
        rw [Iso.inv_hom_id_assoc]

/-- **(KM p. 88, the meaning of `f_{i,j} ∘ [N]`)** Transition units are natural under pullback:
the transition unit of two pulled-back trivializations is the pullback of their transition
unit. -/
theorem trivializationTransitionUnit_localPullbackTrivialization (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    trivializationTransitionUnit (f ⁻¹ᵁ U) (localPullbackTrivializationT f M U e)
        (localPullbackTrivializationT f M U g) =
      Units.map (f.app U).hom.toMonoidHom (trivializationTransitionUnit U e g) := by
  apply Units.ext
  refine (ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv
    Y.ringCatSheaf (f ⁻¹ᵁ U)).injective ?_
  show ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf (f ⁻¹ᵁ U) _ =
    ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf (f ⁻¹ᵁ U) _
  rw [overUnitScalarEnd_transitionUnit, localPullbackTrivialization_inv_comp_hom]
  rfl

/-! ## Pulling back commutes with restricting -/

/-- Pullback of a trivialization commutes with restriction along a morphism of opens: the
`.hom` of both sides is `localDualPullback` of `e.hom` restricted, and
`localDualPullback_restrictD` says those agree. -/
theorem restrict_localPullbackTrivializationT (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ModularCurves.SheafOfModules.restrictOverTrivialization Y.ringCatSheaf
        ((pullback f).obj M) (f ⁻¹ᵁ U) (localPullbackTrivializationT f M U e)
        (Over.mk ((TopologicalSpace.Opens.map f.base).map i)) =
      localPullbackTrivializationT f M V
        (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk i)) := by
  apply Iso.ext
  have h1 : (localPullbackTrivializationT f M U e).hom = localDualPullback f M U e.hom :=
    (localDualPullback_trivialization_homT f M U e).symm
  have h2 : (localPullbackTrivializationT f M V
      (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
        (Over.mk i))).hom =
      localDualPullback f M V
        (ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf M i.op e.hom) :=
    (localDualPullback_trivialization_homT f M V _).symm
  have hrestr := localDualPullback_restrictD f M i.op e.hom
  show ModularCurves.SheafOfModules.dualRestrict Y.ringCatSheaf ((pullback f).obj M)
      ((TopologicalSpace.Opens.map f.base).map i).op
      (localPullbackTrivializationT f M U e).hom = _
  rw [h1, h2]
  exact hrestr.symm

/-- The `≤`-flavoured form of `restrict_localPullbackTrivializationT`, which is how the
overlap computation below uses it. -/
theorem restrict_localPullbackTrivialization (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ModularCurves.SheafOfModules.restrictOverTrivialization Y.ringCatSheaf
        ((pullback f).obj M) (f ⁻¹ᵁ U) (localPullbackTrivializationT f M U e)
        (Over.mk (homOfLE (f.preimage_mono h))) =
      localPullbackTrivializationT f M V
        (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE h))) := by
  have hmor : (TopologicalSpace.Opens.map f.base).map (homOfLE h) =
      homOfLE (f.preimage_mono h) := Subsingleton.elim _ _
  have hco := restrict_localPullbackTrivializationT f M (homOfLE h) e
  rwa [hmor] at hco

/-! ## The splitting: a globally trivial module has coboundary transition cocycle -/

/-- A trivialization over the top open, restricted to an arbitrary open. -/
noncomputable def globalOverTrivializationOn {M : X.Modules}
    (ε : M.over (⊤ : X.Opens) ≅ SheafOfModules.unit (X.ringCatSheaf.over (⊤ : X.Opens)))
    (W : X.Opens) : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) :=
  ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M ⊤ ε
    (Over.mk (homOfLE (le_top : W ≤ ⊤)))

/-- Restricting the restriction of a global trivialization is its restriction: this is what
makes the `h_i` below compatible with shrinking the open, hence patchable on overlaps. -/
theorem restrict_globalOverTrivializationOn {M : X.Modules}
    (ε : M.over (⊤ : X.Opens) ≅ SheafOfModules.unit (X.ringCatSheaf.over (⊤ : X.Opens)))
    {V W : X.Opens} (h : V ≤ W) :
    ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M W
        (globalOverTrivializationOn ε W) (Over.mk (homOfLE h)) =
      globalOverTrivializationOn ε V := by
  have harr : (homOfLE h ≫ homOfLE (le_top : W ≤ ⊤)) = homOfLE (le_top : V ≤ ⊤) :=
    Subsingleton.elim _ _
  refine (ModularCurves.SheafOfModules.restrictOverTrivialization_comp X.ringCatSheaf M ⊤ ε
    (Over.mk (homOfLE (le_top : W ≤ ⊤))) (Over.mk (homOfLE h))).trans ?_
  show ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M ⊤ ε
      (Over.mk (homOfLE h ≫ homOfLE (le_top : W ≤ ⊤))) = _
  rw [harr]
  rfl

/-- **KM's `h_i`**: the unit comparing a local trivialization of `M` on `W` with a global one. -/
noncomputable def globalComparisonUnit {M : X.Modules}
    (ε : M.over (⊤ : X.Opens) ≅ SheafOfModules.unit (X.ringCatSheaf.over (⊤ : X.Opens)))
    {W : X.Opens} (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) : Γ(X, W)ˣ :=
  trivializationTransitionUnit W e (globalOverTrivializationOn ε W)

/-- `h_i` restricted to a smaller open is the comparison unit computed there. -/
theorem globalComparisonUnit_restrict {M : X.Modules}
    (ε : M.over (⊤ : X.Opens) ≅ SheafOfModules.unit (X.ringCatSheaf.over (⊤ : X.Opens)))
    {V W : X.Opens} (h : V ≤ W) (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (globalComparisonUnit ε e) =
      trivializationTransitionUnit V
        (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M W e
          (Over.mk (homOfLE h)))
        (globalOverTrivializationOn ε V) := by
  have hr : trivializationTransitionUnit V
      (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M W e
        (Over.mk (homOfLE h)))
      (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M W
        (globalOverTrivializationOn ε W) (Over.mk (homOfLE h))) =
      Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
        (trivializationTransitionUnit W e (globalOverTrivializationOn ε W)) :=
    trivializationTransitionUnit_restrict h e (globalOverTrivializationOn ε W)
  rw [restrict_globalOverTrivializationOn] at hr
  exact hr.symm

/-- **(AP-D5, the coboundary)** If `M` is trivialized over the top open, the transition unit of
any two local trivializations, restricted to a common open, is the ratio of their comparison
units with the global trivialization. This is KM's `f_{i,j} = h_i / h_j` for the module whose
cocycle is being split — the whole of the existence argument. -/
theorem transitionUnit_restrictOn_eq_mul_inv {M : X.Modules}
    (ε : M.over (⊤ : X.Opens) ≅ SheafOfModules.unit (X.ringCatSheaf.over (⊤ : X.Opens)))
    {V W₁ W₂ : X.Opens} (h₁ : V ≤ W₁) (h₂ : V ≤ W₂)
    (e₁ : M.over W₁ ≅ SheafOfModules.unit (X.ringCatSheaf.over W₁))
    (e₂ : M.over W₂ ≅ SheafOfModules.unit (X.ringCatSheaf.over W₂)) :
    trivializationTransitionUnit V
        (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M W₁ e₁
          (Over.mk (homOfLE h₁)))
        (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M W₂ e₂
          (Over.mk (homOfLE h₂))) =
      Units.map (X.presheaf.map (homOfLE h₁).op).hom.toMonoidHom (globalComparisonUnit ε e₁) *
        (Units.map (X.presheaf.map (homOfLE h₂).op).hom.toMonoidHom
          (globalComparisonUnit ε e₂))⁻¹ := by
  rw [globalComparisonUnit_restrict ε h₁ e₁, globalComparisonUnit_restrict ε h₂ e₂,
    eq_mul_inv_iff_mul_eq]
  exact trivializationTransitionUnit_trans _ _ _ _

/-- **(AP-D5 existence, before pullback)** Over a module trivialized on the top open, every
family of local trivializations has its transition cocycle split by a family of units. -/
theorem exists_transitionUnit_eq_mul_inv {M : X.Modules}
    (ε : M.over (⊤ : X.Opens) ≅ SheafOfModules.unit (X.ringCatSheaf.over (⊤ : X.Opens)))
    {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i))) :
    ∃ h : ∀ i, Γ(X, W i)ˣ, ∀ i j,
      trivializationTransitionUnit (W i ⊓ W j)
          (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (e i)
            (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))))
          (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (e j)
            (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)))) =
        Units.map (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom.toMonoidHom
            (h i) *
          (Units.map (X.presheaf.map
            (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom.toMonoidHom (h j))⁻¹ :=
  ⟨fun i => globalComparisonUnit ε (e i),
    fun _ _ => transitionUnit_restrictOn_eq_mul_inv ε _ _ _ _⟩

/-! ## The assembled statement: `f_{i,j} ∘ [N] = h_i / h_j` -/

/-- **(AP-D5 EXISTENCE — KM p. 88)** Let `M` be an `𝒪_X`-module with trivializations `e i` over
opens `W i`, and suppose the pullback `f^*M` is trivialized over the top open of `Y`. Then there
are units `h_i` on `f ⁻¹ᵁ (W i)` with

  `f^# (f_{i,j}) = h_i · h_j⁻¹`   on `f ⁻¹ᵁ (W i ⊓ W j)`,

where `f_{i,j}` is the transition unit of `e i` and `e j` on `W i ⊓ W j`. For `f = [N]` this is
Katz–Mazur's `f_{i,j} ∘ [N] = h_i / h_j`, and the `h_i` are `globalComparisonUnit` of the
pulled-back trivializations against the global one. -/
theorem exists_pullback_transitionUnit_eq_mul_inv (f : Y ⟶ X) (M : X.Modules)
    (ε : ((pullback f).obj M).over (⊤ : Y.Opens) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over (⊤ : Y.Opens)))
    {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i))) :
    ∃ h : ∀ i, Γ(Y, f ⁻¹ᵁ W i)ˣ, ∀ i j,
      Units.map (f.app (W i ⊓ W j)).hom.toMonoidHom
          (trivializationTransitionUnit (W i ⊓ W j)
            (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (e i)
              (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))))
            (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (e j)
              (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))))) =
        Units.map (Y.presheaf.map (homOfLE
              (f.preimage_mono (inf_le_left : W i ⊓ W j ≤ W i))).op).hom.toMonoidHom (h i) *
          (Units.map (Y.presheaf.map (homOfLE
            (f.preimage_mono (inf_le_right : W i ⊓ W j ≤ W j))).op).hom.toMonoidHom (h j))⁻¹ := by
  refine ⟨fun i => globalComparisonUnit ε (localPullbackTrivializationT f M (W i) (e i)),
    fun i j => ?_⟩
  rw [← trivializationTransitionUnit_localPullbackTrivialization f M (W i ⊓ W j),
    ← restrict_localPullbackTrivialization f M (inf_le_left : W i ⊓ W j ≤ W i) (e i),
    ← restrict_localPullbackTrivialization f M (inf_le_right : W i ⊓ W j ≤ W j) (e j)]
  exact transitionUnit_restrictOn_eq_mul_inv ε _ _ _ _

/-! ## The input: triviality of the pullback in `Pic` -/

/-- Every Picard class has a representing module. -/
theorem exists_toSkeleton_eq (L : Scheme.Pic X) :
    letI := Modules.monoidalCategory X
    ∃ M : X.Modules, L.val = toSkeleton M := by
  letI := Modules.monoidalCategory X
  obtain ⟨M, hM⟩ := Quotient.exists_rep L.val
  exact ⟨M, hM.symm⟩

/-- **(the AP-D4 interface)** A Picard class killed by `Pic.map f` has globally trivial
pullback. For `f = [N]` and `L = κ(Q)` with `Q` an `N`-torsion section, the hypothesis is
`picMap_mulByHom_kappa_eq_one` (`Picard/SelfAdjointN.lean`). -/
theorem nonempty_unitObj_iso_of_picMap_eq_one (f : Y ⟶ X) (L : Scheme.Pic X) (M : X.Modules)
    (hLM : letI := Modules.monoidalCategory X; L.val = toSkeleton M)
    (hL : Scheme.Pic.map f L = 1) :
    Nonempty (unitObj Y ≅ (pullback f).obj M) := by
  letI := Modules.monoidalCategory X
  letI := Modules.monoidalCategory Y
  have hval : (Modules.pullback f).mapSkeleton.obj L.val = 1 :=
    (Scheme.Pic.map_val f L).symm.trans (congrArg Units.val hL)
  rw [hLM, Functor.mapSkeleton_obj_toSkeleton, Skeleton.one_eq] at hval
  obtain ⟨eu⟩ := toSkeleton_eq_toSkeleton_iff.mp hval
  obtain ⟨e0⟩ := nonempty_unitObj_iso_unit (X := Y)
  exact ⟨e0 ≪≫ eu.symm⟩

/-- A global trivialization of a module, read on the over-site of any open. -/
noncomputable def overTrivializationOfUnitObjIso {N : Y.Modules} (iso : unitObj Y ≅ N)
    (U : Y.Opens) : N.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  overTrivializationOfRestrictIso N U
    (restrictIsoOfPullbackIso N U
      ((pullback U.ι).mapIso iso.symm ≪≫ pullbackUnitIso U.ι))

/-- **(AP-D5 EXISTENCE, Picard form)** The assembled statement with the global trivialization of
`f^*M` replaced by its actual source: the vanishing of the pulled-back Picard class. -/
theorem exists_transitionUnit_eq_mul_inv_of_picMap_eq_one (f : Y ⟶ X) (L : Scheme.Pic X)
    (M : X.Modules) (hLM : letI := Modules.monoidalCategory X; L.val = toSkeleton M)
    (hL : Scheme.Pic.map f L = 1) {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i))) :
    ∃ h : ∀ i, Γ(Y, f ⁻¹ᵁ W i)ˣ, ∀ i j,
      Units.map (f.app (W i ⊓ W j)).hom.toMonoidHom
          (trivializationTransitionUnit (W i ⊓ W j)
            (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (e i)
              (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))))
            (ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (e j)
              (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))))) =
        Units.map (Y.presheaf.map (homOfLE
              (f.preimage_mono (inf_le_left : W i ⊓ W j ≤ W i))).op).hom.toMonoidHom (h i) *
          (Units.map (Y.presheaf.map (homOfLE
            (f.preimage_mono (inf_le_right : W i ⊓ W j ≤ W j))).op).hom.toMonoidHom (h j))⁻¹ := by
  obtain ⟨iso⟩ := nonempty_unitObj_iso_of_picMap_eq_one f L M hLM hL
  exact exists_pullback_transitionUnit_eq_mul_inv f M (overTrivializationOfUnitObjIso iso ⊤) W e

end

end AlgebraicGeometry.Scheme.Modules
