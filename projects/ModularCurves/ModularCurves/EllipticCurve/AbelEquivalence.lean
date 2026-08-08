/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.DegreeOneFibreCohomology
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.Picard.IdealModule
import ModularCurves.ForMathlib.LocalFlatnessCriterion

/-!
# The Abel equivalence, evaluation-divisor side (`AP2-B2`/`AP2-B3`, KM pp. 66–67)

KM p. 66, verbatim: *"Because `f_*L` is invertible on `S`, Zariski locally on `S` we may
pick an `O_S`-basis `ℓ` of `f_*L`. We claim that, locally over `S`, the pair `(L, ℓ)` on
`E` defines an effective Cartier divisor in `E`. We must show that we have an exact
sequence `0 → O → L → L/O → 0` with `L/O` flat over `S`. This amounts to the statement
that the map of invertible sheaves `O --ℓ--> L` on `E` is injective, and remains so after
any base change `T → S` on `S`. For this we are reduced to the case `S = Spec(k)` with `k`
a field, and `ℓ ∈ H⁰(E,L)` a `k`-basis, so non-zero, in which case the assertion is
obvious."* Then p. 67: *"Therefore `(L, ℓ)` defines an effective Cartier divisor in `E/S`.
Looking fiber-by-fiber, we see that it is of degree one. By (1.2.7), any effective Cartier
divisor of degree one is a section `P ∈ E(S)`."*

Design (board, 2026-08-08 surveys 1–2): the target vocabulary is the divisor engine —
`RelEffCartierDiv π` / `IsOfficialCartier` (`LevelStructure/CartierDivisor.lean`) with the
module seam `idealModule` / `isInvertible_idealModule` (`Picard/IdealModule.lean`); the
fibrewise flatness criterion is in-tree (`ForMathlib/LocalFlatnessCriterion.lean`, Stacks
00ME, with the relative `_sModule` variant and the `BaseChangeKerCoker` output forms). The
statements below are EXISTENCE-form (Pic-level consumers only need the class), keeping all
defs sorry-free.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- Evaluation against a fixed section is natural: evaluating the restricted functional is
restricting the evaluation. -/
theorem eval_dualRestrict {E : Scheme.{u}} (M : E.Modules) (σ : ↑Γ(M, ⊤))
    {U V : E.Opens} (h : V ≤ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (E.ringCatSheaf.over U)) :
    (ModularCurves.SheafOfModules.dualRestrict E.ringCatSheaf M
        (show Opposite.op U ⟶ Opposite.op V from (homOfLE h).op) φ).val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))
        (show (M.over V).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from
          M.presheaf.map (homOfLE le_top).op σ) =
      E.presheaf.map (homOfLE h).op
        (show ↑Γ(E, U) from φ.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 U)))
          (show (M.over U).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 U))) from
            M.presheaf.map (homOfLE le_top).op σ)) := by
  have hσ : (M.presheaf.map (homOfLE h).op)
      ((M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) σ) =
      (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) σ := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun q ↦ (ConcreteCategory.hom (M.presheaf.map
      (Quiver.Hom.op q))) σ) (Subsingleton.elim _ _)
  have hnat := PresheafOfModules.naturality_apply φ.val
    (CategoryTheory.Over.mkIdTerminal.from (CategoryTheory.Over.mk (homOfLE h))).op
    (show (M.over U).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 U))) from
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op σ)
  simp only [ModularCurves.SheafOfModules.dualRestrict_app_apply]
  exact (congrArg (fun z ↦ φ.val.app (Opposite.op ((CategoryTheory.Over.map
    (homOfLE h)).obj (CategoryTheory.Over.mk (𝟙 V)))) z) hσ.symm).trans hnat

/-- Evaluation is semilinear for the dual's scalar action: the scalar comes out as a ring
multiple (the scalar endomorphism acts by multiplication at the terminal object). -/
theorem eval_smul {E : Scheme.{u}} (M : E.Modules) (V : E.Opens)
    (r : ↑(E.ringCatSheaf.obj.obj (Opposite.op V)))
    (ψ : M.over V ⟶ _root_.SheafOfModules.unit (E.ringCatSheaf.over V))
    (x : (M.over V).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))) :
    letI := ModularCurves.SheafOfModules.dualSectionsModule E.ringCatSheaf M V
    ((r • ψ).val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) x) =
      (show ↑(E.ringCatSheaf.obj.obj (Opposite.op V)) from ψ.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) x) * r := by
  letI := ModularCurves.SheafOfModules.dualSectionsModule E.ringCatSheaf M V
  have hcomp : (r • ψ) = ψ ≫ ModularCurves.SheafOfModules.overUnitScalarEnd
    E.ringCatSheaf V r := rfl
  rw [hcomp]
  have hsplit : (ψ ≫ ModularCurves.SheafOfModules.overUnitScalarEnd
      E.ringCatSheaf V r).val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) x =
      (ModularCurves.SheafOfModules.overUnitScalarEnd E.ringCatSheaf V r).val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))
        (ψ.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) x) := rfl
  rw [hsplit]
  have h0 : (ModularCurves.SheafOfModules.overUnitScalarEnd E.ringCatSheaf V r).val.app
      (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))
      (ψ.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) x) =
      (show ↑(E.ringCatSheaf.obj.obj (Opposite.op V)) from ψ.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) x) *
      (show ↑(E.ringCatSheaf.obj.obj (Opposite.op V)) from
        E.ringCatSheaf.obj.map (𝟙 V).op r) := rfl
  rw [h0]
  refine congrArg (fun z ↦ (show ↑(E.ringCatSheaf.obj.obj (Opposite.op V)) from ψ.val.app
    (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) x) * z) ?_
  show E.ringCatSheaf.obj.map (𝟙 V).op r = r
  rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **(sv2-a)** On an affine open, an invertible module admits a finite cover by basic opens
on which it is trivial: refine the trivialising cover by `IsAffineOpen.exists_basicOpen_le`
and take a finite subcover of the quasi-compact affine. -/
theorem exists_finite_basicOpen_trivialization {E : Scheme.{u}} (N : E.Modules)
    (hN : IsInvertible N) (U : E.affineOpens) :
    ∃ (t : Finset ↑Γ(E, U.1)),
      (U.1 ≤ ⨆ g ∈ t, E.basicOpen g) ∧
      ∀ g ∈ t, E.basicOpen g ≤ U.1 ∧
        Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (E.basicOpen g).ι).obj N ≅ unitObj (E.basicOpen g).toScheme) := by
  obtain ⟨ι, V, hV, htriv⟩ := hN
  -- every point of `U` sits in a basic open of `U` inside some trivialising `V i`
  have hpt : ∀ x : U.1, ∃ g : ↑Γ(E, U.1), E.basicOpen g ≤ U.1 ∧ ↑x ∈ E.basicOpen g ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (E.basicOpen g).ι).obj N ≅ unitObj (E.basicOpen g).toScheme) := by
    intro x
    have hxV : (↑x : E) ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
    obtain ⟨g, hgle, hxg⟩ := U.2.exists_basicOpen_le
      (V := U.1 ⊓ V i) ⟨↑x, ⟨x.2, hi⟩⟩ x.2
    obtain ⟨e⟩ := htriv i
    exact ⟨g, le_trans hgle inf_le_left, hxg,
      ⟨restrictTrivialization (le_trans hgle inf_le_right) e⟩⟩
  classical
  choose g hgle hxg htrivg using hpt
  have hcover : (U.1 : Set E) ⊆ ⋃ x : U.1, ((E.basicOpen (g x)) : Set E) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxg ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := U.2.isCompact.elim_finite_subcover
    (fun x : U.1 ↦ ((E.basicOpen (g x)) : Set E))
    (fun x ↦ (E.basicOpen (g x)).isOpen) hcover
  refine ⟨t.image g, ?_, ?_⟩
  · intro y hy
    have hy' := ht hy
    simp only [Set.mem_iUnion, exists_prop] at hy'
    obtain ⟨x, hxt, hyx⟩ := hy'
    simp only [TopologicalSpace.Opens.mem_iSup, Finset.mem_image]
    exact ⟨g x, ⟨x, hxt, rfl⟩, hyx⟩
  · intro h hh
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hh
    exact ⟨hgle x, htrivg x⟩

/-- The sections of a module trivialised on `W`, as a rank-one free module over the
sections of the structure sheaf: evaluation against the trivialisation is a linear
equivalence (`bijective_evalSection_iso` + `evalSection_add_right`/`_smul_right`). -/
noncomputable def sectionsLinearEquivOfTrivialization {E : Scheme.{u}} (N : E.Modules)
    (W : E.Opens)
    (ψ : N.over W ≅ _root_.SheafOfModules.unit (E.ringCatSheaf.over W)) :
    ↑(N.val.obj (Opposite.op W)) ≃ₗ[↑(E.ringCatSheaf.obj.obj (Opposite.op W))]
      ↑(E.ringCatSheaf.obj.obj (Opposite.op W)) :=
  LinearEquiv.ofBijective
    { toFun := fun m ↦ ModularCurves.SheafOfModules.evalSection E.ringCatSheaf N W ψ.hom m
      map_add' := fun a b ↦
        ModularCurves.SheafOfModules.evalSection_add_right E.ringCatSheaf N W ψ.hom a b
      map_smul' := fun c a ↦
        ModularCurves.SheafOfModules.evalSection_smul_right E.ringCatSheaf N W ψ.hom c a }
    (ModularCurves.SheafOfModules.bijective_evalSection_iso E.ringCatSheaf N W ψ)

@[simp]
theorem sectionsLinearEquivOfTrivialization_apply {E : Scheme.{u}} (N : E.Modules)
    (W : E.Opens)
    (ψ : N.over W ≅ _root_.SheafOfModules.unit (E.ringCatSheaf.over W))
    (m : ↑(N.val.obj (Opposite.op W))) :
    sectionsLinearEquivOfTrivialization N W ψ m =
      ModularCurves.SheafOfModules.evalSection E.ringCatSheaf N W ψ.hom m :=
  rfl

/-- Evaluation against a restricted trivialisation is the restriction of the evaluation:
`restrictOverTrivialization`'s `hom` is definitionally `dualRestrict` of the original, so
this is `evalSection_naturality`. -/
theorem evalSection_restrictOverTrivialization {E : Scheme.{u}} (N : E.Modules)
    (V : E.Opens) (t : N.over V ≅ _root_.SheafOfModules.unit (E.ringCatSheaf.over V))
    {W : E.Opens} (h : W ≤ V) (m : ↑(N.val.obj (Opposite.op V))) :
    ModularCurves.SheafOfModules.evalSection E.ringCatSheaf N W
        (ModularCurves.SheafOfModules.restrictOverTrivialization E.ringCatSheaf N V t
          (CategoryTheory.Over.mk (homOfLE h))).hom
        (N.presheaf.map (homOfLE h).op m) =
      E.presheaf.map (homOfLE h).op
        (ModularCurves.SheafOfModules.evalSection E.ringCatSheaf N V t.hom m) :=
  ModularCurves.SheafOfModules.evalSection_naturality E.ringCatSheaf N
    (show Opposite.op V ⟶ Opposite.op W from (homOfLE h).op) t.hom m

/-- **(sv2-b)** Per-piece clearing on a *trivial* piece: if `N` is trivial on an affine open
`V`, a section over `V ⊓ basicOpen f` becomes, after multiplying by a power of `f`, the
restriction of a section over `V`. Through the trivialisation this is exactly the
structure-sheaf away-localization `IsAffineOpen.isLocalization_basicOpen`. -/
theorem exists_pow_smul_eq_restrict_of_trivial {E : Scheme.{u}} (N : E.Modules)
    (V : E.affineOpens) (f : ↑Γ(E, V.1))
    (e : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback V.1.ι).obj N ≅
      unitObj V.1.toScheme))
    (s' : ↑Γ(N, E.basicOpen f)) :
    ∃ (n : ℕ) (s : ↑Γ(N, V.1)),
      N.presheaf.map (homOfLE (E.basicOpen_le f)).op s =
        (E.presheaf.map (homOfLE (E.basicOpen_le f)).op f) ^ n • s' := by
  obtain ⟨e0⟩ := e
  set ψV : N.over V.1 ≅ _root_.SheafOfModules.unit (E.ringCatSheaf.over V.1) :=
    overTrivializationOfRestrictIso N V.1 (restrictIsoOfPullbackIso N V.1 e0) with hψV
  set ψf : N.over (E.basicOpen f) ≅
      _root_.SheafOfModules.unit (E.ringCatSheaf.over (E.basicOpen f)) :=
    ModularCurves.SheafOfModules.restrictOverTrivialization E.ringCatSheaf N V.1 ψV
      (CategoryTheory.Over.mk (homOfLE (E.basicOpen_le f))) with hψf
  set τV := sectionsLinearEquivOfTrivialization N V.1 ψV with hτV
  set τf := sectionsLinearEquivOfTrivialization N (E.basicOpen f) ψf with hτf
  haveI := V.2.isLocalization_basicOpen f
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj (S := ↑Γ(E, E.basicOpen f)) f (τf s')
  refine ⟨n, τV.symm a, ?_⟩
  apply τf.injective
  have hL : τf (N.presheaf.map (homOfLE (E.basicOpen_le f)).op (τV.symm a)) =
      E.presheaf.map (homOfLE (E.basicOpen_le f)).op a := by
    have h1 : τf (N.presheaf.map (homOfLE (E.basicOpen_le f)).op (τV.symm a)) =
        ModularCurves.SheafOfModules.evalSection E.ringCatSheaf N (E.basicOpen f)
          (ModularCurves.SheafOfModules.restrictOverTrivialization E.ringCatSheaf N V.1 ψV
            (CategoryTheory.Over.mk (homOfLE (E.basicOpen_le f)))).hom
          (N.presheaf.map (homOfLE (E.basicOpen_le f)).op (τV.symm a)) := rfl
    rw [h1, evalSection_restrictOverTrivialization N V.1 ψV (E.basicOpen_le f) (τV.symm a)]
    exact congrArg (fun z ↦ E.presheaf.map (homOfLE (E.basicOpen_le f)).op z)
      (τV.apply_symm_apply a)
  have hR : τf ((E.presheaf.map (homOfLE (E.basicOpen_le f)).op f) ^ n • s') =
      (show ↑(E.ringCatSheaf.obj.obj (Opposite.op (E.basicOpen f))) from
        (E.presheaf.map (homOfLE (E.basicOpen_le f)).op f) ^ n) * τf s' :=
    ModularCurves.SheafOfModules.evalSection_smul_right E.ringCatSheaf N
      (E.basicOpen f) ψf.hom _ s'
  rw [hL, hR]
  have halg : ∀ x : ↑Γ(E, V.1),
      (algebraMap ↑Γ(E, V.1) ↑Γ(E, E.basicOpen f)) x =
        E.presheaf.map (homOfLE (E.basicOpen_le f)).op x := fun x ↦ rfl
  rw [halg, halg] at hna
  exact hna.symm.trans (mul_comm _ _)

/-- **(sv2-e)** Two sections of a trivialised module on an affine open that agree after
restriction to a basic open agree after multiplication by a power of the defining function
(the `f`-torsion is killed): through the trivialisation this is
`IsLocalization.Away.exists_of_eq`. -/
theorem exists_pow_smul_eq_of_restrict_eq {E : Scheme.{u}} (N : E.Modules)
    (V : E.affineOpens) (f : ↑Γ(E, V.1))
    (e : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback V.1.ι).obj N ≅
      unitObj V.1.toScheme))
    (s t : ↑Γ(N, V.1))
    (h : N.presheaf.map (homOfLE (E.basicOpen_le f)).op s =
      N.presheaf.map (homOfLE (E.basicOpen_le f)).op t) :
    ∃ n : ℕ, (f ^ n) • s = (f ^ n) • t := by
  obtain ⟨e0⟩ := e
  set ψV : N.over V.1 ≅ _root_.SheafOfModules.unit (E.ringCatSheaf.over V.1) :=
    overTrivializationOfRestrictIso N V.1 (restrictIsoOfPullbackIso N V.1 e0) with hψV
  set ψf : N.over (E.basicOpen f) ≅
      _root_.SheafOfModules.unit (E.ringCatSheaf.over (E.basicOpen f)) :=
    ModularCurves.SheafOfModules.restrictOverTrivialization E.ringCatSheaf N V.1 ψV
      (CategoryTheory.Over.mk (homOfLE (E.basicOpen_le f))) with hψf
  set τV := sectionsLinearEquivOfTrivialization N V.1 ψV with hτV
  haveI := V.2.isLocalization_basicOpen f
  -- the coordinates of `s` and `t` agree after restriction
  have hcoord : (algebraMap ↑Γ(E, V.1) ↑Γ(E, E.basicOpen f)) (τV s) =
      (algebraMap ↑Γ(E, V.1) ↑Γ(E, E.basicOpen f)) (τV t) := by
    have hs : (algebraMap ↑Γ(E, V.1) ↑Γ(E, E.basicOpen f)) (τV s) =
        ModularCurves.SheafOfModules.evalSection E.ringCatSheaf N (E.basicOpen f) ψf.hom
          (N.presheaf.map (homOfLE (E.basicOpen_le f)).op s) :=
      (evalSection_restrictOverTrivialization N V.1 ψV (E.basicOpen_le f) s).symm
    have ht : (algebraMap ↑Γ(E, V.1) ↑Γ(E, E.basicOpen f)) (τV t) =
        ModularCurves.SheafOfModules.evalSection E.ringCatSheaf N (E.basicOpen f) ψf.hom
          (N.presheaf.map (homOfLE (E.basicOpen_le f)).op t) :=
      (evalSection_restrictOverTrivialization N V.1 ψV (E.basicOpen_le f) t).symm
    rw [hs, ht, h]
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := ↑Γ(E, E.basicOpen f)) f hcoord
  refine ⟨n, τV.injective ?_⟩
  have hs : τV ((f ^ n) • s) =
      (show ↑(E.ringCatSheaf.obj.obj (Opposite.op V.1)) from f ^ n) * τV s :=
    ModularCurves.SheafOfModules.evalSection_smul_right E.ringCatSheaf N V.1 ψV.hom _ s
  have ht : τV ((f ^ n) • t) =
      (show ↑(E.ringCatSheaf.obj.obj (Opposite.op V.1)) from f ^ n) * τV t :=
    ModularCurves.SheafOfModules.evalSection_smul_right E.ringCatSheaf N V.1 ψV.hom _ t
  rw [hs, ht]
  exact hn

/-- **(sv2-d)** Transitivity of the clearing identity: if a section `w` on an open `W`
restricts, on the `f`-locus of `W`, to `f ^ n` times a fixed section, then the same holds
after further restriction to any smaller open. Stated with all opens explicit so the
composite-restriction bridges stay first-order. -/
theorem restrict_clearing_identity {E : Scheme.{u}} (N : E.Modules)
    {U W W' : E.Opens} (hWU : W ≤ U) (hW'W : W' ≤ W) (f : ↑Γ(E, U)) (n : ℕ)
    (s' : ↑Γ(N, E.basicOpen f)) (w : ↑Γ(N, W))
    (hfW : E.basicOpen (E.presheaf.map (homOfLE hWU).op f) ≤ E.basicOpen f)
    (hfW' : E.basicOpen (E.presheaf.map (homOfLE (hW'W.trans hWU)).op f) ≤
      E.basicOpen (E.presheaf.map (homOfLE hWU).op f))
    (hw : N.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE hWU).op f))).op w =
      (E.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE hWU).op f))).op
        (E.presheaf.map (homOfLE hWU).op f)) ^ n •
        N.presheaf.map (homOfLE hfW).op s') :
    N.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE (hW'W.trans hWU)).op f))).op
        (N.presheaf.map (homOfLE hW'W).op w) =
      (E.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE (hW'W.trans hWU)).op f))).op
        (E.presheaf.map (homOfLE (hW'W.trans hWU)).op f)) ^ n •
        N.presheaf.map (homOfLE (hfW'.trans hfW)).op s' := by
  -- restrict the hypothesis along the `f`-locus inclusion
  have hres := congrArg (fun z ↦ N.presheaf.map (homOfLE hfW').op z) hw
  simp only [AlgebraicGeometry.Scheme.Modules.map_smul, map_pow] at hres
  refine Eq.trans ?_ (hres.trans ?_)
  · -- the two restriction composites agree
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun q ↦ (ConcreteCategory.hom (N.presheaf.map (Quiver.Hom.op q))) w)
      (Subsingleton.elim _ _)
  · -- the scalar and the `s'`-restriction match on the nose
    refine congrArg₂ (fun (r : ↑Γ(E, E.basicOpen (E.presheaf.map
        (homOfLE (hW'W.trans hWU)).op f))) z ↦ r ^ n • z) ?_ ?_
    · simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun q ↦ (ConcreteCategory.hom (E.presheaf.map (Quiver.Hom.op q))) f)
        (Subsingleton.elim _ _)
    · simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun q ↦ (ConcreteCategory.hom (N.presheaf.map (Quiver.Hom.op q))) s')
        (Subsingleton.elim _ _)

/-- **(sv2-core, the remaining gap — sections of an invertible module localize)** On an
affine open, a section over a basic open becomes, after multiplication by a power of the
defining function, the restriction of a global-on-`U` section. This is the concrete
away-localization form of quasi-coherence; mathlib's quasi-coherence is presentation-based
(`SheafOfModules.QuasicoherentData`) and carries no sections-over-basic-opens localization,
so it is proved here.

Route (Hartshorne II.5.1(b) shape, all ingredients in the tree): refine the trivialising
cover of the quasi-compact affine `U` to finitely many basic opens `U_{gᵢ}` on which `N` is
trivial; through the trivialisations the sections are `Γ(E, U_{gᵢ})` and the restriction to
`U_{f gᵢ}` is the structure-sheaf away-localization (`IsAffineOpen.isLocalization_basicOpen`),
so each local piece clears its own power of `f`; a further power makes the pieces agree on
overlaps, and the sheaf condition glues them. -/
theorem exists_pow_smul_eq_restrict_of_isInvertible {E : Scheme.{u}} (N : E.Modules)
    (hN : IsInvertible N) (U : E.affineOpens) (f : ↑Γ(E, U.1))
    (s' : ↑Γ(N, E.basicOpen f)) :
    ∃ (n : ℕ) (s : ↑Γ(N, U.1)),
      N.presheaf.map (homOfLE (E.basicOpen_le f)).op s =
        (E.presheaf.map (homOfLE (E.basicOpen_le f)).op f) ^ n • s' := by
  classical
  -- (a) a finite trivialising cover of `U` by basic opens
  obtain ⟨t, hcover, hpiece⟩ := exists_finite_basicOpen_trivialization N hN U
  -- (b) per piece: the section clears a power of `f` there
  have hloc : ∀ g : {g // g ∈ t}, ∃ (m : ℕ) (u : ↑Γ(N, E.basicOpen g.1)),
      N.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f))).op u =
      (E.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f))).op
        (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f)) ^ m •
        N.presheaf.map (homOfLE (by
          rw [Scheme.basicOpen_res]
          exact le_trans inf_le_right le_rfl)).op s' := by
    intro g
    exact exists_pow_smul_eq_restrict_of_trivial N
      ⟨E.basicOpen g.1, U.2.basicOpen g.1⟩
      (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f)
      (hpiece g.1 g.2).2 _
  choose m u hu using hloc
  -- (c) a common exponent for all (finitely many) pieces
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ g : {g // g ∈ t}, m g ≤ n := by
    haveI : Fintype {g // g ∈ t} := FinsetCoe.fintype t
    exact ⟨Finset.univ.sup m, fun g ↦ Finset.le_sup (Finset.mem_univ g)⟩
  -- (d) rescale each piece to the common exponent `n`
  set v : ∀ g : {g // g ∈ t}, ↑Γ(N, E.basicOpen g.1) := fun g ↦
    (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f) ^ (n - m g) • u g with hv
  have hvres : ∀ g : {g // g ∈ t},
      N.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f))).op (v g) =
      (E.presheaf.map (homOfLE (E.basicOpen_le
        (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f))).op
        (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f)) ^ n •
        N.presheaf.map (homOfLE (by
          rw [Scheme.basicOpen_res]
          exact le_trans inf_le_right le_rfl)).op s' := by
    intro g
    rw [hv]
    rw [AlgebraicGeometry.Scheme.Modules.map_smul, hu g, smul_smul, map_pow,
      ← pow_add, Nat.sub_add_cancel (hn g)]
  -- (e) the rescaled pieces agree on overlaps after a further power of `f`
  have hoverlap : ∀ g g' : {g // g ∈ t},
      ∃ k : ℕ,
        ((show ↑Γ(E, E.basicOpen g.1 ⊓ E.basicOpen g'.1) from
            E.presheaf.map (homOfLE ((inf_le_left :
              E.basicOpen g.1 ⊓ E.basicOpen g'.1 ≤ E.basicOpen g.1).trans
              (hpiece g.1 g.2).1)).op f) ^ k) •
            N.presheaf.map (Opens.infLELeft (E.basicOpen g.1) (E.basicOpen g'.1)).op (v g) =
          ((show ↑Γ(E, E.basicOpen g.1 ⊓ E.basicOpen g'.1) from
            E.presheaf.map (homOfLE ((inf_le_left :
              E.basicOpen g.1 ⊓ E.basicOpen g'.1 ≤ E.basicOpen g.1).trans
              (hpiece g.1 g.2).1)).op f) ^ k) •
            N.presheaf.map
              (Opens.infLERight (E.basicOpen g.1) (E.basicOpen g'.1)).op (v g') := by
    intro g g'
    -- the overlap is a basic open of `U`, hence affine
    have haff : IsAffineOpen (E.basicOpen g.1 ⊓ E.basicOpen g'.1) := by
      rw [← Scheme.basicOpen_mul]
      exact U.2.basicOpen _
    -- the `g`-trivialisation restricts to the overlap
    have htrivW : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (E.basicOpen g.1 ⊓ E.basicOpen g'.1).ι).obj N ≅
        unitObj (E.basicOpen g.1 ⊓ E.basicOpen g'.1).toScheme) :=
      ⟨restrictTrivialization (inf_le_left : E.basicOpen g.1 ⊓ E.basicOpen g'.1 ≤
        E.basicOpen g.1) (hpiece g.1 g.2).2.some⟩
    -- apply the `f`-torsion lemma on the overlap
    refine (exists_pow_smul_eq_of_restrict_eq N ⟨_, haff⟩
      (E.presheaf.map (homOfLE ((inf_le_left : E.basicOpen g.1 ⊓ E.basicOpen g'.1 ≤
        E.basicOpen g.1).trans (hpiece g.1 g.2).1)).op f) htrivW
      (N.presheaf.map (Opens.infLELeft (E.basicOpen g.1) (E.basicOpen g'.1)).op (v g))
      (N.presheaf.map (Opens.infLERight (E.basicOpen g.1) (E.basicOpen g'.1)).op (v g'))
      ?_).imp (fun k hk ↦ hk)
    -- the two rescaled pieces agree on the overlap's `f`-locus: both restrict to
    -- `f ^ n • s'` there (two applications of `restrict_clearing_identity`)
    have hgL := restrict_clearing_identity N (hpiece g.1 g.2).1
      (inf_le_left : E.basicOpen g.1 ⊓ E.basicOpen g'.1 ≤ E.basicOpen g.1) f n s' (v g)
      (by rw [Scheme.basicOpen_res]; exact inf_le_right)
      (by rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
          exact inf_le_inf_right _ inf_le_left)
      (hvres g)
    have hgR := restrict_clearing_identity N (hpiece g'.1 g'.2).1
      (inf_le_right : E.basicOpen g.1 ⊓ E.basicOpen g'.1 ≤ E.basicOpen g'.1) f n s' (v g')
      (by rw [Scheme.basicOpen_res]; exact inf_le_right)
      (by rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
          exact inf_le_inf_right _ inf_le_right)
      (hvres g')
    refine hgL.trans (Eq.trans ?_ hgR.symm)
    refine congrArg₂ (fun (r : ↑Γ(E, E.basicOpen (E.presheaf.map (homOfLE ((inf_le_left :
        E.basicOpen g.1 ⊓ E.basicOpen g'.1 ≤ E.basicOpen g.1).trans
        (hpiece g.1 g.2).1)).op f))) z ↦ r ^ n • z) ?_ ?_
    · simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    · exact congrArg (fun q ↦ (ConcreteCategory.hom (N.presheaf.map (Quiver.Hom.op q))) s')
        (Subsingleton.elim _ _)
  -- (f) a uniform overlap exponent, so the rescaled pieces agree on the nose
  choose k hk using hoverlap
  haveI : Fintype {g // g ∈ t} := FinsetCoe.fintype t
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ g g' : {g // g ∈ t}, k g g' ≤ K :=
    ⟨Finset.univ.sup fun p : {g // g ∈ t} × {g // g ∈ t} ↦ k p.1 p.2,
      fun g g' ↦ Finset.le_sup (f := fun p : {g // g ∈ t} × {g // g ∈ t} ↦ k p.1 p.2)
        (Finset.mem_univ (g, g'))⟩
  -- the twice-rescaled pieces
  set w : ∀ g : {g // g ∈ t}, ↑Γ(N, E.basicOpen g.1) := fun g ↦
    (E.presheaf.map (homOfLE (hpiece g.1 g.2).1).op f) ^ K • v g with hw
  -- they agree on overlaps, on the nose
  have hcompat : ∀ g g' : {g // g ∈ t},
      N.presheaf.map (Opens.infLELeft (E.basicOpen g.1) (E.basicOpen g'.1)).op (w g) =
      N.presheaf.map (Opens.infLERight (E.basicOpen g.1) (E.basicOpen g'.1)).op (w g') := by
    sorry
  sorry

/-- **(sv2, the remaining gap — dual sections localize)** A functional on an invertible `M`
over a basic open is, up to a power of the defining section, the restriction of a functional
on the ambient affine open. This is quasi-coherence of `dualObj M` in its concrete
away-localization form; mathlib's quasi-coherence is presentation-based and has no
sections-over-basic-opens localization lemma (board note 2026-08-08), so this is the one
genuine gap left in the `AP2-B2` construction. Route: refine the trivialising cover of `U`
by basic opens (affine `U` is quasi-compact), apply `span_range_eval_eq_of_trivialization`
on each piece, and glue the resulting local preimages by the sheaf condition after clearing
denominators (Hartshorne II.5.1(b)-style; the standard argument for f.p. quasi-coherent
Hom-sheaves). -/
theorem exists_dualRestrict_eq_pow_smul {E : Scheme.{u}} (M : E.Modules)
    (hM : IsInvertible M) (U : E.affineOpens) (f : ↑Γ(E, U.1))
    (φ' : M.over (E.basicOpen f) ⟶
      _root_.SheafOfModules.unit (E.ringCatSheaf.over (E.basicOpen f))) :
    ∃ (n : ℕ) (φ : M.over U.1 ⟶
        _root_.SheafOfModules.unit (E.ringCatSheaf.over U.1)),
      letI := ModularCurves.SheafOfModules.dualSectionsModule E.ringCatSheaf M
        (E.basicOpen f)
      ModularCurves.SheafOfModules.dualRestrict E.ringCatSheaf M
        (show Opposite.op U.1 ⟶ Opposite.op (E.basicOpen f) from
          (homOfLE (E.basicOpen_le f)).op) φ =
      ((show ↑(E.ringCatSheaf.obj.obj (Opposite.op (E.basicOpen f))) from
        E.presheaf.map (homOfLE (E.basicOpen_le f)).op f) ^ n) • φ' := by
  obtain ⟨n, s, hs⟩ := exists_pow_smul_eq_restrict_of_isInvertible (dualObj M)
    hM.dual U f (show ↑Γ(dualObj M, E.basicOpen f) from φ')
  exact ⟨n, s, hs⟩

/-- **(sv1)** On a trivialising open the evaluation ideal of `σ` is principal, generated by
the trivialisation's own evaluation: every functional is `t.hom ≫ E(r)`
(`dualTrivializationLinearEquiv`), and evaluation turns the scalar action into ring
multiplication. -/
theorem span_range_eval_eq_of_trivialization {E : Scheme.{u}} (M : E.Modules)
    (σ : ↑Γ(M, ⊤)) (V : E.Opens)
    (t : M.over V ≅ _root_.SheafOfModules.unit (E.ringCatSheaf.over V)) :
    Ideal.span (Set.range fun φ : M.over V ⟶
        _root_.SheafOfModules.unit (E.ringCatSheaf.over V) =>
      (show ↑Γ(E, V) from φ.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))
        (show (M.over V).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from
          M.presheaf.map (homOfLE le_top).op σ))) =
    Ideal.span {(show ↑Γ(E, V) from
      t.hom.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))
      (show (M.over V).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from
        M.presheaf.map (homOfLE le_top).op σ))} := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro x ⟨φ, rfl⟩
    have hφ : φ = t.hom ≫ ModularCurves.SheafOfModules.overUnitScalarEnd
        E.ringCatSheaf V (ModularCurves.SheafOfModules.dualTrivializationLinearEquiv
          E.ringCatSheaf M V t φ) :=
      ((ModularCurves.SheafOfModules.dualTrivializationLinearEquiv
        E.ringCatSheaf M V t).symm_apply_apply φ).symm
    rw [hφ]
    exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
  · refine Ideal.span_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.subset_span ⟨t.hom, rfl⟩

/-- The vanishing ideal of a global section `σ` of a module `M`: over each affine open,
the ideal of values of local functionals against `σ` (the evaluation ideal). On a
trivialising open this is the principal ideal of the trivialised value of `σ`; the
basic-open compatibility is checked at maximal ideals through trivialising basic opens
(`Ideal.mem_of_localization_maximal` — board note 2026-08-08, no quasi-coherent
localization needed). -/
noncomputable def sectionVanishingIdeal {E : Scheme.{u}} (M : E.Modules)
    (hM : IsInvertible M) (σ : ↑Γ(M, ⊤)) :
    E.IdealSheafData where
  ideal U := Ideal.span (Set.range fun φ : M.over U.1 ⟶
      _root_.SheafOfModules.unit (E.ringCatSheaf.over U.1) =>
    (show ↑Γ(E, U.1) from φ.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1)))
      (show (M.over U.1).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1))) from
        M.presheaf.map (homOfLE le_top).op σ)))
  map_ideal_basicOpen U f := by
    rw [Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro x ⟨y, ⟨φ, rfl⟩, rfl⟩
      have hσ : (M.presheaf.map (homOfLE (E.basicOpen_le f)).op)
          ((M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op) σ) =
          (M.presheaf.map (homOfLE (le_top : (E.affineBasicOpen f).1 ≤ ⊤)).op) σ := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact congrArg (fun q ↦ (ConcreteCategory.hom (M.presheaf.map
          (Quiver.Hom.op q))) σ) (Subsingleton.elim _ _)
      have hnat := PresheafOfModules.naturality_apply φ.val
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE (E.basicOpen_le f)))).op
        (show (M.over U.1).val.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1))) from
          M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op σ)
      refine Ideal.subset_span ?_
      refine ⟨ModularCurves.SheafOfModules.dualRestrict E.ringCatSheaf M
        (show Opposite.op U.1 ⟶ Opposite.op (E.affineBasicOpen f).1 from
          (homOfLE (E.basicOpen_le f)).op) φ, ?_⟩
      simp only [ModularCurves.SheafOfModules.dualRestrict_app_apply]
      exact (congrArg (fun z ↦ φ.val.app (Opposite.op ((CategoryTheory.Over.map
        (homOfLE (E.basicOpen_le f))).obj
        (CategoryTheory.Over.mk (𝟙 (E.affineBasicOpen f).1)))) z) hσ.symm).trans hnat
    · refine Ideal.span_le.mpr ?_
      rintro x ⟨φ', rfl⟩
      obtain ⟨n, φ, hnφ⟩ := exists_dualRestrict_eq_pow_smul M hM U f φ'
      letI := ModularCurves.SheafOfModules.dualSectionsModule E.ringCatSheaf M
        (E.basicOpen f)
      -- evaluate the identity `dualRestrict φ = f^n • φ'`
      have hev := congrArg (fun ψ : M.over (E.basicOpen f) ⟶
          _root_.SheafOfModules.unit (E.ringCatSheaf.over (E.basicOpen f)) ↦
        ψ.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 (E.basicOpen f))))
          (show (M.over (E.basicOpen f)).val.obj
            (Opposite.op (CategoryTheory.Over.mk (𝟙 (E.basicOpen f)))) from
            M.presheaf.map (homOfLE le_top).op σ)) hnφ
      rw [eval_dualRestrict M σ (E.basicOpen_le f) φ,
        eval_smul M (E.basicOpen f) _ φ' _] at hev
      -- the restriction of `f` is a unit on its basic open, so the power divides out
      obtain ⟨w, hw⟩ := (IsUnit.pow n
        (E.toRingedSpace.isUnit_res_basicOpen f)).exists_right_inv
      have hrange : (show ↑Γ(E, U.1) from φ.val.app
          (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1)))
          (show (M.over U.1).val.obj
            (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1))) from
            M.presheaf.map (homOfLE le_top).op σ)) ∈
          Set.range (fun ψ : M.over U.1 ⟶
              _root_.SheafOfModules.unit (E.ringCatSheaf.over U.1) ↦
            (show ↑Γ(E, U.1) from ψ.val.app
              (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1)))
              (show (M.over U.1).val.obj
                (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1))) from
                M.presheaf.map (homOfLE le_top).op σ))) := ⟨φ, rfl⟩
      have hmem := Ideal.subset_span (Set.mem_image_of_mem
        (⇑(CommRingCat.Hom.hom (E.presheaf.map
          (homOfLE (E.basicOpen_le f)).op))) hrange)
      have heq := (congrArg (fun z ↦ z * w) hev).trans
        ((mul_assoc _ _ _).trans
          ((congrArg (fun z ↦ (show ↑Γ(E, E.basicOpen f) from φ'.val.app
            (Opposite.op (CategoryTheory.Over.mk (𝟙 (E.basicOpen f))))
            (show (M.over (E.basicOpen f)).val.obj
              (Opposite.op (CategoryTheory.Over.mk (𝟙 (E.basicOpen f)))) from
              M.presheaf.map (homOfLE le_top).op σ)) * z) hw).trans (mul_one _)))
      have hfinal := Ideal.mul_mem_left _ w hmem
      have heq2 := (mul_comm w _).trans heq
      rw [heq2] at hfinal
      exact hfinal

/-- **(`AP2-B2` + `AP2-B3` head, KM pp. 66–67)** Under the degree-one package, the pair
`(M, ℓ)` — for any base-local basis of the rank-one pushforward — cuts out a relative
effective Cartier divisor whose ideal is the `M`-inverse twist of the pushforward pullback:
`ℐ_D ≅ f^*(f_*M) ⊗ M⁻¹` (round-19 PIN 1: the twist is `(f_*M)`, never `(0^*M)`).

Existence-form packaging of KM's exact sequence `0 → O --ℓ--> M → M/O → 0` with `M/O`
`S`-flat: the divisor's subscheme-over-base carries the flatness, the ideal-module
isomorphism carries the exactness. -/
theorem exists_relEffCartierDiv_of_degreeOne
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E : Scheme.{u}} {π : E ⟶ Spec (.of R)} [IsProper π] [Flat π]
    [IsNoetherian E] [LocallyOfFinitePresentation π]
    (M : E.Modules) (hM : M.IsInvertible)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hpkg : HasDegreeOneFibreCohomology π M U) :
    ∃ D : RelEffCartierDiv π,
      Nonempty (AlgebraicGeometry.Scheme.Modules.idealModule D.ideal ≅
        tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
          ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj M))
          (dualObj M)) := by
  sorry

/-- **(`AP2-B3`, degree part, KM p. 67)** The evaluation divisor has fibre degree one:
"Looking fiber-by-fiber, we see that it is of degree one" — the fibre `h⁰` of the
degree-one package. -/
theorem relEffCartierDiv_degree_one_of_degreeOne
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E : Scheme.{u}} {π : E ⟶ Spec (.of R)} [IsProper π] [Flat π]
    [IsNoetherian E] [LocallyOfFinitePresentation π]
    (M : E.Modules) (hM : M.IsInvertible)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hpkg : HasDegreeOneFibreCohomology π M U)
    (D : RelEffCartierDiv π)
    (hD : Nonempty (AlgebraicGeometry.Scheme.Modules.idealModule D.ideal ≅
      tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj M))
        (dualObj M)))
    (s : Spec (.of R)) : D.degree s = 1 := by
  sorry

end ModularCurves
