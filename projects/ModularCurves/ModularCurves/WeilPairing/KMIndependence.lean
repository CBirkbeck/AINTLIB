/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMBilinear

/-!
# Independence of the Katz–Mazur pairing from the trivialisation dataset (AP-E1-IND)

`torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP` (`WeilPairing/KMUniqueness.lean`)
depends on a *dataset*: the invertible module `M` representing `κ(Q)`, the trivialising cover
`W`, the trivialisations `e` and the normalisation `hnorm`. The Yoneda step of AP-E1 needs the
value to depend on `(P, Q)` alone. This file proves that independence in four legs:

* `torsionSplittingEval_eq_of_transitionUnit_eq` (AP-E1-IND1) — same cover, equal cocycles ⟹
  equal values. The module `M` and the trivialisations enter `torsionSplittingEval` only
  through the transition cocycle, so this is the pin (`eq_torsionSplittingEval`) applied to a
  normalised splitting borrowed from the other dataset.
* refinement invariance (AP-E1-IND2) — restricting the dataset to a refinement of the cover
  does not change the value.
* normalised-coboundary invariance (AP-E1-IND3) — two normalised cocycles on one cover
  differing by the coboundary of units `c i` give the same value. The torsion of `P` is what
  kills the correction: `c i ∘ [N] ∘ P = c i ∘ 0`.
* transport along a module isomorphism (AP-E1-IND4) and the master statement (AP-E1-IND5):
  any two datasets for the same `Q` give the same value, via a common refinement.

## What is *not* used

Nothing here touches `exists_torsionPoint_of_mem_kerMulByN` (AP-D4 `⊇`), so no declaration
below inherits its `sorryAx`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-- Regrouping a coboundary correction in a commutative group: the two `g`-factors cancel.
Stated over abstract elements so the AC-normalisation runs on atoms, never on section terms. -/
private theorem mul_coboundary_regroup {G : Type*} [CommGroup G] (a a' b b' g : G) :
    a * a'⁻¹ * (b * b'⁻¹) = a * b * g⁻¹ * (a' * b' * g⁻¹)⁻¹ := by
  have hg : a * b * g⁻¹ * (a' * b' * g⁻¹)⁻¹ = a * b * ((a' * b')⁻¹ * (g⁻¹ * g)) := by
    rw [mul_inv (a' * b') g⁻¹, inv_inv]
    ac_rfl
  rw [hg, inv_mul_cancel, mul_one, mul_inv a' b']
  ac_rfl

/-- Evaluating along a morphism that *equals* a section whose value is pinned by a global
unit: the dependent transport (`z ⁻¹ᵁ V` changes with `z`) is discharged by `subst`. -/
private theorem sectionEval_eq_resUnit_of_eq {Y T : Scheme.{u}} {z z' : T ⟶ Y} (hzz : z = z')
    (V : Y.Opens) (u : Γ(Y, V)ˣ) {C : Γ(T, ⊤)ˣ}
    (hC : Scheme.resUnit (le_top : z' ⁻¹ᵁ V ≤ ⊤) C = sectionEval z' V u) :
    sectionEval z V u = Scheme.resUnit (le_top : z ⁻¹ᵁ V ≤ ⊤) C := by
  subst hzz; exact hC.symm

section General

variable {X : Scheme.{u}}

/-- Sections of the structure sheaf commute (the same local instance
`Picard/InvertibleSheafCocycle.lean` declares for the scalar-endomorphism ring equivalence). -/
local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- Two objects of `Over U` in the (thin) opens category agree once their underlying opens
do: the structure morphism is a subsingleton. Restriction of trivialisations along
`Over`-objects is therefore insensitive to how the `≤`-path was assembled. -/
private theorem over_opens_ext {U : X.Opens} {A B : Over U} (h : A.left = B.left) : A = B := by
  obtain ⟨Al, ⟨⟨⟩⟩, Ah⟩ := A
  obtain ⟨Bl, ⟨⟨⟩⟩, Bh⟩ := B
  obtain rfl : Al = Bl := h
  obtain rfl : Ah = Bh := Subsingleton.elim _ _
  rfl

/-- Restricting a trivialisation in two stages depends only on the endpoints, not on the
intermediate open: both composites collapse to a single restriction
(`restrictOverTrivialization_comp`) along `Over`-objects that agree by thinness
(`over_opens_ext`), and the `HEq`-transport keeps the dependent motive well-typed. -/
private theorem restrictOverTrivialization_comp_eq {V₁ V₂ V₃ U : X.Opens} (M : X.Modules)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (h₁ : V₃ ≤ V₁) (h₂ : V₁ ≤ U) (h₃ : V₃ ≤ V₂) (h₄ : V₂ ≤ U) :
    SheafOfModules.restrictOverTrivialization X.ringCatSheaf M V₁
        (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE h₂)))
        (Over.mk (homOfLE h₁)) =
      SheafOfModules.restrictOverTrivialization X.ringCatSheaf M V₂
        (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE h₄)))
        (Over.mk (homOfLE h₃)) := by
  refine (SheafOfModules.restrictOverTrivialization_comp X.ringCatSheaf M U e
      (Over.mk (homOfLE h₂)) (Over.mk (homOfLE h₁))).trans
    (Eq.trans ?_ (SheafOfModules.restrictOverTrivialization_comp X.ringCatSheaf M U e
      (Over.mk (homOfLE h₄)) (Over.mk (homOfLE h₃))).symm)
  have hobj : (Over.map (Over.mk (homOfLE h₂)).hom).obj (Over.mk (homOfLE h₁)) =
      (Over.map (Over.mk (homOfLE h₄)).hom).obj (Over.mk (homOfLE h₃)) :=
    over_opens_ext rfl
  exact eq_of_heq (Eq.rec (motive := fun B _ =>
      HEq (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          ((Over.map (Over.mk (homOfLE h₂)).hom).obj (Over.mk (homOfLE h₁))))
        (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e B))
    HEq.rfl hobj)

/-- **(AP-E1-IND2, cocycle half)** Restricting a trivialisation family along a refinement of
the cover restricts the transition cocycle: for `r : ι' → ι` and `V a ≤ W (r a)`,

  `f'_{a,b} = f_{r a, r b} |_{V a ⊓ V b}`.

Both sides are `trivializationTransitionUnit`s of two-stage restrictions of `e (r a)`,
`e (r b)`, which agree by `restrictOverTrivialization_comp_eq`. -/
theorem transitionUnitOfCover_restrict (M : X.Modules) {ι ι' : Type*}
    (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)))
    (r : ι' → ι) (V : ι' → X.Opens) (hle : ∀ a, V a ≤ W (r a)) (a b : ι') :
    transitionUnitOfCover M V
        (fun a => SheafOfModules.restrictOverTrivialization
          X.ringCatSheaf M (W (r a)) (e (r a)) (Over.mk (homOfLE (hle a)))) a b =
      Scheme.resUnit (inf_le_inf (hle a) (hle b)) (transitionUnitOfCover M W e (r a) (r b)) := by
  have hrestr := trivializationTransitionUnit_restrict
    (M := M) (inf_le_inf (hle a) (hle b))
    (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W (r a)) (e (r a))
      (Over.mk (homOfLE (inf_le_left : W (r a) ⊓ W (r b) ≤ W (r a)))))
    (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W (r b)) (e (r b))
      (Over.mk (homOfLE (inf_le_right : W (r a) ⊓ W (r b) ≤ W (r b)))))
  refine Eq.trans (congrArg₂ (trivializationTransitionUnit (V a ⊓ V b)) ?_ ?_) hrestr
  · exact restrictOverTrivialization_comp_eq M (e (r a))
      (inf_le_left : V a ⊓ V b ≤ V a) (hle a)
      (inf_le_inf (hle a) (hle b)) (inf_le_left : W (r a) ⊓ W (r b) ≤ W (r a))
  · exact restrictOverTrivialization_comp_eq M (e (r b))
      (inf_le_right : V a ⊓ V b ≤ V b) (hle b)
      (inf_le_inf (hle a) (hle b)) (inf_le_right : W (r a) ⊓ W (r b) ≤ W (r b))

/-- Normalisation of the cocycle along a section survives restriction to a refined cover. -/
theorem transitionUnitOfCover_restrict_mem_sectionUnits {T : Scheme.{u}} (M : X.Modules)
    {ι ι' : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)))
    {z : T ⟶ X}
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈ sectionUnits z (W i ⊓ W j))
    (r : ι' → ι) (V : ι' → X.Opens) (hle : ∀ a, V a ≤ W (r a)) (a b : ι') :
    transitionUnitOfCover M V
        (fun a => SheafOfModules.restrictOverTrivialization
          X.ringCatSheaf M (W (r a)) (e (r a)) (Over.mk (homOfLE (hle a)))) a b ∈
      sectionUnits z (V a ⊓ V b) := by
  rw [mem_sectionUnits_iff, transitionUnitOfCover_restrict M W e r V hle a b,
    sectionEval_resUnit]
  rw [show sectionEval z (W (r a) ⊓ W (r b)) (transitionUnitOfCover M W e (r a) (r b)) = 1
    from hnorm (r a) (r b)]
  exact map_one _

/-- The transition unit between two trivialisations is invariant under pre-composition with
a common isomorphism: the `ψ`-factors cancel in `(ψ ≪≫ a).inv ≫ (ψ ≪≫ b).hom`. -/
theorem trivializationTransitionUnit_iso_trans {M M' : X.Modules} (U : X.Opens)
    (ψ : M.over U ≅ M'.over U)
    (a b : M'.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    trivializationTransitionUnit U (ψ ≪≫ a) (ψ ≪≫ b) =
      trivializationTransitionUnit U a b := by
  apply Units.ext
  let E := ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv X.ringCatSheaf U
  apply E.injective
  have h1 : E (trivializationTransitionUnit U (ψ ≪≫ a) (ψ ≪≫ b) : Γ(X, U)) =
      (ψ ≪≫ a).inv ≫ (ψ ≪≫ b).hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U (ψ ≪≫ a) (ψ ≪≫ b)
  have h2 : E (trivializationTransitionUnit U a b : Γ(X, U)) = a.inv ≫ b.hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U a b
  rw [h1, h2, Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- **(AP-E1-IND4, restriction half)** `restrictOverTrivialization` is natural in the module:
restricting the `φ`-transported trivialisation is transporting the restricted one. -/
theorem restrictOverTrivialization_map_iso {M M' : X.Modules} (φ : M ≅ M') (U : X.Opens)
    (e : M'.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) (V : Over U) :
    SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
        ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).mapIso φ ≪≫ e) V =
      (_root_.SheafOfModules.overFunctor X.ringCatSheaf V.left).mapIso φ ≪≫
        SheafOfModules.restrictOverTrivialization X.ringCatSheaf M' U e V := by
  apply Iso.ext
  have key : ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M).inv ≫
      (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map
        ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map φ.hom) =
      (_root_.SheafOfModules.overFunctor X.ringCatSheaf V.left).map φ.hom ≫
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M').inv :=
    ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).inv.naturality φ.hom).symm
  show ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M).inv ≫
      (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map
        ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map φ.hom ≫ e.hom) ≫
      (_root_.SheafOfModules.overMapUnitIso V.hom).hom =
    (_root_.SheafOfModules.overFunctor X.ringCatSheaf V.left).map φ.hom ≫
      ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M').inv ≫
      (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map e.hom ≫
      (_root_.SheafOfModules.overMapUnitIso V.hom).hom
  rw [Functor.map_comp]
  calc ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M).inv ≫
        ((_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map
          ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map φ.hom) ≫
        (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map e.hom) ≫
        (_root_.SheafOfModules.overMapUnitIso V.hom).hom
      = (((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M).inv ≫
          (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map
            ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map φ.hom)) ≫
          (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map e.hom ≫
          (_root_.SheafOfModules.overMapUnitIso V.hom).hom := by
        simp only [Category.assoc]
    _ = ((_root_.SheafOfModules.overFunctor X.ringCatSheaf V.left).map φ.hom ≫
          ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M').inv) ≫
          (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).map e.hom ≫
          (_root_.SheafOfModules.overMapUnitIso V.hom).hom := by rw [key]
    _ = _ := by simp only [Category.assoc]

/-- **Two trivialisation families of one module differ by a coboundary**: the comparison
units `c i := trivializationTransitionUnit (W i) (a i) (b i)` satisfy

  `f^a_{i,j} = f^b_{i,j} · (c_i |_{W i ⊓ W j}) · (c_j |_{W i ⊓ W j})⁻¹`.

This is the cocycle algebra `ttu(aᵢ,aⱼ) = ttu(aᵢ,bᵢ)·ttu(bᵢ,bⱼ)·ttu(bⱼ,aⱼ)` (two applications
of `trivializationTransitionUnit_trans`), with the outer factors read as restrictions of the
`c`'s (`trivializationTransitionUnit_restrict`, `_symm`). -/
theorem transitionUnitOfCover_eq_mul_coboundary (M : X.Modules) {ι : Type*}
    (W : ι → X.Opens)
    (a b : ∀ i, M.over (W i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)))
    (i j : ι) :
    transitionUnitOfCover M W a i j = transitionUnitOfCover M W b i j *
      (Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i)
          (trivializationTransitionUnit (W i) (a i) (b i)) *
        (Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j)
          (trivializationTransitionUnit (W j) (a j) (b j)))⁻¹) := by
  set rai := SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (a i)
    (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))) with hrai
  set raj := SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (a j)
    (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))) with hraj
  set rbi := SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (b i)
    (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))) with hrbi
  set rbj := SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (b j)
    (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))) with hrbj
  have h1 : trivializationTransitionUnit (W i ⊓ W j) rai rbi *
      trivializationTransitionUnit (W i ⊓ W j) rbi raj =
      trivializationTransitionUnit (W i ⊓ W j) rai raj :=
    trivializationTransitionUnit_trans (W i ⊓ W j) rai rbi raj
  have h2 : trivializationTransitionUnit (W i ⊓ W j) rbi rbj *
      trivializationTransitionUnit (W i ⊓ W j) rbj raj =
      trivializationTransitionUnit (W i ⊓ W j) rbi raj :=
    trivializationTransitionUnit_trans (W i ⊓ W j) rbi rbj raj
  have hsym : trivializationTransitionUnit (W i ⊓ W j) rbj raj =
      (trivializationTransitionUnit (W i ⊓ W j) raj rbj)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      (trivializationTransitionUnit_symm (W i ⊓ W j) raj rbj)
  have hresi : trivializationTransitionUnit (W i ⊓ W j) rai rbi =
      Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i)
        (trivializationTransitionUnit (W i) (a i) (b i)) :=
    trivializationTransitionUnit_restrict (inf_le_left : W i ⊓ W j ≤ W i) (a i) (b i)
  have hresj : trivializationTransitionUnit (W i ⊓ W j) raj rbj =
      Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j)
        (trivializationTransitionUnit (W j) (a j) (b j)) :=
    trivializationTransitionUnit_restrict (inf_le_right : W i ⊓ W j ≤ W j) (a j) (b j)
  show trivializationTransitionUnit (W i ⊓ W j) rai raj =
    trivializationTransitionUnit (W i ⊓ W j) rbi rbj * _
  rw [← h1, ← h2, hsym, hresi, hresj]
  ac_rfl

/-- **(AP-E1-IND4)** Transporting the trivialisation family along a module isomorphism
`φ : M ≅ M'` leaves the transition cocycle unchanged. -/
theorem transitionUnitOfCover_map_iso {M M' : X.Modules} (φ : M ≅ M') {ι : Type*}
    (W : ι → X.Opens)
    (e' : ∀ i, M'.over (W i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)))
    (i j : ι) :
    transitionUnitOfCover M W
        (fun i => (_root_.SheafOfModules.overFunctor X.ringCatSheaf (W i)).mapIso φ ≪≫
          e' i) i j =
      transitionUnitOfCover M' W e' i j := by
  show trivializationTransitionUnit (W i ⊓ W j) _ _ = trivializationTransitionUnit _ _ _
  rw [restrictOverTrivialization_map_iso φ (W i) (e' i)
      (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))),
    restrictOverTrivialization_map_iso φ (W j) (e' j)
      (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)))]
  exact trivializationTransitionUnit_iso_trans (W i ⊓ W j) _ _ _

end General

section Curve

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)
variable (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)

/-- **(AP-E1-IND1)** `torsionSplittingEval` depends on the dataset only through the transition
cocycle: two datasets for the same torsion section `Q`, over the same cover, with equal
transition units, give the same value at every `P`.

`M` and `e` enter the construction only through `transitionUnitOfCover M W e`; a normalised
splitting of the pulled-back cocycle borrowed from the first dataset is one for the second, and
the pin `eq_torsionSplittingEval` identifies the two values. -/
theorem torsionSplittingEval_eq_of_transitionUnit_eq
    (M M' : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    (hM' : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M')
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (e' : ∀ i, M'.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (hnorm' : ∀ i j, transitionUnitOfCover M' W e' i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (heq : ∀ i j, transitionUnitOfCover M W e i j = transitionUnitOfCover M' W e' i j)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) :
    torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP =
      torsionSplittingEval E hsm t N Q hQ M' hM' W hW e' hnorm' P hP := by
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm
  exact eq_torsionSplittingEval E hsm t N Q hQ M' hM' W hW e' hnorm' P hP h hn
    (fun i j => heq i j ▸ hsplit i j)
    (fun i => resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP h hn hsplit i)

/-- **(AP-E1-IND2)** Refinement invariance: computing `h(P)` from the dataset restricted to a
refinement `V` of the cover `W` (along `r : ι' → ι` with `V a ≤ W (r a)`) gives the same value.

The normalised splitting units over `W` restrict to normalised splitting units over `V`
(`Scheme.resUnit` along `[N]⁻¹`-preimages), the cocycles match by
`transitionUnitOfCover_restrict`, and the pin `eq_torsionSplittingEval` on the `V`-side
identifies the `W`-side value. The normalisation hypothesis `hnorm'` of the restricted dataset
is proof-irrelevant data — `transitionUnitOfCover_restrict_mem_sectionUnits` discharges it at
any call site. -/
theorem torsionSplittingEval_restrict_cover
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι ι' : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (r : ι' → ι) (V : ι' → (pullback E.π t).Opens) (hV : iSup V = ⊤)
    (hle : ∀ a, V a ≤ W (r a))
    (hnorm' : ∀ a b, transitionUnitOfCover M V
        (fun a => SheafOfModules.restrictOverTrivialization
          (pullback E.π t).ringCatSheaf M (W (r a)) (e (r a))
          (Over.mk (homOfLE (hle a)))) a b ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (V a ⊓ V b))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) :
    torsionSplittingEval E hsm t N Q hQ M hM V hV
        (fun a => SheafOfModules.restrictOverTrivialization
          (pullback E.π t).ringCatSheaf M (W (r a)) (e (r a))
          (Over.mk (homOfLE (hle a)))) hnorm' P hP =
      torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP := by
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm
  -- the restricted splitting units
  refine (eq_torsionSplittingEval E hsm t N Q hQ M hM V hV _ hnorm' P hP
    (fun a => Scheme.resUnit ((mulByN E t N).preimage_mono (hle a)) (h (r a)))
    (fun a => ?_) (fun a b => ?_) (fun a => ?_)).symm
  · -- normalisation restricts
    rw [mem_sectionUnits_iff, sectionEval_resUnit]
    rw [show sectionEval (baseChangeZero E.π E.zero E.zero_π t)
        (mulByN E t N ⁻¹ᵁ W (r a)) (h (r a)) = 1 from hn (r a)]
    exact map_one _
  · -- the splitting identity restricts
    refine (congrArg (Units.map ((mulByN E t N).app (V a ⊓ V b)).hom.toMonoidHom)
        (transitionUnitOfCover_restrict M W e r V hle a b)).trans ?_
    refine ((resUnit_map_app (mulByN E t N) (inf_le_inf (hle a) (hle b))
        (transitionUnitOfCover M W e (r a) (r b))).symm).trans ?_
    refine (congrArg (Scheme.resUnit ((mulByN E t N).preimage_mono
        (inf_le_inf (hle a) (hle b)))) (hsplit (r a) (r b))).trans ?_
    refine (map_mul _ _ _).trans ?_
    refine (congrArg (Scheme.resUnit ((mulByN E t N).preimage_mono
        (inf_le_inf (hle a) (hle b))) (Scheme.resUnit
          (inf_le_left : mulByN E t N ⁻¹ᵁ W (r a) ⊓ mulByN E t N ⁻¹ᵁ W (r b) ≤
            mulByN E t N ⁻¹ᵁ W (r a)) (h (r a))) * ·)
        (map_inv _ _)).trans ?_
    exact congrArg₂ (fun x y => x * y⁻¹)
      ((Scheme.resUnit_resUnit _ _ _).trans (Scheme.resUnit_resUnit _ _ _).symm)
      ((Scheme.resUnit_resUnit _ _ _).trans (Scheme.resUnit_resUnit _ _ _).symm)
  · -- the glued value restricts
    have hspec := resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP h hn
      hsplit (r a)
    refine Eq.trans ?_ ((sectionEval_resUnit (P.1 : T ⟶ pullback E.π t)
      ((mulByN E t N).preimage_mono (hle a)) (h (r a))).symm)
    refine Eq.trans ?_ (congrArg (Scheme.resUnit
      ((P.1 : T ⟶ pullback E.π t).preimage_mono
        ((mulByN E t N).preimage_mono (hle a)))) hspec)
    exact (Scheme.resUnit_resUnit _ _ _).symm

/-- **(AP-E1-IND3)** Normalised-coboundary invariance: two datasets for the same torsion
section `Q`, over the same cover, whose cocycles differ by the coboundary of units
`c i ∈ Γ(W i)ˣ`, give the same value at every `N`-torsion `P`.

The zero-section values `γ i := c i ∘ 0` agree on overlaps — both cocycles are normalised, so
the coboundary is too — and glue to a global unit `γ` of the base. If `h` is a normalised
splitting for the first dataset, then `h_i · (c_i ∘ [N]) · (π^# γ)⁻¹` is one for the second:
it splits because the `π^# γ` factors cancel in ratios (`resUnit_globalTwist`), and it is
normalised because `c_i ∘ [N] ∘ 0 = c_i ∘ 0` reads off `γ` (`zero_comp_mulByHom_baseChange`).
Evaluating at `P` kills the correction outright: `c_i ∘ [N] ∘ P = c_i ∘ 0` **because `P` is
`N`-torsion** (`comp_mulByN_eq_baseChangeZero`), and `π^# γ ∘ P = γ` because `P` is a section
— so the value along `P` is the first dataset's, and the pin closes. -/
theorem torsionSplittingEval_eq_of_mul_coboundary
    (M M' : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    (hM' : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M')
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (e' : ∀ i, M'.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (hnorm' : ∀ i j, transitionUnitOfCover M' W e' i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (c : ∀ i, Γ(pullback E.π t, W i)ˣ)
    (hco : ∀ i j, transitionUnitOfCover M' W e' i j =
      transitionUnitOfCover M W e i j *
        (Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i) (c i) *
          (Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j) (c j))⁻¹))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) :
    torsionSplittingEval E hsm t N Q hQ M' hM' W hW e' hnorm' P hP =
      torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP := by
  -- the zero-section values of the `c i` agree on overlaps and glue to a global unit `γ`
  have hzero : ∀ i j,
      Scheme.resUnit ((baseChangeZero E.π E.zero E.zero_π t).preimage_mono
          (inf_le_left : W i ⊓ W j ≤ W i))
        (sectionEval (baseChangeZero E.π E.zero E.zero_π t) (W i) (c i)) =
      Scheme.resUnit ((baseChangeZero E.π E.zero E.zero_π t).preimage_mono
          (inf_le_right : W i ⊓ W j ≤ W j))
        (sectionEval (baseChangeZero E.π E.zero E.zero_π t) (W j) (c j)) := by
    intro i j
    have h1 : sectionEval (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)
        (transitionUnitOfCover M' W e' i j) = 1 := hnorm' i j
    rw [hco i j, map_mul, map_mul, map_inv,
      show sectionEval (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)
        (transitionUnitOfCover M W e i j) = 1 from hnorm i j, one_mul,
      sectionEval_resUnit, sectionEval_resUnit] at h1
    exact (mul_inv_eq_one.mp h1)
  obtain ⟨γ, hγ⟩ := exists_globalUnit_restrict
    (fun i => baseChangeZero E.π E.zero E.zero_π t ⁻¹ᵁ W i)
    ((baseChangeZero E.π E.zero E.zero_π t).iSup_preimage_eq_top hW)
    (fun i => sectionEval (baseChangeZero E.π E.zero E.zero_π t) (W i) (c i))
    hzero
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm
  -- the corrected splitting `h_i · (c_i ∘ [N]) · (π^# γ)⁻¹` for the second dataset
  refine (eq_torsionSplittingEval E hsm t N Q hQ M' hM' W hW e' hnorm' P hP
    (fun i => h i * Units.map ((mulByN E t N).app (W i)).hom.toMonoidHom (c i) *
      (globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W i) γ)⁻¹)
    (fun i => ?_) (fun i j => ?_) (fun i => ?_)).symm
  · -- normalised: `h_i ∘ 0 = 1`, `c_i ∘ [N] ∘ 0 = γ`, `π^# γ ∘ 0 = γ`
    have hEcN : sectionEval (baseChangeZero E.π E.zero E.zero_π t) (mulByN E t N ⁻¹ᵁ W i)
        (Units.map ((mulByN E t N).app (W i)).hom.toMonoidHom (c i)) =
        Scheme.resUnit (le_top : (baseChangeZero E.π E.zero E.zero_π t ≫ mulByN E t N) ⁻¹ᵁ
          W i ≤ ⊤) γ :=
      (sectionEval_pullback (mulByN E t N) (baseChangeZero E.π E.zero E.zero_π t) (W i)
        (c i)).trans
        (sectionEval_eq_resUnit_of_eq (zero_comp_mulByHom_baseChange E t (N : ℤ)) (W i) (c i)
          (hγ i))
    rw [mem_sectionUnits_iff, map_mul, map_mul, map_inv,
      show sectionEval (baseChangeZero E.π E.zero E.zero_π t) (mulByN E t N ⁻¹ᵁ W i) (h i) = 1
        from hn i, one_mul,
      sectionEval_globalTwist (baseChangeZero_snd E.π E.zero E.zero_π t)]
    exact mul_inv_eq_one.mpr hEcN
  · -- splits the second cocycle: the `π^# γ` factors cancel in the ratio
    have hmapco := congrArg
      (Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom) (hco i j)
    rw [map_mul, map_mul, map_inv] at hmapco
    refine hmapco.trans ?_
    have hci : Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i) (c i)) =
        Scheme.resUnit ((mulByN E t N).preimage_mono (inf_le_left : W i ⊓ W j ≤ W i))
          (Units.map ((mulByN E t N).app (W i)).hom.toMonoidHom (c i)) :=
      (resUnit_map_app (mulByN E t N) (inf_le_left : W i ⊓ W j ≤ W i) (c i)).symm
    have hcj : Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j) (c j)) =
        Scheme.resUnit ((mulByN E t N).preimage_mono (inf_le_right : W i ⊓ W j ≤ W j))
          (Units.map ((mulByN E t N).app (W j)).hom.toMonoidHom (c j)) :=
      (resUnit_map_app (mulByN E t N) (inf_le_right : W i ⊓ W j ≤ W j) (c j)).symm
    rw [hsplit i j, hci, hcj, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
      show Scheme.resUnit (inf_le_left : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W i)
        (globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W i) γ) =
        globalTwist (pullback.snd E.π t)
          (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j) γ from
        resUnit_globalTwist (pullback.snd E.π t) _ γ,
      show Scheme.resUnit (inf_le_right : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W j)
        (globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W j) γ) =
        globalTwist (pullback.snd E.π t)
          (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j) γ from
        resUnit_globalTwist (pullback.snd E.π t) _ γ]
    exact mul_coboundary_regroup _ _ _ _ _
  · -- the value at `P` sees no correction: `[N]P = 0` and `π ∘ P = 𝟙`
    have hspec := resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP h hn
      hsplit i
    have hPcN : sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i)
        (Units.map ((mulByN E t N).app (W i)).hom.toMonoidHom (c i)) =
        Scheme.resUnit (le_top : ((P.1 : T ⟶ pullback E.π t) ≫ mulByN E t N) ⁻¹ᵁ W i ≤ ⊤)
          γ :=
      (sectionEval_pullback (mulByN E t N) (P.1 : T ⟶ pullback E.π t) (W i) (c i)).trans
        (sectionEval_eq_resUnit_of_eq (comp_mulByN_eq_baseChangeZero E t N P hP) (W i) (c i)
          (hγ i))
    have hPγ : sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i)
        (globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W i) γ) =
        Scheme.resUnit (le_top : (P.1 : T ⟶ pullback E.π t) ⁻¹ᵁ
          (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤) γ :=
      sectionEval_globalTwist P.2 (mulByN E t N ⁻¹ᵁ W i) γ
    have hsplit3 : sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i)
        (h i * Units.map ((mulByN E t N).app (W i)).hom.toMonoidHom (c i) *
          (globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W i) γ)⁻¹) =
        sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i) *
          sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i)
            (Units.map ((mulByN E t N).app (W i)).hom.toMonoidHom (c i)) *
          (sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i)
            (globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W i) γ))⁻¹ :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (map_mul _ _ _) (map_inv _ _))
    refine hspec.trans (Eq.trans ?_ hsplit3.symm)
    rw [hPcN, hPγ]
    exact (mul_inv_cancel_right _ _).symm

/-- **(AP-E1-IND5, the master independence)** Any two full datasets — module representing
`κ(Q)`, trivialising cover, trivialisations, normalisation — compute the same
`torsionSplittingEval` at every `N`-torsion `P`. This is what makes KM's `h(P)` a function
of `(P, Q)` alone, the prerequisite for the Yoneda step of AP-E1.

Chain: refine both covers to `V (i,j) := W i ⊓ W' j` (IND2 twice); transport `e'` along the
isomorphism `M ≅ M'` supplied by the common skeleton class (IND4 + IND1); the two remaining
families trivialise the *same* module over the *same* cover, so they differ by the coboundary
of their comparison units (`transitionUnitOfCover_eq_mul_coboundary`) and IND3 closes. -/
theorem torsionSplittingEval_congr_dataset
    (M M' : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    (hM' : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M')
    {ι ι' : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (W' : ι' → (pullback E.π t).Opens) (hW' : iSup W' = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (e' : ∀ i, M'.over (W' i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W' i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (hnorm' : ∀ i j, transitionUnitOfCover M' W' e' i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W' i ⊓ W' j))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) :
    torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP =
      torsionSplittingEval E hsm t N Q hQ M' hM' W' hW' e' hnorm' P hP := by
  -- the isomorphism between the two representing modules
  obtain ⟨φ⟩ := toSkeleton_eq_toSkeleton_iff.mp (hM.symm.trans hM')
  -- the common refinement
  set V : ι × ι' → (pullback E.π t).Opens := fun p => W p.1 ⊓ W' p.2 with hVdef
  have hV : iSup V = ⊤ := by
    rw [hVdef, iSup_prod]
    have hstep : ∀ i, ⨆ j, (W i ⊓ W' j) = W i ⊓ ⨆ j, W' j := fun i =>
      (inf_iSup_eq _ _).symm
    calc ⨆ i, ⨆ j, (W i ⊓ W' j) = ⨆ i, (W i ⊓ ⨆ j, W' j) := iSup_congr hstep
      _ = ⊤ := by rw [hW']; simp only [inf_top_eq]; exact hW
  have hle₁ : ∀ p : ι × ι', V p ≤ W p.1 := fun p => inf_le_left
  have hle₂ : ∀ p : ι × ι', V p ≤ W' p.2 := fun p => inf_le_right
  -- the two restricted families over `V`
  set eV : ∀ p : ι × ι', M.over (V p) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (V p)) :=
    fun p => SheafOfModules.restrictOverTrivialization
      (pullback E.π t).ringCatSheaf M (W p.1) (e p.1) (Over.mk (homOfLE (hle₁ p))) with heV
  set e'V : ∀ p : ι × ι', M'.over (V p) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (V p)) :=
    fun p => SheafOfModules.restrictOverTrivialization
      (pullback E.π t).ringCatSheaf M' (W' p.2) (e' p.2) (Over.mk (homOfLE (hle₂ p))) with he'V
  have hnormV : ∀ a b, transitionUnitOfCover M V eV a b ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (V a ⊓ V b) := fun a b =>
    transitionUnitOfCover_restrict_mem_sectionUnits M W e hnorm Prod.fst V hle₁ a b
  have hnorm'V : ∀ a b, transitionUnitOfCover M' V e'V a b ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (V a ⊓ V b) := fun a b =>
    transitionUnitOfCover_restrict_mem_sectionUnits M' W' e' hnorm' Prod.snd V hle₂ a b
  -- the `φ`-transported family trivialises `M` with `e'V`'s cocycle
  set eφ : ∀ p : ι × ι', M.over (V p) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (V p)) :=
    fun p => (_root_.SheafOfModules.overFunctor (pullback E.π t).ringCatSheaf
      (V p)).mapIso φ ≪≫ e'V p with heφ
  have hcoφ : ∀ a b, transitionUnitOfCover M V eφ a b =
      transitionUnitOfCover M' V e'V a b := fun a b =>
    transitionUnitOfCover_map_iso φ V e'V a b
  have hnormφ : ∀ a b, transitionUnitOfCover M V eφ a b ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (V a ⊓ V b) := fun a b =>
    (hcoφ a b).symm ▸ hnorm'V a b
  -- chain the four equalities
  calc torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP
      = torsionSplittingEval E hsm t N Q hQ M hM V hV eV hnormV P hP :=
        (torsionSplittingEval_restrict_cover E hsm t N Q hQ M hM W hW e hnorm Prod.fst V hV
          hle₁ hnormV P hP).symm
    _ = torsionSplittingEval E hsm t N Q hQ M hM V hV eφ hnormφ P hP :=
        (torsionSplittingEval_eq_of_mul_coboundary E hsm t N Q hQ M M hM hM V hV eV eφ
          hnormV hnormφ
          (fun p => trivializationTransitionUnit (V p) (eφ p) (eV p))
          (fun a b => (transitionUnitOfCover_eq_mul_coboundary M V eφ eV a b))
          P hP).symm
    _ = torsionSplittingEval E hsm t N Q hQ M' hM' V hV e'V hnorm'V P hP :=
        torsionSplittingEval_eq_of_transitionUnit_eq E hsm t N Q hQ M M' hM hM' V hV eφ e'V
          hnormφ hnorm'V hcoφ P hP
    _ = torsionSplittingEval E hsm t N Q hQ M' hM' W' hW' e' hnorm' P hP :=
        torsionSplittingEval_restrict_cover E hsm t N Q hQ M' hM' W' hW' e' hnorm' Prod.snd
          V hV hle₂ hnorm'V P hP

end Curve

end ModularCurves
