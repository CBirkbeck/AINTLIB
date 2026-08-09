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

section General

variable {X : Scheme.{u}}

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

end Curve

end ModularCurves
