/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldLeaf

/-!
# The glue dataset ([G2])

`exists_normalized_chart_dataset`: the zero-section–normalized dataset built from the
common-principal chart family, with transitions **dressed by the generator ratios** on
every overlap. This is `exists_normalized_dataset` (KMDataset) replayed with the
`[G1]` chart family in place of the invertibility choice, tracking the transition
formula through the normalisation's refine-and-rescale.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

private theorem overUnitScalarIso_one {Y : Scheme.{u}} (U : Y.Opens) :
    overUnitScalarIso U (1 : Γ(Y, U)ˣ) =
      Iso.refl (_root_.SheafOfModules.unit (Y.ringCatSheaf.over U)) := by
  letI : ∀ (Z : (TopologicalSpace.Opens ↥Y)ᵒᵖ),
      IsMulCommutative (Y.ringCatSheaf.obj.obj Z) := fun Z => by
    change IsMulCommutative (Y.presheaf.obj Z)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩
  apply Iso.ext
  show SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U ((1 : Γ(Y, U)ˣ) : Γ(Y, U)) =
    𝟙 _
  exact ((SheafOfModules.overUnitScalarEndRingHom
    Y.ringCatSheaf U).map_one).trans End.one_def

private theorem mul_inv_mul_inv_cancel' {G : Type*} [CommGroup G] (a b : G) :
    a * b⁻¹ * a⁻¹ * b = 1 := by
  rw [show a * b⁻¹ * a⁻¹ * b = (a * a⁻¹) * (b⁻¹ * b) from by ac_rfl,
    mul_inv_cancel, inv_mul_cancel, one_mul]

private theorem sectionEval_id' {Y : Scheme.{u}} (U : Y.Opens) (u : Γ(Y, U)ˣ) :
    sectionEval (𝟙 Y) U u = u :=
  Units.ext rfl

private theorem sections_subsingleton_of_le_bot' {Y : Scheme.{u}} {V : Y.Opens}
    (hV : V ≤ ⊥) : Subsingleton Γ(Y, V) := by
  obtain rfl : V = ⊥ := le_bot_iff.mp hV
  infer_instance

/-- **([G2] the normalized chart dataset)** From a `κ(Q)`-presentation `M` with a
tensor-ideal dictionary and common-principal covers for both ideals, there is a
zero-section–normalized trivialisation dataset for `M` whose transitions on every
inhabited overlap are the generator-ratio units up to overlap-unit dressing, with the
generator data exposed at the charts. -/
theorem exists_normalized_chart_dataset
    (Q : (E.baseChange t).Point (𝟙 T)) (M : (CategoryTheory.Limits.pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (CategoryTheory.Limits.pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    [AlgebraicGeometry.IsIntegral (CategoryTheory.Limits.pullback E.π t)]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from (CategoryTheory.Limits.pullback E.π t)))]
    (J₁ J₂ : (CategoryTheory.Limits.pullback E.π t).IdealSheafData)
    (e_dict : M.tensorObj (Scheme.Modules.idealModule J₁) ≅ Scheme.Modules.idealModule J₂)
    (h₁ : ∀ c : ↥(CategoryTheory.Limits.pullback E.π t), ∃ V : (CategoryTheory.Limits.pullback E.π t).affineOpens,
      c ∈ V.1 ∧ ∃ f : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1))),
      J₁.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1))))
    (h₂ : ∀ c : ↥(CategoryTheory.Limits.pullback E.π t), ∃ V : (CategoryTheory.Limits.pullback E.π t).affineOpens,
      c ∈ V.1 ∧ ∃ f : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1))),
      J₂.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1)))) :
    ∃ (V : ↥(CategoryTheory.Limits.pullback E.π t) → (CategoryTheory.Limits.pullback E.π t).affineOpens)
      (f₁ f₂ : ∀ c, ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1))))
      (ι' : Type u) (W : ι' → (CategoryTheory.Limits.pullback E.π t).Opens) (_ : iSup W = ⊤)
      (e : ∀ i, M.over (W i) ≅
        _root_.SheafOfModules.unit ((CategoryTheory.Limits.pullback E.π t).ringCatSheaf.over (W i))),
      (∀ c, J₁.ideal (V c) = Ideal.span {f₁ c}) ∧
      (∀ c, f₁ c ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1)))) ∧
      (∀ c, J₂.ideal (V c) = Ideal.span {f₂ c}) ∧
      (∀ c, f₂ c ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1)))) ∧
      (∀ i j, transitionUnitOfCover M W e i j ∈
        sectionUnits (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)) ∧
      (∀ i j, Nonempty ↥((W i ⊓ W j) : (CategoryTheory.Limits.pullback E.π t).Opens) →
        ∃ (c d : ↥(CategoryTheory.Limits.pullback E.π t)) (hWc : W i ≤ (V c).1) (hWd : W j ≤ (V d).1)
          (a b u₁ u₂ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j)))ˣ),
          transitionUnitOfCover M W e i j = a * (u₂ * u₁⁻¹) * b⁻¹ ∧
          (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_left).trans hWc : W i ⊓ W j ≤ (V c).1)).op (f₁ c) =
            (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_right).trans hWd : W i ⊓ W j ≤ (V d).1)).op (f₁ d) *
              (u₁ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j)))) ∧
          (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_left).trans hWc : W i ⊓ W j ≤ (V c).1)).op (f₂ c) =
            (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_right).trans hWd : W i ⊓ W j ≤ (V d).1)).op (f₂ d) *
              (u₂ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j))))) := by
  classical
  set z : T ⟶ pullback E.π t := baseChangeZero E.π E.zero E.zero_π t with hz
  obtain ⟨V, f₁, f₂, hWsup, hspan₁, hnzd₁, hfmem₁, hspan₂, hnzd₂, hfmem₂⟩ :=
    exists_chart_family J₁ J₂ h₁ h₂
  set W₀ : ↥(pullback E.π t) → (pullback E.π t).Opens := fun c => (V c).1 with hW₀def
  have hW₀ : iSup W₀ = ⊤ := hWsup
  have e₀ : ∀ c, M.over (W₀ c) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W₀ c)) :=
    fun c => Scheme.Modules.overTrivializationOfRestrictIso M (W₀ c)
      (restrictIsoOfPullbackIso M (W₀ c)
        (pullbackTrivOfTensorIdeal M J₁ J₂ e_dict (V c) (f₁ c) (f₂ c)
          (hspan₁ c) (hnzd₁ c) (hfmem₁ c) (hspan₂ c) (hnzd₂ c) (hfmem₂ c)))
  obtain ⟨d, hd⟩ := exists_transitionUnit_eq_mul_inv_of_picMap_eq_one z
    (kappa E hsm t Q) M hM (kappa_mem_ker E hsm t Q) W₀ e₀
  -- the zero image is closed
  haveI hsep : IsSeparated (pullback.snd E.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t ‹_›
  haveI hzci : IsClosedImmersion z := by
    refine MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated)
      z (pullback.snd E.π t) hsep ?_
    rw [hz, baseChangeZero_snd]
    infer_instance
  set Zc : (pullback E.π t).Opens :=
    ⟨(Set.range z.base)ᶜ, (z.isClosedEmbedding.isClosed_range).isOpen_compl⟩ with hZc
  have hzZc : z ⁻¹ᵁ Zc ≤ ⊥ := by
    intro x hx
    exact absurd (Set.mem_range_self x) hx
  -- the two-family cover
  set W : ↥(pullback E.π t) ⊕ ↥(pullback E.π t) → (pullback E.π t).Opens := Sum.elim
    (fun i => W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))
    (fun i => W₀ i ⊓ Zc) with hWdef
  have hW : iSup W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hmem : x ∈ Set.range z.base
    · obtain ⟨y, rfl⟩ := hmem
      have hy : z.base y ∈ (⊤ : (pullback E.π t).Opens) := trivial
      rw [← hW₀, TopologicalSpace.Opens.mem_iSup] at hy
      obtain ⟨i, hi⟩ := hy
      refine ⟨Sum.inl i, hi, ?_⟩
      show (pullback.snd E.π t).base (z.base y) ∈ (z ⁻¹ᵁ W₀ i)
      have hzy : (pullback.snd E.π t).base (z.base y) = y := by
        have := congrArg (fun m : T ⟶ T => m.base y) (baseChangeZero_snd E.π E.zero
          E.zero_π t)
        simpa using this
      rw [hzy]
      exact hi
    · have hx : x ∈ (⊤ : (pullback E.π t).Opens) := trivial
      rw [← hW₀, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨Sum.inr i, hi, hmem⟩
  -- the trivialisation family: rescaled near the zero image, plain off it
  set cZ : ∀ i : ↥(pullback E.π t), Γ(pullback E.π t, W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))ˣ :=
    fun i => unitPullback (pullback.snd E.π t) (z ⁻¹ᵁ W₀ i)
      (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) inf_le_right (d i) with hcZ
  set e : ∀ a : ↥(pullback E.π t) ⊕ ↥(pullback E.π t), M.over (W a) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W a)) :=
    fun a => match a with
      | .inl i => SheafOfModules.restrictOverTrivialization
          (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
          (Over.mk (homOfLE (inf_le_left :
            W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i))) ≪≫
        overUnitScalarIso _ (cZ i)
      | .inr i => SheafOfModules.restrictOverTrivialization
          (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
          (Over.mk (homOfLE (inf_le_left : W₀ i ⊓ Zc ≤ W₀ i))) with hedef
  refine ⟨V, f₁, f₂, ↥(pullback E.π t) ⊕ ↥(pullback E.π t), W, hW, e,
    hspan₁, hnzd₁, hspan₂, hnzd₂, ?_, ?_⟩
  swap
  · -- the dressed transitions (stage 2)
    intro a b hne
    cases a with
    | inl i => cases b with
      | inl j => sorry
      | inr j => sorry
    | inr i => cases b with
      | inl j => sorry
      | inr j => sorry
  intro a b
  rw [mem_sectionUnits_iff]
  -- any overlap touching the off-zero family has empty zero-trace
  have hvac : ∀ (V : (pullback E.π t).Opens), V ≤ Zc →
      ∀ (u : Γ(pullback E.π t, V)ˣ), sectionEval z V u = 1 := by
    intro V hV u
    haveI := sections_subsingleton_of_le_bot'
      ((z.preimage_mono hV).trans hzZc)
    exact Units.ext (Subsingleton.elim _ _)
  cases a with
  | inr i =>
      exact hvac _ (le_trans inf_le_left inf_le_right) _
  | inl i =>
      cases b with
      | inr j =>
          exact hvac _ (le_trans inf_le_right inf_le_right) _
      | inl j =>
          -- the genuine case: both charts rescaled near the zero image
          have hzπ : z ≫ pullback.snd E.π t = 𝟙 T := by
            rw [hz]; exact baseChangeZero_snd E.π E.zero E.zero_π t
          have hVle : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
              (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j :=
            inf_le_inf inf_le_left inf_le_left
          -- the unscaled cocycle over the refined overlap reads the original one
          have hAB : trivializationTransitionUnit
              ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i))))
                (Over.mk (homOfLE (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)))))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j) ≤ W₀ j))))
                (Over.mk (homOfLE (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))))) =
              Scheme.resUnit hVle (transitionUnitOfCover M W₀ e₀ i j) :=
            (congrArg₂ (trivializationTransitionUnit _)
              (restrictOverTrivialization_comp_eq M (e₀ i)
                (inf_le_left) (inf_le_left) hVle (inf_le_left : W₀ i ⊓ W₀ j ≤ W₀ i))
              (restrictOverTrivialization_comp_eq M (e₀ j)
                (inf_le_right) (inf_le_left) hVle
                (inf_le_right : W₀ i ⊓ W₀ j ≤ W₀ j))).trans
            (trivializationTransitionUnit_restrict (M := M) hVle
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                (Over.mk (homOfLE (inf_le_left : W₀ i ⊓ W₀ j ≤ W₀ i))))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                (Over.mk (homOfLE (inf_le_right : W₀ i ⊓ W₀ j ≤ W₀ j)))))
          -- split the scalar corrections off
          have hco : trivializationTransitionUnit
              ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i))) ≪≫
                  overUnitScalarIso (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))
                (Over.mk (homOfLE inf_le_left)))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j) ≤ W₀ j))) ≪≫
                  overUnitScalarIso (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j))
                (Over.mk (homOfLE inf_le_right))) =
              Scheme.resUnit hVle (transitionUnitOfCover M W₀ e₀ i j) *
                (Scheme.resUnit (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))⁻¹ *
                Scheme.resUnit (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j) :=
            (congrArg₂ (trivializationTransitionUnit _)
              (restrictOverTrivialization_trans_scalarIso inf_le_left
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i)))) (cZ i))
              (restrictOverTrivialization_trans_scalarIso inf_le_right
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j) ≤ W₀ j)))) (cZ j))).trans
            ((trivializationTransitionUnit_trans_scalarIso _ _ _ _ _).trans
              (congrArg (fun x => x *
                (Scheme.resUnit (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))⁻¹ *
                Scheme.resUnit (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j)) hAB))
          -- evaluate along the zero section and cancel the `d`-atoms
          have hEB : ∀ (k : ↥(pullback E.π t)) (hk : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
              (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                W₀ k ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ k))
              (p' : z ⁻¹ᵁ ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))) ≤
                (𝟙 T) ⁻¹ᵁ (z ⁻¹ᵁ W₀ k)),
              sectionEval z ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
                (Scheme.resUnit hk (cZ k)) =
              Scheme.resUnit p' (d k) := by
            intro k hk p'
            refine ((congrArg (sectionEval z _)
              (resUnit_unitPullback (pullback.snd E.π t) inf_le_right hk (d k))).trans
              (sectionEval_unitPullback (pullback.snd E.π t) z
                (hk.trans inf_le_right) (d k))).trans ?_
            refine (resUnit_sectionEval_congr hzπ (z ⁻¹ᵁ W₀ k) (d k)
              (z.preimage_mono (hk.trans inf_le_right)) p').trans ?_
            exact congrArg (Scheme.resUnit p') (sectionEval_id' (z ⁻¹ᵁ W₀ k) (d k))
          have hkey : sectionEval z
              ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
              (Scheme.resUnit hVle (transitionUnitOfCover M W₀ e₀ i j) *
                (Scheme.resUnit (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))⁻¹ *
                Scheme.resUnit (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j)) = 1 := by
            rw [map_mul, map_mul, map_inv]
            rw [show sectionEval z _ (Scheme.resUnit hVle
                (transitionUnitOfCover M W₀ e₀ i j)) =
              Scheme.resUnit (z.preimage_mono hVle)
                (Scheme.resUnit (z.preimage_mono (inf_le_left : W₀ i ⊓ W₀ j ≤ W₀ i))
                    (d i) *
                  (Scheme.resUnit (z.preimage_mono (inf_le_right : W₀ i ⊓ W₀ j ≤ W₀ j))
                    (d j))⁻¹) from
              (sectionEval_resUnit z hVle _).trans
                (congrArg (Scheme.resUnit (z.preimage_mono hVle)) (hd i j))]
            rw [hEB i inf_le_left
                ((z.preimage_mono (inf_le_left)).trans (z.preimage_mono (inf_le_left))),
              hEB j inf_le_right
                ((z.preimage_mono (inf_le_right)).trans (z.preimage_mono (inf_le_left))),
              map_mul, map_inv, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit]
            exact mul_inv_mul_inv_cancel' _ _
          exact (congrArg (sectionEval z
            ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
              (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))) hco).trans hkey

end ModularCurves
