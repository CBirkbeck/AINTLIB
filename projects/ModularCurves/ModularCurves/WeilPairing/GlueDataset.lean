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

/-- **([3c-iv-a] the germ equation)** The function-field germ of a dressed transition,
in division-free multiplicative form: `t·b·f₁ᶜ·f₂ᵈ = a·f₂ᶜ·f₁ᵈ` at germs. Downstream
the `a`, `b` germs die at divisor level (units), leaving the generator-quotient
`r_d/r_c` reading. -/
theorem germToFunctionField_transition_dressed {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X]
    {Wij Vc Vd : X.Opens} (hc : Wij ≤ Vc) (hd : Wij ≤ Vd) [Nonempty Wij] [Nonempty Vc] [Nonempty Vd]
    (tval a b u₁ u₂ : Γ(X, Wij)ˣ)
    (f₁c f₂c : Γ(X, Vc)) (f₁d f₂d : Γ(X, Vd))
    (heq : tval = a * (u₂ * u₁⁻¹) * b⁻¹)
    (hu₁ : X.presheaf.map (homOfLE hc).op f₁c =
      X.presheaf.map (homOfLE hd).op f₁d * (u₁ : Γ(X, Wij)))
    (hu₂ : X.presheaf.map (homOfLE hc).op f₂c =
      X.presheaf.map (homOfLE hd).op f₂d * (u₂ : Γ(X, Wij))) :
    X.germToFunctionField Wij ((tval : Γ(X, Wij))) *
      X.germToFunctionField Wij ((b : Γ(X, Wij))) *
      X.germToFunctionField Vc f₁c * X.germToFunctionField Vd f₂d =
    X.germToFunctionField Wij ((a : Γ(X, Wij))) *
      X.germToFunctionField Vc f₂c * X.germToFunctionField Vd f₁d := by
  have hunits : tval * b * u₁ = a * u₂ := by rw [heq]; group
  have hC := congrArg (fun (x : Γ(X, Wij)) => X.germToFunctionField Wij x)
    (congrArg Units.val hunits)
  simp only [Units.val_mul, map_mul] at hC
  have hA := congrArg (fun (x : Γ(X, Wij)) => X.germToFunctionField Wij x) hu₁
  have hB := congrArg (fun (x : Γ(X, Wij)) => X.germToFunctionField Wij x) hu₂
  simp only [map_mul] at hA hB
  have hr₁c : X.germToFunctionField Wij (X.presheaf.map (homOfLE hc).op f₁c) =
      X.germToFunctionField Vc f₁c :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hc) (genericPoint X) _ _
  have hr₂c : X.germToFunctionField Wij (X.presheaf.map (homOfLE hc).op f₂c) =
      X.germToFunctionField Vc f₂c :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hc) (genericPoint X) _ _
  have hr₁d : X.germToFunctionField Wij (X.presheaf.map (homOfLE hd).op f₁d) =
      X.germToFunctionField Vd f₁d :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hd) (genericPoint X) _ _
  have hr₂d : X.germToFunctionField Wij (X.presheaf.map (homOfLE hd).op f₂d) =
      X.germToFunctionField Vd f₂d :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hd) (genericPoint X) _ _
  rw [hr₁c, hr₁d] at hA
  rw [hr₂c, hr₂d] at hB
  rw [hA, hB]
  linear_combination (X.germToFunctionField Vd f₁d *
    X.germToFunctionField Vd f₂d) * hC



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

private theorem transitionUnit_restrict_rescale {Y : Scheme.{u}} {M : Y.Modules}
    {Wi Wj Ui Uj : Y.Opens} (hUi : Ui ≤ Wi) (hUj : Uj ≤ Wj)
    (ei : M.over Wi ≅ _root_.SheafOfModules.unit (Y.ringCatSheaf.over Wi))
    (ej : M.over Wj ≅ _root_.SheafOfModules.unit (Y.ringCatSheaf.over Wj))
    (ci : Γ(Y, Ui)ˣ) (cj : Γ(Y, Uj)ˣ) :
    trivializationTransitionUnit (Ui ⊓ Uj)
      (SheafOfModules.restrictOverTrivialization Y.ringCatSheaf M Ui
        (SheafOfModules.restrictOverTrivialization Y.ringCatSheaf M Wi ei
          (Over.mk (homOfLE hUi)) ≪≫ overUnitScalarIso Ui ci)
        (Over.mk (homOfLE (inf_le_left : Ui ⊓ Uj ≤ Ui))))
      (SheafOfModules.restrictOverTrivialization Y.ringCatSheaf M Uj
        (SheafOfModules.restrictOverTrivialization Y.ringCatSheaf M Wj ej
          (Over.mk (homOfLE hUj)) ≪≫ overUnitScalarIso Uj cj)
        (Over.mk (homOfLE (inf_le_right : Ui ⊓ Uj ≤ Uj)))) =
    Units.map (Y.presheaf.map (homOfLE
        (inf_le_inf hUi hUj : Ui ⊓ Uj ≤ Wi ⊓ Wj)).op).hom.toMonoidHom
      (trivializationTransitionUnit (Wi ⊓ Wj)
        (SheafOfModules.restrictOverTrivialization Y.ringCatSheaf M Wi ei
          (Over.mk (homOfLE (inf_le_left : Wi ⊓ Wj ≤ Wi))))
        (SheafOfModules.restrictOverTrivialization Y.ringCatSheaf M Wj ej
          (Over.mk (homOfLE (inf_le_right : Wi ⊓ Wj ≤ Wj))))) *
      (Scheme.resUnit (inf_le_left : Ui ⊓ Uj ≤ Ui) ci)⁻¹ *
      Scheme.resUnit (inf_le_right : Ui ⊓ Uj ≤ Uj) cj := by
  refine (congrArg₂ (trivializationTransitionUnit _)
    (restrictOverTrivialization_trans_scalarIso inf_le_left _ ci)
    (restrictOverTrivialization_trans_scalarIso inf_le_right _ cj)).trans ?_
  refine (trivializationTransitionUnit_trans_scalarIso _ _ _ _ _).trans ?_
  refine congrArg (fun x => x *
    (Scheme.resUnit (inf_le_left : Ui ⊓ Uj ≤ Ui) ci)⁻¹ *
    Scheme.resUnit (inf_le_right : Ui ⊓ Uj ≤ Uj) cj) ?_
  refine (congrArg₂ (trivializationTransitionUnit _)
    (restrictOverTrivialization_comp_eq M ei inf_le_left hUi
      (inf_le_inf hUi hUj) (inf_le_left : Wi ⊓ Wj ≤ Wi))
    (restrictOverTrivialization_comp_eq M ej inf_le_right hUj
      (inf_le_inf hUi hUj) (inf_le_right : Wi ⊓ Wj ≤ Wj))).trans ?_
  exact trivializationTransitionUnit_restrict (inf_le_inf hUi hUj) _ _

private theorem res_res {Y : Scheme.{u}} {A B C : Y.Opens}
    (hAB : A ≤ B) (hBC : B ≤ C) (x : Γ(Y, C)) :
    Y.presheaf.map (homOfLE hAB).op (Y.presheaf.map (homOfLE hBC).op x) =
      Y.presheaf.map (homOfLE (hAB.trans hBC)).op x := by
  have h := congrArg (fun (φ : _ ⟶ _) =>
    (CategoryTheory.ConcreteCategory.hom (Y.presheaf.map φ)) x)
    (Subsingleton.elim ((homOfLE hBC).op ≫ (homOfLE hAB).op)
      (homOfLE (hAB.trans hBC)).op)
  refine Eq.trans ?_ h
  exact (congrArg (fun (φ : _ ⟶ _) =>
    (CategoryTheory.ConcreteCategory.hom φ) x)
    (Y.presheaf.map_comp (homOfLE hBC).op (homOfLE hAB).op)).symm

/-- **([G-REL] the overlap relation)** Pushing a split dressed transition into the
function field along a dominant `τ`: the `h`-germs and the `τ`-pulled generator germs
satisfy one division-free multiplicative relation per overlap. The pointwise divisor
computation of `H·τ♭r` consumes exactly this. -/
theorem germ_split_transition_rel {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (τ : X ⟶ X) [IsDominant τ]
    {Wij Vc Vd : X.Opens} (hc : Wij ≤ Vc) (hd : Wij ≤ Vd)
    [Nonempty Wij] [Nonempty Vc] [Nonempty Vd]
    [Nonempty (τ ⁻¹ᵁ Wij : X.Opens)]
    (tval a b u₁ u₂ : Γ(X, Wij)ˣ)
    (f₁c f₂c : Γ(X, Vc)) (f₁d f₂d : Γ(X, Vd))
    (heq : tval = a * (u₂ * u₁⁻¹) * b⁻¹)
    (hu₁ : X.presheaf.map (homOfLE hc).op f₁c =
      X.presheaf.map (homOfLE hd).op f₁d * (u₁ : Γ(X, Wij)))
    (hu₂ : X.presheaf.map (homOfLE hc).op f₂c =
      X.presheaf.map (homOfLE hd).op f₂d * (u₂ : Γ(X, Wij)))
    (hi hj : Γ(X, τ ⁻¹ᵁ Wij)ˣ)
    (hsplit : Units.map (Scheme.Hom.app τ Wij).hom.toMonoidHom tval = hi * hj⁻¹) :
    X.germToFunctionField (τ ⁻¹ᵁ Wij) ((hi : Γ(X, τ ⁻¹ᵁ Wij))) *
      τ.functionFieldMap.hom (X.germToFunctionField Wij ((b : Γ(X, Wij))) *
        X.germToFunctionField Vc f₁c * X.germToFunctionField Vd f₂d) =
    X.germToFunctionField (τ ⁻¹ᵁ Wij) ((hj : Γ(X, τ ⁻¹ᵁ Wij))) *
      τ.functionFieldMap.hom (X.germToFunctionField Wij ((a : Γ(X, Wij))) *
        X.germToFunctionField Vc f₂c * X.germToFunctionField Vd f₁d) := by
  have h3civ := germToFunctionField_transition_dressed hc hd tval a b u₁ u₂
    f₁c f₂c f₁d f₂d heq hu₁ hu₂
  have hτ := congrArg τ.functionFieldMap.hom h3civ
  simp only [map_mul] at hτ
  have hunits : Units.map (Scheme.Hom.app τ Wij).hom.toMonoidHom tval * hj = hi := by
    rw [hsplit, inv_mul_cancel_right]
  have hval := congrArg (fun (x : Γ(X, τ ⁻¹ᵁ Wij)ˣ) =>
    X.germToFunctionField (τ ⁻¹ᵁ Wij) ((x : Γ(X, τ ⁻¹ᵁ Wij)))) hunits
  simp only [Units.val_mul, map_mul, Units.coe_map, MonoidHom.coe_coe] at hval
  have hnat : τ.functionFieldMap.hom
      (X.germToFunctionField Wij ((tval : Γ(X, Wij)))) =
      X.germToFunctionField (τ ⁻¹ᵁ Wij)
        ((Scheme.Hom.app τ Wij).hom ((tval : Γ(X, Wij)))) :=
    functionFieldMap_germToFunctionField τ Wij ((tval : Γ(X, Wij)))
  have hval' : τ.functionFieldMap.hom
      (X.germToFunctionField Wij ((tval : Γ(X, Wij)))) *
      X.germToFunctionField (τ ⁻¹ᵁ Wij) ((hj : Γ(X, τ ⁻¹ᵁ Wij))) =
      X.germToFunctionField (τ ⁻¹ᵁ Wij) ((hi : Γ(X, τ ⁻¹ᵁ Wij))) := by
    rw [hnat]
    exact hval
  simp only [map_mul]
  linear_combination (X.germToFunctionField (τ ⁻¹ᵁ Wij)
      ((hj : Γ(X, τ ⁻¹ᵁ Wij)))) * hτ -
    (τ.functionFieldMap.hom (X.germToFunctionField Wij ((b : Γ(X, Wij)))) *
      τ.functionFieldMap.hom (X.germToFunctionField Vc f₁c) *
      τ.functionFieldMap.hom (X.germToFunctionField Vd f₂d)) * hval'

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
      | inl j =>
          have hne₀ : Nonempty ↥((W₀ i ⊓ W₀ j : (pullback E.π t).Opens)) :=
            ⟨⟨hne.some.1, ⟨hne.some.2.1.1, hne.some.2.2.1⟩⟩⟩
          obtain ⟨a₀, b₀, u₁₀, u₂₀, heq₀, hu₁₀, hu₂₀⟩ :=
            exists_transition_dressed_of_charts M J₁ J₂ e_dict W₀ e₀ i j
              (V i) (V j) rfl rfl (f₁ i) (f₂ i) (f₁ j) (f₂ j)
              (hspan₁ i) (hnzd₁ i) (hfmem₁ i) (hspan₂ i) (hnzd₂ i) (hfmem₂ i)
              (hspan₁ j) (hnzd₁ j) (hfmem₁ j) (hspan₂ j) (hnzd₂ j) (hfmem₂ j) hne₀
          have hform := transitionUnit_restrict_rescale
            (inf_le_left : W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i)
            (inf_le_left : W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j) ≤ W₀ j)
            (e₀ i) (e₀ j) (cZ i) (cZ j)
          refine ⟨i, j,
            (show W (Sum.inl i) ≤ ((V i).1 : (pullback E.π t).Opens) from inf_le_left),
            (show W (Sum.inl j) ≤ ((V j).1 : (pullback E.π t).Opens) from inf_le_left),
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom a₀,
            (Scheme.resUnit (inf_le_right : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))) (cZ j))⁻¹ *
              Scheme.resUnit (inf_le_left : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))) (cZ i) *
              Units.map ((pullback E.π t).presheaf.map (homOfLE
                (inf_le_inf inf_le_left inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom b₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₁₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₂₀, ?_, ?_, ?_⟩
          · refine hform.trans ?_
            refine (congrArg (fun x => Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom x *
              (Scheme.resUnit (inf_le_left : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))) (cZ i))⁻¹ *
              Scheme.resUnit (inf_le_right : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))) (cZ j)) heq₀).trans ?_
            simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
          · have h1 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op)) hu₁₀
            rw [map_mul] at h1
            rw [res_res, res_res] at h1
            exact h1
          · have h2 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op)) hu₂₀
            rw [map_mul] at h2
            rw [res_res, res_res] at h2
            exact h2
      | inr j =>
          have hne₀ : Nonempty ↥((W₀ i ⊓ W₀ j : (pullback E.π t).Opens)) :=
            ⟨⟨hne.some.1, ⟨hne.some.2.1.1, hne.some.2.2.1⟩⟩⟩
          obtain ⟨a₀, b₀, u₁₀, u₂₀, heq₀, hu₁₀, hu₂₀⟩ :=
            exists_transition_dressed_of_charts M J₁ J₂ e_dict W₀ e₀ i j
              (V i) (V j) rfl rfl (f₁ i) (f₂ i) (f₁ j) (f₂ j)
              (hspan₁ i) (hnzd₁ i) (hfmem₁ i) (hspan₂ i) (hnzd₂ i) (hfmem₂ i)
              (hspan₁ j) (hnzd₁ j) (hfmem₁ j) (hspan₂ j) (hnzd₂ j) (hfmem₂ j) hne₀
          have hform := transitionUnit_restrict_rescale
            (inf_le_left : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ≤ W₀ i)
            (inf_le_left : (W₀ j ⊓ Zc) ≤ W₀ j)
            (e₀ i) (e₀ j) (cZ i) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ)
          have hmaskR : e (Sum.inr j) =
              SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ j)
                (e₀ j) (Over.mk (homOfLE (inf_le_left : (W₀ j ⊓ Zc) ≤ W₀ j))) ≪≫
                overUnitScalarIso (W₀ j ⊓ Zc) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ) := by
            rw [overUnitScalarIso_one]
            exact (Iso.trans_refl _).symm
          refine ⟨i, j,
            (show W (Sum.inl i) ≤ ((V i).1 : (pullback E.π t).Opens) from inf_le_left),
            (show W (Sum.inr j) ≤ ((V j).1 : (pullback E.π t).Opens) from inf_le_left),
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom a₀,
            (Scheme.resUnit (inf_le_right : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ j ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ))⁻¹ *
              Scheme.resUnit (inf_le_left : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))) (cZ i) *
              Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom b₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₁₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₂₀, ?_, ?_, ?_⟩
          · refine Eq.trans (congrArg (fun x₂ =>
              trivializationTransitionUnit ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc))
                (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))
                  (e (Sum.inl i))
                  (Over.mk (homOfLE (inf_le_left : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))))))
                (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ j ⊓ Zc) x₂
                  (Over.mk (homOfLE (inf_le_right : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ j ⊓ Zc))))))
            hmaskR) (hform.trans ?_)
            refine (congrArg (fun x => Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom x *
              (Scheme.resUnit (inf_le_left : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))) (cZ i))⁻¹ *
              Scheme.resUnit (inf_le_right : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ j ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ)) heq₀).trans ?_
            simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
          · have h1 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op)) hu₁₀
            rw [map_mul] at h1
            rw [res_res, res_res] at h1
            exact h1
          · have h2 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op)) hu₂₀
            rw [map_mul] at h2
            rw [res_res, res_res] at h2
            exact h2
    | inr i => cases b with
      | inl j =>
          have hne₀ : Nonempty ↥((W₀ i ⊓ W₀ j : (pullback E.π t).Opens)) :=
            ⟨⟨hne.some.1, ⟨hne.some.2.1.1, hne.some.2.2.1⟩⟩⟩
          obtain ⟨a₀, b₀, u₁₀, u₂₀, heq₀, hu₁₀, hu₂₀⟩ :=
            exists_transition_dressed_of_charts M J₁ J₂ e_dict W₀ e₀ i j
              (V i) (V j) rfl rfl (f₁ i) (f₂ i) (f₁ j) (f₂ j)
              (hspan₁ i) (hnzd₁ i) (hfmem₁ i) (hspan₂ i) (hnzd₂ i) (hfmem₂ i)
              (hspan₁ j) (hnzd₁ j) (hfmem₁ j) (hspan₂ j) (hnzd₂ j) (hfmem₂ j) hne₀
          have hform := transitionUnit_restrict_rescale
            (inf_le_left : (W₀ i ⊓ Zc) ≤ W₀ i)
            (inf_le_left : (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ j)
            (e₀ i) (e₀ j) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ) (cZ j)
          have hmaskL : e (Sum.inr i) =
              SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ i)
                (e₀ i) (Over.mk (homOfLE (inf_le_left : (W₀ i ⊓ Zc) ≤ W₀ i))) ≪≫
                overUnitScalarIso (W₀ i ⊓ Zc) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ) := by
            rw [overUnitScalarIso_one]
            exact (Iso.trans_refl _).symm
          refine ⟨i, j,
            (show W (Sum.inr i) ≤ ((V i).1 : (pullback E.π t).Opens) from inf_le_left),
            (show W (Sum.inl j) ≤ ((V j).1 : (pullback E.π t).Opens) from inf_le_left),
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom a₀,
            (Scheme.resUnit (inf_le_right : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))) (cZ j))⁻¹ *
              Scheme.resUnit (inf_le_left : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ i ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ) *
              Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom b₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₁₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₂₀, ?_, ?_, ?_⟩
          · refine Eq.trans (congrArg (fun x₁ =>
              trivializationTransitionUnit ((W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
                (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ i ⊓ Zc) x₁
                  (Over.mk (homOfLE (inf_le_left : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ i ⊓ Zc)))))
                (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))
                  (e (Sum.inl j))
                  (Over.mk (homOfLE (inf_le_right : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))))))
            hmaskL) (hform.trans ?_)
            refine (congrArg (fun x => Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom x *
              (Scheme.resUnit (inf_le_left : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ i ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ))⁻¹ *
              Scheme.resUnit (inf_le_right : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))) (cZ j)) heq₀).trans ?_
            simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
          · have h1 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op)) hu₁₀
            rw [map_mul] at h1
            rw [res_res, res_res] at h1
            exact h1
          · have h2 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j)).op)) hu₂₀
            rw [map_mul] at h2
            rw [res_res, res_res] at h2
            exact h2
      | inr j =>
          have hne₀ : Nonempty ↥((W₀ i ⊓ W₀ j : (pullback E.π t).Opens)) :=
            ⟨⟨hne.some.1, ⟨hne.some.2.1.1, hne.some.2.2.1⟩⟩⟩
          obtain ⟨a₀, b₀, u₁₀, u₂₀, heq₀, hu₁₀, hu₂₀⟩ :=
            exists_transition_dressed_of_charts M J₁ J₂ e_dict W₀ e₀ i j
              (V i) (V j) rfl rfl (f₁ i) (f₂ i) (f₁ j) (f₂ j)
              (hspan₁ i) (hnzd₁ i) (hfmem₁ i) (hspan₂ i) (hnzd₂ i) (hfmem₂ i)
              (hspan₁ j) (hnzd₁ j) (hfmem₁ j) (hspan₂ j) (hnzd₂ j) (hfmem₂ j) hne₀
          have hform := transitionUnit_restrict_rescale
            (inf_le_left : (W₀ i ⊓ Zc) ≤ W₀ i)
            (inf_le_left : (W₀ j ⊓ Zc) ≤ W₀ j)
            (e₀ i) (e₀ j) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ)
          have hmaskL : e (Sum.inr i) =
              SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ i)
                (e₀ i) (Over.mk (homOfLE (inf_le_left : (W₀ i ⊓ Zc) ≤ W₀ i))) ≪≫
                overUnitScalarIso (W₀ i ⊓ Zc) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ) := by
            rw [overUnitScalarIso_one]
            exact (Iso.trans_refl _).symm
          have hmaskR : e (Sum.inr j) =
              SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ j)
                (e₀ j) (Over.mk (homOfLE (inf_le_left : (W₀ j ⊓ Zc) ≤ W₀ j))) ≪≫
                overUnitScalarIso (W₀ j ⊓ Zc) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ) := by
            rw [overUnitScalarIso_one]
            exact (Iso.trans_refl _).symm
          refine ⟨i, j,
            (show W (Sum.inr i) ≤ ((V i).1 : (pullback E.π t).Opens) from inf_le_left),
            (show W (Sum.inr j) ≤ ((V j).1 : (pullback E.π t).Opens) from inf_le_left),
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom a₀,
            (Scheme.resUnit (inf_le_right : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ j ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ))⁻¹ *
              Scheme.resUnit (inf_le_left : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ i ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ) *
              Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom b₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₁₀,
            Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom u₂₀, ?_, ?_, ?_⟩
          · refine Eq.trans (congrArg₂ (fun x₁ x₂ =>
              trivializationTransitionUnit ((W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc))
                (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ i ⊓ Zc) x₁
                  (Over.mk (homOfLE (inf_le_left : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ i ⊓ Zc)))))
                (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W₀ j ⊓ Zc) x₂
                  (Over.mk (homOfLE (inf_le_right : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ j ⊓ Zc))))))
            hmaskL hmaskR) (hform.trans ?_)
            refine (congrArg (fun x => Units.map ((pullback E.π t).presheaf.map (homOfLE
              (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op).hom.toMonoidHom x *
              (Scheme.resUnit (inf_le_left : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ i ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ i ⊓ Zc))ˣ))⁻¹ *
              Scheme.resUnit (inf_le_right : (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ (W₀ j ⊓ Zc)) (1 : Γ((pullback E.π t), (W₀ j ⊓ Zc))ˣ)) heq₀).trans ?_
            simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
          · have h1 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op)) hu₁₀
            rw [map_mul] at h1
            rw [res_res, res_res] at h1
            exact h1
          · have h2 := congrArg (CategoryTheory.ConcreteCategory.hom
              ((pullback E.π t).presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
                (W₀ i ⊓ Zc) ⊓ (W₀ j ⊓ Zc) ≤ W₀ i ⊓ W₀ j)).op)) hu₂₀
            rw [map_mul] at h2
            rw [res_res, res_res] at h2
            exact h2
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


/-- **([G2′] the per-chart normalized dataset)** Strengthening of
`exists_normalized_chart_dataset`: the overlap dressing of every transition decomposes
into **per-chart** units `A i` around the fixed chart assignment `ch` — on every
inhabited overlap,

  `t_ij = A i |_{ij} · (u₂ · u₁⁻¹) · (A j |_{ij})⁻¹`,

with `u₁, u₂` the generator-comparison units of the charts `V (ch i)`, `V (ch j)`.
This is the form the pointwise divisor computation (`ORD-G`) consumes: at a point `p`
over `W i`, every factor is either a unit germ on a neighbourhood of `p` (`A i`, `h i`)
or a generator-ratio germ with span-pinned order. Proof route (cont.20): the G2
construction with the e-family compared to the restricted native trivialisations —
`m_ij = u₂u₁⁻¹` via `restrictOverTrivialization_comp` +
`overTrivializationOfRestrictOpenTrivialization` +
`restrictOpenTrivialization_restrictIsoOfPullbackIso` + PACKAGE-mid + the read-off from
two `restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu` instances
(`nuPullback_mul` for the generator change). -/
theorem exists_normalized_chart_dataset_perChart
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
        _root_.SheafOfModules.unit ((CategoryTheory.Limits.pullback E.π t).ringCatSheaf.over (W i)))
      (ch : ι' → ↥(CategoryTheory.Limits.pullback E.π t))
      (A : ∀ i, ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i)))ˣ),
      (∀ c, J₁.ideal (V c) = Ideal.span {f₁ c}) ∧
      (∀ c, f₁ c ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1)))) ∧
      (∀ c, J₂.ideal (V c) = Ideal.span {f₂ c}) ∧
      (∀ c, f₂ c ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1)))) ∧
      (∀ i j, transitionUnitOfCover M W e i j ∈
        sectionUnits (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)) ∧
      (∀ i, W i ≤ (V (ch i)).1) ∧
      (∀ i j (hWch : ∀ k, W k ≤ (V (ch k)).1), Nonempty ↥((W i ⊓ W j) : (CategoryTheory.Limits.pullback E.π t).Opens) →
        ∃ (u₁ u₂ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j)))ˣ),
          transitionUnitOfCover M W e i j =
            Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i) (A i) * (u₂ * u₁⁻¹) *
              (Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j) (A j))⁻¹ ∧
          (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_left).trans (hWch i) : W i ⊓ W j ≤ (V (ch i)).1)).op (f₁ (ch i)) =
            (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_right).trans (hWch j) : W i ⊓ W j ≤ (V (ch j)).1)).op (f₁ (ch j)) *
              (u₁ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j)))) ∧
          (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_left).trans (hWch i) : W i ⊓ W j ≤ (V (ch i)).1)).op (f₂ (ch i)) =
            (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_right).trans (hWch j) : W i ⊓ W j ≤ (V (ch j)).1)).op (f₂ (ch j)) *
              (u₂ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j))))) := by
  sorry

end ModularCurves
