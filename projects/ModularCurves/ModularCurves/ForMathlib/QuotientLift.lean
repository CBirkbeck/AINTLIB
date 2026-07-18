/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineQuotient
import ModularCurves.ForMathlib.SchemeActionFree

/-!
# Morphism descent over an open of the scheme quotient ([a5-W2])

The restricted universal property of `SchemeAction.quotient`: a `G`-invariant morphism out of
`pullback quotientπ j` (the `G`-stable open of `X` over an open immersion `j : Q' ⟶ X/G`)
descends uniquely to `Q'`.

## Main results

* `epi_pullback_snd_quotientπ` — the restricted quotient cover is an epimorphism (fppf: flat from
  `etale_quotientπ`, surjective by base change; `Flat.epi_of_flat_of_surjective`). Uniqueness.
* `exists_quotientπ_lift_of_isOpenImmersion` — existence: glue the affine keystone
  `exists_invariantsπ_lift_of_isOpenImmersion` over the quotient-chart cover; overlap agreement by
  the epi property; `Scheme.Cover.glueMorphisms`.

## Implementation notes

This is what descends the `[a5]` fppf-comparison `E|_{D(a)} ⟶ projModel W₁` through the curve's
quotient to `(E/G)|` — the last morphism-level descent the KM 4.7 engine needs.
-/
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace AlgebraicGeometry.SchemeAction
variable {G : Type u} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)

set_option backward.isDefEq.respectTransparency.types false in
/-- For a free action, the pullback of the quotient projection along an open immersion is epic. -/
theorem epi_pullback_snd_quotientπ [Finite G]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T)
    {Q' : Scheme.{u}} (j : Q' ⟶ σ.quotient V hVs hVa) [IsOpenImmersion j] :
    Epi (pullback.snd (σ.quotientπ V hVs hVa hVmem) j) := by
  haveI hsurj : Surjective (σ.quotientπ V hVs hVa hVmem) :=
    ⟨σ.quotientπ_surjective V hVs hVa hVmem⟩
  haveI : Etale (σ.quotientπ V hVs hVa hVmem) := σ.etale_quotientπ V hVs hVa hVmem hfree
  haveI : Surjective (pullback.snd (σ.quotientπ V hVs hVa hVmem) j) :=
    MorphismProperty.pullback_snd _ _ hsurj
  exact Flat.epi_of_flat_of_surjective _

private theorem overlap_eq {Z Q'' Y W₁ W₂ T P₁ P₂ E : Scheme.{u}} {s : Z ⟶ Q''}
    {ρ₁ : P₁ ⟶ Z} {sd₁ : P₁ ⟶ W₁} {ι₁ : W₁ ⟶ Q''}
    {ρ₂ : P₂ ⟶ Z} {sd₂ : P₂ ⟶ W₂} {ι₂ : W₂ ⟶ Q''}
    (h₁ : IsPullback ρ₁ sd₁ s ι₁) (h₂ : IsPullback ρ₂ sd₂ s ι₂)
    {f : Z ⟶ Y} {q₁ : W₁ ⟶ Y} {q₂ : W₂ ⟶ Y}
    (hq₁ : sd₁ ≫ q₁ = ρ₁ ≫ f) (hq₂ : sd₂ ≫ q₂ = ρ₂ ≫ f)
    (t₁ : T ⟶ W₁) (t₂ : T ⟶ W₂) (ht : t₁ ≫ ι₁ = t₂ ≫ ι₂)
    (e : E ⟶ T) (m : E ⟶ Z) [Epi e] (hm : m ≫ s = e ≫ t₁ ≫ ι₁) :
    t₁ ≫ q₁ = t₂ ≫ q₂ := by
  have w₁ : m ≫ s = (e ≫ t₁) ≫ ι₁ := by rw [hm, Category.assoc]
  have w₂ : m ≫ s = (e ≫ t₂) ≫ ι₂ := by rw [hm, Category.assoc, ht]
  rw [← cancel_epi e, ← Category.assoc, ← h₁.lift_snd m (e ≫ t₁) w₁,
    ← Category.assoc, ← h₂.lift_snd m (e ≫ t₂) w₂, Category.assoc, Category.assoc,
    hq₁, hq₂, ← Category.assoc, ← Category.assoc, h₁.lift_fst m (e ≫ t₁) w₁,
    h₂.lift_fst m (e ≫ t₂) w₂]

section Lift

variable [Finite G] [IsAffineHom (pullback.diagonal (terminal.from X))]
  (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x) {Q' : Scheme.{u}} (j : Q' ⟶ σ.quotient V hVs hVa)

private noncomputable def chartHom (x : X) :
    ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}) ⟶ σ.localQuotient (hVs x) :=
  j.resLE (σ.quotientChart V hVs hVa x) (j ⁻¹ᵁ σ.quotientChart V hVs hVa x) le_rfl ≫
    (σ.quotientChartIso V hVs hVa x).inv

private instance isOpenImmersion_chartHom [IsOpenImmersion j] (x : X) :
    IsOpenImmersion (chartHom σ V hVs hVa j x) := by
  haveI : IsOpenImmersion (j.resLE (σ.quotientChart V hVs hVa x)
      (j ⁻¹ᵁ σ.quotientChart V hVs hVa x) le_rfl) := by
    delta Scheme.Hom.resLE
    infer_instance
  unfold chartHom
  infer_instance

private theorem chartHom_comp (x : X) :
    chartHom σ V hVs hVa j x ≫ (σ.quotientChartIso V hVs hVa x).hom ≫
        (σ.quotientChart V hVs hVa x).ι =
      (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι ≫ j := by
  simp only [chartHom, Category.assoc, Iso.inv_hom_id_assoc, Scheme.Hom.resLE_comp_ι]

private theorem isPullback_chartHom (x : X) :
    letI := σ.gammaMulSemiringAction (hVs x)
    IsPullback
      (pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) (chartHom σ V hVs hVa j x) ≫
        (hVa x).isoSpec.inv ≫ (V x).ι)
      (pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) (chartHom σ V hVs hVa j x))
      (σ.quotientπ V hVs hVa hVmem)
      ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι ≫ j) := by
  letI := σ.gammaMulSemiringAction (hVs x)
  have hbase : IsPullback (chartHom σ V hVs hVa j x) (𝟙 _)
      (σ.quotientChartIso V hVs hVa x).hom
      (chartHom σ V hVs hVa j x ≫ (σ.quotientChartIso V hVs hVa x).hom) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp]⟩
  have hleft := (IsPullback.of_hasPullback (invariantsπ G ↑Γ(X, V x) ℤ)
      (chartHom σ V hVs hVa j x)).paste_vert hbase
  rw [Category.comp_id] at hleft
  have hchart : IsPullback ((hVa x).isoSpec.inv)
      (invariantsπ G ↑Γ(X, V x) ℤ ≫ (σ.quotientChartIso V hVs hVa x).hom)
      (σ.localQuotientπ (hVs x) (hVa x) ≫ (σ.quotientChartIso V hVs hVa x).hom)
      (𝟙 ((σ.quotientChart V hVs hVa x : Scheme.{u}))) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, localQuotientπ_eq σ (hVs x) (hVa x), ← Category.assoc,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hright := hchart.paste_horiz
    (σ.isPullback_quotientπ_quotientChart V hVs hVa hVmem x)
  rw [Category.id_comp] at hright
  have hresult := hleft.paste_horiz hright
  rw [show (chartHom σ V hVs hVa j x ≫ (σ.quotientChartIso V hVs hVa x).hom) ≫
      (σ.quotientChart V hVs hVa x).ι = (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι ≫ j from by
    rw [Category.assoc]; exact chartHom_comp σ V hVs hVa j x] at hresult
  exact hresult

private theorem exists_chart_isPullback_lift {Y : Scheme.{u}} [IsOpenImmersion j]
    (f : pullback (σ.quotientπ V hVs hVa hVmem) j ⟶ Y)
    (hf : ∀ g : G, pullback.map (σ.quotientπ V hVs hVa hVmem) j
        (σ.quotientπ V hVs hVa hVmem) j (σ.hom g) (𝟙 Q') (𝟙 _)
        (by rw [Category.comp_id, hom_quotientπ]) (by simp) ≫ f = f)
    (x : X) :
    ∃ (P : Scheme.{u}) (ρ : P ⟶ pullback (σ.quotientπ V hVs hVa hVmem) j)
      (sd : P ⟶ ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}))
      (qx : ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}) ⟶ Y),
      IsPullback ρ sd (pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
          (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι ∧
        sd ≫ qx = ρ ≫ f := by
  letI := σ.gammaMulSemiringAction (hVs x)
  have hrect := σ.isPullback_chartHom V hVs hVa hVmem j x
  have hw : (pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) (chartHom σ V hVs hVa j x) ≫
        (hVa x).isoSpec.inv ≫ (V x).ι) ≫ σ.quotientπ V hVs hVa hVmem =
      (pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) (chartHom σ V hVs hVa j x) ≫
        (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) ≫ j := by
    rw [hrect.w, Category.assoc]
  have hinv : ∀ g : G, pullbackSpecSMul G ↑Γ(X, V x) ℤ (chartHom σ V hVs hVa j x) g ≫
      (pullback.lift _ _ hw ≫ f) = pullback.lift _ _ hw ≫ f := by
    intro g
    have hcomm : pullbackSpecSMul G ↑Γ(X, V x) ℤ (chartHom σ V hVs hVa j x) g ≫
        pullback.lift _ _ hw =
        pullback.lift _ _ hw ≫ pullback.map (σ.quotientπ V hVs hVa hVmem) j
          (σ.quotientπ V hVs hVa hVmem) j (σ.hom g) (𝟙 Q') (𝟙 _)
          (by rw [Category.comp_id, hom_quotientπ]) (by simp) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullbackSpecSMul_fst_assoc, specSMul_isoSpec_inv_assoc, Scheme.Hom.resLE_comp_ι]
      · simp only [Category.assoc, pullback.lift_snd, pullbackSpecSMul_snd_assoc,
          Category.comp_id]
    rw [← Category.assoc, hcomm, Category.assoc, hf g]
  obtain ⟨qx, hqx⟩ := exists_invariantsπ_lift_of_isOpenImmersion G ↑Γ(X, V x) ℤ
    (chartHom σ V hVs hVa j x) (pullback.lift _ _ hw ≫ f) hinv
  refine ⟨pullback (invariantsπ G ↑Γ(X, V x) ℤ) (chartHom σ V hVs hVa j x),
    pullback.lift _ _ hw, pullback.snd _ _, qx, ?_, hqx⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ hw)
    (IsPullback.of_hasPullback (σ.quotientπ V hVs hVa hVmem) j)
  rw [pullback.lift_fst _ _ hw]
  exact hrect

end Lift

private lemma exists_mem_quotientChart_preimage [Finite G]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    {Q' : Scheme.{u}} (j : Q' ⟶ σ.quotient V hVs hVa) (p : Q') :
    ∃ (x : X) (y : ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u})),
      (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι y = p := by
  have hmem : j p ∈ (⊤ : (σ.quotient V hVs hVa).Opens) := trivial
  rw [← σ.iSup_quotientChart_eq_top V hVs hVa] at hmem
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  have h : p ∈ Set.range ⇑(j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, hy⟩ := h
  exact ⟨x, y, hy⟩

private theorem exists_quotientπ_lift_of_chartwise [Finite G]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T)
    {Q' Y : Scheme.{u}} (j : Q' ⟶ σ.quotient V hVs hVa) [IsOpenImmersion j]
    (f : pullback (σ.quotientπ V hVs hVa hVmem) j ⟶ Y)
    (hlift : ∀ x : X,
      ∃ (P : Scheme.{u}) (ρ : P ⟶ pullback (σ.quotientπ V hVs hVa hVmem) j)
        (sd : P ⟶ ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}))
        (qx : ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}) ⟶ Y),
        IsPullback ρ sd (pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
            (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι ∧
          sd ≫ qx = ρ ≫ f) :
    ∃ q : Q' ⟶ Y, pullback.snd (σ.quotientπ V hVs hVa hVmem) j ≫ q = f := by
  classical
  choose P ρ sd qx hPB hq using hlift
  have hcov : ∀ p : Q',
      ∃ (x : X) (y : ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u})),
        (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι y = p :=
    fun p => σ.exists_mem_quotientChart_preimage V hVs hVa j p
  have hover : ∀ x y : X,
      pullback.fst ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι)
          ((j ⁻¹ᵁ σ.quotientChart V hVs hVa y).ι) ≫ qx x =
        pullback.snd ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι)
          ((j ⁻¹ᵁ σ.quotientChart V hVs hVa y).ι) ≫ qx y := by
    intro x y
    haveI hepi : Epi (pullback.snd (σ.quotientπ V hVs hVa hVmem)
        ((pullback.fst ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι)
            ((j ⁻¹ᵁ σ.quotientChart V hVs hVa y).ι) ≫
          (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) ≫ j)) :=
      σ.epi_pullback_snd_quotientπ V hVs hVa hVmem hfree _
    exact overlap_eq (hPB x) (hPB y) (hq x) (hq y)
      (pullback.fst _ _) (pullback.snd _ _) pullback.condition
      (pullback.snd (σ.quotientπ V hVs hVa hVmem)
        ((pullback.fst ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι)
            ((j ⁻¹ᵁ σ.quotientChart V hVs hVa y).ι) ≫
          (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) ≫ j))
      (pullback.map (σ.quotientπ V hVs hVa hVmem)
        ((pullback.fst ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι)
            ((j ⁻¹ᵁ σ.quotientChart V hVs hVa y).ι) ≫
          (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) ≫ j)
        (σ.quotientπ V hVs hVa hVmem) j (𝟙 X)
        (pullback.fst ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι)
            ((j ⁻¹ᵁ σ.quotientChart V hVs hVa y).ι) ≫
          (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) (𝟙 _)
        (by simp) (by simp))
      (pullback.lift_snd _ _ _)
  obtain ⟨q, hq'⟩ : ∃ q : Q' ⟶ Y,
      ∀ x : X, (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι ≫ q = qx x :=
    ⟨(Scheme.Cover.mkOfCovers (↥X)
        (fun x => ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}))
        (fun x => (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) hcov).glueMorphisms qx hover,
      fun x => (Scheme.Cover.mkOfCovers (↥X)
        (fun x => ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}))
        (fun x => (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) hcov).ι_glueMorphisms qx hover x⟩
  refine ⟨q, ?_⟩
  refine Scheme.Cover.hom_ext ((Scheme.Cover.mkOfCovers (↥X)
      (fun x => ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x) : Scheme.{u}))
      (fun x => (j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) hcov).pullback₁
        (pullback.snd (σ.quotientπ V hVs hVa hVmem) j)) _ _ fun x => ?_
  show pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
        ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) ≫
        pullback.snd (σ.quotientπ V hVs hVa hVmem) j ≫ q =
      pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
        ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) ≫ f
  rw [show pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
        ((j ⁻¹ᵁ σ.quotientChart V hVs hVa x).ι) = (hPB x).isoPullback.inv ≫ ρ x from
      ((hPB x).isoPullback_inv_fst).symm,
    Category.assoc, Category.assoc, cancel_epi, ← Category.assoc, (hPB x).w,
    Category.assoc, hq' x]
  exact hq x

/-- A `G`-invariant morphism on the pullback of the quotient projection descends over an open. -/
theorem exists_quotientπ_lift_of_isOpenImmersion [Finite G]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T)
    {Q' Y : Scheme.{u}} (j : Q' ⟶ σ.quotient V hVs hVa) [IsOpenImmersion j]
    (f : pullback (σ.quotientπ V hVs hVa hVmem) j ⟶ Y)
    (hf : ∀ g : G, pullback.map (σ.quotientπ V hVs hVa hVmem) j
        (σ.quotientπ V hVs hVa hVmem) j (σ.hom g) (𝟙 Q') (𝟙 _)
        (by rw [Category.comp_id, hom_quotientπ]) (by simp) ≫ f = f) :
    ∃ q : Q' ⟶ Y, pullback.snd (σ.quotientπ V hVs hVa hVmem) j ≫ q = f := by
  apply σ.exists_quotientπ_lift_of_chartwise V hVs hVa hVmem hfree j f
  exact σ.exists_chart_isPullback_lift V hVs hVa hVmem j f hf

end AlgebraicGeometry.SchemeAction
