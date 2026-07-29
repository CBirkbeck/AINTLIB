import Mathlib.RingTheory.Smooth.NoetherianDescent
import ModularCurves.ForMathlib.FinitePresentationDescent

/-!
# Smooth models over filtered-colimit stages

This file shows that a chosen finite-presentation model of a smooth algebra becomes
smooth at a sufficiently large stage. The proof uses the finite-type coefficient model
from Stacks Project, Tag 00TP and then identifies it with the chosen model by descending
an algebra equivalence and both inverse identities.
-/

universe u

open TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uS : ∀ i, 𝒮 i →ₐ[R] A}
  {B : Type u} [CommRing B] [Algebra A B]

private noncomputable def SpreadData.ofStageModel
    (i : ι) (C : Type u) [CommRing C] [Algebra (𝒮 i) C]
    [FinitePresentation (𝒮 i) C]
    (e : letI : Algebra (𝒮 i) A := (uS i).toRingHom.toAlgebra
      (A ⊗[𝒮 i] C) ≃ₐ[A] B) : SpreadData 𝒮 uS B := by
  letI : Algebra (𝒮 i) A := (uS i).toRingHom.toAlgebra
  let P := Presentation.ofFinitePresentation (𝒮 i) C
  let q : (MvPolynomial (Fin (Presentation.ofFinitePresentationVars (𝒮 i) C)) (𝒮 i) ⧸
      Ideal.span (Set.range P.relation)) ≃ₐ[𝒮 i] C :=
    (Ideal.quotientEquivAlgOfEq (𝒮 i) P.span_range_relation_eq_ker).trans
      (P.quotientEquiv.restrictScalars (𝒮 i))
  let tq : (A ⊗[𝒮 i] (MvPolynomial
      (Fin (Presentation.ofFinitePresentationVars (𝒮 i) C)) (𝒮 i) ⧸
        Ideal.span (Set.range P.relation))) ≃ₐ[A] (A ⊗[𝒮 i] C) :=
    Algebra.TensorProduct.congr AlgEquiv.refl q
  exact
    { i₀ := i
      m := Presentation.ofFinitePresentationVars (𝒮 i) C
      k := Presentation.ofFinitePresentationRels (𝒮 i) C
      g := P.relation
      equiv := ⟨(presentedBaseChange P.relation).symm |>.trans tq |>.trans e⟩ }

private theorem SpreadData.smooth_ofStageModel
    (i : ι) (C : Type u) [CommRing C] [Algebra (𝒮 i) C]
    [FinitePresentation (𝒮 i) C] [Smooth (𝒮 i) C]
    (e : letI : Algebra (𝒮 i) A := (uS i).toRingHom.toAlgebra
      (A ⊗[𝒮 i] C) ≃ₐ[A] B)
    {j : ι} (hij : i ≤ j) :
    Smooth (𝒮 j) ((SpreadData.ofStageModel (uS := uS) i C e).spreadStage
      (t := t) (show (SpreadData.ofStageModel (uS := uS) i C e).i₀ ≤ j from hij)) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let P := Presentation.ofFinitePresentation (𝒮 i) C
  let q : (MvPolynomial (Fin (Presentation.ofFinitePresentationVars (𝒮 i) C)) (𝒮 i) ⧸
      Ideal.span (Set.range P.relation)) ≃ₐ[𝒮 i] C :=
    (Ideal.quotientEquivAlgOfEq (𝒮 i) P.span_range_relation_eq_ker).trans
      (P.quotientEquiv.restrictScalars (𝒮 i))
  let tq : ((𝒮 j) ⊗[𝒮 i] (MvPolynomial
      (Fin (Presentation.ofFinitePresentationVars (𝒮 i) C)) (𝒮 i) ⧸
        Ideal.span (Set.range P.relation))) ≃ₐ[𝒮 j] ((𝒮 j) ⊗[𝒮 i] C) :=
    Algebra.TensorProduct.congr AlgEquiv.refl q
  let eStage := tq.symm.trans (presentedBaseChange P.relation)
  exact Smooth.of_equiv eStage

private noncomputable def SpreadData.mapToStageSpreadStageEquiv
    (D : SpreadData 𝒮 uS B) (H : IsFilteredAlgColimit R 𝒮 t A uS)
    {i j : ι} (hi : D.i₀ ≤ i) (hij : i ≤ j) :
    (D.mapToStage H hi).spreadStage (t := t) hij ≃ₐ[𝒮 j]
      D.spreadStage (t := t) (hi.trans hij) := by
  change (MvPolynomial (Fin D.m) (𝒮 j) ⧸ Ideal.span (Set.range fun r =>
      MvPolynomial.map (t hij).toRingHom
        (MvPolynomial.map (t hi).toRingHom (D.g r)))) ≃ₐ[𝒮 j]
    (MvPolynomial (Fin D.m) (𝒮 j) ⧸ Ideal.span (Set.range fun r =>
      MvPolynomial.map (t (hi.trans hij)).toRingHom (D.g r)))
  refine Ideal.quotientEquivAlgOfEq (𝒮 j) ?_
  congr 2
  funext r
  rw [MvPolynomial.map_map, H.t_comp]

private theorem SpreadData.exists_algEquiv_at_stage
    {B₁ B₂ : Type u} [CommRing B₁] [Algebra A B₁]
    [CommRing B₂] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uS B₁) (D₂ : SpreadData 𝒮 uS B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uS) (e : B₁ ≃ₐ[A] B₂) :
    ∃ (j : ι) (h₁ : D₁.i₀ ≤ j) (h₂ : D₂.i₀ ≤ j),
      Nonempty (D₁.spreadStage (t := t) h₁ ≃ₐ[𝒮 j]
        D₂.spreadStage (t := t) h₂) := by
  classical
  haveI := H.directed
  haveI := H.nonempty
  obtain ⟨i, hi₁, hi₂⟩ := exists_ge_ge D₁.i₀ D₂.i₀
  let E₁ := D₁.mapToStage H hi₁
  let E₂ := D₂.mapToStage H hi₂
  obtain ⟨jf, h₁f, h₂f, f, hf⟩ :=
    SpreadData.exists_map_at_stage H E₁ E₂ rfl e.toAlgHom
  obtain ⟨jg, h₂g, h₁g, g, hg⟩ :=
    SpreadData.exists_map_at_stage H E₂ E₁ rfl e.symm.toAlgHom
  obtain ⟨k, hfk, hgk⟩ := exists_ge_ge jf jg
  let h₁k := h₁f.trans hfk
  let h₂k := h₂f.trans hfk
  let fK := E₁.mapAtLaterStage E₂ H h₁f h₂f hfk f
  let gK := E₂.mapAtLaterStage E₁ H h₂g h₁g hgk g
  have hfK (x : E₁.spreadStage (t := t) h₁k) :
      E₂.stageToColimit H ⟨k, h₂k⟩ (fK x) =
        e (E₁.stageToColimit H ⟨k, h₁k⟩ x) :=
    E₁.mapAtLaterStage_colimit E₂ H h₁f h₂f hfk f e.toAlgHom hf x
  have hgK (x : E₂.spreadStage (t := t) h₂k) :
      E₁.stageToColimit H ⟨k, h₁k⟩ (gK x) =
        e.symm (E₂.stageToColimit H ⟨k, h₂k⟩ x) :=
    E₂.mapAtLaterStage_colimit E₁ H h₂g h₁g hgk g e.symm.toAlgHom hg x
  let gf := gK.comp fK
  let id₁ := AlgHom.id (𝒮 k) (E₁.spreadStage (t := t) h₁k)
  have hgfColimit (x : E₁.spreadStage (t := t) h₁k) :
      E₁.stageToColimit H ⟨k, h₁k⟩ (gf x) =
        E₁.stageToColimit H ⟨k, h₁k⟩ (id₁ x) := by
    calc
      E₁.stageToColimit H ⟨k, h₁k⟩ (gf x) =
          e.symm (E₂.stageToColimit H ⟨k, h₂k⟩ (fK x)) := hgK (fK x)
      _ = e.symm (e (E₁.stageToColimit H ⟨k, h₁k⟩ x)) := congrArg e.symm (hfK x)
      _ = E₁.stageToColimit H ⟨k, h₁k⟩ x := e.symm_apply_apply _
      _ = E₁.stageToColimit H ⟨k, h₁k⟩ (id₁ x) := rfl
  let Cgf := Classical.choice (E₁.exists_common_eq_mapAtLaterStage E₁ H h₁k h₁k
    (ρ := Fin 1) (fun _ => gf) (fun _ => id₁) (fun _ x => hgfColimit x))
  let l := Cgf.stage
  let hkl : k ≤ l := Cgf.le_stage
  let h₁l := h₁k.trans hkl
  let h₂l := h₂k.trans hkl
  let fL := E₁.mapAtLaterStage E₂ H h₁k h₂k hkl fK
  let gL := E₂.mapAtLaterStage E₁ H h₂k h₁k hkl gK
  have hgfL : gL.comp fL = AlgHom.id (𝒮 l) (E₁.spreadStage (t := t) h₁l) := by
    have h := Cgf.maps_agree 0
    rw [E₁.mapAtLaterStage_comp E₂ E₁ H h₁k h₂k h₁k hkl fK gK,
      E₁.mapAtLaterStage_id H h₁k hkl] at h
    exact h
  have hfL (x : E₁.spreadStage (t := t) h₁l) :
      E₂.stageToColimit H ⟨l, h₂l⟩ (fL x) =
        e (E₁.stageToColimit H ⟨l, h₁l⟩ x) :=
    E₁.mapAtLaterStage_colimit E₂ H h₁k h₂k hkl fK e.toAlgHom hfK x
  have hgL (x : E₂.spreadStage (t := t) h₂l) :
      E₁.stageToColimit H ⟨l, h₁l⟩ (gL x) =
        e.symm (E₂.stageToColimit H ⟨l, h₂l⟩ x) :=
    E₂.mapAtLaterStage_colimit E₁ H h₂k h₁k hkl gK e.symm.toAlgHom hgK x
  let fg := fL.comp gL
  let id₂ := AlgHom.id (𝒮 l) (E₂.spreadStage (t := t) h₂l)
  have hfgColimit (x : E₂.spreadStage (t := t) h₂l) :
      E₂.stageToColimit H ⟨l, h₂l⟩ (fg x) =
        E₂.stageToColimit H ⟨l, h₂l⟩ (id₂ x) := by
    calc
      E₂.stageToColimit H ⟨l, h₂l⟩ (fg x) =
          e (E₁.stageToColimit H ⟨l, h₁l⟩ (gL x)) := hfL (gL x)
      _ = e (e.symm (E₂.stageToColimit H ⟨l, h₂l⟩ x)) := congrArg e (hgL x)
      _ = E₂.stageToColimit H ⟨l, h₂l⟩ x := e.apply_symm_apply _
      _ = E₂.stageToColimit H ⟨l, h₂l⟩ (id₂ x) := rfl
  let Cfg := Classical.choice (E₂.exists_common_eq_mapAtLaterStage E₂ H h₂l h₂l
    (ρ := Fin 1) (fun _ => fg) (fun _ => id₂) (fun _ x => hfgColimit x))
  let m := Cfg.stage
  let hlm : l ≤ m := Cfg.le_stage
  let h₁m := h₁l.trans hlm
  let h₂m := h₂l.trans hlm
  let fM := E₁.mapAtLaterStage E₂ H h₁l h₂l hlm fL
  let gM := E₂.mapAtLaterStage E₁ H h₂l h₁l hlm gL
  have hfgM : fM.comp gM = AlgHom.id (𝒮 m) (E₂.spreadStage (t := t) h₂m) := by
    have h := Cfg.maps_agree 0
    rw [E₂.mapAtLaterStage_comp E₁ E₂ H h₂l h₁l h₂l hlm gL fL,
      E₂.mapAtLaterStage_id H h₂l hlm] at h
    exact h
  have hgfM : gM.comp fM = AlgHom.id (𝒮 m) (E₁.spreadStage (t := t) h₁m) := by
    have h := congrArg (E₁.mapAtLaterStage E₁ H h₁l h₁l hlm) hgfL
    rw [E₁.mapAtLaterStage_comp E₂ E₁ H h₁l h₂l h₁l hlm fL gL,
      E₁.mapAtLaterStage_id H h₁l hlm] at h
    exact h
  let em : E₁.spreadStage (t := t) h₁m ≃ₐ[𝒮 m]
      E₂.spreadStage (t := t) h₂m :=
    AlgEquiv.ofAlgHom fM gM hfgM hgfM
  let e₁ := D₁.mapToStageSpreadStageEquiv H hi₁ h₁m
  let e₂ := D₂.mapToStageSpreadStageEquiv H hi₂ h₂m
  exact ⟨m, hi₁.trans h₁m, hi₂.trans h₂m, ⟨e₁.symm.trans (em.trans e₂)⟩⟩

/-- A chosen finite-presentation model of a smooth algebra over a filtered colimit
becomes smooth at some stage and remains smooth at every later stage.

The Noetherian hypothesis is imposed only on the coefficient ring used to present the
filtered system. It is not imposed on the colimit algebra or on any later stage. -/
theorem SpreadData.exists_smooth_stage
    (D : SpreadData 𝒮 uS B) (H : IsFilteredAlgColimit R 𝒮 t A uS)
    [IsNoetherianRing R] [Algebra R B] [IsScalarTower R A B] [Smooth A B] :
    ∃ (i : ι) (hi : D.i₀ ≤ i), ∀ ⦃j : ι⦄ (hij : i ≤ j),
      Smooth (𝒮 j) (D.spreadStage (t := t) (hi.trans hij)) := by
  classical
  obtain ⟨A₀, B₀, hB₀Ring, hB₀Alg, hA₀, hB₀Smooth, ⟨eB⟩⟩ :=
    Smooth.exists_subalgebra_fg R A B
  letI : CommRing B₀ := hB₀Ring
  letI : Algebra A₀ B₀ := hB₀Alg
  letI : Smooth A₀ B₀ := hB₀Smooth
  letI : FiniteType R A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  letI : FinitePresentation R A₀ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨i, f₀, hf₀⟩ := H.exists_factor_of_finitePresentation A₀ A₀.val
  letI : Algebra A₀ (𝒮 i) := f₀.toRingHom.toAlgebra
  letI : Algebra (𝒮 i) A := (uS i).toRingHom.toAlgebra
  letI : IsScalarTower A₀ (𝒮 i) A := IsScalarTower.of_algebraMap_eq fun x => by
    change (x : A) = uS i (f₀ x)
    exact (AlgHom.congr_fun hf₀ x).symm
  let C := (𝒮 i) ⊗[A₀] B₀
  let eC : (A ⊗[𝒮 i] C) ≃ₐ[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A₀ (𝒮 i) A A B₀).trans eB.symm
  let E := SpreadData.ofStageModel (uS := uS) i C eC
  obtain ⟨k, hkD, hkE, ⟨eStage⟩⟩ :=
    D.exists_algEquiv_at_stage E H (AlgEquiv.refl : B ≃ₐ[A] B)
  haveI hSmoothE : Smooth (𝒮 k) (E.spreadStage (t := t) hkE) :=
    SpreadData.smooth_ofStageModel (t := t) (uS := uS) i C eC hkE
  haveI hSmoothD : Smooth (𝒮 k) (D.spreadStage (t := t) hkD) :=
    Smooth.of_equiv eStage.symm
  refine ⟨k, hkD, fun {j} hkj => ?_⟩
  letI : Algebra (𝒮 k) (𝒮 j) := (t hkj).toRingHom.toAlgebra
  exact Smooth.of_equiv
    (A := (𝒮 j) ⊗[𝒮 k] (D.spreadStage (t := t) hkD))
    (B := D.spreadStage (t := t) (hkD.trans hkj))
    (D.spreadStageBaseChangeEquiv hkj hkD H)

end Algebra
