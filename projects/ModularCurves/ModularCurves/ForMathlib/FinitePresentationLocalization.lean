import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.BaseChange
import ModularCurves.ForMathlib.FinitePresentationDescent

/-!
# Spreading principal opens of finitely presented affine algebras

This file supplements finite-presentation spreading with the element and localization
data defining a principal open. The resulting stage localization is finitely presented,
and base change to the filtered colimit recovers the original localization.
-/

open TensorProduct

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
  {B : Type u} [CommRing B] [Algebra A B]

/-- The explicit base-change equivalence from a spread model to its colimit algebra. -/
noncomputable def SpreadData.baseChangeColimEquiv
    (D : SpreadData 𝒮 uA B) ⦃i : ι⦄ (h : D.i₀ ≤ i)
    (H : IsFilteredAlgColimit R 𝒮 t A uA) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    (A ⊗[𝒮 i] D.spreadStage (t := t) h) ≃ₐ[A] B := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  exact ((presentedBaseChange
    (fun j' => MvPolynomial.map (t h).toRingHom (D.g j'))).trans
      (Ideal.quotientEquivAlgOfEq A
        (congrArg (fun f => Ideal.span (Set.range f)) (funext fun j' => by
          rw [MvPolynomial.map_map]
          exact congrArg (fun f => MvPolynomial.map f (D.g j')) (H.u_comp h))))).trans
    (Classical.choice D.equiv)

/-- The colimit base-change equivalence sends a pure tensor from the stage model to the
corresponding element under `stageToColimit`. -/
lemma SpreadData.baseChangeColimEquiv_tmul
    (D : SpreadData 𝒮 uA B) ⦃i : ι⦄ (h : D.i₀ ≤ i)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (x : D.spreadStage (t := t) h) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    D.baseChangeColimEquiv h H (1 ⊗ₜ x) =
      D.stageToColimit H ⟨i, h⟩ x := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [SpreadData.baseChangeColimEquiv,
    SpreadData.stageToColimit_apply, AlgEquiv.trans_apply]
  change Classical.choice D.equiv
    (Ideal.quotientEquivAlgOfEq A _
      ((presentedBaseChange
        (fun j' => MvPolynomial.map (t h).toRingHom (D.g j')))
        (1 ⊗ₜ[𝒮 i] Ideal.Quotient.mk _ p))) = _
  rw [show (presentedBaseChange
      (fun j' => MvPolynomial.map (t h).toRingHom (D.g j')))
      (1 ⊗ₜ[𝒮 i] Ideal.Quotient.mk _ p) =
      presentedBaseChangeAux
        (fun j' => MvPolynomial.map (t h).toRingHom (D.g j'))
        (Ideal.Quotient.mk _ p) by
      rw [presentedBaseChange, AlgEquiv.ofAlgHom_apply,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]]
  rw [presentedBaseChangeAux_mk, Ideal.quotientEquivAlgOfEq_mk, presentedU_mk]
  rfl

/-- Every element of the colimit algebra is represented in a later spread model. -/
theorem SpreadData.exists_stageToColimit_eq
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA) (b : B) :
    ∃ (P : {i : ι // D.i₀ ≤ i}) (b_i : D.spreadStage (t := t) P.2),
      D.stageToColimit H P b_i = b := by
  classical
  letI : ∀ P : {i : ι // D.i₀ ≤ i},
      Algebra (𝒮 D.i₀) (D.spreadStage (t := t) P.2) :=
    fun P => ((algebraMap (𝒮 P.1) (D.spreadStage (t := t) P.2)).comp
      (t P.2).toRingHom).toAlgebra
  letI : Algebra (𝒮 D.i₀) B :=
    ((algebraMap A B).comp (uA D.i₀).toRingHom).toAlgebra
  exact (D.isFilteredAlgColimit H).jointly_surjective b

/-- A principal localization of a spread model is finitely presented over the stage base. -/
theorem SpreadData.away_finitePresentation
    (D : SpreadData 𝒮 uA B) {i : ι} (h : D.i₀ ≤ i)
    (b_i : D.spreadStage (t := t) h) :
    FinitePresentation (𝒮 i) (Localization.Away b_i) := by
  letI : FinitePresentation (𝒮 i) (D.spreadStage (t := t) h) :=
    D.spreadStage_finitePresentation h
  letI : FinitePresentation (D.spreadStage (t := t) h)
      (Localization.Away b_i) := inferInstance
  exact FinitePresentation.trans (𝒮 i) (D.spreadStage (t := t) h)
    (Localization.Away b_i)

private noncomputable def awayAlgEquivOfAlgEquiv
    {S T C : Type u} [CommRing S] [CommRing T] [CommRing C]
    [Algebra S T] [Algebra S C] (e : T ≃ₐ[S] C) (x : T) :
    Localization.Away x ≃ₐ[S] Localization.Away (e x) := by
  have hpowers : Submonoid.map e.toRingEquiv.toMonoidHom (Submonoid.powers x) =
      Submonoid.powers (e x) := by
    rw [Submonoid.map_powers]
    rfl
  exact IsLocalization.algEquivOfAlgEquiv _ _ e hpowers

private noncomputable def awayTensorBaseChangeEquiv
    {S T C : Type u} [CommRing S] [CommRing T] [CommRing C]
    {W : Type u} [CommRing W] [Algebra S T] [Algebra S W] [Algebra T C]
    (e : T ⊗[S] W ≃ₐ[T] C) (x : W) :
    (T ⊗[S] Localization.Away x) ≃ₐ[T]
      Localization.Away (e ((1 : T) ⊗ₜ[S] x)) :=
  (IsLocalization.Away.tensorProductEquivTMulRight S T x
    (Localization.Away x)).trans
      (awayAlgEquivOfAlgEquiv e ((1 : T) ⊗ₜ[S] x))

/-- Base change of a principal localization of a spread model recovers the localization
at the represented colimit element. -/
theorem SpreadData.away_baseChange
    (D : SpreadData 𝒮 uA B) {i : ι} (h : D.i₀ ≤ i)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (b_i : D.spreadStage (t := t) h) (b : B)
    (hb : D.stageToColimit H ⟨i, h⟩ b_i = b) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    Nonempty ((A ⊗[𝒮 i] Localization.Away b_i) ≃ₐ[A]
      Localization.Away b) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let e := D.baseChangeColimEquiv h H
  have he : e ((1 : A) ⊗ₜ[𝒮 i] b_i) = b :=
    (D.baseChangeColimEquiv_tmul h H b_i).trans hb
  rw [← he]
  exact ⟨awayTensorBaseChangeEquiv e b_i⟩

/-- A principal open of a finitely presented affine algebra over a filtered colimit
descends to a finitely presented principal open at one stage and is recovered by base
change. -/
theorem IsFilteredAlgColimit.exists_spreadAway
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (B : Type u) [CommRing B] [Algebra A B] [FinitePresentation A B]
    (b : B) :
    ∃ (D : SpreadData 𝒮 uA B) (i : ι) (h : D.i₀ ≤ i)
        (b_i : D.spreadStage (t := t) h),
      D.stageToColimit H ⟨i, h⟩ b_i = b ∧
        letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
        FinitePresentation (𝒮 i) (Localization.Away b_i) ∧
          Nonempty ((A ⊗[𝒮 i] Localization.Away b_i) ≃ₐ[A]
            Localization.Away b) := by
  classical
  obtain ⟨D⟩ := exists_spreadData B H
  obtain ⟨P, b_i, hb_i⟩ := D.exists_stageToColimit_eq H b
  refine ⟨D, P.1, P.2, b_i, hb_i, D.away_finitePresentation P.2 b_i, ?_⟩
  exact D.away_baseChange P.2 H b_i b hb_i

end Algebra
