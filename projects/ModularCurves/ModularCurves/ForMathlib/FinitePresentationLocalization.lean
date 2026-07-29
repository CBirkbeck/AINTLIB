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

private theorem SpreadData.isLocalization_away_of_baseChange
    (D : SpreadData 𝒮 uA B) {i : ι} (h : D.i₀ ≤ i)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (b_i : D.spreadStage (t := t) h) (b : B)
    (hb : D.stageToColimit H ⟨i, h⟩ b_i = b) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    let e := D.baseChangeColimEquiv h H
    letI : Algebra (A ⊗[𝒮 i] D.spreadStage (t := t) h)
        (Localization.Away b) :=
      ((algebraMap B (Localization.Away b)).comp e.toRingHom).toAlgebra
    IsLocalization
      ((Submonoid.powers b_i).map
        (Algebra.TensorProduct.includeRight (R := 𝒮 i) (A := A)))
      (Localization.Away b) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let e := D.baseChangeColimEquiv h H
  letI : Algebra (A ⊗[𝒮 i] D.spreadStage (t := t) h)
      (Localization.Away b) :=
    ((algebraMap B (Localization.Away b)).comp e.toRingHom).toAlgebra
  refine IsLocalization.of_ringEquiv_left
    (M₁ := Submonoid.powers b)
    (M₂ := (Submonoid.powers b_i).map
      (Algebra.TensorProduct.includeRight (R := 𝒮 i) (A := A)))
    e.toRingEquiv ?_ ?_
  · simp only [Submonoid.map_powers,
      Algebra.TensorProduct.includeRight_apply]
    exact congrArg Submonoid.powers
      ((D.baseChangeColimEquiv_tmul h H b_i).trans hb)
  · intro x
    rfl

/-- The explicit base-change equivalence for a principal localization of a spread
model, with its target identified using the chosen colimit representative. -/
noncomputable def SpreadData.awayBaseChangeEquiv
    (D : SpreadData 𝒮 uA B) {i : ι} (h : D.i₀ ≤ i)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (b_i : D.spreadStage (t := t) h) (b : B)
    (hb : D.stageToColimit H ⟨i, h⟩ b_i = b) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    (A ⊗[𝒮 i] Localization.Away b_i) ≃ₐ[A] Localization.Away b := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let e := D.baseChangeColimEquiv h H
  letI : Algebra (A ⊗[𝒮 i] D.spreadStage (t := t) h)
      (Localization.Away b) :=
    ((algebraMap B (Localization.Away b)).comp e.toRingHom).toAlgebra
  letI : IsScalarTower A (A ⊗[𝒮 i] D.spreadStage (t := t) h)
      (Localization.Away b) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap A (Localization.Away b) x =
        algebraMap B (Localization.Away b) (e (x ⊗ₜ[𝒮 i] 1))
      rw [show x ⊗ₜ[𝒮 i] (1 : D.spreadStage (t := t) h) =
        algebraMap A (A ⊗[𝒮 i] D.spreadStage (t := t) h) x by rfl,
        e.commutes,
        IsScalarTower.algebraMap_apply A B (Localization.Away b)]
  haveI := D.isLocalization_away_of_baseChange h H b_i b hb
  exact IsLocalization.tensorProductEquivOfMapIncludeRight
    (𝒮 i) A (Submonoid.powers b_i) (Localization.Away b_i)
      (Localization.Away b)

/-- On elements from the stage model, the explicit away-localization equivalence
is the stage-to-colimit map followed by the localization algebra map. -/
lemma SpreadData.awayBaseChangeEquiv_tmul_algebraMap
    (D : SpreadData 𝒮 uA B) {i : ι} (h : D.i₀ ≤ i)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (b_i : D.spreadStage (t := t) h) (b : B)
    (hb : D.stageToColimit H ⟨i, h⟩ b_i = b)
    (x : D.spreadStage (t := t) h) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    D.awayBaseChangeEquiv h H b_i b hb
        (1 ⊗ₜ[𝒮 i]
          algebraMap (D.spreadStage (t := t) h)
            (Localization.Away b_i) x) =
      algebraMap B (Localization.Away b)
        (D.stageToColimit H ⟨i, h⟩ x) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let e := D.baseChangeColimEquiv h H
  letI : Algebra (A ⊗[𝒮 i] D.spreadStage (t := t) h)
      (Localization.Away b) :=
    ((algebraMap B (Localization.Away b)).comp e.toRingHom).toAlgebra
  letI : IsScalarTower A (A ⊗[𝒮 i] D.spreadStage (t := t) h)
      (Localization.Away b) :=
    IsScalarTower.of_algebraMap_eq fun y => by
      change algebraMap A (Localization.Away b) y =
        algebraMap B (Localization.Away b) (e (y ⊗ₜ[𝒮 i] 1))
      rw [show y ⊗ₜ[𝒮 i] (1 : D.spreadStage (t := t) h) =
        algebraMap A (A ⊗[𝒮 i] D.spreadStage (t := t) h) y by rfl,
        e.commutes,
        IsScalarTower.algebraMap_apply A B (Localization.Away b)]
  haveI := D.isLocalization_away_of_baseChange h H b_i b hb
  change IsLocalization.tensorProductEquivOfMapIncludeRight
      (𝒮 i) A (Submonoid.powers b_i) (Localization.Away b_i)
        (Localization.Away b)
      (1 ⊗ₜ[𝒮 i]
        algebraMap (D.spreadStage (t := t) h)
          (Localization.Away b_i) x) =
    algebraMap B (Localization.Away b)
      (D.stageToColimit H ⟨i, h⟩ x)
  rw [IsLocalization.tensorProductEquivOfMapIncludeRight_tmul]
  change algebraMap B (Localization.Away b)
      (e (1 ⊗ₜ[𝒮 i] x)) =
    algebraMap B (Localization.Away b)
      (D.stageToColimit H ⟨i, h⟩ x)
  rw [D.baseChangeColimEquiv_tmul h H x]

/-- The explicit away-localization base-change equivalences identify the scalar
extension of a compatible stage map with the canonical map at the colimit. -/
theorem SpreadData.awayBaseChangeEquiv_map
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (F : B₁ →ₐ[A] B₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f x) =
      F (D₁.stageToColimit H ⟨i, h₁⟩ x))
    (b_i : D₁.spreadStage (t := t) h₁) (b : B₁)
    (hb : D₁.stageToColimit H ⟨i, h₁⟩ b_i = b) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    (D₂.awayBaseChangeEquiv h₂ H (f b_i) (F b)
        ((hf b_i).trans (congrArg F hb))).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A A)
          (IsLocalization.Away.mapₐ
            (Localization.Away b_i) (Localization.Away (f b_i)) f b_i)) =
      (IsLocalization.Away.mapₐ
          (Localization.Away b) (Localization.Away (F b)) F b).comp
        (D₁.awayBaseChangeEquiv h₁ H b_i b hb).toAlgHom := by
  subst b
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i)
      (Localization.Away (F (D₁.stageToColimit H ⟨i, h₁⟩ b_i))) :=
    ((algebraMap A
        (Localization.Away (F (D₁.stageToColimit H ⟨i, h₁⟩ b_i)))).comp
      (algebraMap (𝒮 i) A)).toAlgebra
  letI : IsScalarTower (𝒮 i) A
      (Localization.Away (F (D₁.stageToColimit H ⟨i, h₁⟩ b_i))) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers b_i)
  apply RingHom.ext
  intro x
  change D₂.awayBaseChangeEquiv h₂ H (f b_i)
      (F (D₁.stageToColimit H ⟨i, h₁⟩ b_i))
      ((hf b_i).trans (congrArg F rfl))
      ((Algebra.TensorProduct.map (AlgHom.id A A)
        (IsLocalization.Away.mapₐ
          (Localization.Away b_i) (Localization.Away (f b_i)) f b_i))
        (1 ⊗ₜ[𝒮 i]
          algebraMap (D₁.spreadStage (t := t) h₁)
            (Localization.Away b_i) x)) =
    (IsLocalization.Away.mapₐ
      (Localization.Away (D₁.stageToColimit H ⟨i, h₁⟩ b_i))
      (Localization.Away
        (F (D₁.stageToColimit H ⟨i, h₁⟩ b_i)))
      F (D₁.stageToColimit H ⟨i, h₁⟩ b_i))
      (D₁.awayBaseChangeEquiv h₁ H b_i
        (D₁.stageToColimit H ⟨i, h₁⟩ b_i) rfl
        (1 ⊗ₜ[𝒮 i]
          algebraMap (D₁.spreadStage (t := t) h₁)
            (Localization.Away b_i) x))
  rw [Algebra.TensorProduct.map_tmul]
  simp only [map_one]
  rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rw [D₂.awayBaseChangeEquiv_tmul_algebraMap,
    D₁.awayBaseChangeEquiv_tmul_algebraMap]
  rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  exact congrArg
    (algebraMap B₂
      (Localization.Away
        (F (D₁.stageToColimit H ⟨i, h₁⟩ b_i))))
    (hf x)

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
  exact ⟨D.awayBaseChangeEquiv h H b_i b hb⟩

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
