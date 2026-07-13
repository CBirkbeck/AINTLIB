import ModularCurves.ForMathlib.FinitePresentationBaseChangeEquiv

/-!
# Reflecting principal-localization equivalences at a finite stage

The explicit base-change equivalence for a spread algebra extends to its
principal localizations. This identifies scalar extension of a canonical away
map with the literal away map between the later spread models.
-/

universe u

open TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}

private theorem SpreadData.map_powers_tmul_eq
    {B : Type u} [CommRing B] [Algebra A B]
    (D : SpreadData 𝒮 uA B) {i j : ι} (h : D.i₀ ≤ i) (hij : i ≤ j)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (b_i : D.spreadStage (t := t) h)
    (b_j : D.spreadStage (t := t) (h.trans hij))
    (hb : D.stageTransition H
      (show (⟨i, h⟩ : {q : ι // D.i₀ ≤ q}) ≤
        ⟨j, h.trans hij⟩ from hij) b_i = b_j) :
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    Submonoid.map (D.spreadStageBaseChangeEquiv hij h H)
        (Submonoid.powers ((1 : 𝒮 j) ⊗ₜ[𝒮 i] b_i)) =
      Submonoid.powers b_j := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers
    ((D.spreadStageBaseChangeEquiv_tmul hij h H b_i).trans hb)

/-- Scalar extension of a principal localization of a spread model is the
principal localization at the transitioned function. -/
noncomputable def SpreadData.awayStageBaseChangeEquiv
    {B : Type u} [CommRing B] [Algebra A B]
    (D : SpreadData 𝒮 uA B) {i j : ι} (h : D.i₀ ≤ i) (hij : i ≤ j)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (b_i : D.spreadStage (t := t) h)
    (b_j : D.spreadStage (t := t) (h.trans hij))
    (hb : D.stageTransition H
      (show (⟨i, h⟩ : {q : ι // D.i₀ ≤ q}) ≤
        ⟨j, h.trans hij⟩ from hij) b_i = b_j) :
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    𝒮 j ⊗[𝒮 i] Localization.Away b_i ≃ₐ[𝒮 j]
      Localization.Away b_j := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  exact (IsLocalization.Away.tensorProductEquivTMulRight
    (𝒮 i) (𝒮 j) b_i (Localization.Away b_i)).trans
      (IsLocalization.algEquivOfAlgEquiv
        (Localization.Away ((1 : 𝒮 j) ⊗ₜ[𝒮 i] b_i))
        (Localization.Away b_j)
        (D.spreadStageBaseChangeEquiv hij h H)
        (D.map_powers_tmul_eq h hij H b_i b_j hb))

/-- The stage-localization base-change equivalence sends a pure tensor of a
localized stage element to the localization of its stage transition. -/
theorem SpreadData.awayStageBaseChangeEquiv_tmul_algebraMap
    {B : Type u} [CommRing B] [Algebra A B]
    (D : SpreadData 𝒮 uA B) {i j : ι} (h : D.i₀ ≤ i) (hij : i ≤ j)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (b_i : D.spreadStage (t := t) h)
    (b_j : D.spreadStage (t := t) (h.trans hij))
    (hb : D.stageTransition H
      (show (⟨i, h⟩ : {q : ι // D.i₀ ≤ q}) ≤
        ⟨j, h.trans hij⟩ from hij) b_i = b_j)
    (x : D.spreadStage (t := t) h) :
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    D.awayStageBaseChangeEquiv h hij H b_i b_j hb
        (1 ⊗ₜ[𝒮 i]
          algebraMap (D.spreadStage (t := t) h)
            (Localization.Away b_i) x) =
      algebraMap (D.spreadStage (t := t) (h.trans hij))
        (Localization.Away b_j)
        (D.stageTransition H
          (show (⟨i, h⟩ : {q : ι // D.i₀ ≤ q}) ≤
            ⟨j, h.trans hij⟩ from hij) x) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  simp only [SpreadData.awayStageBaseChangeEquiv, AlgEquiv.trans_apply]
  rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
  rw [IsLocalization.algEquivOfAlgEquiv_eq]
  rw [D.spreadStageBaseChangeEquiv_tmul]

private theorem SpreadData.stageTransition_image_eq_mapAtLaterStage
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (b_i : D₁.spreadStage (t := t) h₁)
    (b_j : D₁.spreadStage (t := t) (h₁.trans hij))
    (hb : D₁.stageTransition H
      (show (⟨i, h₁⟩ : {q : ι // D₁.i₀ ≤ q}) ≤
        ⟨j, h₁.trans hij⟩ from hij) b_i = b_j) :
    D₂.stageTransition H
        (show (⟨i, h₂⟩ : {q : ι // D₂.i₀ ≤ q}) ≤
          ⟨j, h₂.trans hij⟩ from hij) (f b_i) =
      D₁.mapAtLaterStage D₂ H h₁ h₂ hij f b_j := by
  exact (D₁.mapAtLaterStage_stageTransition D₂ H h₁ h₂ hij f b_i).symm.trans
    (congrArg (D₁.mapAtLaterStage D₂ H h₁ h₂ hij f) hb)

/-- Stage-localization base change is natural for the canonical away map. -/
theorem SpreadData.awayStageBaseChangeEquiv_map
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (b_i : D₁.spreadStage (t := t) h₁)
    (b_j : D₁.spreadStage (t := t) (h₁.trans hij))
    (hb : D₁.stageTransition H
      (show (⟨i, h₁⟩ : {q : ι // D₁.i₀ ≤ q}) ≤
        ⟨j, h₁.trans hij⟩ from hij) b_i = b_j) :
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    let f_j := D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
    let hb₂ := D₁.stageTransition_image_eq_mapAtLaterStage
      D₂ H h₁ h₂ hij f b_i b_j hb
    (D₂.awayStageBaseChangeEquiv h₂ hij H (f b_i) (f_j b_j) hb₂).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j))
          (IsLocalization.Away.mapₐ
            (Localization.Away b_i) (Localization.Away (f b_i)) f b_i)) =
      (IsLocalization.Away.mapₐ
          (Localization.Away b_j) (Localization.Away (f_j b_j)) f_j b_j).comp
        (D₁.awayStageBaseChangeEquiv h₁ hij H b_i b_j hb).toAlgHom := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let f_j := D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
  let hb₂ := D₁.stageTransition_image_eq_mapAtLaterStage
    D₂ H h₁ h₂ hij f b_i b_j hb
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers b_i)
  apply RingHom.ext
  intro x
  change D₂.awayStageBaseChangeEquiv h₂ hij H (f b_i) (f_j b_j) hb₂
      ((Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j))
        (IsLocalization.Away.mapₐ
          (Localization.Away b_i) (Localization.Away (f b_i)) f b_i))
        (1 ⊗ₜ[𝒮 i]
          algebraMap (D₁.spreadStage (t := t) h₁)
            (Localization.Away b_i) x)) =
    (IsLocalization.Away.mapₐ
      (Localization.Away b_j) (Localization.Away (f_j b_j)) f_j b_j)
      (D₁.awayStageBaseChangeEquiv h₁ hij H b_i b_j hb
        (1 ⊗ₜ[𝒮 i]
          algebraMap (D₁.spreadStage (t := t) h₁)
            (Localization.Away b_i) x))
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rw [D₂.awayStageBaseChangeEquiv_tmul_algebraMap,
    D₁.awayStageBaseChangeEquiv_tmul_algebraMap]
  rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  exact congrArg
    (algebraMap (D₂.spreadStage (t := t) (h₂.trans hij))
      (Localization.Away (f_j b_j)))
    (D₁.mapAtLaterStage_stageTransition D₂ H h₁ h₂ hij f x).symm

private theorem SpreadData.tensorProduct_awayMap_bijective
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (F : B₁ →ₐ[A] B₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f x) =
      F (D₁.stageToColimit H ⟨i, h₁⟩ x))
    (b_i : D₁.spreadStage (t := t) h₁) (b : B₁)
    (hb : D₁.stageToColimit H ⟨i, h₁⟩ b_i = b)
    (hbij : Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away b) (Localization.Away (F b)) F b)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) A)
        (IsLocalization.Away.mapₐ
          (Localization.Away b_i) (Localization.Away (f b_i)) f b_i)) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let E₁ := D₁.awayBaseChangeEquiv h₁ H b_i b hb
  let E₂ := D₂.awayBaseChangeEquiv h₂ H (f b_i) (F b)
    ((hf b_i).trans (congrArg F hb))
  let g := Algebra.TensorProduct.map (AlgHom.id A A)
    (IsLocalization.Away.mapₐ
      (Localization.Away b_i) (Localization.Away (f b_i)) f b_i)
  have hcomp : Function.Bijective (E₂.toAlgHom.comp g) := by
    rw [D₁.awayBaseChangeEquiv_map D₂ h₁ h₂ H f F hf b_i b hb]
    exact hbij.comp E₁.bijective
  exact (E₂.bijective.of_comp_iff' g).mp hcomp

private theorem SpreadData.awayMapAtLaterStage_bijective
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (b_i : D₁.spreadStage (t := t) h₁)
    (hbij :
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      Function.Bijective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) (𝒮 j))
          (IsLocalization.Away.mapₐ
            (Localization.Away b_i) (Localization.Away (f b_i)) f b_i))) :
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    let b_j := D₁.stageTransition H
      (show (⟨i, h₁⟩ : {q : ι // D₁.i₀ ≤ q}) ≤
        ⟨j, h₁.trans hij⟩ from hij) b_i
    let f_j := D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
    Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away b_j) (Localization.Away (f_j b_j)) f_j b_j) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let b_j := D₁.stageTransition H
    (show (⟨i, h₁⟩ : {q : ι // D₁.i₀ ≤ q}) ≤
      ⟨j, h₁.trans hij⟩ from hij) b_i
  let f_j := D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
  let hb₂ := D₁.stageTransition_image_eq_mapAtLaterStage
    D₂ H h₁ h₂ hij f b_i b_j rfl
  let E₁ := D₁.awayStageBaseChangeEquiv h₁ hij H b_i b_j rfl
  let E₂ := D₂.awayStageBaseChangeEquiv h₂ hij H (f b_i) (f_j b_j) hb₂
  let g_j := IsLocalization.Away.mapₐ
    (Localization.Away b_j) (Localization.Away (f_j b_j)) f_j b_j
  let g := Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j))
    (IsLocalization.Away.mapₐ
      (Localization.Away b_i) (Localization.Away (f b_i)) f b_i)
  have hleft : Function.Bijective (E₂.toAlgHom.comp g) :=
    E₂.bijective.comp hbij
  have hright : Function.Bijective (g_j.comp E₁.toAlgHom) := by
    rw [← D₁.awayStageBaseChangeEquiv_map D₂ H h₁ h₂ hij f b_i b_j rfl]
    exact hleft
  exact (Function.Bijective.of_comp_iff g_j E₁.bijective).mp hright

/-- A compatible canonical away map that is bijective over the filtered
colimit becomes the literal bijective away map after one later stage. -/
theorem SpreadData.exists_awayMapAtLaterStage_bijective
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (F : B₁ →ₐ[A] B₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f x) =
      F (D₁.stageToColimit H ⟨i, h₁⟩ x))
    (b_i : D₁.spreadStage (t := t) h₁) (b : B₁)
    (hb : D₁.stageToColimit H ⟨i, h₁⟩ b_i = b)
    (hbij : Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away b) (Localization.Away (F b)) F b)) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      let b_j := D₁.stageTransition H
        (show (⟨i, h₁⟩ : {q : ι // D₁.i₀ ≤ q}) ≤
          ⟨j, h₁.trans hij⟩ from hij) b_i
      let f_j := D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
      Function.Bijective
        (IsLocalization.Away.mapₐ
          (Localization.Away b_j) (Localization.Away (f_j b_j)) f_j b_j) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let g := IsLocalization.Away.mapₐ
    (Localization.Away b_i) (Localization.Away (f b_i)) f b_i
  haveI : FinitePresentation (𝒮 i) (Localization.Away b_i) :=
    D₁.away_finitePresentation h₁ b_i
  haveI : FinitePresentation (𝒮 i) (Localization.Away (f b_i)) :=
    D₂.away_finitePresentation h₂ (f b_i)
  have hg : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) A) g) :=
    D₁.tensorProduct_awayMap_bijective D₂ H h₁ h₂ f F hf b_i b hb hbij
  obtain ⟨j, hij, hj⟩ := H.exists_tensorProductMap_bijective g hg
  exact ⟨j, hij,
    D₁.awayMapAtLaterStage_bijective D₂ H h₁ h₂ hij f b_i hj⟩

end Algebra
