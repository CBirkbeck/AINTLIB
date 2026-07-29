import ModularCurves.ForMathlib.FinitePresentationAwayMap

/-!
# Synchronizing finite families of principal-localization maps

Bijectivity of canonical away maps persists under later spread transitions.
Consequently finitely many such maps between varying spread models can be
realized at one common stage.
-/

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}

private theorem SpreadData.elementAtLaterStage_trans
    {B : Type u} [CommRing B] [Algebra A B]
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j k : ι} (h : D.i₀ ≤ i) (hij : i ≤ j) (hjk : j ≤ k)
    (b_i : D.spreadStage (t := t) h) :
    D.elementAtLaterStage H (h.trans hij) hjk
        (D.elementAtLaterStage H h hij b_i) =
      D.elementAtLaterStage H h (hij.trans hjk) b_i := by
  exact D.stageTransition_trans H h hij hjk b_i

private theorem awayMap_bijective_congr
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S →ₐ[R] T) (a b : S) (hf : f = g) (ha : a = b)
    (h : Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away a) (Localization.Away (f a)) f a)) :
    Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away b) (Localization.Away (g b)) g b) := by
  subst g
  subst b
  exact h

private theorem SpreadData.awayMapAtLaterStage_bijective_trans
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j k : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (hij : i ≤ j) (hjk : j ≤ k)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (b_i : D₁.spreadStage (t := t) h₁)
    (hbij :
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      Function.Bijective
        (D₁.awayMapAtLaterStage D₂ H h₁ h₂ hij f b_i)) :
    letI : Algebra (𝒮 i) (𝒮 k) :=
      (t (hij.trans hjk)).toRingHom.toAlgebra
    Function.Bijective
      (D₁.awayMapAtLaterStage D₂ H h₁ h₂ (hij.trans hjk) f b_i) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) (𝒮 k) := (t hjk).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 k) :=
    (t (hij.trans hjk)).toRingHom.toAlgebra
  have h := D₁.awayMapAtLaterStage_bijective D₂ H
    (h₁.trans hij) (h₂.trans hij) hjk
    (D₁.mapAtLaterStage D₂ H h₁ h₂ hij f)
    (D₁.elementAtLaterStage H h₁ hij b_i) hbij
  unfold SpreadData.awayMapAtLaterStage at h ⊢
  exact awayMap_bijective_congr _ _ _ _
    (D₁.mapAtLaterStage_trans D₂ H h₁ h₂ hij hjk f)
    (D₁.elementAtLaterStage_trans H h₁ hij hjk b_i) h

private structure SpreadData.AwayMapStage
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (b_i : D₁.spreadStage (t := t) h₁) where
  stage : ι
  le_stage : i ≤ stage
  map_bijective :
    letI : Algebra (𝒮 i) (𝒮 stage) := (t le_stage).toRingHom.toAlgebra
    Function.Bijective
      (D₁.awayMapAtLaterStage D₂ H h₁ h₂ le_stage f b_i)

private theorem SpreadData.exists_awayMapStage
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
    Nonempty (D₁.AwayMapStage D₂ H h₁ h₂ f b_i) := by
  obtain ⟨j, hij, hj⟩ := D₁.exists_awayMapAtLaterStage_bijective
    D₂ H h₁ h₂ f F hf b_i b hb hbij
  refine ⟨⟨j, hij, ?_⟩⟩
  exact hj

/-- A finite family of compatible bijective away maps between varying spread
models can be realized simultaneously at one common later stage. -/
theorem SpreadData.exists_common_awayMapAtLaterStage_bijective
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {κ ρ : Type*} [Finite ρ]
    (B : κ → Type u) [∀ q, CommRing (B q)] [∀ q, Algebra A (B q)]
    (D : ∀ q, SpreadData 𝒮 uA (B q)) (src dst : ρ → κ)
    {i : ι} (h : ∀ q, (D q).i₀ ≤ i)
    (f : ∀ r,
      (D (src r)).spreadStage (t := t) (h (src r)) →ₐ[𝒮 i]
        (D (dst r)).spreadStage (t := t) (h (dst r)))
    (F : ∀ r, B (src r) →ₐ[A] B (dst r))
    (hf : ∀ r x,
      (D (dst r)).stageToColimit H ⟨i, h (dst r)⟩ (f r x) =
        F r ((D (src r)).stageToColimit H ⟨i, h (src r)⟩ x))
    (b_i : ∀ r, (D (src r)).spreadStage (t := t) (h (src r)))
    (b : ∀ r, B (src r))
    (hb : ∀ r,
      (D (src r)).stageToColimit H ⟨i, h (src r)⟩ (b_i r) = b r)
    (hbij : ∀ r, Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away (b r)) (Localization.Away (F r (b r)))
          (F r) (b r))) :
    ∃ (j : ι) (hij : i ≤ j),
      ∀ r,
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      Function.Bijective ((D (src r)).awayMapAtLaterStage (D (dst r)) H
        (h (src r)) (h (dst r)) hij (f r) (b_i r)) := by
  classical
  let C : ∀ r, (D (src r)).AwayMapStage (D (dst r)) H
      (h (src r)) (h (dst r)) (f r) (b_i r) := fun r =>
    Classical.choice ((D (src r)).exists_awayMapStage
      (D (dst r)) H (h (src r)) (h (dst r)) (f r) (F r) (hf r)
        (b_i r) (b r) (hb r) (hbij r))
  letI : Fintype ρ := Fintype.ofFinite ρ
  haveI := H.directed
  haveI := H.nonempty
  obtain ⟨j, hjall⟩ :=
    (insert i (Finset.univ.image fun r => (C r).stage)).exists_le
  have hij : i ≤ j := hjall i (Finset.mem_insert_self i _)
  have hC : ∀ r, (C r).stage ≤ j := fun r => hjall (C r).stage
    (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem (fun r => (C r).stage) (Finset.mem_univ r)))
  refine ⟨j, hij, fun r => ?_⟩
  exact (D (src r)).awayMapAtLaterStage_bijective_trans
    (D (dst r)) H (h (src r)) (h (dst r)) (C r).le_stage (hC r)
      (f r) (b_i r) (C r).map_bijective

end Algebra
