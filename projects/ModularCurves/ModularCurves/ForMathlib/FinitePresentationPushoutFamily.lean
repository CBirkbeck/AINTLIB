import ModularCurves.ForMathlib.FinitePresentationPushout

/-!
# Synchronizing finite families of spread pushout squares

A pushout square of spread-stage algebra maps remains a pushout under every
later transition. Consequently finitely many colimit pushout squares can be
realized simultaneously at one common stage.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}

private structure SpreadData.PushoutStage
    {B₀ B₁ B₂ B₃ : Type u}
    [CommRing B₀] [CommRing B₁] [CommRing B₂] [CommRing B₃]
    [Algebra A B₀] [Algebra A B₁] [Algebra A B₂] [Algebra A B₃]
    (D₀ : SpreadData 𝒮 uA B₀) (D₁ : SpreadData 𝒮 uA B₁)
    (D₂ : SpreadData 𝒮 uA B₂) (D₃ : SpreadData 𝒮 uA B₃)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₀ : D₀.i₀ ≤ i) (h₁ : D₁.i₀ ≤ i)
    (h₂ : D₂.i₀ ≤ i) (h₃ : D₃.i₀ ≤ i)
    (f : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₁.spreadStage (t := t) h₁)
    (g : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (inl : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (inr : D₂.spreadStage (t := t) h₂ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃) where
  stage : ι
  le_stage : i ≤ stage
  map_isPushout :
    letI : Algebra (𝒮 i) (𝒮 stage) := (t le_stage).toRingHom.toAlgebra
    CategoryTheory.IsPushout
      (CommRingCat.ofHom
        (D₀.mapAtLaterStage D₁ H h₀ h₁ le_stage f).toRingHom)
      (CommRingCat.ofHom
        (D₀.mapAtLaterStage D₂ H h₀ h₂ le_stage g).toRingHom)
      (CommRingCat.ofHom
        (D₁.mapAtLaterStage D₃ H h₁ h₃ le_stage inl).toRingHom)
      (CommRingCat.ofHom
        (D₂.mapAtLaterStage D₃ H h₂ h₃ le_stage inr).toRingHom)

private theorem SpreadData.exists_pushoutStage
    {B₀ B₁ B₂ B₃ : Type u}
    [CommRing B₀] [CommRing B₁] [CommRing B₂] [CommRing B₃]
    [Algebra A B₀] [Algebra A B₁] [Algebra A B₂] [Algebra A B₃]
    (D₀ : SpreadData 𝒮 uA B₀) (D₁ : SpreadData 𝒮 uA B₁)
    (D₂ : SpreadData 𝒮 uA B₂) (D₃ : SpreadData 𝒮 uA B₃)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₀ : D₀.i₀ ≤ i) (h₁ : D₁.i₀ ≤ i)
    (h₂ : D₂.i₀ ≤ i) (h₃ : D₃.i₀ ≤ i)
    (f : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₁.spreadStage (t := t) h₁)
    (g : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (inl : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (inr : D₂.spreadStage (t := t) h₂ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (h : inl.comp f = inr.comp g)
    (F : B₀ →ₐ[A] B₁) (G : B₀ →ₐ[A] B₂)
    (Inl : B₁ →ₐ[A] B₃) (Inr : B₂ →ₐ[A] B₃)
    (hf : ∀ x, D₁.stageToColimit H ⟨i, h₁⟩ (f x) =
      F (D₀.stageToColimit H ⟨i, h₀⟩ x))
    (hg : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (g x) =
      G (D₀.stageToColimit H ⟨i, h₀⟩ x))
    (hinl : ∀ x, D₃.stageToColimit H ⟨i, h₃⟩ (inl x) =
      Inl (D₁.stageToColimit H ⟨i, h₁⟩ x))
    (hinr : ∀ x, D₃.stageToColimit H ⟨i, h₃⟩ (inr x) =
      Inr (D₂.stageToColimit H ⟨i, h₂⟩ x))
    (Hpush : CategoryTheory.IsPushout (CommRingCat.ofHom F.toRingHom)
      (CommRingCat.ofHom G.toRingHom) (CommRingCat.ofHom Inl.toRingHom)
      (CommRingCat.ofHom Inr.toRingHom)) :
    Nonempty (D₀.PushoutStage D₁ D₂ D₃ H h₀ h₁ h₂ h₃ f g inl inr) := by
  obtain ⟨j, hij, hj⟩ := D₀.exists_isPushout_mapAtLaterStage D₁ D₂ D₃ H
    h₀ h₁ h₂ h₃ f g inl inr h F G Inl Inr hf hg hinl hinr Hpush
  exact ⟨⟨j, hij, hj⟩⟩

/-- A finite family of compatible colimit pushout squares between varying
spread models is simultaneously a pushout at one common later stage. -/
theorem SpreadData.exists_common_isPushout_mapAtLaterStage
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {ω ρ : Type*} [Finite ρ]
    (B : ω → Type u) [∀ q, CommRing (B q)] [∀ q, Algebra A (B q)]
    (D : ∀ q, SpreadData 𝒮 uA (B q))
    (corner₀ corner₁ corner₂ corner₃ : ρ → ω)
    {i : ι} (h : ∀ q, (D q).i₀ ≤ i)
    (f : ∀ r,
      (D (corner₀ r)).spreadStage (t := t) (h (corner₀ r)) →ₐ[𝒮 i]
        (D (corner₁ r)).spreadStage (t := t) (h (corner₁ r)))
    (g : ∀ r,
      (D (corner₀ r)).spreadStage (t := t) (h (corner₀ r)) →ₐ[𝒮 i]
        (D (corner₂ r)).spreadStage (t := t) (h (corner₂ r)))
    (inl : ∀ r,
      (D (corner₁ r)).spreadStage (t := t) (h (corner₁ r)) →ₐ[𝒮 i]
        (D (corner₃ r)).spreadStage (t := t) (h (corner₃ r)))
    (inr : ∀ r,
      (D (corner₂ r)).spreadStage (t := t) (h (corner₂ r)) →ₐ[𝒮 i]
        (D (corner₃ r)).spreadStage (t := t) (h (corner₃ r)))
    (hsquare : ∀ r, (inl r).comp (f r) = (inr r).comp (g r))
    (F : ∀ r, B (corner₀ r) →ₐ[A] B (corner₁ r))
    (G : ∀ r, B (corner₀ r) →ₐ[A] B (corner₂ r))
    (Inl : ∀ r, B (corner₁ r) →ₐ[A] B (corner₃ r))
    (Inr : ∀ r, B (corner₂ r) →ₐ[A] B (corner₃ r))
    (hf : ∀ r x,
      (D (corner₁ r)).stageToColimit H ⟨i, h (corner₁ r)⟩ (f r x) =
        F r ((D (corner₀ r)).stageToColimit H ⟨i, h (corner₀ r)⟩ x))
    (hg : ∀ r x,
      (D (corner₂ r)).stageToColimit H ⟨i, h (corner₂ r)⟩ (g r x) =
        G r ((D (corner₀ r)).stageToColimit H ⟨i, h (corner₀ r)⟩ x))
    (hinl : ∀ r x,
      (D (corner₃ r)).stageToColimit H ⟨i, h (corner₃ r)⟩ (inl r x) =
        Inl r ((D (corner₁ r)).stageToColimit H ⟨i, h (corner₁ r)⟩ x))
    (hinr : ∀ r x,
      (D (corner₃ r)).stageToColimit H ⟨i, h (corner₃ r)⟩ (inr r x) =
        Inr r ((D (corner₂ r)).stageToColimit H ⟨i, h (corner₂ r)⟩ x))
    (Hpush : ∀ r, CategoryTheory.IsPushout (CommRingCat.ofHom (F r).toRingHom)
      (CommRingCat.ofHom (G r).toRingHom) (CommRingCat.ofHom (Inl r).toRingHom)
      (CommRingCat.ofHom (Inr r).toRingHom)) :
    ∃ (j : ι) (hij : i ≤ j), ∀ r,
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      CategoryTheory.IsPushout
        (CommRingCat.ofHom
          ((D (corner₀ r)).mapAtLaterStage (D (corner₁ r)) H
            (h (corner₀ r)) (h (corner₁ r)) hij (f r)).toRingHom)
        (CommRingCat.ofHom
          ((D (corner₀ r)).mapAtLaterStage (D (corner₂ r)) H
            (h (corner₀ r)) (h (corner₂ r)) hij (g r)).toRingHom)
        (CommRingCat.ofHom
          ((D (corner₁ r)).mapAtLaterStage (D (corner₃ r)) H
            (h (corner₁ r)) (h (corner₃ r)) hij (inl r)).toRingHom)
        (CommRingCat.ofHom
          ((D (corner₂ r)).mapAtLaterStage (D (corner₃ r)) H
            (h (corner₂ r)) (h (corner₃ r)) hij (inr r)).toRingHom) := by
  classical
  let C : ∀ r, (D (corner₀ r)).PushoutStage
      (D (corner₁ r)) (D (corner₂ r)) (D (corner₃ r)) H
      (h (corner₀ r)) (h (corner₁ r)) (h (corner₂ r)) (h (corner₃ r))
      (f r) (g r) (inl r) (inr r) := fun r =>
    Classical.choice ((D (corner₀ r)).exists_pushoutStage
      (D (corner₁ r)) (D (corner₂ r)) (D (corner₃ r)) H
      (h (corner₀ r)) (h (corner₁ r)) (h (corner₂ r)) (h (corner₃ r))
      (f r) (g r) (inl r) (inr r) (hsquare r)
      (F r) (G r) (Inl r) (Inr r) (hf r) (hg r) (hinl r) (hinr r) (Hpush r))
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
  exact (D (corner₀ r)).isPushout_mapAtLaterStage_trans
    (D (corner₁ r)) (D (corner₂ r)) (D (corner₃ r)) H
    (h (corner₀ r)) (h (corner₁ r)) (h (corner₂ r)) (h (corner₃ r))
    (C r).le_stage (hC r) (f r) (g r) (inl r) (inr r) (C r).map_isPushout

end Algebra
