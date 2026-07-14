import ModularCurves.ForMathlib.FinitePresentationFunctorCover

/-!
# Spreading finite families of algebra equivalences

A finite family of equivalences between finitely presented algebras over a filtered
colimit can be represented by equivalences at one common stage. Both directions are
spread simultaneously, and the two inverse identities are synchronized before the
stage equivalences are assembled.
-/

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}

/-- A finite family of algebra equivalences between varying spread models descends to
one common stage, with the descended equivalences compatible with the colimit maps. -/
theorem IsFilteredAlgColimit.exists_spreadAlgEquivFamily
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {κ μ : Type u} [Finite μ]
    (B : κ → Type u) [∀ q, CommRing (B q)] [∀ q, Algebra A (B q)]
    (D : ∀ q, SpreadData 𝒮 uA (B q)) (i₀ : ι)
    (h₀ : ∀ q, (D q).i₀ = i₀) (src dst : μ → κ)
    (e : ∀ a, B (src a) ≃ₐ[A] B (dst a)) :
    ∃ (j : ι) (hj : i₀ ≤ j)
        (e' : ∀ a,
          (D (src a)).spreadStage (t := t) ((h₀ (src a)).le.trans hj) ≃ₐ[𝒮 j]
            (D (dst a)).spreadStage (t := t) ((h₀ (dst a)).le.trans hj)),
      ∀ a x,
        (D (dst a)).stageToColimit H
            ⟨j, (h₀ (dst a)).le.trans hj⟩ (e' a x) =
          e a ((D (src a)).stageToColimit H
            ⟨j, (h₀ (src a)).le.trans hj⟩ x) := by
  classical
  let mapSrc : μ ⊕ μ → κ := Sum.elim src dst
  let mapDst : μ ⊕ μ → κ := Sum.elim dst src
  let map : ∀ a, B (mapSrc a) →ₐ[A] B (mapDst a)
    | Sum.inl a => (e a).toAlgHom
    | Sum.inr a => (e a).symm.toAlgHom
  obtain ⟨j, hj, f, hf⟩ := SpreadData.exists_common_maps_at_stage H
    B D i₀ h₀ mapSrc mapDst map
  let h : ∀ q, (D q).i₀ ≤ j := fun q => (h₀ q).le.trans hj
  let forward : ∀ a,
      (D (src a)).spreadStage (t := t) (h (src a)) →ₐ[𝒮 j]
        (D (dst a)).spreadStage (t := t) (h (dst a)) :=
    fun a => f (Sum.inl a)
  let backward : ∀ a,
      (D (dst a)).spreadStage (t := t) (h (dst a)) →ₐ[𝒮 j]
        (D (src a)).spreadStage (t := t) (h (src a)) :=
    fun a => f (Sum.inr a)
  have hforward : ∀ a x,
      (D (dst a)).stageToColimit H ⟨j, h (dst a)⟩ (forward a x) =
        (e a).toAlgHom ((D (src a)).stageToColimit H ⟨j, h (src a)⟩ x) := by
    intro a x
    convert hf (Sum.inl a) x using 1 <;> rfl
  have hbackward : ∀ a x,
      (D (src a)).stageToColimit H ⟨j, h (src a)⟩ (backward a x) =
        (e a).symm.toAlgHom ((D (dst a)).stageToColimit H ⟨j, h (dst a)⟩ x) := by
    intro a x
    convert hf (Sum.inr a) x using 1 <;> rfl
  let relationObj : μ ⊕ μ → κ := Sum.elim src dst
  let left : ∀ r,
      (D (relationObj r)).spreadStage (t := t) (h (relationObj r)) →ₐ[𝒮 j]
        (D (relationObj r)).spreadStage (t := t) (h (relationObj r))
    | Sum.inl a => (backward a).comp (forward a)
    | Sum.inr a => (forward a).comp (backward a)
  let right : ∀ r,
      (D (relationObj r)).spreadStage (t := t) (h (relationObj r)) →ₐ[𝒮 j]
        (D (relationObj r)).spreadStage (t := t) (h (relationObj r)) :=
    fun r => AlgHom.id (𝒮 j) ((D (relationObj r)).spreadStage (t := t) (h (relationObj r)))
  have hrel : ∀ r x,
      (D (relationObj r)).stageToColimit H ⟨j, h (relationObj r)⟩ (left r x) =
        (D (relationObj r)).stageToColimit H ⟨j, h (relationObj r)⟩ (right r x) := by
    intro r x
    cases r with
    | inl a =>
        change (D (src a)).stageToColimit H ⟨j, h (src a)⟩
            (backward a (forward a x)) =
          (D (src a)).stageToColimit H ⟨j, h (src a)⟩ x
        rw [hbackward, hforward]
        exact (e a).symm_apply_apply _
    | inr a =>
        change (D (dst a)).stageToColimit H ⟨j, h (dst a)⟩
            (forward a (backward a x)) =
          (D (dst a)).stageToColimit H ⟨j, h (dst a)⟩ x
        rw [hforward, hbackward]
        exact (e a).apply_symm_apply _
  let C := Classical.choice (SpreadData.exists_common_eq_mapFamilyAtLaterStage
    B D H h relationObj relationObj left right hrel)
  let forward' : ∀ a,
      (D (src a)).spreadStage (t := t) ((h (src a)).trans C.le_stage) →ₐ[𝒮 C.stage]
        (D (dst a)).spreadStage (t := t) ((h (dst a)).trans C.le_stage) :=
    fun a => (D (src a)).mapAtLaterStage (D (dst a)) H
      (h (src a)) (h (dst a)) C.le_stage (forward a)
  let backward' : ∀ a,
      (D (dst a)).spreadStage (t := t) ((h (dst a)).trans C.le_stage) →ₐ[𝒮 C.stage]
        (D (src a)).spreadStage (t := t) ((h (src a)).trans C.le_stage) :=
    fun a => (D (dst a)).mapAtLaterStage (D (src a)) H
      (h (dst a)) (h (src a)) C.le_stage (backward a)
  have hbackward_forward : ∀ a, (backward' a).comp (forward' a) =
      AlgHom.id (𝒮 C.stage)
        ((D (src a)).spreadStage (t := t) ((h (src a)).trans C.le_stage)) := by
    intro a
    calc
      (backward' a).comp (forward' a) =
          (D (src a)).mapAtLaterStage (D (src a)) H
            (h (src a)) (h (src a)) C.le_stage ((backward a).comp (forward a)) :=
        ((D (src a)).mapAtLaterStage_comp (D (dst a)) (D (src a)) H
          (h (src a)) (h (dst a)) (h (src a)) C.le_stage
          (forward a) (backward a)).symm
      _ = (D (src a)).mapAtLaterStage (D (src a)) H
          (h (src a)) (h (src a)) C.le_stage
            (AlgHom.id (𝒮 j)
              ((D (src a)).spreadStage (t := t) (h (src a)))) :=
        C.maps_agree (Sum.inl a)
      _ = _ := (D (src a)).mapAtLaterStage_id H (h (src a)) C.le_stage
  have hforward_backward : ∀ a, (forward' a).comp (backward' a) =
      AlgHom.id (𝒮 C.stage)
        ((D (dst a)).spreadStage (t := t) ((h (dst a)).trans C.le_stage)) := by
    intro a
    calc
      (forward' a).comp (backward' a) =
          (D (dst a)).mapAtLaterStage (D (dst a)) H
            (h (dst a)) (h (dst a)) C.le_stage ((forward a).comp (backward a)) :=
        ((D (dst a)).mapAtLaterStage_comp (D (src a)) (D (dst a)) H
          (h (dst a)) (h (src a)) (h (dst a)) C.le_stage
          (backward a) (forward a)).symm
      _ = (D (dst a)).mapAtLaterStage (D (dst a)) H
          (h (dst a)) (h (dst a)) C.le_stage
            (AlgHom.id (𝒮 j)
              ((D (dst a)).spreadStage (t := t) (h (dst a)))) :=
        C.maps_agree (Sum.inr a)
      _ = _ := (D (dst a)).mapAtLaterStage_id H (h (dst a)) C.le_stage
  let e' : ∀ a,
      (D (src a)).spreadStage (t := t) ((h (src a)).trans C.le_stage) ≃ₐ[𝒮 C.stage]
        (D (dst a)).spreadStage (t := t) ((h (dst a)).trans C.le_stage) :=
    fun a => AlgEquiv.ofAlgHom (forward' a) (backward' a)
      (hforward_backward a) (hbackward_forward a)
  refine ⟨C.stage, hj.trans C.le_stage, e', fun a x => ?_⟩
  change (D (dst a)).stageToColimit H
      ⟨C.stage, (h (dst a)).trans C.le_stage⟩ (forward' a x) =
    (e a).toAlgHom ((D (src a)).stageToColimit H
      ⟨C.stage, (h (src a)).trans C.le_stage⟩ x)
  exact (D (src a)).mapAtLaterStage_colimit (D (dst a)) H
    (h (src a)) (h (dst a)) C.le_stage (forward a) (e a).toAlgHom
    (hforward a) x

end Algebra
