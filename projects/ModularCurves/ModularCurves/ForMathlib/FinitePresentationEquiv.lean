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

/-- An equivalence between spread models remains bijective after transport to a
later stage. -/
theorem SpreadData.mapAtLaterStage_bijective
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (e : D₁.spreadStage (t := t) h₁ ≃ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂) :
    Function.Bijective (D₁.mapAtLaterStage D₂ H h₁ h₂ hij e.toAlgHom) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let E := (D₁.spreadStageBaseChangeEquiv hij h₁ H).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : 𝒮 j ≃ₐ[𝒮 j] 𝒮 j) e).trans
      (D₂.spreadStageBaseChangeEquiv hij h₂ H))
  exact E.bijective

/-- A finite family of algebra equivalences between varying spread models descends to
one common stage, with the descended equivalences compatible with the colimit maps. -/
theorem IsFilteredAlgColimit.exists_spreadAlgEquivFamily
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {κ μ : Type*} [Finite μ]
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

/-- One algebra equivalence between colimit algebras descends to an equivalence
between spread models whose presentations start at the same stage. -/
theorem IsFilteredAlgColimit.exists_spreadAlgEquiv
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {B₁ B₂ : Type u} [instB₁ : CommRing B₁] [instB₂ : CommRing B₂]
    [algB₁ : Algebra A B₁] [algB₂ : Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (h₀ : D₁.i₀ = D₂.i₀) (e : B₁ ≃ₐ[A] B₂) :
    ∃ (j : ι) (h₁ : D₁.i₀ ≤ j) (h₂ : D₂.i₀ ≤ j)
        (e' : D₁.spreadStage (t := t) h₁ ≃ₐ[𝒮 j]
          D₂.spreadStage (t := t) h₂),
      ∀ x, D₂.stageToColimit H ⟨j, h₂⟩ (e' x) =
        e (D₁.stageToColimit H ⟨j, h₁⟩ x) := by
  let B : Bool → Type u
    | false => B₁
    | true => B₂
  let commRingB : ∀ q, CommRing (B q)
    | false => instB₁
    | true => instB₂
  let algebraB : ∀ q, Algebra A (B q)
    | false => algB₁
    | true => algB₂
  letI instCommRingB (q : Bool) : CommRing (B q) := commRingB q
  letI instAlgebraB (q : Bool) : Algebra A (B q) := algebraB q
  let D : ∀ q, SpreadData 𝒮 uA (B q)
    | false => D₁
    | true => D₂
  let h₀' : ∀ q, (D q).i₀ = D₁.i₀
    | false => rfl
    | true => h₀.symm
  let src : Unit → Bool := fun _ => false
  let dst : Unit → Bool := fun _ => true
  let equiv : ∀ a, B (src a) ≃ₐ[A] B (dst a) := fun _ => e
  obtain ⟨j, hj, e', he'⟩ := H.exists_spreadAlgEquivFamily
    (κ := Bool) (μ := Unit) B D D₁.i₀ h₀' src dst equiv
  refine ⟨j, hj, h₀.symm.le.trans hj, e' (), ?_⟩
  exact he' ()

/-- A stage map compatible with an equivalence of the colimit algebras becomes
bijective after transport to a later stage. -/
theorem SpreadData.exists_mapAtLaterStage_bijective
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (h₀ : D₁.i₀ = D₂.i₀) {i : ι}
    (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (e : B₁ ≃ₐ[A] B₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f x) =
      e (D₁.stageToColimit H ⟨i, h₁⟩ x)) :
    ∃ (j : ι) (hij : i ≤ j),
      Function.Bijective (D₁.mapAtLaterStage D₂ H h₁ h₂ hij f) := by
  obtain ⟨j, h₁j, h₂j, e', he'⟩ := H.exists_spreadAlgEquiv D₁ D₂ h₀ e
  haveI := H.directed
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  let f_k := D₁.mapAtLaterStage D₂ H h₁ h₂ hik f
  let e_k := D₁.mapAtLaterStage D₂ H h₁j h₂j hjk e'.toAlgHom
  have hf_k : ∀ x, D₂.stageToColimit H ⟨k, h₂.trans hik⟩ (f_k x) =
      e (D₁.stageToColimit H ⟨k, h₁.trans hik⟩ x) :=
    D₁.mapAtLaterStage_colimit D₂ H h₁ h₂ hik f e hf
  have he_k : ∀ x, D₂.stageToColimit H ⟨k, h₂j.trans hjk⟩ (e_k x) =
      e (D₁.stageToColimit H ⟨k, h₁j.trans hjk⟩ x) :=
    D₁.mapAtLaterStage_colimit D₂ H h₁j h₂j hjk e'.toAlgHom e he'
  let C := Classical.choice (D₁.exists_common_eq_mapAtLaterStage
    (ρ := Fin 1) D₂ H (h₁.trans hik) (h₂.trans hik)
      (fun _ => f_k) (fun _ => e_k) (fun _ x => (hf_k x).trans (he_k x).symm))
  refine ⟨C.stage, hik.trans C.le_stage, ?_⟩
  have hmaps : D₁.mapAtLaterStage D₂ H h₁ h₂ (hik.trans C.le_stage) f =
      D₁.mapAtLaterStage D₂ H h₁j h₂j (hjk.trans C.le_stage) e'.toAlgHom := by
    calc
      D₁.mapAtLaterStage D₂ H h₁ h₂ (hik.trans C.le_stage) f =
          D₁.mapAtLaterStage D₂ H (h₁.trans hik) (h₂.trans hik) C.le_stage f_k :=
        (D₁.mapAtLaterStage_trans D₂ H h₁ h₂ hik C.le_stage f).symm
      _ = D₁.mapAtLaterStage D₂ H (h₁.trans hik) (h₂.trans hik) C.le_stage e_k :=
        C.maps_agree 0
      _ = D₁.mapAtLaterStage D₂ H h₁j h₂j (hjk.trans C.le_stage) e'.toAlgHom :=
        D₁.mapAtLaterStage_trans D₂ H h₁j h₂j hjk C.le_stage e'.toAlgHom
  rw [hmaps]
  exact D₁.mapAtLaterStage_bijective D₂ H h₁j h₂j
    (hjk.trans C.le_stage) e'

end Algebra
