import ModularCurves.ForMathlib.AffineOpenImmersionCover
import ModularCurves.ForMathlib.FinitePresentationAwayMapFamily
import ModularCurves.ForMathlib.FinitePresentationFunctorCover

/-!
# Spreading finite families of affine open immersions

A finite principal-cover witness for a stage algebra map remains a witness after
transport once the canonical maps on the corresponding principal localizations
are bijective. Combining this observation with finite synchronization gives one
stage at which finitely many affine spectrum maps are all open immersions.
-/

universe u

namespace Algebra

open CategoryTheory

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}

private structure SpecMapAwayCover
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) where
  index : Type u
  finite_index : Finite index
  source : index → S
  image_span : Ideal.span (Set.range fun k => f (source k)) = ⊤
  map_bijective : ∀ k, Function.Bijective
    (IsLocalization.Away.map
      (Localization.Away (source k))
      (Localization.Away (f (source k))) f (source k))

private theorem nonempty_specMapAwayCover
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (hopen : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))) :
    Nonempty (SpecMapAwayCover f) := by
  letI := hopen
  obtain ⟨κ, hκ, b, hspan, hbij⟩ :=
    AlgebraicGeometry.exists_awayCover_of_isOpenImmersion_SpecMap f
  exact ⟨⟨κ, hκ, b, hspan, hbij⟩⟩

private theorem span_range_map_eq_top
    {S T κ : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (b : κ → S)
    (h : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun k => f (b k)) = ⊤ := by
  have hrange : Set.range (fun k => f (b k)) = f '' Set.range b := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨b k, ⟨k, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  rw [hrange, ← Ideal.map_span, h, Ideal.map_top]

/-- Transporting a stage map sends a directly transported element to the direct
transport of its image. -/
theorem SpreadData.mapAtLaterStage_elementAtLaterStage
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (b_i : D₁.spreadStage (t := t) h₁) :
    D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
        (D₁.elementAtLaterStage H h₁ hij b_i) =
      D₂.elementAtLaterStage H h₂ hij (f b_i) := by
  exact D₁.mapAtLaterStage_stageTransition D₂ H h₁ h₂ hij f b_i

/-- A finite principal cover whose canonical away maps are bijective verifies
that the transported affine spectrum map is an open immersion. -/
theorem SpreadData.isOpenImmersion_mapAtLaterStage
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    {κ : Type u} [Finite κ]
    (b_i : κ → D₁.spreadStage (t := t) h₁)
    (hspan : Ideal.span (Set.range fun k => f (b_i k)) = ⊤)
    (hbij : ∀ k,
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      Function.Bijective
        (D₁.awayMapAtLaterStage D₂ H h₁ h₂ hij f (b_i k))) :
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (D₁.mapAtLaterStage D₂ H h₁ h₂ hij f).toRingHom)) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let f_j := D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
  let b_j := fun k => D₁.elementAtLaterStage H h₁ hij (b_i k)
  apply AlgebraicGeometry.isOpenImmersion_SpecMap_of_awayCover
    f_j.toRingHom b_j
  · letI : Algebra (𝒮 D₂.i₀) (D₂.spreadStage (t := t) h₂) :=
      ((algebraMap (𝒮 i) (D₂.spreadStage (t := t) h₂)).comp
        (t h₂).toRingHom).toAlgebra
    letI : Algebra (𝒮 D₂.i₀) (D₂.spreadStage (t := t) (h₂.trans hij)) :=
      ((algebraMap (𝒮 j) (D₂.spreadStage (t := t) (h₂.trans hij))).comp
        (t (h₂.trans hij)).toRingHom).toAlgebra
    let tr₂ := D₂.stageTransition H
      (P := ⟨i, h₂⟩) (Q := ⟨j, h₂.trans hij⟩) hij
    have hspan' : Ideal.span (Set.range fun k => tr₂ (f (b_i k))) = ⊤ :=
      span_range_map_eq_top tr₂.toRingHom _ hspan
    have himage : (fun k => f_j (b_j k)) = fun k => tr₂ (f (b_i k)) := by
      funext k
      exact D₁.mapAtLaterStage_elementAtLaterStage D₂ H h₁ h₂ hij f (b_i k)
    change Ideal.span (Set.range fun k => f_j (b_j k)) = ⊤
    rw [himage]
    exact hspan'
  · intro k
    change Function.Bijective
      (D₁.awayMapAtLaterStage D₂ H h₁ h₂ hij f (b_i k))
    exact hbij k

/-- Finitely many compatible stage maps with finite principal-cover witnesses
become affine open immersions simultaneously at one common later stage. -/
theorem SpreadData.exists_common_isOpenImmersion_mapAtLaterStage
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {ω ρ : Type u} [Finite ρ] (κ : ρ → Type u) [∀ r, Finite (κ r)]
    (B : ω → Type u) [∀ q, CommRing (B q)] [∀ q, Algebra A (B q)]
    (D : ∀ q, SpreadData 𝒮 uA (B q)) (src dst : ρ → ω)
    {i : ι} (h : ∀ q, (D q).i₀ ≤ i)
    (f : ∀ r,
      (D (src r)).spreadStage (t := t) (h (src r)) →ₐ[𝒮 i]
        (D (dst r)).spreadStage (t := t) (h (dst r)))
    (F : ∀ r, B (src r) →ₐ[A] B (dst r))
    (hf : ∀ r x,
      (D (dst r)).stageToColimit H ⟨i, h (dst r)⟩ (f r x) =
        F r ((D (src r)).stageToColimit H ⟨i, h (src r)⟩ x))
    (b_i : ∀ r, κ r →
      (D (src r)).spreadStage (t := t) (h (src r)))
    (b : ∀ r, κ r → B (src r))
    (hb : ∀ r k,
      (D (src r)).stageToColimit H ⟨i, h (src r)⟩ (b_i r k) = b r k)
    (hspan : ∀ r,
      Ideal.span (Set.range fun k => f r (b_i r k)) = ⊤)
    (hbij : ∀ r k, Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away (b r k))
        (Localization.Away (F r (b r k))) (F r) (b r k))) :
    ∃ (j : ι) (hij : i ≤ j),
      ∀ r,
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          ((D (src r)).mapAtLaterStage (D (dst r)) H
            (h (src r)) (h (dst r)) hij (f r)).toRingHom)) := by
  obtain ⟨j, hij, hlocal⟩ :=
    SpreadData.exists_common_awayMapAtLaterStage_bijective H B D
      (fun q : Σ r, κ r => src q.1) (fun q : Σ r, κ r => dst q.1)
      h (fun q : Σ r, κ r => f q.1) (fun q : Σ r, κ r => F q.1)
      (fun q x => hf q.1 x) (fun q : Σ r, κ r => b_i q.1 q.2)
      (fun q : Σ r, κ r => b q.1 q.2) (fun q => hb q.1 q.2)
      (fun q => hbij q.1 q.2)
  refine ⟨j, hij, fun r => ?_⟩
  exact (D (src r)).isOpenImmersion_mapAtLaterStage
    (D (dst r)) H (h (src r)) (h (dst r)) hij (f r) (b_i r)
      (hspan r) fun k => hlocal ⟨r, k⟩

/-- Finitely many arrows in a spread functor whose colimit spectrum maps are open
immersions become open immersions simultaneously at one later functor stage. -/
theorem SpreadData.FunctorModel.exists_common_isOpenImmersion_mapToStage
    {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
    {H : IsFilteredAlgColimit R 𝒮 t A uA}
    (M : SpreadData.FunctorModel F H)
    {ρ : Type u} [Finite ρ] (src dst : ρ → J)
    (a : ∀ r, src r ⟶ dst r)
    (hopen : ∀ r, AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (F.map (a r)).hom.toRingHom))) :
    ∃ (j : ι) (hij : M.stage ≤ j),
      ∀ r, AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          ((M.mapToStage hij).map (a r)).toRingHom)) := by
  classical
  let C : ∀ r, SpecMapAwayCover (F.map (a r)).hom.toRingHom := fun r =>
    Classical.choice (nonempty_specMapAwayCover _ (hopen r))
  let κ : ρ → Type u := fun r => (C r).index
  letI : ∀ r, Finite (κ r) := fun r => (C r).finite_index
  let b : ∀ r, κ r → F.obj (src r) := fun r => (C r).source
  obtain ⟨i, hMi, b_i, hb_i, hspan_i⟩ :=
    M.exists_common_mapCoverAtLaterStage κ src dst a b fun r => (C r).image_span
  let N := M.mapToStage hMi
  have hbij (r) (k) : Function.Bijective
      (IsLocalization.Away.mapₐ
        (Localization.Away (b r k))
        (Localization.Away ((F.map (a r)).hom (b r k)))
        (F.map (a r)).hom (b r k)) := by
    change Function.Bijective
      (IsLocalization.Away.map
        (Localization.Away ((C r).source k))
        (Localization.Away ((F.map (a r)).hom.toRingHom ((C r).source k)))
        (F.map (a r)).hom.toRingHom ((C r).source k))
    exact (C r).map_bijective k
  obtain ⟨j, hij, hj⟩ :=
    SpreadData.exists_common_isOpenImmersion_mapAtLaterStage
      H κ (fun X => F.obj X) N.object src dst N.le_stage
        (fun r => N.map (a r)) (fun r => (F.map (a r)).hom)
        (fun r x => N.map_colimit (a r) x) b_i b hb_i hspan_i hbij
  refine ⟨j, hMi.trans hij, fun r => ?_⟩
  change AlgebraicGeometry.IsOpenImmersion
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((M.object (src r)).mapAtLaterStage (M.object (dst r)) H
        (M.le_stage (src r)) (M.le_stage (dst r)) (hMi.trans hij)
          (M.map (a r))).toRingHom))
  rw [← (M.object (src r)).mapAtLaterStage_trans (M.object (dst r)) H
    (M.le_stage (src r)) (M.le_stage (dst r)) hMi hij (M.map (a r))]
  exact hj r

end Algebra
