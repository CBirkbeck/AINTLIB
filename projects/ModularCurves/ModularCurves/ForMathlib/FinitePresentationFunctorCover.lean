import ModularCurves.ForMathlib.FinitePresentationFunctor
import ModularCurves.ForMathlib.FinitePresentationPrincipalCover

/-!
# Transporting spread functors with principal affine covers

A finite algebra functor may have to move to a later approximation stage in order to
retain a finite principal-open cover on one of its objects. This file transports the
whole functor, including its literal functor laws and colimit compatibility, and keeps
the cover functions at the same later stage.
-/

open CategoryTheory TensorProduct

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
  {B : Type u} [CommRing B] [Algebra A B]

private theorem span_range_map_eq_top
    {S T κ : Type*} [CommRing S] [CommRing T]
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

/-- A finite family of colimit elements can be represented at a spread stage later
than any prescribed system index. -/
theorem SpreadData.exists_common_stageToColimit_eq_atLaterStage
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (i : ι) {κ : Type*} [Finite κ] (b : κ → B) :
    ∃ (S : {j : ι // D.i₀ ≤ j}), i ≤ S.1 ∧
      ∃ (b_S : κ → D.spreadStage (t := t) S.2),
        ∀ k, D.stageToColimit H S (b_S k) = b k := by
  classical
  obtain ⟨Q, b_Q, hb_Q⟩ := D.exists_common_stageToColimit_eq H b
  haveI := H.directed
  obtain ⟨j, hij, hQj⟩ := exists_ge_ge i Q.1
  let S : {j : ι // D.i₀ ≤ j} := ⟨j, Q.2.trans hQj⟩
  refine ⟨S, hij, fun k => D.stageTransition H hQj (b_Q k), fun k => ?_⟩
  exact (D.stageToColimit_stageTransition H Q.2 hQj (b_Q k)).trans (hb_Q k)

private theorem SpreadData.exists_span_eq_top_atLaterStage
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h : D.i₀ ≤ i) {κ : Type*} [Finite κ]
    (b_i : κ → D.spreadStage (t := t) h)
    (hspan : Ideal.span (Set.range fun k =>
      D.stageToColimit H ⟨i, h⟩ (b_i k)) = ⊤) :
    ∃ (j : ι) (hij : i ≤ j),
      Ideal.span (Set.range fun k =>
        D.stageTransition H
          (P := ⟨i, h⟩) (Q := ⟨j, h.trans hij⟩) hij (b_i k)) = ⊤ := by
  classical
  cases nonempty_fintype κ
  let b : κ → B := fun k => D.stageToColimit H ⟨i, h⟩ (b_i k)
  have hsurj : Function.Surjective (Fintype.linearCombination B b) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination B b).mp hspan
  obtain ⟨c, hc⟩ := hsurj 1
  obtain ⟨P, hiP, c_P, hc_P⟩ :=
    D.exists_common_stageToColimit_eq_atLaterStage H i c
  let b_P : κ → D.spreadStage (t := t) P.2 :=
    fun k => D.stageTransition H
      (P := ⟨i, h⟩) (Q := P) hiP (b_i k)
  have hb_P (k : κ) : D.stageToColimit H P (b_P k) = b k :=
    D.stageToColimit_stageTransition H h hiP (b_i k)
  have hsum_colimit :
      D.stageToColimit H P (∑ k, c_P k * b_P k) =
        D.stageToColimit H P 1 := by
    rw [map_sum, map_one]
    calc
      ∑ k, D.stageToColimit H P (c_P k * b_P k) =
          ∑ k, D.stageToColimit H P (c_P k) *
            D.stageToColimit H P (b_P k) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [map_mul]
      _ = ∑ k, c k * b k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hc_P k, hb_P k]
      _ = 1 := by
        simpa [Fintype.linearCombination_apply, smul_eq_mul] using hc
  letI : ∀ Q : {j // D.i₀ ≤ j},
      Algebra (𝒮 D.i₀) (D.spreadStage (t := t) Q.2) :=
    fun Q => ((algebraMap (𝒮 Q.1) (D.spreadStage (t := t) Q.2)).comp
      (t Q.2).toRingHom).toAlgebra
  letI : Algebra (𝒮 D.i₀) B :=
    ((algebraMap A B).comp (uA D.i₀).toRingHom).toAlgebra
  obtain ⟨Q, hPQ, hsum⟩ :=
    (D.isFilteredAlgColimit H).eq_at_stage _ _ hsum_colimit
  let b_Q : κ → D.spreadStage (t := t) Q.2 :=
    fun k => D.stageTransition H
      (P := P) (Q := Q) hPQ (b_P k)
  let c_Q : κ → D.spreadStage (t := t) Q.2 :=
    fun k => D.stageTransition H
      (P := P) (Q := Q) hPQ (c_P k)
  have hsum_stage : ∑ k, c_Q k * b_Q k = 1 := by
    calc
      ∑ k, c_Q k * b_Q k =
          D.stageTransition H (P := P) (Q := Q) hPQ
            (∑ k, c_P k * b_P k) := by
              simp [b_Q, c_Q, map_sum, map_mul]
      _ = D.stageTransition H (P := P) (Q := Q) hPQ 1 := hsum
      _ = 1 := map_one _
  refine ⟨Q.1, hiP.trans hPQ, (Ideal.eq_top_iff_one _).mpr ?_⟩
  have hb_Q (k : κ) :
      D.stageTransition H
        (P := ⟨i, h⟩) (Q := Q) (hiP.trans hPQ) (b_i k) = b_Q k := by
    exact (D.stageTransition_trans H h hiP hPQ (b_i k)).symm
  rw [show (fun k => D.stageTransition H
      (P := ⟨i, h⟩) (Q := Q) (hiP.trans hPQ) (b_i k)) = b_Q by
    funext k
    exact hb_Q k]
  rw [← hsum_stage]
  exact Ideal.sum_mem _ fun k _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self k))

/-- A finite unit-ideal family can be represented at a spread stage later than any
prescribed index while retaining its unit-ideal relation. -/
theorem SpreadData.exists_common_stageToColimit_eq_span_eq_top_atLaterStage
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (i : ι) {κ : Type*} [Finite κ] (b : κ → B)
    (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (S : {j : ι // D.i₀ ≤ j}), i ≤ S.1 ∧
      ∃ (b_S : κ → D.spreadStage (t := t) S.2),
        (∀ k, D.stageToColimit H S (b_S k) = b k) ∧
          Ideal.span (Set.range b_S) = ⊤ := by
  obtain ⟨P, hiP, b_P, hb_P⟩ :=
    D.exists_common_stageToColimit_eq_atLaterStage H i b
  have hspan_P : Ideal.span (Set.range fun k =>
      D.stageToColimit H P (b_P k)) = ⊤ := by
    rw [show (fun k => D.stageToColimit H P (b_P k)) = b by
      funext k
      exact hb_P k]
    exact hspan
  obtain ⟨j, hPj, hspan_j⟩ :=
    D.exists_span_eq_top_atLaterStage H P.2 b_P hspan_P
  let S : {j : ι // D.i₀ ≤ j} := ⟨j, P.2.trans hPj⟩
  let b_j : κ → D.spreadStage (t := t) S.2 :=
    fun k => D.stageTransition H (P := P) (Q := S) hPj (b_P k)
  refine ⟨S, hiP.trans hPj, b_j, fun k => ?_, hspan_j⟩
  exact (D.stageToColimit_stageTransition H P.2 hPj (b_P k)).trans (hb_P k)

private theorem SpreadData.exists_map_span_eq_top_atLaterStage
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f_i : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (F : B₁ →ₐ[A] B₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f_i x) =
      F (D₁.stageToColimit H ⟨i, h₁⟩ x))
    {κ : Type*} [Finite κ]
    (b_i : κ → D₁.spreadStage (t := t) h₁)
    (hspan : Ideal.span (Set.range fun k =>
      F (D₁.stageToColimit H ⟨i, h₁⟩ (b_i k))) = ⊤) :
    ∃ (j : ι) (hij : i ≤ j),
      Ideal.span (Set.range fun k =>
        D₁.mapAtLaterStage D₂ H h₁ h₂ hij f_i
          (D₁.stageTransition H
            (P := ⟨i, h₁⟩) (Q := ⟨j, h₁.trans hij⟩) hij (b_i k))) = ⊤ := by
  have hspan_i : Ideal.span (Set.range fun k =>
      D₂.stageToColimit H ⟨i, h₂⟩ (f_i (b_i k))) = ⊤ := by
    rw [show (fun k => D₂.stageToColimit H ⟨i, h₂⟩ (f_i (b_i k))) =
      fun k => F (D₁.stageToColimit H ⟨i, h₁⟩ (b_i k)) by
        funext k
        exact hf (b_i k)]
    exact hspan
  obtain ⟨j, hij, hspan_j⟩ :=
    D₂.exists_span_eq_top_atLaterStage H h₂
      (fun k => f_i (b_i k)) hspan_i
  refine ⟨j, hij, ?_⟩
  rw [show (fun k =>
      D₁.mapAtLaterStage D₂ H h₁ h₂ hij f_i
        (D₁.stageTransition H
          (P := ⟨i, h₁⟩) (Q := ⟨j, h₁.trans hij⟩) hij (b_i k))) =
      fun k => D₂.stageTransition H
        (P := ⟨i, h₂⟩) (Q := ⟨j, h₂.trans hij⟩) hij (f_i (b_i k)) by
          funext k
          exact D₁.mapAtLaterStage_stageTransition D₂ H
            h₁ h₂ hij f_i (b_i k)]
  exact hspan_j

private theorem SpreadData.exists_mapCoverAtLaterStage
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f_i : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (F : B₁ →ₐ[A] B₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f_i x) =
      F (D₁.stageToColimit H ⟨i, h₁⟩ x))
    {κ : Type*} [Finite κ] (b : κ → B₁)
    (hspan : Ideal.span (Set.range fun k => F (b k)) = ⊤) :
    ∃ (j : ι) (hij : i ≤ j)
        (b_j : κ → D₁.spreadStage (t := t) (h₁.trans hij)),
      (∀ k, D₁.stageToColimit H ⟨j, h₁.trans hij⟩ (b_j k) = b k) ∧
        Ideal.span (Set.range fun k =>
          D₁.mapAtLaterStage D₂ H h₁ h₂ hij f_i (b_j k)) = ⊤ := by
  obtain ⟨P, hiP, b_P, hb_P⟩ :=
    D₁.exists_common_stageToColimit_eq_atLaterStage H i b
  let f_P := D₁.mapAtLaterStage D₂ H h₁ h₂ hiP f_i
  have hf_P (x) :
      D₂.stageToColimit H ⟨P.1, h₂.trans hiP⟩ (f_P x) =
        F (D₁.stageToColimit H ⟨P.1, h₁.trans hiP⟩ x) :=
    D₁.mapAtLaterStage_colimit D₂ H h₁ h₂ hiP f_i F hf x
  have hspan_P : Ideal.span (Set.range fun k =>
      F (D₁.stageToColimit H ⟨P.1, h₁.trans hiP⟩ (b_P k))) = ⊤ := by
    rw [show (fun k => F (D₁.stageToColimit H
      ⟨P.1, h₁.trans hiP⟩ (b_P k))) = fun k => F (b k) by
        funext k
        rw [hb_P k]]
    exact hspan
  obtain ⟨Q, hPQ, hspan_Q⟩ :=
    D₁.exists_map_span_eq_top_atLaterStage D₂ H
      (h₁.trans hiP) (h₂.trans hiP) f_P F hf_P b_P hspan_P
  let hiQ : i ≤ Q := hiP.trans hPQ
  let b_Q : κ → D₁.spreadStage (t := t) (h₁.trans hiQ) :=
    fun k => D₁.stageTransition H
      (P := ⟨P.1, h₁.trans hiP⟩) (Q := ⟨Q, h₁.trans hiQ⟩) hPQ (b_P k)
  have hb_Q (k : κ) :
      D₁.stageToColimit H ⟨Q, h₁.trans hiQ⟩ (b_Q k) = b k :=
    (D₁.stageToColimit_stageTransition H (h₁.trans hiP) hPQ (b_P k)).trans
      (hb_P k)
  refine ⟨Q, hiQ, b_Q, hb_Q, ?_⟩
  rw [← D₁.mapAtLaterStage_trans D₂ H h₁ h₂ hiP hPQ f_i]
  exact hspan_Q

section Functor

variable {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
  {H : IsFilteredAlgColimit R 𝒮 t A uA}

/-- Transport a spread functor model to a later system stage. -/
noncomputable def SpreadData.FunctorModel.mapToStage
    (M : SpreadData.FunctorModel F H) {j : ι} (hij : M.stage ≤ j) :
    SpreadData.FunctorModel F H where
  stage := j
  object := M.object
  le_stage X := (M.le_stage X).trans hij
  map f := (M.object _).mapAtLaterStage (M.object _) H
    (M.le_stage _) (M.le_stage _) hij (M.map f)
  map_id X := by
    rw [M.map_id]
    exact (M.object X).mapAtLaterStage_id H (M.le_stage X) hij
  map_comp f g := by
    rw [M.map_comp]
    exact (M.object _).mapAtLaterStage_comp (M.object _) (M.object _) H
      (M.le_stage _) (M.le_stage _) (M.le_stage _) hij (M.map f) (M.map g)
  map_colimit f x := (M.object _).mapAtLaterStage_colimit (M.object _) H
    (M.le_stage _) (M.le_stage _) hij (M.map f) (F.map f).hom (M.map_colimit f) x

/-- Move a spread functor to a stage where representatives of a finite source family
have images under one chosen arrow which generate the unit ideal. -/
theorem SpreadData.FunctorModel.exists_mapCoverAtLaterStage
    (M : SpreadData.FunctorModel F H) {X Y : J} (a : X ⟶ Y)
    {κ : Type*} [Finite κ] (b : κ → F.obj X)
    (hspan : Ideal.span (Set.range fun k => (F.map a).hom (b k)) = ⊤) :
    ∃ (j : ι) (hij : M.stage ≤ j)
        (b_j : κ → (M.object X).spreadStage (t := t)
          ((M.le_stage X).trans hij)),
      (∀ k, (M.object X).stageToColimit H
          ⟨j, (M.le_stage X).trans hij⟩ (b_j k) = b k) ∧
        Ideal.span (Set.range fun k =>
          (M.mapToStage hij).map a (b_j k)) = ⊤ := by
  exact (M.object X).exists_mapCoverAtLaterStage
    (M.object Y) H (M.le_stage X) (M.le_stage Y) (M.map a)
      (F.map a).hom (M.map_colimit a) b hspan

private structure SpreadData.FunctorModel.MapCoverStage
    (M : SpreadData.FunctorModel F H) {X Y : J} (a : X ⟶ Y)
    {κ : Type*} (b : κ → F.obj X) where
  stage : ι
  le_stage : M.stage ≤ stage
  source : κ → (M.object X).spreadStage (t := t)
    ((M.le_stage X).trans le_stage)
  source_colimit : ∀ k, (M.object X).stageToColimit H
    ⟨stage, (M.le_stage X).trans le_stage⟩ (source k) = b k
  image_span : Ideal.span (Set.range fun k =>
    (M.object X).mapAtLaterStage (M.object Y) H
      (M.le_stage X) (M.le_stage Y) le_stage (M.map a) (source k)) = ⊤

private theorem SpreadData.FunctorModel.exists_mapCoverStage
    (M : SpreadData.FunctorModel F H) {X Y : J} (a : X ⟶ Y)
    {κ : Type*} [Finite κ] (b : κ → F.obj X)
    (hspan : Ideal.span (Set.range fun k => (F.map a).hom (b k)) = ⊤) :
    Nonempty (M.MapCoverStage a b) := by
  obtain ⟨j, hij, b_j, hb_j, hspan_j⟩ :=
    M.exists_mapCoverAtLaterStage a b hspan
  exact ⟨⟨j, hij, b_j, hb_j, hspan_j⟩⟩

/-- Move a spread functor to one stage where finite source families for finitely
many chosen arrows have unit-ideal image families simultaneously. -/
theorem SpreadData.FunctorModel.exists_common_mapCoverAtLaterStage
    (M : SpreadData.FunctorModel F H)
    {ρ : Type u} [Finite ρ] (κ : ρ → Type u) [∀ r, Finite (κ r)]
    (src dst : ρ → J) (a : ∀ r, src r ⟶ dst r)
    (b : ∀ r, κ r → F.obj (src r))
    (hspan : ∀ r,
      Ideal.span (Set.range fun k => (F.map (a r)).hom (b r k)) = ⊤) :
    ∃ (j : ι) (hij : M.stage ≤ j)
        (b_j : ∀ r, κ r → (M.object (src r)).spreadStage (t := t)
          ((M.le_stage (src r)).trans hij)),
      (∀ r k, (M.object (src r)).stageToColimit H
          ⟨j, (M.le_stage (src r)).trans hij⟩ (b_j r k) = b r k) ∧
        ∀ r, Ideal.span (Set.range fun k =>
          (M.mapToStage hij).map (a r) (b_j r k)) = ⊤ := by
  classical
  let C : ∀ r, M.MapCoverStage (a r) (b r) := fun r =>
    Classical.choice (M.exists_mapCoverStage (a r) (b r) (hspan r))
  letI : Fintype ρ := Fintype.ofFinite ρ
  haveI := H.directed
  haveI := H.nonempty
  obtain ⟨j, hjall⟩ :=
    (insert M.stage (Finset.univ.image fun r => (C r).stage)).exists_le
  have hij : M.stage ≤ j := hjall M.stage (Finset.mem_insert_self _ _)
  have hC : ∀ r, (C r).stage ≤ j := fun r => hjall (C r).stage
    (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem (fun r => (C r).stage) (Finset.mem_univ r)))
  let b_j : ∀ r, κ r → (M.object (src r)).spreadStage (t := t)
      ((M.le_stage (src r)).trans hij) := fun r k =>
    (M.object (src r)).stageTransition H
      (P := ⟨(C r).stage, (M.le_stage (src r)).trans (C r).le_stage⟩)
      (Q := ⟨j, (M.le_stage (src r)).trans hij⟩) (hC r) ((C r).source k)
  have hb_j (r) (k) : (M.object (src r)).stageToColimit H
      ⟨j, (M.le_stage (src r)).trans hij⟩ (b_j r k) = b r k :=
    ((M.object (src r)).stageToColimit_stageTransition H
      ((M.le_stage (src r)).trans (C r).le_stage) (hC r) ((C r).source k)).trans
        ((C r).source_colimit k)
  have himage (r) : (fun k =>
      (M.mapToStage hij).map (a r) (b_j r k)) = fun k =>
      (M.object (dst r)).stageTransition H
        (P := ⟨(C r).stage, (M.le_stage (dst r)).trans (C r).le_stage⟩)
        (Q := ⟨j, (M.le_stage (dst r)).trans hij⟩) (hC r)
          ((M.object (src r)).mapAtLaterStage (M.object (dst r)) H
            (M.le_stage (src r)) (M.le_stage (dst r)) (C r).le_stage
              (M.map (a r)) ((C r).source k)) := by
    funext k
    change (M.object (src r)).mapAtLaterStage (M.object (dst r)) H
      (M.le_stage (src r)) (M.le_stage (dst r)) hij (M.map (a r)) (b_j r k) = _
    calc
      _ = (M.object (src r)).mapAtLaterStage (M.object (dst r)) H
          ((M.le_stage (src r)).trans (C r).le_stage)
          ((M.le_stage (dst r)).trans (C r).le_stage) (hC r)
          ((M.object (src r)).mapAtLaterStage (M.object (dst r)) H
            (M.le_stage (src r)) (M.le_stage (dst r)) (C r).le_stage
              (M.map (a r))) (b_j r k) := by
            rw [(M.object (src r)).mapAtLaterStage_trans (M.object (dst r)) H
              (M.le_stage (src r)) (M.le_stage (dst r))
              (C r).le_stage (hC r) (M.map (a r))]
      _ = _ := (M.object (src r)).mapAtLaterStage_stageTransition
        (M.object (dst r)) H
        ((M.le_stage (src r)).trans (C r).le_stage)
        ((M.le_stage (dst r)).trans (C r).le_stage) (hC r)
        ((M.object (src r)).mapAtLaterStage (M.object (dst r)) H
          (M.le_stage (src r)) (M.le_stage (dst r)) (C r).le_stage
            (M.map (a r))) ((C r).source k)
  refine ⟨j, hij, b_j, hb_j, fun r => ?_⟩
  letI : Algebra (𝒮 (M.object (dst r)).i₀)
      ((M.object (dst r)).spreadStage (t := t)
        ((M.le_stage (dst r)).trans (C r).le_stage)) :=
    ((algebraMap (𝒮 (C r).stage) _).comp
      (t ((M.le_stage (dst r)).trans (C r).le_stage)).toRingHom).toAlgebra
  letI : Algebra (𝒮 (M.object (dst r)).i₀)
      ((M.object (dst r)).spreadStage (t := t)
        ((M.le_stage (dst r)).trans hij)) :=
    ((algebraMap (𝒮 j) _).comp
      (t ((M.le_stage (dst r)).trans hij)).toRingHom).toAlgebra
  rw [himage r]
  exact span_range_map_eq_top
    ((M.object (dst r)).stageTransition H
      (P := ⟨(C r).stage, (M.le_stage (dst r)).trans (C r).le_stage⟩)
      (Q := ⟨j, (M.le_stage (dst r)).trans hij⟩) (hC r)).toRingHom
    (fun k => (M.object (src r)).mapAtLaterStage (M.object (dst r)) H
      (M.le_stage (src r)) (M.le_stage (dst r)) (C r).le_stage
        (M.map (a r)) ((C r).source k))
    (C r).image_span

/-- Move a spread functor to a stage where a finite principal cover on one chosen
object is represented. The cover relation, finite presentation of each principal
localization, and memberwise base-change recovery all hold at that same stage. -/
theorem SpreadData.FunctorModel.exists_principalCoverAtLaterStage
    (M : SpreadData.FunctorModel F H) (X : J)
    {κ : Type*} [Finite κ] (b : κ → F.obj X)
    (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (j : ι) (hij : M.stage ≤ j)
        (b_j : κ → (M.object X).spreadStage (t := t)
          ((M.le_stage X).trans hij)),
      (∀ k, (M.object X).stageToColimit H
          ⟨j, (M.le_stage X).trans hij⟩ (b_j k) = b k) ∧
        Ideal.span (Set.range b_j) = ⊤ ∧
        (∀ k, FinitePresentation (𝒮 j) (Localization.Away (b_j k))) ∧
        (letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
          ∀ k, Nonempty ((A ⊗[𝒮 j] Localization.Away (b_j k)) ≃ₐ[A]
            Localization.Away (b k))) := by
  obtain ⟨S, hij, b_j, hb_j, hspan_j⟩ :=
    (M.object X).exists_common_stageToColimit_eq_span_eq_top_atLaterStage H
      M.stage b hspan
  refine ⟨S.1, hij, b_j, hb_j, hspan_j,
    fun k => (M.object X).away_finitePresentation S.2 (b_j k), ?_⟩
  letI : Algebra (𝒮 S.1) A := (uA S.1).toRingHom.toAlgebra
  exact fun k => (M.object X).away_baseChange S.2 H (b_j k) (b k) (hb_j k)

end Functor

end Algebra
