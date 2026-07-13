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
  classical
  cases nonempty_fintype κ
  have hsurj : Function.Surjective (Fintype.linearCombination B b) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination B b).mp hspan
  obtain ⟨c, hc⟩ := hsurj 1
  let bc : κ ⊕ κ → B := Sum.elim b c
  obtain ⟨P, hiP, bc_i, hbc_i⟩ :=
    D.exists_common_stageToColimit_eq_atLaterStage H i bc
  let b_i : κ → D.spreadStage (t := t) P.2 := fun k => bc_i (Sum.inl k)
  let c_i : κ → D.spreadStage (t := t) P.2 := fun k => bc_i (Sum.inr k)
  have hsum_colimit :
      D.stageToColimit H P (∑ k, c_i k * b_i k) =
        D.stageToColimit H P 1 := by
    rw [map_sum, map_one]
    calc
      ∑ k, D.stageToColimit H P (c_i k * b_i k) =
          ∑ k, D.stageToColimit H P (c_i k) *
            D.stageToColimit H P (b_i k) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [map_mul]
      _ = ∑ k, c k * b k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [show D.stageToColimit H P (c_i k) = c k by
          exact hbc_i (Sum.inr k),
          show D.stageToColimit H P (b_i k) = b k by
            exact hbc_i (Sum.inl k)]
      _ = 1 := by
        simpa [Fintype.linearCombination_apply, smul_eq_mul] using hc
  letI : ∀ Q : {i // D.i₀ ≤ i},
      Algebra (𝒮 D.i₀) (D.spreadStage (t := t) Q.2) :=
    fun Q => ((algebraMap (𝒮 Q.1) (D.spreadStage (t := t) Q.2)).comp
      (t Q.2).toRingHom).toAlgebra
  letI : Algebra (𝒮 D.i₀) B :=
    ((algebraMap A B).comp (uA D.i₀).toRingHom).toAlgebra
  obtain ⟨Q, hPQ, hsum⟩ :=
    (D.isFilteredAlgColimit H).eq_at_stage _ _ hsum_colimit
  let b_j : κ → D.spreadStage (t := t) Q.2 :=
    fun k => D.stageTransition H hPQ (b_i k)
  let c_j : κ → D.spreadStage (t := t) Q.2 :=
    fun k => D.stageTransition H hPQ (c_i k)
  have hsum_stage : ∑ k, c_j k * b_j k = 1 := by
    calc
      ∑ k, c_j k * b_j k =
          D.stageTransition H hPQ (∑ k, c_i k * b_i k) := by
            simp [b_j, c_j, map_sum, map_mul]
      _ = D.stageTransition H hPQ 1 := hsum
      _ = 1 := map_one _
  refine ⟨Q, hiP.trans hPQ, b_j, fun k => ?_, (Ideal.eq_top_iff_one _).mpr ?_⟩
  · exact (D.stageToColimit_stageTransition H P.2 hPQ (b_i k)).trans
      (hbc_i (Sum.inl k))
  · rw [← hsum_stage]
    exact Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self k))

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
