import ModularCurves.ForMathlib.FinitePresentationLocalization

/-!
# Spreading finite principal affine covers

This file synchronizes finitely many functions in a spread model. If the functions
generate the unit ideal in the colimit algebra, they generate the unit ideal at a
later finite stage. Thus their principal localizations form an affine cover there,
and each member recovers the original principal open after base change.
-/

open TensorProduct

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
  {B : Type u} [CommRing B] [Algebra A B]

/-- Finitely many elements of the colimit algebra are represented simultaneously
in one spread model. -/
theorem SpreadData.exists_common_stageToColimit_eq
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {κ : Type*} [Finite κ] (b : κ → B) :
    ∃ (P : {i : ι // D.i₀ ≤ i})
        (b_i : κ → D.spreadStage (t := t) P.2),
      ∀ k, D.stageToColimit H P (b_i k) = b k := by
  classical
  letI : ∀ P : {i // D.i₀ ≤ i},
      Algebra (𝒮 D.i₀) (D.spreadStage (t := t) P.2) :=
    fun P => ((algebraMap (𝒮 P.1) (D.spreadStage (t := t) P.2)).comp
      (t P.2).toRingHom).toAlgebra
  letI : Algebra (𝒮 D.i₀) B :=
    ((algebraMap A B).comp (uA D.i₀).toRingHom).toAlgebra
  exact (D.isFilteredAlgColimit H).exists_common_lift b

/-- A finite family generating the unit ideal in the colimit algebra is represented
by a family generating the unit ideal at one later spread stage. -/
theorem SpreadData.exists_common_stageToColimit_eq_span_eq_top
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {κ : Type*} [Finite κ] (b : κ → B)
    (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (P : {i : ι // D.i₀ ≤ i})
        (b_i : κ → D.spreadStage (t := t) P.2),
      (∀ k, D.stageToColimit H P (b_i k) = b k) ∧
        Ideal.span (Set.range b_i) = ⊤ := by
  classical
  cases nonempty_fintype κ
  have hsurj : Function.Surjective (Fintype.linearCombination B b) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination B b).mp hspan
  obtain ⟨c, hc⟩ := hsurj 1
  let bc : κ ⊕ κ → B := Sum.elim b c
  obtain ⟨P, bc_i, hbc_i⟩ := D.exists_common_stageToColimit_eq H bc
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
  refine ⟨Q, b_j, fun k => ?_, (Ideal.eq_top_iff_one _).mpr ?_⟩
  · exact (D.stageToColimit_stageTransition H P.2 hPQ (b_i k)).trans
      (hbc_i (Sum.inl k))
  · rw [← hsum_stage]
    exact Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self k))

/-- A finite principal affine cover of a finitely presented colimit algebra descends
to a principal affine cover at one stage. Every member is finitely presented over the
stage base and is recovered by base change. -/
theorem IsFilteredAlgColimit.exists_spreadAwayCover
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    (B : Type u) [CommRing B] [Algebra A B] [FinitePresentation A B]
    {κ : Type*} [Finite κ] (b : κ → B)
    (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (D : SpreadData 𝒮 uA B) (i : ι) (h : D.i₀ ≤ i)
        (b_i : κ → D.spreadStage (t := t) h),
      (∀ k, D.stageToColimit H ⟨i, h⟩ (b_i k) = b k) ∧
        Ideal.span (Set.range b_i) = ⊤ ∧
        (∀ k, FinitePresentation (𝒮 i) (Localization.Away (b_i k))) ∧
        (letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
          ∀ k, Nonempty ((A ⊗[𝒮 i] Localization.Away (b_i k)) ≃ₐ[A]
            Localization.Away (b k))) := by
  classical
  obtain ⟨D⟩ := exists_spreadData B H
  obtain ⟨P, b_i, hb_i, hspan_i⟩ :=
    D.exists_common_stageToColimit_eq_span_eq_top H b hspan
  refine ⟨D, P.1, P.2, b_i, hb_i, hspan_i,
    fun k => D.away_finitePresentation P.2 (b_i k), ?_⟩
  letI : Algebra (𝒮 P.1) A := (uA P.1).toRingHom.toAlgebra
  exact fun k => D.away_baseChange P.2 H (b_i k) (b k) (hb_i k)

end Algebra
